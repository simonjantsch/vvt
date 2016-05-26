{-# LANGUAGE PackageImports,FlexibleContexts, DeriveGeneric #-}
module RSM.OldRsmModule
    ( emptyRSM1
    , RSM1State(..)
    ,runRsm1
    )
where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe(catMaybes)
import Data.Set (Set)
import qualified Data.Set as Set
import Language.SMTLib2
import "mtl" Control.Monad.State (runStateT,modify)
import "mtl" Control.Monad.Trans (lift)
import Prelude hiding (mapM,sequence)
import Data.Traversable (mapM,sequence)

import Safe (headMay)

data RSM1State loc var = RSM1State { rsmLocations :: Map loc (RSMLoc var) }

data RSMLoc var = RSMLoc { rsmClasses :: Map (Set var) (Set (Map var Integer))
                         }

instance Show var => Show (RSMLoc var) where
    show loc = show (rsmClasses loc)

data Coeffs b var = Coeffs { coeffsVar :: Map var (Expr b IntType)
                           , coeffsConst :: Expr b IntType
                           }

emptyRSM1 :: RSM1State loc var
emptyRSM1 = RSM1State Map.empty

addRSMState ::
    (Ord loc,Ord var)
    => loc
    -> Map var Integer
    -> RSM1State loc var
    -> RSM1State loc var
addRSMState loc instrs st
  = st { rsmLocations = Map.map (\loc -> loc {rsmClasses = mergeClassesWithOverlappingVars 5 (rsmClasses loc)}) $
                        Map.insertWith
                        joinLoc
                        loc
                        (RSMLoc { rsmClasses = Map.singleton (Map.keysSet instrs) (Set.singleton instrs)})
                        (rsmLocations st)
       }
  where
    joinLoc :: Ord var => RSMLoc var -> RSMLoc var -> RSMLoc var
    joinLoc l1 l2 = RSMLoc { rsmClasses = Map.unionWith Set.union (rsmClasses l1) (rsmClasses l2)
                           }
mergeClassesWithOverlappingVars ::
    Ord var =>
    Int
 -> Map (Set var) (Set (Map var Integer))
 -> Map (Set var) (Set (Map var Integer))
mergeClassesWithOverlappingVars count classes =
    case headMay (Map.assocs classes) of
      Nothing -> Map.empty
      Just (varSet, states) ->
          let (newClassStates, keysMerged) =
                  Map.foldrWithKey (\newVarSet newStates (newClassStates, keysMerged) ->
                                        case Set.size (Set.intersection varSet newVarSet) >= count of
                                          True -> (Set.union newStates newClassStates, newVarSet : keysMerged)
                                          False -> (newClassStates, keysMerged)
                                   ) (states, [varSet]) (Map.delete varSet classes)
              newKey = foldr Set.union Set.empty keysMerged
              leftOver =
                  Map.difference
                  classes
                  (Map.fromList . catMaybes $ map (\k -> fmap ((,) k) (Map.lookup k classes)) keysMerged)
          in Map.insert newKey newClassStates (mergeClassesWithOverlappingVars count leftOver)


createCoeffs :: (Backend b,Ord var) => Set var -> SMT b (Coeffs b var)
createCoeffs instrs = do
  coeffs <- mapM (\instr -> do
                     c <- declareVar int
                     return (instr,c)
                 ) (Set.toAscList instrs)
  c <- declareVar int
  return $ Coeffs { coeffsVar = Map.fromAscList coeffs
                  , coeffsConst = c
                  }

notAllZero :: Backend b => Coeffs b var -> SMT b (Expr b BoolType)
notAllZero coeffs = or' [ not' (c .==. cint 0)
                        | c <- Map.elems (coeffsVar coeffs) ]

createLine :: (Backend b,Ord var)
              => Coeffs b var -> Map var Integer -> SMT b (Expr b BoolType)
createLine coeffs vars = do
  lhs <- case Map.elems $ Map.intersectionWith (\c i -> c .*. cint i
                                               ) (coeffsVar coeffs) vars of
         [x] -> x
         xs -> plus xs
  let rhs = coeffsConst coeffs
  lhs .==. rhs

createLines :: (Backend b,Ord var) => Coeffs b var -> Set (Map var Integer)
               -> SMT b (Map (ClauseId b) (Map var Integer))
createLines coeffs points = do
  res <- mapM
         (\point ->
              let pointVarsAndCoeffsAreDisjoint =
                      null $
                      Set.intersection (Map.keysSet $ coeffsVar coeffs) (Map.keysSet point)
              in case pointVarsAndCoeffsAreDisjoint  of
                   True -> return Nothing
                   False -> do
                     cid <- createLine coeffs point >>= assertId
                     return $ Just (cid,point)
              ) (Set.toList points)
  return $ Map.fromList $ catMaybes res

extractLine :: (Backend b,Ord var) => Coeffs b var
            -> SMT b (Integer,[(var,Integer)])
extractLine coeffs = do
  rcoeffs <- mapM getValue (coeffsVar coeffs)
  IntValue rconst <- getValue (coeffsConst coeffs)
  return (rconst,[ (var,val)
                 | (var,IntValue val) <- Map.toList rcoeffs
                 , val/=0 ])


mineStates ::
    (Backend b, SMTMonad b ~ IO, Ord var, Show var)
    => IO b
    -> RSM1State loc var
    -> IO (RSM1State loc var,[(Integer,[(var,Integer)])])
mineStates backend st
  = runStateT
    (do
        nlocs <- mapM (\loc -> do
                          newclasses <-
                              sequence $
                              Map.mapWithKey
                                     (\vars cls -> do
                                        (newclass, nprops) <- lift $ mineClass vars cls
                                        modify (nprops++)
                                        return newclass
                                     )(rsmClasses loc)
                          return $ RSMLoc newclasses
                      ) (rsmLocations st)
        return $ RSM1State nlocs
    ) []
  where
    mineClass vars cls
      | Set.size cls <= 2 = return (cls, [])
      | Set.size cls > 6 = return (Set.empty, [])
    mineClass vars cls = do
      withBackendExitCleanly backend $ do
        setOption (ProduceUnsatCores True)
        setOption (ProduceModels True)
        let varPairs =
                map Set.fromList [[var1, var2] |
                                  var1 <- (Set.toList vars)
                                 , var2 <- (Set.toList vars)
                                 , var1 /= var2]
        individualLines <-
            mapM
            (\vars ->
                 stack $ do
                   coeffs <- createCoeffs vars
                   notAllZero coeffs >>= assert
                   revMp <- createLines coeffs cls
                   res <- checkSat
                   case res of
                     Sat -> do
                        line <- extractLine coeffs
                        return [line]
                     Unsat -> return []
            )(vars : varPairs)
        case individualLines of
           [] -> return (cls, [])
           _ -> return (Set.empty, Set.toList . Set.fromList $ foldr (++) [] individualLines)

runRsm1 ::
    (Backend b, SMTMonad b ~ IO, Ord var, Show var, Ord loc)
    => IO b
    -> loc
    -> Map var Integer
    -> RSM1State loc var
    -> IO (RSM1State loc var, [(Integer, [(var,Integer)])])
runRsm1 backend location state oldRsmState =
    mineStates backend (addRSMState location state oldRsmState)
