{-# LANGUAGE PackageImports,FlexibleContexts, DeriveGeneric #-}
module RSM where

import Args

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Language.SMTLib2
import Language.SMTLib2.Internals.Backend (SMTMonad)
import qualified Language.SMTLib2.Internals.Interface as I
import Language.SMTLib2.Internals.Embed
import "mtl" Control.Monad.State (runStateT,modify, get)
import "mtl" Control.Monad.Trans (lift, MonadIO)
import Prelude hiding (mapM,sequence)
import Data.Aeson as A
import Data.Traversable (mapM,sequence)
import Data.GADT.Show
import Data.GADT.Compare
import qualified Data.Text as T
import Data.Time.Clock

import GHC.Generics as G

newtype CollectedStates =
    CollectedStates
    { unpackCollectedStates :: Map T.Text [[Either Bool Integer]] }
    deriving G.Generic

instance A.ToJSON CollectedStates


data RSMState loc var = RSMState { rsmLocations :: Map loc (RSMLoc var)
                                 , rsmStates :: CollectedStates
                                 , rsmTiming :: NominalDiffTime
                                 , rsmProducedLines :: Set (Integer,[(var,Integer)])
                                 }

data RSMLoc var = RSMLoc { rsmClasses :: Map (Set var) (Set (Map var Integer))
                         }

data Coeffs b var = Coeffs { coeffsVar :: Map var (Expr b IntType)
                           , coeffsConst :: Expr b IntType
                           }

emptyRSM :: RSMState loc var
emptyRSM = RSMState Map.empty (CollectedStates Map.empty) 0 Set.empty

addRSMState :: (Ord loc,Ord var) => loc -> Map var Integer -> (Set T.Text, [Either Bool Integer])
               -> RSMState loc var -> RSMState loc var
addRSMState loc instrs (pc, concr_state) st
  = st { rsmLocations = Map.insertWith
                        joinLoc
                        loc
                        (RSMLoc { rsmClasses = Map.singleton (Map.keysSet instrs) (Set.singleton instrs)})
                        (rsmLocations st)
       , rsmStates = CollectedStates $
                     Map.insertWithKey
                     (\_ new_val old_val -> ((head new_val) : old_val))
                     (head (Set.toList pc))
                     [concr_state]
                     (unpackCollectedStates $ rsmStates st)
       }
  where
    joinLoc :: Ord var => RSMLoc var -> RSMLoc var -> RSMLoc var
    joinLoc l1 l2 = RSMLoc { rsmClasses = Map.unionWith Set.union (rsmClasses l1) (rsmClasses l2)
                           }

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
notAllZero coeffs = do
  args <- sequence [ I.constant (0::Integer) >>=
                     embed.(c :==:) >>=
                     embed.Not
                   | c <- Map.elems (coeffsVar coeffs) ]
  embed $ OrLst args

createLine :: (Backend b,Ord var, MonadIO (SMTMonad b))
              => Coeffs b var -> Map var Integer -> SMT b (Expr b BoolType)
createLine coeffs vars = do
  lhs <- case Map.elems $ Map.intersectionWith (\c i -> do
                                                   i' <- constant (IntValueC i)
                                                   embed $ c I.:*: i'
                                               ) (coeffsVar coeffs) vars of
         [x] -> x
         xs -> do
           rxs <- sequence xs
           embed $ PlusLst rxs
  let rhs = coeffsConst coeffs
      line = lhs :==: rhs
  --liftIO $ putStrLn (show line)
  embed $ line

createLines :: (Backend b,Ord var, MonadIO (SMTMonad b)) => Coeffs b var -> Set (Map var Integer)
               -> SMT b (Map (ClauseId b) (Map var Integer))
createLines coeffs points = do
  res <- mapM (\point -> do
                  cid <- createLine coeffs point >>= assertId
                  return (cid,point)
              ) (Set.toList points)
  return $ Map.fromList res

newtype RSMVars var e = RSMVars (Map var (e IntType))

data RSMVar :: * -> Type -> * where
  RSMVar :: var -> RSMVar var IntType

deriving instance Show var => Show (RSMVar var tp)

instance Show var => GShow (RSMVar var) where
  gshowsPrec = showsPrec

instance Eq var => GEq (RSMVar var) where
  geq (RSMVar v1) (RSMVar v2) = if v1==v2
                                then Just Refl
                                else Nothing

instance Ord var => GCompare (RSMVar var) where
  gcompare (RSMVar v1) (RSMVar v2) = case compare v1 v2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT

instance (Show var,Ord var) => Composite (RSMVars var) where
  type CompDescr (RSMVars var) = Map var ()
  type RevComp (RSMVars var) = RSMVar var
  compositeType mp = RSMVars (fmap (const IntRepr) mp)
  foldExprs f (RSMVars mp) = do
    mp' <- sequence $ Map.mapWithKey
           (\var -> f (RSMVar var)) mp
    return (RSMVars mp')
  createComposite f mp = do
    mp' <- sequence $ Map.mapWithKey (\instr _ -> f IntRepr (RSMVar instr)) mp
    return (RSMVars mp')
  accessComposite (RSMVar instr) (RSMVars mp) = mp Map.! instr
  eqComposite (RSMVars mp1) (RSMVars mp2) = do
    res <- sequence $ Map.elems $ Map.intersectionWith
           (\e1 e2 -> embed $ e1 :==: e2) mp1 mp2
    case res of
      [] -> embedConst (BoolValueC True)
      [e] -> return e
      _ -> embed $ AndLst res
  revType _ _ (RSMVar _) = IntRepr

instance GetType (RSMVar v) where
  getType (RSMVar _) = IntRepr

extractLine :: (Backend b,Ord var) => Coeffs b var
            -> SMT b (Integer,[(var,Integer)])
extractLine coeffs = do
  rcoeffs <- mapM getValue (coeffsVar coeffs)
  IntValueC rconst <- getValue (coeffsConst coeffs)
  return (rconst,[ (var,val)
                 | (var,IntValueC val) <- Map.toList rcoeffs
                 , val/=0 ])

mineStates ::
    (Backend b, SMTMonad b ~ IO, Ord var, Show var)
    => IO b
    -> [Set var]
    -> RSMState loc var
    -> IO (RSMState loc var,[(Integer,[(var,Integer)])])
mineStates backend relevantVarSubsets st
  = runStateT
    (do
        nlocs <- mapM (\loc -> do
                          newclasses <-
                              sequence $
                              Map.mapWithKey
                                     (\_vars cls -> do
                                        (newclass, nprops) <- lift $ mineClass cls
                                        props <- get
                                        --liftIO $ putStrLn $ "##\n\n" ++ (show props) ++ "\n\n##"
                                        modify (nprops++)
                                        return newclass
                                     )(rsmClasses loc)
                          return $ RSMLoc newclasses
                      ) (rsmLocations st)
        return $ st { rsmLocations = nlocs }
    ) []
  where
    mineClass cls
      | Set.size cls <= 2 = return (cls, [])
      | Set.size cls > 6 = return (Set.empty, [])
    mineClass cls = do
      withBackendExitCleanly backend $ do
        setOption (ProduceUnsatCores True)
        setOption (ProduceModels True)
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
            ) relevantVarSubsets
        case individualLines of
           [] -> return (cls, [])
           _ -> return (Set.empty, Set.toList . Set.fromList $ foldr (++) [] individualLines)
