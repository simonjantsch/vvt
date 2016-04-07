{-# LANGUAGE PackageImports,FlexibleContexts, DeriveGeneric #-}
module RSM where

import Args

import Data.List (intersect, partition)
import Data.Map (Map)
import Data.Maybe
import Data.Ratio
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Language.SMTLib2
import Language.SMTLib2.Internals.Backend (SMTMonad)
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Interface hiding (constant)
import qualified Language.SMTLib2.Internals.Interface as I
import Language.SMTLib2.Internals.Embed
import "mtl" Control.Monad.State (runStateT,modify, get)
import "mtl" Control.Monad.Trans (lift, liftIO, MonadIO)
import Prelude hiding (mapM,sequence)
import Data.Traversable (mapM,sequence)
import Data.GADT.Show
import Data.GADT.Compare
import qualified Data.Text as T
import Data.Time.Clock

import GHC.Generics as G

newtype Point var = Point { pointToMap :: Map var Integer }

instance Eq var => Eq (Point var) where
    p1 == p2 =
        pointToMap p1 == pointToMap p2

instance Ord var => Ord (Point var) where
    compare p1 p2 =
        compare (pointToMap p1) (pointToMap p2)

instance Show var => Show (Point var) where
    show p = show (pointToMap p)

data VarDiff = VarDiff Integer
             | NoDiff deriving Show

newtype Slope var = Slope (Map var VarDiff)

instance Show var => Show (Slope var) where
    show (Slope sl) = show sl

data Line var =
    Line
    { linePointOnLine :: Point var
    , lineSlope :: Slope var
    }

instance Show var => Show (Line var) where
    show line =
        "point: " ++ (show $ linePointOnLine line) ++ "\n slope: " ++ (show $ lineSlope line)

data RSMState loc var = RSMState { rsmLocations :: Map loc (RSMLoc var)
                                 -- , rsmProgramVarDepMap :: Map AnyLispName (Set AnyLispName)
                                 , rsmTiming :: NominalDiffTime
                                 , rsmProducedLines :: [(Line var)]
                                 }

data RSMLoc var = RSMLoc { rsmLocPoints :: Set (Point var)
                         , rsmLocCandidateLines :: [(Line var, Integer)]
                         -- ^ The integer indicates how many points still have to be found for
                         -- the line to be proposed as a predicate
                         }

-- emptyRSM :: LispProgram -> RSMState loc var
emptyRSM =
    -- let varDepMap = buildVarDependencyGraph prog
    -- in
    RSMState
    { rsmLocations = Map.empty
    -- , rsmProgramVarDepMap = varDepMap
    , rsmTiming = 0
    , rsmProducedLines = []
    }

emptyLoc :: RSMLoc var
emptyLoc =
    RSMLoc
    { rsmLocPoints = Set.empty
    , rsmLocCandidateLines = []
    }

-- | Returns the difference of two points in the variable var, if
-- any of the points does not contain the variable, it returns Nothing
getDiffRegardingVar :: Ord var => var -> Point var -> Point var -> Maybe VarDiff
getDiffRegardingVar var point1 point2 =
    case (getPointValue point1 var, getPointValue point2 var) of
      (Just val1, Just val2) ->
          case val1 - val2 of
            0 -> Just $ NoDiff
            someVal -> Just $ VarDiff someVal
      _ -> Nothing

getSlopeBetweenPoints :: Ord var => Point var -> Point var -> Slope var
getSlopeBetweenPoints p1 p2 =
    Slope $
    Map.fromList $
    mapMaybe (\var -> fmap ((,) var) (getDiffRegardingVar var p1 p2)) (commonVars p1 p2)

-- | Returns all the Variables that a given Point is defined in
getVars :: (Ord var) => Point var -> [var]
getVars (Point varValMap) = Map.keys varValMap

commonVars :: (Ord var) => Point var -> Point var -> [var]
commonVars p1 p2 = intersect (getVars p1) (getVars p2)

getPointValue :: (Ord var) => Point var -> var -> Maybe Integer
getPointValue point var = Map.lookup var (pointToMap point)

inducedLine :: (Ord var) => Point var -> Point var -> Line var
inducedLine p1 p2 =
    Line
    { linePointOnLine = reducePointToVars p1 (commonVars p1 p2)
    , lineSlope = getSlopeBetweenPoints p1 p2
    }

reducePointToVars :: (Ord var) => Point var -> [var] -> Point var
reducePointToVars (Point varValMap) vars =
    Point $ Map.filterWithKey (\var _ -> elem var vars) varValMap

toSymmEqForm :: Ord var => Line var -> [(Integer, [(var,Integer)])]
toSymmEqForm line@(Line p0 (Slope slopeMap)) =
    let constantVars = Map.filter (\varDiff -> case varDiff of
                                                 NoDiff -> True
                                                 _ -> False
                                  ) slopeMap
        dropConstantsFromVars = Map.difference slopeMap constantVars
        lcmVarDiffs =
            Map.foldr (\(VarDiff newVd) lcmSofar -> lcm (abs newVd) lcmSofar) 1 dropConstantsFromVars
    in map (\constVar ->
           let Just constVal = Map.lookup constVar (pointToMap p0)
           in (constVal, [(constVar, 1)])
           ) (Map.keys constantVars)
       ++
       (
       Map.elems $
       Map.mapWithKey (\var _ ->
                    let c = valThis * (round $ lcmVarDiffs % varDiffThis) * signCorrVd1
                            - valNext * (round $ lcmVarDiffs % varDiffNext) * signCorrVd2
                        coeffThis = signCorrVd1 * (round $ lcmVarDiffs % varDiffThis)
                        coeffNext = (- signCorrVd2) * (round $ lcmVarDiffs % varDiffNext)

                        Just valThis = Map.lookup var (pointToMap p0)
                        Just (VarDiff varDiffThis) = Map.lookup var slopeMap
                        signCorrVd1 = signOf varDiffThis

                        idxThis = Map.findIndex var dropConstantsFromVars
                        idxNext = idxThis +1
                        varNext = fst $ Map.elemAt idxNext dropConstantsFromVars
                        Just valNext = Map.lookup varNext (pointToMap p0)
                        Just (VarDiff varDiffNext) = Map.lookup varNext slopeMap
                        signCorrVd2 = signOf varDiffNext

                        signOf int =
                            case int < 0 of
                              True -> -1
                              False -> 1

                    in (c, [(var, coeffThis), (varNext, coeffNext)])
               ) (Map.deleteMax dropConstantsFromVars)
       )

-- | OnLine checks if Point p is on Line l in any Subdimension of
-- the variables.
-- For Example (1,0,1) shoule be on Line (2,1,0) + (-1,-1,-1)*t
-- in the subdimension (x1,x2), thus [x1,x2] should be returned.
onLine :: (Ord var) => Point var -> Line var -> [var]
onLine point line@(Line p0 (Slope lineSlope)) =
    let (Slope slopePointP0) = getSlopeBetweenPoints point p0
        (nonConstantVars, constantVars) =
            (\(mbNonConst, mbConst) -> (catMaybes mbNonConst, catMaybes mbConst)) $
            unzip $
            map (\var ->
                     let Just varDiffSlopeLine = Map.lookup var lineSlope
                         Just varDiffPointP0 = Map.lookup var slopePointP0
                     -- | Gather relevant variables out of the common variables.
                     -- Variables that are constant in one slope
                     -- and nonconstant in the other can be discarded
                     -- Lookup ist guaranteed to succeed, because all variables are
                     -- from the common variables.
                     in
                       case (varDiffSlopeLine, varDiffPointP0) of
                         ((VarDiff _), NoDiff) -> (Nothing, Nothing)
                         (NoDiff, (VarDiff _)) -> (Nothing, Nothing)
                         (NoDiff, NoDiff) -> (Nothing, Just var)
                         _ -> (Just var, Nothing)
                ) (commonVars p0 point)
        allVarPairs = allDiffPairs nonConstantVars
        in
          constantVars ++
          foldr (\(var1, var2) sofar ->
                   let Just dxdySl1 = getCorrespSlope (var1, var2) (Slope lineSlope)
                       Just dxdySl2 = getCorrespSlope (var1, var2) (Slope slopePointP0)
                   in
                     if dxdySl1 == dxdySl2 || dxdySl1 == -dxdySl2
                     then var1 : var2 : sofar
                     else sofar
              ) [] allVarPairs
    where
      getCorrespSlope :: (Ord var) => (var, var) -> Slope var -> Maybe Rational
      getCorrespSlope (var1, var2) (Slope slope) =
          let mbVar1Diff = Map.lookup var1 slope
              mbVar2Diff = Map.lookup var2 slope
          in
            case (mbVar1Diff, mbVar2Diff) of
              (Just (VarDiff var1Diff), Just (VarDiff var2Diff)) ->
                  Just $ var1Diff % var2Diff
              _ -> Nothing

      allDiffPairs [] = []
      allDiffPairs (x:[]) = []
      allDiffPairs (x:xs) = [(x, y) | y <- xs] ++ (allDiffPairs xs)

addNewPoint ::
    (Ord loc,Ord var, Show var)
    => loc
    -> Point var
    -> RSMState loc var
    -> IO (RSMState loc var, Set [(Integer, [(var, Integer)])])
addNewPoint loc point st =
    case Set.member point (rsmLocPoints rsmLoc) of
      True ->  return (st, Set.empty)
      False -> do
        let onSomeLineAlready =
                any
                (\line -> onLine point line /= [])
                (rsmProducedLines st)
        if onSomeLineAlready
          then return (st, Set.empty)
          else do
            promoteOldCandidateLines <-
                mapM (\(line, score) -> do
                        putStrLn $ "Checking if point: " ++ show point
                                     ++ " is on line: " ++ show line
                        case onLine point line of
                          [] -> return (line, score)
                          _ -> return (line, score+1)
                     ) (rsmLocCandidateLines rsmLoc)
            let (newLines, newPoints) = getNewLinesAndDropPointsOnLines point (rsmLocPoints rsmLoc)
                candidateLines = promoteOldCandidateLines ++ newLines
                (linesToPromote, newCandidateLines) =
                    partition ((> 3) . snd) candidateLines
                newPredicates =
                    Set.fromList $ map toSymmEqForm (fst $ unzip linesToPromote)
                newRsmState =
                    st { rsmLocations =
                             Map.insert
                             loc
                             (RSMLoc (Set.insert point newPoints) newCandidateLines)
                             (rsmLocations st)
                       , rsmProducedLines = (rsmProducedLines st) ++ (fst $ unzip linesToPromote)
                       }
            putStrLn $ "Got new Point: " ++ (show point)
            putStrLn $ "Points in Location: " ++ (show $ rsmLocPoints rsmLoc)
            putStrLn $ "Produced new lines: " ++ (show $ map (toSymmEqForm . fst) newLines)
            return (newRsmState, newPredicates)

    where
      --TODO: check how this was done before
      rsmLoc = fromMaybe emptyLoc (Map.lookup loc (rsmLocations st))

      getNewLinesAndDropPointsOnLines ::
          Ord var
          => Point var
          -> Set (Point var)
          -> ([(Line var, Integer)], Set (Point var))
      getNewLinesAndDropPointsOnLines newPoint points
          | points == Set.empty = ([], Set.empty)
          | otherwise =
              let (newLines, ptsToAlter) = getNewLines newPoint points
                  newPoints =
                      Map.foldrWithKey (\pt varsToDrop oldPoints ->
                                            let newPointMbEmpty = dropVars varsToDrop pt
                                                dropOldPoint = Set.delete pt oldPoints
                                            in case newPointMbEmpty of
                                                 Nothing ->
                                                     dropOldPoint
                                                 Just newPoint ->
                                                     Set.insert newPoint dropOldPoint
                                       ) points ptsToAlter
              in (newLines, newPoints)
          where
            getNewLines ::
                Ord var
                => Point var
                -> Set (Point var)
                -> ([(Line var, Integer)], Map (Point var) (Set var))
            -- ^ Returns lines and a map indicating which variables
            -- where used in lines for every point that is on some line
            getNewLines newPoint points
                | points == Set.empty = ([], Map.empty)
                | otherwise =
                    let firstPoint = Set.elemAt 0 points
                        inducedLineByFirstPoint = inducedLine firstPoint newPoint
                        (score, pointsToAlter) =
                            Set.foldr (\pointToCheck sofar@(score, ptsWithVarsToDropSofar) ->
                                           case onLine pointToCheck inducedLineByFirstPoint of
                                             [] -> sofar
                                             varsOnLine ->
                                                 let updateVarsToDrop p =
                                                         Map.insertWith Set.union p (Set.fromList varsOnLine)
                                                 in
                                                   ( score+1
                                                   , updateVarsToDrop firstPoint $
                                                     updateVarsToDrop pointToCheck $
                                                     ptsWithVarsToDropSofar
                                                   )
                                      ) (0, Map.empty) (Set.delete firstPoint points)
                        firstPointLineWithScore =
                            case score of
                              0 -> []
                              nonEmptyScore ->
                                  [(inducedLineByFirstPoint, nonEmptyScore+2)]
                        (linesByOtherPoints, addPtsToAlter) =
                            getNewLines newPoint (Set.delete firstPoint points)
                    in ( firstPointLineWithScore ++ linesByOtherPoints
                       , Map.unionWith Set.union pointsToAlter addPtsToAlter
                       )

            -- | Reduces Point to the variables not in vars. If point is empty hereafter
            -- Nothing is returned
            dropVars :: Ord var => (Set var) -> Point var -> Maybe (Point var)
            dropVars vars point@(Point varValMap) =
                let newVarValMap = Map.filterWithKey (\var _ -> not (Set.member var vars)) varValMap
                in
                  case null newVarValMap of
                    True -> Nothing
                    False -> Just $ Point newVarValMap
-- addRSMState ::
--     (Ord loc,Ord var)
--     => loc
--     -> Point var
--     -> RSMState loc var
--     -> RSMState loc var
-- addRSMState loc instrs st
--   = st { rsmLocations = Map.insertWith
--                         joinLoc
--                         loc
--                         (RSMLoc { rsmClasses = Map.singleton (Map.keysSet instrs) (Set.singleton instrs)})
--                         (rsmLocations st)
--        }
--   where
--     joinLoc :: Ord var => RSMLoc var -> RSMLoc var -> RSMLoc var
--     joinLoc l1 l2 = RSMLoc { rsmClasses = Map.unionWith Set.union (rsmClasses l1) (rsmClasses l2)
--                            }

-- createCoeffs :: (Backend b,Ord var) => Set var -> SMT b (Coeffs b var)
-- createCoeffs instrs = do
--   coeffs <- mapM (\instr -> do
--                      c <- declareVar int
--                      return (instr,c)
--                  ) (Set.toAscList instrs)
--   c <- declareVar int
--   return $ Coeffs { coeffsVar = Map.fromAscList coeffs
--                   , coeffsConst = c
--                   }

-- notAllZero :: Backend b => Coeffs b var -> SMT b (Expr b BoolType)
-- notAllZero coeffs = do
--   args <- sequence [ I.constant (0::Integer) >>=
--                      embed.(c :==:) >>=
--                      embed.Not
--                    | c <- Map.elems (coeffsVar coeffs) ]
--   embed $ OrLst args

-- createLine :: (Backend b,Ord var, MonadIO (SMTMonad b))
--               => Coeffs b var -> Point var -> SMT b (Expr b BoolType)
-- createLine coeffs vars = do
--   lhs <- case Map.elems $ Map.intersectionWith (\c i -> do
--                                                    i' <- constant (IntValueC i)
--                                                    embed $ c I.:*: i'
--                                                ) (coeffsVar coeffs) vars of
--          [x] -> x
--          xs -> do
--            rxs <- sequence xs
--            embed $ PlusLst rxs
--   let rhs = coeffsConst coeffs
--       line = lhs :==: rhs
--   --liftIO $ putStrLn (show line)
--   embed $ line

-- createLines :: (Backend b,Ord var, MonadIO (SMTMonad b)) => Coeffs b var -> Set (Point var)
--                -> SMT b (Map (ClauseId b) (Point var))
-- createLines coeffs points = do
--   res <- mapM (\point -> do
--                   cid <- createLine coeffs point >>= assertId
--                   return (cid,point)
--               ) (Set.toList points)
--   return $ Map.fromList res

-- newtype RSMVars var e = RSMVars (Map var (e IntType))

-- data RSMVar :: * -> Type -> * where
--   RSMVar :: var -> RSMVar var IntType

-- deriving instance Show var => Show (RSMVar var tp)

-- instance Show var => GShow (RSMVar var) where
--   gshowsPrec = showsPrec

-- instance Eq var => GEq (RSMVar var) where
--   geq (RSMVar v1) (RSMVar v2) = if v1==v2
--                                 then Just Refl
--                                 else Nothing

-- instance Ord var => GCompare (RSMVar var) where
--   gcompare (RSMVar v1) (RSMVar v2) = case compare v1 v2 of
--     EQ -> GEQ
--     LT -> GLT
--     GT -> GGT

-- instance (Show var,Ord var) => Composite (RSMVars var) where
--   type CompDescr (RSMVars var) = Map var ()
--   type RevComp (RSMVars var) = RSMVar var
--   compositeType mp = RSMVars (fmap (const IntRepr) mp)
--   foldExprs f (RSMVars mp) = do
--     mp' <- sequence $ Map.mapWithKey
--            (\var -> f (RSMVar var)) mp
--     return (RSMVars mp')
--   createComposite f mp = do
--     mp' <- sequence $ Map.mapWithKey (\instr _ -> f IntRepr (RSMVar instr)) mp
--     return (RSMVars mp')
--   accessComposite (RSMVar instr) (RSMVars mp) = mp Map.! instr
--   eqComposite (RSMVars mp1) (RSMVars mp2) = do
--     res <- sequence $ Map.elems $ Map.intersectionWith
--            (\e1 e2 -> embed $ e1 :==: e2) mp1 mp2
--     case res of
--       [] -> embedConst (BoolValueC True)
--       [e] -> return e
--       _ -> embed $ AndLst res
--   revType _ _ (RSMVar _) = IntRepr

-- instance GetType (RSMVar v) where
--   getType (RSMVar _) = IntRepr

-- extractLine :: (Backend b,Ord var) => Coeffs b var
--             -> SMT b (Integer,[(var,Integer)])
-- extractLine coeffs = do
--   rcoeffs <- mapM getValue (coeffsVar coeffs)
--   IntValueC rconst <- getValue (coeffsConst coeffs)
--   return (rconst,[ (var,val)
--                  | (var,IntValueC val) <- Map.toList rcoeffs
--                  , val/=0 ])

-- mineStates ::
--     (Backend b, SMTMonad b ~ IO, Ord var, Show var)
--     => IO b
--     -- -> [Set var]
--     -> RSMState loc var
--     -> IO (RSMState loc var,[(Integer,[(var,Integer)])])
-- mineStates backend relevantVarSubsets st
--   = runStateT
--     (do
--         nlocs <- mapM (\loc -> do
--                           newclasses <-
--                               sequence $
--                               Map.mapWithKey
--                                      (\_vars cls -> do
--                                         (newclass, nprops) <- lift $ mineClass cls
--                                         props <- get
--                                         --liftIO $ putStrLn $ "##\n\n" ++ (show props) ++ "\n\n##"
--                                         modify (nprops++)
--                                         return newclass
--                                      )(rsmClasses loc)
--                           return $ RSMLoc newclasses
--                       ) (rsmLocations st)
--         return $ st { rsmLocations = nlocs }
--     ) []
--   where
--     mineClass cls
--       | Set.size cls <= 2 = return (cls, [])
--       | Set.size cls > 6 = return (Set.empty, [])
--     mineClass cls = do
--       --putStrLn "entered mineState"
--       withBackendExitCleanly backend $ do
--         setOption (ProduceUnsatCores True)
--         setOption (ProduceModels True)
--         -- let varPairs =
--         --         map Set.fromList [[var1, var2] |
--         --                           var1 <- (Set.toList vars)
--         --                          , var2 <- (Set.toList vars)
--         --                          , var1 /= var2]
--         individualLines <-
--             mapM
--             (\vars ->
--                  stack $ do
--                    coeffs <- createCoeffs vars
--                    notAllZero coeffs >>= assert
--                    revMp <- createLines coeffs cls
--                    res <- checkSat
--                    case res of
--                      Sat -> do
--                         --liftIO $ putStrLn "\n\n***found a Line***\n\n"
--                         line <- extractLine coeffs
--                         return [line]
--                      Unsat -> return []
--             ) relevantVarSubsets --(vars : varPairs)
--         case individualLines of
--            [] -> return (cls, [])
--            _ -> return (Set.empty, Set.toList . Set.fromList $ foldr (++) [] individualLines)


--                 --       core <- getUnsatCore
--                 --       let coreMp = Map.fromList [ (cid,()) | cid <- core ]
--                 --           coreLines = Set.fromList $ Map.elems $ Map.intersection revMp coreMp
--                 --       return $ Left coreLines
--                 -- case res of
--                 --   Right lines -> return (Just (Set.empty,[lines]))
--                 --   Left coreLines -> do
--                 --       let noCoreLines = Set.difference cls coreLines
--                 --           Just (coreLine1,coreLines1) = Set.minView coreLines
--                 --           Just (coreLine2,coreLines2) = Set.minView coreLines1
--                 --       res1 <- mineClass vars (Set.insert coreLine1 noCoreLines)
--                 --       case res1 of
--                 --         Just (ncls,lines) -> return (Just (Set.union coreLines1 ncls,lines))
--                 --         Nothing -> do
--                 --            res2 <- mineClass vars (Set.insert coreLine2 noCoreLines)
--                 --            case res2 of
--                 --              Just (ncls,lines) -> return (Just (Set.insert coreLine1 $
--                 --                                                 Set.union coreLines2 ncls,lines)
--                 --                                          )
--                 --              Nothing -> return Nothing
