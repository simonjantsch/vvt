{-# LANGUAGE PackageImports,FlexibleContexts, DeriveGeneric #-}
module RSM.NewRsmModule
    ( emptyRSM2
    , Point(..)
    , RSM2State(..)
    , runRsm2
    )
where

import Control.Monad
import Data.List.Extra
import Data.Map (Map)
import Data.Maybe
import Data.Ratio
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Prelude hiding (mapM,sequence)
import Test.QuickCheck

import Safe

newtype Point var = Point { pointToMap :: Map var Integer }

instance Arbitrary (Point Char) where
    arbitrary = do
      vals <- arbitrary
      return $ Point (Map.fromList $ zip "abcd" vals)

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

instance Arbitrary VarDiff where
    arbitrary = do
        i <- arbitrary :: Gen Int
        if (i `mod` 2) == 0
          then
              do val <- arbitrary
                 if val == 0
                   then return NoDiff
                   else return $ VarDiff val
          else return NoDiff

newtype Slope var = Slope (Map var VarDiff)

instance Show var => Show (Slope var) where
    show (Slope sl) = show sl

instance Arbitrary (Slope Char) where
    arbitrary = do
      vals <- arbitrary
      return $ Slope $ Map.fromList (zip "abcd" vals)

data Line var =
    Line
    { linePointOnLine :: Point var
    , lineSlope :: Slope var
    }

instance Arbitrary (Line Char) where
    arbitrary = do
      arbitraryPoint <- arbitrary
      arbitrarySlope <- arbitrary
      if getVarsSlope arbitrarySlope == getVars arbitraryPoint
        then return $ Line arbitraryPoint arbitrarySlope
        else arbitrary


instance Show var => Show (Line var) where
    show line =
        "point: " ++ (show $ linePointOnLine line) ++ "\n slope: " ++ (show $ lineSlope line)

data RSM2State loc var = RSM2State { rsmLocations :: Map loc (RSMLoc var)
                                   , rsmProducedLines :: [(Line var)]
                                   }

data RSMLoc var = RSMLoc { rsmLocPoints :: Set (Point var)
                         , rsmLocCandidateLines :: [(Line var, Integer)]
                         -- ^ The integer indicates how many points still have to be found for
                         -- the line to be proposed as a predicate
                         }

emptyRSM2 :: RSM2State loc var
emptyRSM2 =
    RSM2State
    { rsmLocations = Map.empty
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

getVarsLine :: Ord var => Line var -> [var]
getVarsLine (Line p0 _) = getVars p0

getVarsSlope :: Ord var => Slope var -> [var]
getVarsSlope (Slope varVarDiffMap) = Map.keys varVarDiffMap

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
            (\(mbNonConst, mbConst) ->
                 (catMaybes mbNonConst, catMaybes mbConst)) $
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
                         ((VarDiff _), NoDiff) -> (Nothing, Just var)
                         (NoDiff, (VarDiff _)) -> (Nothing, Nothing)
                         (NoDiff, NoDiff) -> (Nothing, Just var)
                         _ -> (Just var, Nothing)
                     ) (commonVars p0 point)
        allVarPairs = allDiffPairs nonConstantVars
        in
          constantVars ++
          foldr (\(var1, var2) sofar ->
                   let Just var1Diff = Map.lookup var1 slopePointP0
                       Just var2Diff = Map.lookup var2 slopePointP0
                   in case (var1Diff, var2Diff) of
                        (NoDiff, NoDiff) -> var1 : var2 : sofar
                        -- ^ If the values of point coincide exactly with the values of p0
                        -- in a pair of variables, point is on every line that goes through
                        -- p0 in these variables
                        (VarDiff _, VarDiff _) ->
                            let Just dxdySl1 = getCorrespSlope (var1, var2) (Slope lineSlope)
                                Just dxdySl2 = getCorrespSlope (var1, var2) (Slope slopePointP0)
                            in
                              if dxdySl1 == dxdySl2 -- || dxdySl1 == -dxdySl2 -- TODO: assure that this is right!
                                then var1 : var2 : sofar
                                else sofar
                        _ -> sofar
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

runRsm2 ::
    (Ord loc,Ord var, Show var)
    => loc
    -> Point var
    -> RSM2State loc var
    -> (RSM2State loc var, Set [(Integer, [(var, Integer)])])
runRsm2 loc newPoint st =
    case Set.member newPoint (rsmLocPoints rsmLoc) of
      True ->  (st, Set.empty)
      False ->
        let mbReducedPoint =
                dropVars (Set.fromList (concatMap (onLine newPoint) (rsmProducedLines st))) newPoint
        in
          case mbReducedPoint of
            Nothing -> (st, Set.empty)
            Just reducedPoint ->
             let (promoteOldCandidateLines, varsOnCandidateLines) =
                     unzip $
                     map (\(line, score) ->
                              case onLine reducedPoint line of
                                [] -> ((line, score), [])
                                vars -> ((line, score+1), vars)
                         ) (rsmLocCandidateLines rsmLoc)
                 mbPoint = dropVars (Set.fromList $ concat varsOnCandidateLines) reducedPoint
                 (newLines, newPoints) =
                     case mbPoint of
                       Nothing -> ([], Set.empty)
                       Just point -> getNewLinesAndDropPointsOnLines point (rsmLocPoints rsmLoc)
                 candidateLines = promoteOldCandidateLines ++ newLines
                 (linesToPromote, newCandidateLines) =
                     partition ((> 3) . snd) candidateLines
                 newPredicates =
                     Set.fromList $ map toSymmEqForm (fst $ unzip linesToPromote)
                 newRsmState =
                     st { rsmLocations =
                              Map.insert
                              loc
                              (RSMLoc newPoints newCandidateLines)
                              (rsmLocations st)
                        , rsmProducedLines = (rsmProducedLines st) ++ (fst $ unzip linesToPromote)
                        }
             -- putStrLn $ "Got new Point: " ++ (show point)
             -- putStrLn $ "Points in Location: " ++ (show $ rsmLocPoints rsmLoc)
             -- putStrLn $ "Produced new lines: " ++ (show $ map (toSymmEqForm . fst) newLines)
             in (newRsmState, newPredicates)

    where
      --TODO: check how this was done before
      rsmLoc = fromMaybe emptyLoc (Map.lookup loc (rsmLocations st))

      getNewLinesAndDropPointsOnLines ::
          Ord var
          => Point var
          -> Set (Point var)
          -> ([(Line var, Integer)], Set (Point var))
      getNewLinesAndDropPointsOnLines newPoint points
          | points == Set.empty = ([], Set.singleton newPoint)
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
                                       ) (Set.insert newPoint points) ptsToAlter
              in (newLines, newPoints)

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
                                         updateVarsToDrop newPoint $
                                         ptsWithVarsToDropSofar
                                       )
                          ) (0, Map.empty) (Set.delete firstPoint points)
            candVarSetListWithPointsOnNumber =
                Map.fromList $ Map.elems $
                Map.map (\varSet1 ->
                             ( varSet1
                             , Map.size $
                                  Map.filter
                                  (\varSet2 -> varSet2 `Set.isSubsetOf` varSet1)
                                  pointsToAlter
                             )
                        ) pointsToAlter
            mbBestVarSet = fmap fst (lastMay $ sortOn snd (Map.toList candVarSetListWithPointsOnNumber))
        in
          case join $ fmap (flip reduceLineToVars inducedLineByFirstPoint) mbBestVarSet of
            Just reducedLine ->
                let firstPointLineWithScore =
                        case score of
                          0 -> []
                          nonEmptyScore ->
                              [(reducedLine, nonEmptyScore+2)]
                    (linesByOtherPoints, addPtsToAlter) =
                        getNewLines newPoint (Set.delete firstPoint points)
                in ( firstPointLineWithScore ++ linesByOtherPoints
                   , Map.unionWith Set.union pointsToAlter addPtsToAlter
                   )
            Nothing -> getNewLines newPoint (Set.delete firstPoint points)

-- | Reduces Point to the variables not in vars. If point is empty hereafter
-- Nothing is returned
dropVars :: Ord var => Set var -> Point var -> Maybe (Point var)
dropVars vars point@(Point varValMap) =
    let newVarValMap = Map.filterWithKey (\var _ -> not (Set.member var vars)) varValMap
    in
      case null newVarValMap of
        True -> Nothing
        False -> Just $ Point newVarValMap

reduceLineToVars :: Ord var => Set var -> Line var -> Maybe (Line var)
reduceLineToVars vars line@(Line p0 (Slope slope)) =
    let reducedPoint = reducePointToVars (linePointOnLine line) (Set.toList vars)
    in case null (pointToMap reducedPoint) of
         True -> Nothing
         False -> Just $ Line reducedPoint reducedSlope
    where
      reducedSlope = Slope $ Map.filterWithKey (\var _ -> elem var vars) slope

prop_onLine1 :: Line Char -> Property
prop_onLine1 l1 =
    (==>) (nonConstantVars l1 > 2) (onLine (linePointOnLine l1) l1 == getVarsLine l1)

nonConstantVars line =
    length (getNonconstVarsLine line)
    where
      getNonconstVarsLine (Line _ (Slope vardiffMap)) =
          map fst $
          filter (\(_, vardiff) ->
                 case vardiff of
                   NoDiff -> False
                   VarDiff _ -> True
                 ) (Map.toList vardiffMap)
