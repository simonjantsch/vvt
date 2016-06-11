module RSM.RSM
    ( CollectedStates(..)
    , RSM(..)
    , emptyRsm
    , runRsm
    )
where

import RSM.OldRsmModule
import RSM.NewRsmModule

import Data.Map (Map)
import Data.Set (Set)
import Language.SMTLib2.Pipe
import qualified Data.Map as Map
import qualified Data.Set as Set

newtype CollectedStates loc =
    CollectedStates
    { unpackCollectedStates :: Map loc [[Either Bool Integer]] }

data RSM loc var =
    RSM { rsm_collectedStates :: CollectedStates loc
        , rsm_Rsm1State :: RSM1State loc var
        , rsm_Rsm2State :: RSM2State loc var
        }

emptyRsm :: RSM loc var
emptyRsm = RSM (CollectedStates Map.empty) emptyRSM1 emptyRSM2

runRsm ::
    (Show loc, Ord loc, Show var, Ord var)
    => RSM loc var
    -> loc
    -> Map var Integer
    -> [(Either Bool Integer)]
    -> Bool -- ^ only use newRSM
    -> Bool -- ^ only use oldRSM
    -> IO (RSM loc var, Set ([(Integer, [(var,Integer)])]))
runRsm oldRsmState loc partState fullState onlyNew onlyOld =
    do (newRsm, newPreds) <-
           case (onlyNew, onlyOld) of
             (True, True) -> error "you cannot put both onlyNewRSM and onlyOldRSM on true"
             (False, True) ->
                 do (newRsm1, rsm1Preds) <- runOldRSM
                    return $ (RSM newCollectedStates newRsm1 emptyRSM2, Set.singleton rsm1Preds)
             (True, False) ->
                 let (newRsm2, rsm2Preds) = runNewRSM
                 in return $ (RSM newCollectedStates emptyRSM1 newRsm2, rsm2Preds)
             _ ->
                 do (newRsm1, rsm1Preds) <- runOldRSM
                    let (newRsm2, rsm2Preds) = runNewRSM
                    return $ (RSM newCollectedStates newRsm1 newRsm2, Set.insert rsm1Preds rsm2Preds)
       return $ (newRsm, newPreds)
    where
      oldRsm1 = rsm_Rsm1State oldRsmState
      oldRsm2 = rsm_Rsm2State oldRsmState
      newCollectedStates =
          CollectedStates $
          Map.insertWith
          (\new_val old_val -> ((head new_val) : old_val))
          loc
          [fullState]
          (unpackCollectedStates $ rsm_collectedStates oldRsmState)
      runOldRSM = runRsm1 (createPipe "z3" ["-smt2","-in"]) loc partState oldRsm1
      runNewRSM = runRsm2 loc (Point partState) oldRsm2
