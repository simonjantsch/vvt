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
    -> IO (RSM loc var, Set ([(Integer, [(var,Integer)])]))
runRsm oldRsmState loc partState fullState =
    do (newRsm1, rsm1Preds) <-
           runRsm1 (createPipe "z3" ["-smt2","-in"]) loc partState oldRsm1
       let (newRsm2, rsm2Preds) = runRsm2 loc (Point partState) oldRsm2
           newRsm = RSM newCollectedStates newRsm1 newRsm2
       return $ (newRsm, Set.insert rsm1Preds $ rsm2Preds)
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
