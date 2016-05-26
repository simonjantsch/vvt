{-# LANGUAGE DeriveGeneric #-}
module RSM.RSM
    ( CollectedStates(..)
    , RSM(..)
    , emptyRsm
    , runRsm
    )
where

import RSM.OldRsmModule

--import Data.Aeson as A
import Data.Map (Map)
import GHC.Generics as G
import Language.SMTLib2.Pipe
import qualified Data.Map as Map


newtype CollectedStates loc =
    CollectedStates
    { unpackCollectedStates :: Map loc [[Either Bool Integer]] }
    deriving G.Generic

--instance A.ToJSON loc => A.ToJSON (CollectedStates loc) where

data RSM loc var =
    RSM { rsm_collectedStates :: CollectedStates loc
        , rsm_Rsm1State :: RSM1State loc var
--        , rsm_newRsmState :: NewRsmState loc var
        }

emptyRsm :: RSM loc var
emptyRsm = RSM (CollectedStates Map.empty) emptyRSM1 -- emptyNewRsmState

runRsm ::
    (Show loc, Ord loc, Ord var)
    => RSM loc var
    -> loc
    -> Map var Integer
    -> [(Either Bool Integer)]
    -> IO ((RSM loc var, [(Integer, [(var,Integer)])]))
runRsm oldRsmState loc partState fullState =
    do (newRsm1, rsm1Preds) <-
           runRsm1 (createPipe "z3" ["-smt2","-in"]) loc partState oldRsm1
       --let (rsm2Preds, newRsm2) = handleNewStateRsm2 partState loc
       let newRsm = RSM newCollectedStates newRsm1
       return $ (newRsm, rsm1Preds)
    where
      oldRsm1 = rsm_Rsm1State oldRsmState
      newCollectedStates =
          CollectedStates $
          Map.insertWith
          (\new_val old_val -> ((head new_val) : old_val))
          loc
          [fullState]
          (unpackCollectedStates $ rsm_collectedStates oldRsmState)


-- type Line var = (Integer, [(var,Integer)])

-- class Monad m => RsmModule r m where
--     type RsmState r
--     handleNewProgramState :: RsmState r -> ProgramState -> m (RsmState r, [Predicate])

-- runPredicateExtractors ::
--     MonadIO m
--     => ProgramState
--     -> [AnyRsmModule]
--     -> m ([AnyRsmModule], [Predicate])
-- runPredicateExtractors state rsmModules =
--     forM rsmModules $ \(MkGenericRsmModule r) -> do
--       newRsmState <- handleNewProgramState state r
