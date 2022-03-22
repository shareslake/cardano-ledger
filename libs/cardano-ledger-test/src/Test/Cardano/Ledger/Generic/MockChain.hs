{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Cardano.Ledger.Generic.MockChain where

import Cardano.Ledger.BaseTypes (ShelleyBase)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Era (Crypto))
import Cardano.Ledger.Keys (KeyHash, KeyRole (..))
import Cardano.Ledger.Shelley.LedgerState
  ( DPState (..),
    DState (..),
    EpochState (..),
    LedgerState (..),
    NewEpochState (..),
    PState (..),
    UTxOState (..),
  )
import Cardano.Ledger.Shelley.RewardUpdate (PulsingRewUpdate)
import Cardano.Ledger.Shelley.Rules.Ledger (LedgerEnv)
import Cardano.Ledger.Shelley.Rules.Ledgers (LEDGERS, LedgersEnv (..), LedgersEvent, LedgersPredicateFailure)
import Cardano.Ledger.Shelley.Rules.Rupd (RupdEnv)
import Cardano.Ledger.Shelley.Rules.Tick (TICK, TickEvent, TickPredicateFailure)
import Cardano.Slotting.Slot (EpochNo, SlotNo)
import Control.State.Transition
  ( Embed (..),
    STS (..),
    TRC (..),
    TransitionRule,
    judgmentContext,
    trans,
  )
import Data.Default.Class (Default)
import qualified Data.Map as Map
import Data.Maybe.Strict (StrictMaybe)
import Data.Sequence (Seq (..))
import GHC.Word (Word64)
import Test.Cardano.Ledger.Generic.Proof hiding (lift)

-- ================================================

data MOCKCHAIN era

data MOCKBBODY era

data MockChainFailure era
  = MockChainFromTickFailure (TickPredicateFailure era)
  | MockChainFromLedgersFailure (LedgersPredicateFailure era)

data MockChainEvent era
  = MockChainFromTickEvent (TickEvent era)
  | MockChainFromLedgersEvent (LedgersEvent era)

data MockBlock era = MockBlock
  { mbIssuer :: KeyHash 'BlockIssuer (Crypto era),
    mbSlot :: SlotNo,
    mbTrans :: Seq (Core.Tx era)
  }

data MockChainState era = MockChainState
  { mcsNes :: NewEpochState era,
    mcsIssuers :: IssuerMap era
  }

type IssuerMap era = Map.Map (KeyHash 'BlockIssuer (Crypto era)) Word64

-- ======================================================================

type MockChainConstraints era =
  ( State (Core.EraRule "LEDGER" era) ~ (UTxOState era, DPState (Crypto era)),
    Signal (Core.EraRule "LEDGER" era) ~ Core.Tx era,
    Environment (Core.EraRule "LEDGER" era) ~ LedgerEnv era,
    State (Core.EraRule "RUPD" era) ~ StrictMaybe (PulsingRewUpdate (Crypto era)),
    Signal (Core.EraRule "RUPD" era) ~ SlotNo,
    Environment (Core.EraRule "RUPD" era) ~ RupdEnv era,
    State (Core.EraRule "NEWEPOCH" era) ~ NewEpochState era,
    Signal (Core.EraRule "NEWEPOCH" era) ~ EpochNo,
    Environment (Core.EraRule "NEWEPOCH" era) ~ (),
    Embed (Core.EraRule "LEDGER" era) (LEDGERS era),
    Embed (Core.EraRule "NEWEPOCH" era) (TICK era),
    Embed (Core.EraRule "RUPD" era) (TICK era),
    Default (State (Core.EraRule "PPUP" era))
  )

instance
  ( Reflect era,
    MockChainConstraints era
  ) =>
  STS (MOCKCHAIN era)
  where
  type State (MOCKCHAIN era) = MockChainState era
  type Signal (MOCKCHAIN era) = MockBlock era
  type Environment (MOCKCHAIN era) = ()
  type BaseM (MOCKCHAIN era) = ShelleyBase
  type PredicateFailure (MOCKCHAIN era) = MockChainFailure era
  type Event (MOCKCHAIN era) = MockChainEvent era
  initialRules = []
  transitionRules = [chainTransition]

chainTransition ::
  forall era.
  ( Reflect era,
    MockChainConstraints era
  ) =>
  TransitionRule (MOCKCHAIN era)
chainTransition = do
  TRC (_, MockChainState nes imap, MockBlock issuer slot txs) <- judgmentContext

  nes' <- trans @(TICK era) $ TRC ((), nes, slot)

  let NewEpochState _epochNo _ _ epochState _ _ = nes'
      EpochState account _ ledgerState _ pparams _ = epochState
      LedgerState _ (DPState (DState _ _ _genDelegs _) (PState _ _ _)) = ledgerState

  let newimap = Map.unionWith (+) imap (Map.singleton issuer 1)

  newledgerState <-
    trans @(LEDGERS era) $
      TRC (LedgersEnv slot pparams account, ledgerState, txs)

  let newEpochstate = epochState {esLState = newledgerState}
      newNewEpochState = nes' {nesEs = newEpochstate}

  pure (MockChainState newNewEpochState newimap)

-- ===========================
-- Embed instances

instance
  ( STS (TICK era),
    Signal (Core.EraRule "RUPD" era) ~ SlotNo,
    State (Core.EraRule "RUPD" era) ~ StrictMaybe (PulsingRewUpdate (Crypto era)),
    Environment (Core.EraRule "RUPD" era) ~ RupdEnv era,
    State (Core.EraRule "NEWEPOCH" era) ~ NewEpochState era,
    Signal (Core.EraRule "NEWEPOCH" era) ~ EpochNo,
    State (Core.EraRule "NEWEPOCH" era) ~ NewEpochState era,
    Environment (Core.EraRule "NEWEPOCH" era) ~ ()
  ) =>
  Embed (TICK era) (MOCKCHAIN era)
  where
  wrapFailed = MockChainFromTickFailure
  wrapEvent = MockChainFromTickEvent

instance
  ( STS (LEDGERS era),
    State (Core.EraRule "LEDGER" era) ~ (UTxOState era, DPState (Crypto era)),
    Environment (Core.EraRule "LEDGER" era) ~ LedgerEnv era,
    Signal (Core.EraRule "LEDGER" era) ~ Core.Tx era
  ) =>
  Embed (LEDGERS era) (MOCKCHAIN era)
  where
  wrapFailed = MockChainFromLedgersFailure
  wrapEvent = MockChainFromLedgersEvent

-- ================================================================

deriving instance
  (Show (TickEvent era), Show (LedgersEvent era)) => Show (MockChainEvent era)

deriving instance
  (Eq (TickEvent era), Eq (LedgersEvent era)) => Eq (MockChainEvent era)

deriving instance
  (Show (TickPredicateFailure era), Show (LedgersPredicateFailure era)) => Show (MockChainFailure era)

deriving instance
  (Eq (TickPredicateFailure era), Eq (LedgersPredicateFailure era)) => Eq (MockChainFailure era)
