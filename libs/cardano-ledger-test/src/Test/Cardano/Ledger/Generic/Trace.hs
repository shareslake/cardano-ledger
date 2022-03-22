{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.Generic.Trace where

import Cardano.Binary (ToCBOR)
import Cardano.Ledger.BaseTypes (Globals, mkTxIxPartial)
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Core (EraRule)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Era (Crypto))
import Cardano.Ledger.Shelley.LedgerState (AccountState (..), DPState, LedgerState (..), UTxOState (..))
import Cardano.Ledger.Shelley.Rules.Delegs (DelegsEnv)
import Cardano.Ledger.Shelley.Rules.Ledger (LEDGER, LedgerEnv (..))
import Cardano.Ledger.Shelley.Rules.Ledgers (LEDGERS, LedgersEnv (..))
import Cardano.Ledger.Shelley.Rules.Utxo (UtxoEnv)
import Cardano.Ledger.Shelley.TxBody (DCert)
import Cardano.Ledger.TxIn (TxIn)
import Control.Monad.Trans.Reader (ReaderT (..))
import Control.State.Transition.Extended (Embed (..), STS (..))
import Control.State.Transition.Trace.Generator.QuickCheck (HasTrace (..))
import Data.Default.Class (Default)
import Data.Functor.Identity (Identity (runIdentity))
import Data.Sequence (Seq (..))
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set)
import GHC.Records (HasField)
import Test.Cardano.Ledger.Generic.GenState
  ( GenEnv (..),
    GenState (..),
    getReserves,
    getSlot,
    getTreasury,
  )
-- import Control.State.Transition.Trace(applySTSTest,checkTrace)
-- import Test.Cardano.Ledger.Shelley.Rules.Chain (CHAIN, ChainState (..), initialShelleyState)
-- import qualified Cardano.Ledger.Babbage.PParams(PParams'(..))
-- import qualified Cardano.Ledger.Alonzo.PParams(PParams'(..))
-- import qualified Cardano.Ledger.Shelley.PParams(PParams'(..))
import Test.Cardano.Ledger.Generic.Proof
import Test.Cardano.Ledger.Generic.Properties (genValidatedTx)
import Test.Tasty.QuickCheck (Arbitrary (..), Gen)

-- =================================================
-- Synonym Constraints

type ShowCore era =
  ( Show (Core.PParams era),
    Show (Core.Tx era),
    Show (Core.Value era),
    Show (Core.TxOut era),
    Show (State (EraRule "PPUP" era))
  )

type ToCBORCore era = (ToCBOR (Core.TxBody era), ToCBOR (Core.TxOut era), ToCBOR (Core.Value era))

type LEDGERRule era =
  ( Environment (EraRule "DELEGS" era) ~ DelegsEnv era,
    Signal (EraRule "UTXOW" era) ~ Core.Tx era,
    State (EraRule "UTXOW" era) ~ UTxOState era,
    Environment (EraRule "UTXOW" era) ~ UtxoEnv era,
    State (EraRule "DELEGS" era) ~ DPState (Crypto era),
    Signal (EraRule "DELEGS" era) ~ Seq (DCert (Crypto era)),
    Embed (EraRule "DELEGS" era) (LEDGER era),
    Embed (EraRule "UTXOW" era) (LEDGER era),
    Embed (EraRule "UTXOW" era) (LEDGER era),
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin,
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era)))
  )

-- ==============================================================
-- HasTrace instance of LEDGER

instance
  ( Reflect era,
    GoodCrypto (Crypto era),
    LEDGERRule era,
    ToCBORCore era,
    ShowCore era
  ) =>
  HasTrace (LEDGER era) (GenState era)
  where
  type BaseEnv (LEDGER era) = Globals

  interpretSTS globals act = runIdentity $ runReaderT act globals

  envGen gstate =
    LedgerEnv (getSlot gstate)
      <$> arbitrary
      <*> pure ((gePParams . gsGenEnv) gstate)
      <*> pure
        ( AccountState
            (getTreasury gstate)
            (getReserves gstate)
        )

  sigGen genstate _ledgerenv (utxostate, _dpstate) = genTx genstate utxostate

  shrinkSignal _x = []

-- | We make this a toplevel function because we will have to call it
--   in the LEDGERS Rule as well.
genTx :: Reflect era => GenState era -> UTxOState era -> Gen (Core.Tx era)
genTx genstate utxostate =
  runReaderT
    (snd <$> (genValidatedTx (gsProof genstate)))
    (genstate {gsPrevUTxO = _utxo utxostate})

-- ====================================
-- HasTrace instance of LEDGERS

type LEDGERSRule era =
  ( Signal (EraRule "LEDGER" era) ~ Core.Tx era,
    State (EraRule "LEDGER" era) ~ (UTxOState era, DPState (Crypto era)),
    Environment (EraRule "LEDGER" era) ~ LedgerEnv era,
    Embed (EraRule "LEDGER" era) (LEDGERS era),
    Default (State (EraRule "PPUP" era))
  )

instance
  ( Reflect era,
    GoodCrypto (Crypto era),
    LEDGERSRule era,
    Signal (EraRule "LEDGER" era) ~ Core.Tx era
  ) =>
  HasTrace (LEDGERS era) (GenState era)
  where
  type BaseEnv (LEDGERS era) = Globals

  interpretSTS globals act = runIdentity $ runReaderT act globals

  envGen gstate =
    pure $
      LedgersEnv
        (getSlot gstate)
        ((gePParams . gsGenEnv) gstate)
        ( AccountState
            (getTreasury gstate)
            (getReserves gstate)
        )

  -- a LEDGERS signal is a sequence of LEDGER signals (Seq (ValidatedTx era))
  sigGen genstate ledgersenv (LedgerState u dp) =
    fst <$> mapSeqM (genAndApplyTx reify) (envs, (u, dp))
    where
      label (LedgersEnv slot pp acct) txix = (LedgerEnv slot txix pp acct)
      envs = [label ledgersenv (mkTxIxPartial i) | i <- [0 .. 10]]
      genAndApplyTx ::
        Proof era ->
        (LedgerEnv era, (UTxOState era, DPState (Crypto era))) ->
        Gen (Core.Tx era, (UTxOState era, DPState (Crypto era)))
      genAndApplyTx proof (ledgerenv, (utxoSt, _dp)) = do
        tx <- genTx genstate utxoSt
        goSTS
          (LEDGER proof)
          ledgerenv
          (utxoSt, dp)
          tx
          ( \case
              Left predfails -> error ("LEDGER sigGen: " <> show predfails)
              Right x -> pure (tx, x)
          )

  shrinkSignal _x = []

mapSeqM :: Monad m => ((a, s) -> m (b, s)) -> ([a], s) -> m (Seq b, s)
mapSeqM _ ([], state) = pure (Empty, state)
mapSeqM f (x : xs, s0) = do
  (x', s1) <- f (x, s0)
  (xs', s2) <- mapSeqM f (xs, s1)
  pure (x' :<| xs', s2)

-- ======================================
