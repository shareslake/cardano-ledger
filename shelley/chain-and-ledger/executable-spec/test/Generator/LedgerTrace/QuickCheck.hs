{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- The HasTrace instance relies on test generators and so cannot
-- be included with the LEDGER STS
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Generator.LedgerTrace.QuickCheck where

import           Control.Monad (foldM)
import           Data.Functor.Identity (runIdentity)
import qualified Data.Sequence as Seq
import           Data.Word (Word64)
import           Test.QuickCheck (Gen)

import           BaseTypes (Globals)
import           ConcreteCryptoTypes (DPState, LEDGER, LEDGERS, Tx, UTxOState)
import           Control.Monad.Trans.Reader (runReaderT)
import           Control.State.Transition.Extended (IRC, TRC (..), applySTS)
import qualified Control.State.Transition.Trace.Generator.QuickCheck as TQC

import           Generator.Core.Constants (maxGenesisUTxOouts, minGenesisUTxOouts, numBaseScripts)
import           Generator.Core.QuickCheck (coreNodeKeys, genCoin, genUtxo0, genesisDelegs0,
                     traceKeyHashMap, traceKeyPairs, traceKeyPairsByStakeHash,
                     traceMSigCombinations, traceMSigScripts)
import           Generator.Update.QuickCheck (genPParams)
import           Generator.Utxo.QuickCheck (genTx)
import           LedgerState (pattern LedgerState, genesisState)
import           Shrinkers (shrinkTx)
import           Slot (SlotNo (..))
import           STS.Ledger (LedgerEnv (..))
import           STS.Ledgers (LedgersEnv (..))
import           TxData (Ix)

import           Test.Utils (runShelleyBase)

-- The LEDGER STS combines utxo and delegation rules and allows for generating transactions
-- with meaningful delegation certificates.
instance TQC.HasTrace LEDGER Word64 where
  envGen _ =
    LedgerEnv <$> pure (SlotNo 0)
              <*> pure 0
              <*> genPParams
              <*> genCoin 1000000 10000000

  sigGen _ = genTx_

  shrinkSignal = shrinkTx

  type BaseEnv LEDGER = Globals
  interpretSTS globals act = runIdentity $ runReaderT act globals

instance TQC.HasTrace LEDGERS Word64 where
  envGen _ =
    LedgersEnv <$> pure (SlotNo 0)
               <*> genPParams
               <*> genCoin 1000000 10000000

  -- a LEDGERS signal is a sequence of LEDGER signals
  sigGen maxTxs (LedgersEnv slotNo pParams reserves) (LedgerState utxoSt dpSt) = do
      (_, _, txs') <-
        foldM genAndApplyTx
              (utxoSt, dpSt, [])
              [0 .. (fromIntegral maxTxs - 1)]

      pure $ Seq.fromList (reverse txs') -- reverse Newest first to Oldest first
    where
      genAndApplyTx
        :: (UTxOState, DPState, [Tx])
        -> TxData.Ix
        -> Gen (UTxOState, DPState, [Tx])
      genAndApplyTx (u, dp, txs) ix = do
        let ledgerEnv = LedgerEnv slotNo ix pParams reserves
        tx <- genTx_ ledgerEnv (u, dp)

        let res = runShelleyBase $ applySTS @LEDGER (TRC (ledgerEnv, (u, dp), tx))
        pure $ case res of
          Left _ ->
            (u, dp, txs)
          Right (u',dp') ->
            (u',dp', tx:txs)

  shrinkSignal = const []

  type BaseEnv LEDGERS = Globals
  interpretSTS globals act = runIdentity $ runReaderT act globals

genTx_
  :: LedgerEnv
  -> (UTxOState, DPState)
  -> Gen Tx
genTx_ env st =
  genTx
    env
    st
    traceKeyPairs
    traceKeyHashMap
    (traceMSigCombinations $ take numBaseScripts traceMSigScripts)
    coreNodeKeys
    traceKeyPairsByStakeHash

-- | Generate initial state for the LEDGER STS using the STS environment.
--
-- Note: this function must be usable in place of 'applySTS' and needs to align
-- with the signature 'RuleContext sts -> Gen (Either [[PredicateFailure sts]] (State sts))'.
-- To achieve this we (1) use 'IRC LEDGER' (the "initial rule context") instead of simply 'LedgerEnv'
-- and (2) always return Right (since this function does not raise predicate failures).
mkGenesisLedgerState
  :: IRC LEDGER
  -> Gen (Either a (UTxOState, DPState))
mkGenesisLedgerState _ = do
  utxo0 <- genUtxo0 minGenesisUTxOouts maxGenesisUTxOouts
  let (LedgerState utxoSt dpSt) = genesisState genesisDelegs0 utxo0
  pure $ Right (utxoSt, dpSt)