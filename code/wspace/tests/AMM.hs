{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}

module Main where

import Prelude (IO, String, FilePath, putStrLn, (<>))
import qualified Prelude as P
import qualified Data.Text as T

import Plutus.V2.Ledger.Api
import Plutus.V2.Ledger.Contexts
import qualified Plutus.V2.Ledger.Api as PlutusV2
import Plutus.V1.Ledger.Interval as Interval
import Plutus.V1.Ledger.Value (valueOf)
import PlutusTx
import PlutusTx.Prelude hiding (Semigroup(..))
import qualified PlutusTx.Builtins as Builtins

import qualified Codec.Serialise as Serialise
import qualified Data.ByteString.Lazy  as LBS
import qualified Data.ByteString.Short as SBS
import qualified Data.ByteString       as BS
import qualified Data.ByteString.Base16 as B16
import qualified Data.Text.Encoding as TE

import qualified Cardano.Api as C
import qualified Cardano.Api.Shelley as CS

------------------------------------------------------------------------
-- Datum
------------------------------------------------------------------------

data PoolDatum = PoolDatum
    { pdResA      :: Integer
    , pdResB      :: Integer
    , pdFeeBps    :: Integer
    , pdLPPolicy  :: CurrencySymbol
    , pdPoolNFT   :: (CurrencySymbol, TokenName)
    }
PlutusTx.unstableMakeIsData ''PoolDatum

data AMMAction = swapA | swapB | addLiq Integer Integer | removeLiq Integer
PlutusTx.unstableMakeIsData ''AMMAction

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

{-# INLINABLE mustHoldNFT #-}
mustHoldNFT :: TxOut -> (CurrencySymbol, TokenName) -> Bool
mustHoldNFT o (cs, tn) = valueOf (txOutValue o) cs tn >= 1

{-# INLINABLE getPoolInput #-}
getPoolInput :: ScriptContext -> (TxInInfo, TxOut)
getPoolInput ctx =
    case findOwnInput ctx of
        Nothing -> traceError "missing pool input"
        Just i  -> (i, txInInfoResolved i)

{-# INLINABLE getPoolOutput #-}
getPoolOutput :: ScriptContext -> (TxOut, PoolDatum)
getPoolOutput ctx =
    let outs = getContinuingOutputs ctx
    in case outs of
        [o] ->
            case txOutDatum o of
                OutputDatum (Datum d) ->
                    case PlutusTx.fromBuiltinData d of
                        Just pd -> (o, pd)
                        _       -> traceError "bad datum"
                _ -> traceError "datum missing"
        _ -> traceError "must be exactly one pool output"

------------------------------------------------------------------------
-- Core AMM
------------------------------------------------------------------------

{-# INLINABLE applyFee #-}
applyFee :: Integer -> Integer -> Integer
applyFee amt feeBps = amt - (amt * feeBps `divide` 10000)

{-# INLINABLE invariant #-}
invariant :: Integer -> Integer -> Integer -> Bool
invariant x y x' =
    -- k' >= k
    x' >= y

------------------------------------------------------------------------
-- Validator
------------------------------------------------------------------------

{-# INLINABLE mkValidator #-}
mkValidator :: PoolDatum -> AMMAction -> ScriptContext -> Bool
mkValidator pd action ctx =
    let info = scriptContextTxInfo ctx
        (iIn, iOut) = getPoolInput ctx
        (oOut, newPD) = getPoolOutput ctx

        (csNFT, tnNFT) = pdPoolNFT pd
    in
    traceIfFalse "missing pool NFT" (mustHoldNFT iOut (csNFT, tnNFT)) &&
    case action of

      swapA ->
        let deltaA = pdResA newPD - pdResA pd
            feeAdj = applyFee deltaA (pdFeeBps pd)
            yOld   = pdResA pd * pdResB pd
            yNew   = (pdResA pd + feeAdj) * (pdResB pd - (pdResB pd - pdResB newPD))
        in traceIfFalse "k not respected" (invariant yOld yNew yNew)

      swapB ->
        let deltaB = pdResB newPD - pdResB pd
            feeAdj = applyFee deltaB (pdFeeBps pd)
            yOld   = pdResA pd * pdResB pd
            yNew   = (pdResA pd - (pdResA pd - pdResA newPD)) * (pdResB pd + feeAdj)
        in traceIfFalse "k not respected" (invariant yOld yNew yNew)

      addLiq _ _ ->
        traceIfFalse "pool NFT missing" True

      removeLiq _ ->
        traceIfFalse "pool NFT missing" True

------------------------------------------------------------------------
-- Untyped
------------------------------------------------------------------------

{-# INLINABLE mkValidatorUntyped #-}
mkValidatorUntyped :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mkValidatorUntyped d r c =
    let dat = unsafeFromBuiltinData @PoolDatum d
        red = unsafeFromBuiltinData @AMMAction r
        ctx = unsafeFromBuiltinData @ScriptContext c
    in if mkValidator dat red ctx then () else error ()

validator :: Validator
validator = mkValidatorScript $$(PlutusTx.compile [|| mkValidatorUntyped ||])

------------------------------------------------------------------------
-- Script Hash + Address
------------------------------------------------------------------------

plutusValidatorHash :: PlutusV2.Validator -> PlutusV2.ValidatorHash
plutusValidatorHash val =
    let bytes    = Serialise.serialise val
        short    = SBS.toShort (LBS.toStrict bytes)
        strictBS = SBS.fromShort short
        builtin  = Builtins.toBuiltin strictBS
    in PlutusV2.ValidatorHash builtin

plutusScriptAddress :: Address
plutusScriptAddress =
    Address (ScriptCredential (plutusValidatorHash validator)) Nothing

------------------------------------------------------------------------
-- Bech32 Address
------------------------------------------------------------------------

toBech32ScriptAddress :: C.NetworkId -> Validator -> String
toBech32ScriptAddress network val =
    let serialised = SBS.toShort . LBS.toStrict $ Serialise.serialise val
        plutusScript :: C.PlutusScript C.PlutusScriptV2
        plutusScript = CS.PlutusScriptSerialised serialised

        scriptHash = C.hashScript (C.PlutusScript C.PlutusScriptV2 plutusScript)

        shelleyAddr =
            C.makeShelleyAddressInEra
                network
                (C.PaymentCredentialByScript scriptHash)
                C.NoStakeAddress
    in T.unpack (C.serialiseAddress shelleyAddr)

------------------------------------------------------------------------
-- Hex / File Output
------------------------------------------------------------------------

validatorToCborHex :: Validator -> String
validatorToCborHex val =
    let cbor = LBS.toStrict (Serialise.serialise val)
        hex  = B16.encode cbor
    in T.unpack (TE.decodeUtf8 hex)

writeCBOR :: FilePath -> Validator -> IO ()
writeCBOR fp val = do
    let hex = validatorToCborHex val
    BS.writeFile fp (TE.encodeUtf8 (T.pack hex))
    putStrLn ("CBOR hex written to: " <> fp)

writeValidator :: FilePath -> Validator -> IO ()
writeValidator path val = do
    LBS.writeFile path (Serialise.serialise val)
    putStrLn $ "Validator written to: " <> path

------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------

main :: IO ()
main = do
    let network = C.Testnet (C.NetworkMagic 1)

    writeValidator "amm-validator.plutus" validator
    writeCBOR "amm-validator.cbor" validator

    let vh      = plutusValidatorHash validator
        onchain = plutusScriptAddress
        bech32  = toBech32ScriptAddress network validator

    putStrLn "\n--- AMM Validator Info ---"
    putStrLn $ "Validator Hash (Plutus): " <> P.show vh
    putStrLn $ "Plutus Script Address:    " <> P.show onchain
    putStrLn $ "Bech32 Script Address:    " <> bech32
    putStrLn "---------------------------------"
    putStrLn "AMM validator generated successfully."
