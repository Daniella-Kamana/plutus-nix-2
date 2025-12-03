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
import PlutusTx.Prelude hiding (Semigroup(..), unless)
import qualified PlutusTx.Builtins as Builtins

import qualified Codec.Serialise as Serialise
import qualified Data.ByteString.Lazy  as LBS
import qualified Data.ByteString.Short as SBS
import qualified Data.ByteString       as BS
import qualified Data.ByteString.Base16 as B16
import qualified Data.Text.Encoding as TE

import qualified Cardano.Api as C
import qualified Cardano.Api.Shelley as CS

------------------------------------------------------------
-- DATA TYPES
------------------------------------------------------------

data AccessPass = AccessPass
    { apResourceId :: BuiltinByteString
    , apExpiry     :: POSIXTime
    , apPassId     :: BuiltinByteString
    , apCurrency   :: CurrencySymbol
    , apToken      :: TokenName
    }
PlutusTx.unstableMakeIsData ''AccessPass

data RevocationList = RevocationList
    { rlRevokedIds :: [BuiltinByteString]
    }
PlutusTx.unstableMakeIsData ''RevocationList

data AccessAction = UsePass | UpdateRevocations
PlutusTx.unstableMakeIsData ''AccessAction

------------------------------------------------------------
-- HELPERS
------------------------------------------------------------

{-# INLINABLE passPresent #-}
passPresent :: ScriptContext -> CurrencySymbol -> TokenName -> Bool
passPresent ctx cs tn =
    case findOwnInput ctx of
        Nothing -> traceError "no script input"
        Just i  ->
            let v = txOutValue $ txInInfoResolved i
            in valueOf v cs tn >= 1

{-# INLINABLE passNotRevoked #-}
passNotRevoked :: BuiltinByteString -> [BuiltinByteString] -> Bool
passNotRevoked pid revoked =
    not (pid `elem` revoked)

------------------------------------------------------------
-- VALIDATOR
------------------------------------------------------------

{-# INLINABLE mkValidator #-}
mkValidator :: (AccessPass, RevocationList) -> AccessAction -> ScriptContext -> Bool
mkValidator (pass, rlist) action ctx =
    case action of
        UsePass ->
            traceIfFalse "missing pass NFT" (passPresent ctx (apCurrency pass) (apToken pass)) &&
            traceIfFalse "pass revoked" (passNotRevoked (apPassId pass) (rlRevokedIds rlist)) &&
            traceIfFalse "pass expired" validExpiry

        UpdateRevocations ->
            traceIfFalse "admin sign required" adminSigned

  where
    info = scriptContextTxInfo ctx
    nowOK = Interval.contains (Interval.to (apExpiry pass)) (txInfoValidRange info)
    validExpiry = nowOK
    adminSigned = True  -- integrate admin PKH if needed

------------------------------------------------------------
-- UNTYPED
------------------------------------------------------------

{-# INLINABLE mkValidatorUntyped #-}
mkValidatorUntyped :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mkValidatorUntyped d r c =
    let dat = unsafeFromBuiltinData @(AccessPass, RevocationList) d
        red = unsafeFromBuiltinData @AccessAction r
        ctx = unsafeFromBuiltinData @ScriptContext c
    in if mkValidator dat red ctx then () else error ()

validator :: Validator
validator = mkValidatorScript $$(PlutusTx.compile [|| mkValidatorUntyped ||])

------------------------------------------------------------
-- HASH + ADDRESS
------------------------------------------------------------

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

------------------------------------------------------------
-- OFF-CHAIN ADDR
------------------------------------------------------------

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

------------------------------------------------------------
-- CBOR
------------------------------------------------------------

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

------------------------------------------------------------
-- RAW SCRIPT
------------------------------------------------------------

writeValidator :: FilePath -> Validator -> IO ()
writeValidator path val = do
    LBS.writeFile path (Serialise.serialise val)
    putStrLn $ "Validator written to: " <> path

------------------------------------------------------------
-- MAIN
------------------------------------------------------------

main :: IO ()
main = do
    let network = C.Testnet (C.NetworkMagic 1)

    writeValidator "access-validator.plutus" validator
    writeCBOR      "access-validator.cbor"   validator

    let vh     = plutusValidatorHash validator
        addrOn = plutusScriptAddress
        addrB  = toBech32ScriptAddress network validator

    putStrLn "\n--- Access Control Validator ---"
    putStrLn $ "Validator Hash:  " <> P.show vh
    putStrLn $ "Plutus Address:  " <> P.show addrOn
    putStrLn $ "Bech32 Address:  " <> addrB
    putStrLn "--------------------------------"
