{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Prelude (IO, String, FilePath, putStrLn, (<>))
import qualified Prelude as P
import qualified Data.Text as T

import Plutus.V2.Ledger.Api
import Plutus.V2.Ledger.Contexts
import qualified Plutus.V2.Ledger.Api as PlutusV2
import Plutus.V1.Ledger.Interval as Interval
import Plutus.V1.Ledger.Value (valueOf, adaSymbol, adaToken)
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

-- Bounty Datum & Redeemer
data BountyDatum = BountyDatum
    { bdScopeHash :: BuiltinByteString
    , bdMaxPayout :: Integer
    , bdArbiter   :: PubKeyHash
    , bdDeadline  :: POSIXTime
    , bdBountyNFT :: (CurrencySymbol, TokenName)
    , bdMSafeVH   :: ValidatorHash
    }
PlutusTx.unstableMakeIsData ''BountyDatum

data BountyAction =
      SubmitPoC BuiltinByteString PubKeyHash    -- PoC hash, researcher PKH
    | ClaimPayout PubKeyHash Integer            -- researcher PKH, amount
    | RefundToArbiter                           -- arbiter refunds remaining after deadline
    | IncidentSpend PubKeyHash Integer          -- beneficiary PKH, amount (requires MSafe input)
PlutusTx.unstableMakeIsData ''BountyAction

-- MSafe Datum & Redeemer (multisig)
data MSafeDatum = MSafeDatum
    { msSigners   :: [PubKeyHash]
    , msThreshold :: Integer
    }
PlutusTx.unstableMakeIsData ''MSafeDatum

data MSafeAction = MSafeSpend
PlutusTx.unstableMakeIsData ''MSafeAction

{-# INLINABLE valuePaidTo #-}
valuePaidTo :: TxInfo -> PubKeyHash -> Integer
valuePaidTo info pkh =
    let outs = txInfoOutputs info
        isToPubKey o = case txOutAddress o of
                         Address (PubKeyCredential p) _ -> p == pkh
                         _                              -> False
        vals = [ valueOf (txOutValue o) adaSymbol adaToken | o <- outs, isToPubKey o ]
    in case vals of
         [] -> 0
         _  -> foldl (+) 0 vals

{-# INLINABLE scriptInputContainsNFT #-}
scriptInputContainsNFT :: ScriptContext -> CurrencySymbol -> TokenName -> Bool
scriptInputContainsNFT ctx cs tn =
    case findOwnInput ctx of
        Nothing -> False
        Just i  ->
            let v = txOutValue $ txInInfoResolved i
            in valueOf v cs tn >= 1

{-# INLINABLE findInputWithValidatorHash #-}
findInputWithValidatorHash :: ValidatorHash -> TxInfo -> Bool
findInputWithValidatorHash vh info =
    let ins = txInfoInputs info
        hasScriptInput i = case txOutAddress (txInInfoResolved i) of
                             Address (ScriptCredential vh') _ -> vh' == vh
                             _                                -> False
    in any hasScriptInput ins

{-# INLINABLE mkBountyValidator #-}
mkBountyValidator :: BountyDatum -> BountyAction -> ScriptContext -> Bool
mkBountyValidator bd action ctx =
    let info = scriptContextTxInfo ctx
        (csNFT, tnNFT) = bdBountyNFT bd
        paidToPublisher = valuePaidTo info (bdArbiter bd)
        nowRange = txInfoValidRange info
        afterDeadline = Interval.contains (Interval.from (bdDeadline bd + 1)) nowRange
    in case action of

      SubmitPoC pocHash researcher ->
        traceIfFalse "researcher signature missing" (txSignedBy info researcher) &&
        traceIfFalse "must include bounty NFT in input" (scriptInputContainsNFT ctx csNFT tnNFT)

      ClaimPayout researcher amt ->
        traceIfFalse "arbiter signature required" (txSignedBy info (bdArbiter bd)) &&
        traceIfFalse "amount exceeds max" (amt <= bdMaxPayout bd) &&
        traceIfFalse "researcher not paid" (valuePaidTo info researcher >= amt) &&
        traceIfFalse "bounty input must include NFT" (scriptInputContainsNFT ctx csNFT tnNFT)

      RefundToArbiter ->
        traceIfFalse "only arbiter can refund" (txSignedBy info (bdArbiter bd)) &&
        traceIfFalse "too early to refund" afterDeadline &&
        traceIfFalse "arbiter not paid" (paidToPublisher >= 0) &&
        traceIfFalse "bounty input must include NFT" (scriptInputContainsNFT ctx csNFT tnNFT)

      IncidentSpend beneficiary amt ->
        traceIfFalse "msafe not used as input" (findInputWithValidatorHash (bdMSafeVH bd) info) &&
        traceIfFalse "beneficiary not paid" (valuePaidTo info beneficiary >= amt) &&
        traceIfFalse "bounty input must include NFT" (scriptInputContainsNFT ctx csNFT tnNFT)

{-# INLINABLE mkBountyValidatorUntyped #-}
mkBountyValidatorUntyped :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mkBountyValidatorUntyped d r c =
    let dat = unsafeFromBuiltinData @BountyDatum d
        red = unsafeFromBuiltinData @BountyAction r
        ctx = unsafeFromBuiltinData @ScriptContext c
    in if mkBountyValidator dat red ctx then () else error ()

bountyValidator :: Validator
bountyValidator = mkValidatorScript $$(PlutusTx.compile [|| mkBountyValidatorUntyped ||])

{-# INLINABLE mkMSafeValidator #-}
mkMSafeValidator :: MSafeDatum -> MSafeAction -> ScriptContext -> Bool
mkMSafeValidator md _ ctx =
    let info = scriptContextTxInfo ctx
        signers = msSigners md
        thresh  = msThreshold md
        signedCount = length (filter (\pk -> txSignedBy info pk) signers)
    in traceIfFalse "insufficient signers" (signedCount >= thresh)

{-# INLINABLE mkMSafeValidatorUntyped #-}
mkMSafeValidatorUntyped :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mkMSafeValidatorUntyped d r c =
    let dat = unsafeFromBuiltinData @MSafeDatum d
        red = unsafeFromBuiltinData @MSafeAction r
        ctx = unsafeFromBuiltinData @ScriptContext c
    in if mkMSafeValidator dat red ctx then () else error ()

msafeValidator :: Validator
msafeValidator = mkValidatorScript $$(PlutusTx.compile [|| mkMSafeValidatorUntyped ||])

{-# INLINABLE plutusValidatorHash #-}
plutusValidatorHash :: PlutusV2.Validator -> PlutusV2.ValidatorHash
plutusValidatorHash val =
    let bytes    = Serialise.serialise val
        short    = SBS.toShort (LBS.toStrict bytes)
        strictBS = SBS.fromShort short
        builtin  = Builtins.toBuiltin strictBS
    in PlutusV2.ValidatorHash builtin

plutusScriptAddress :: Address
plutusScriptAddress =
    Address (ScriptCredential (plutusValidatorHash bountyValidator)) Nothing

msafeScriptAddress :: Address
msafeScriptAddress =
    Address (ScriptCredential (plutusValidatorHash msafeValidator)) Nothing

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

main :: IO ()
main = do
    let network = C.Testnet (C.NetworkMagic 1)

    writeValidator "bounty-validator.plutus" bountyValidator
    writeCBOR "bounty-validator.cbor" bountyValidator

    writeValidator "msafe-validator.plutus" msafeValidator
    writeCBOR "msafe-validator.cbor" msafeValidator

    let vh      = plutusValidatorHash bountyValidator
        onchain = plutusScriptAddress
        bech32  = toBech32ScriptAddress network bountyValidator

    putStrLn "\n--- Bounty & MSafe Validators ---"
    putStrLn $ "Bounty Validator Hash (Plutus): " <> P.show vh
    putStrLn $ "Bounty Script Address:          " <> P.show onchain
    putStrLn $ "Bounty Bech32 Address:          " <> bech32
    putStrLn "---------------------------------"
    putStrLn "Bounty & MSafe validators generated successfully."
