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

data ArticleDatum = ArticleDatum
    { adPublisher  :: PubKeyHash
    , adContentHash :: BuiltinByteString
    , adTs         :: POSIXTime
    , adPrice      :: Integer
    , adEntPolicy  :: CurrencySymbol
    }
PlutusTx.unstableMakeIsData ''ArticleDatum

data ArticleAction = Purchase | Tip Integer
PlutusTx.unstableMakeIsData ''ArticleAction

{-# INLINABLE valuePaidTo #-}
valuePaidTo :: TxInfo -> PubKeyHash -> Integer
valuePaidTo info pkh =
    let outs = txInfoOutputs info
        isToPubKey o = case txOutAddress o of
                         Address (PubKeyCredential p) _ -> p == pkh
                         _                              -> False
    in mconcat [ valueOf (txOutValue o) adaSymbol adaToken | o <- outs, isToPubKey o ]

{-# INLINABLE findPoolInputByValidatorHash #-}
findPoolInputByValidatorHash :: ValidatorHash -> TxInfo -> Bool
findPoolInputByValidatorHash vh info =
    let ins = txInfoInputs info
        hasScriptInput i = case txOutAddress (txInInfoResolved i) of
                             Address (ScriptCredential vh') _ -> vh' == vh
                             _                                -> False
    in any hasScriptInput ins

{-# INLINABLE mkArticleValidator #-}
mkArticleValidator :: ArticleDatum -> ArticleAction -> ScriptContext -> Bool
mkArticleValidator ad action ctx =
    let info = scriptContextTxInfo ctx
        vh = plutusValidatorHash validator
        tokenName = TokenName (adContentHash ad)
        mintedAmt = valueOf (txInfoMint info) (adEntPolicy ad) tokenName
        paidToPublisherAda = valuePaidTo info (adPublisher ad)
    in case action of
         Purchase ->
             traceIfFalse "must mint entitlement" (mintedAmt == 1) &&
             traceIfFalse "must spend article UTxO" (findOwnInput ctx /= Nothing) &&
             traceIfFalse "must spend article script input (validator hash presence)" (findPoolInputByValidatorHash vh info) &&
             traceIfFalse "price not paid to publisher" (paidToPublisherAda >= adPrice ad)

         Tip amt ->
             traceIfFalse "tip must be positive" (amt > 0) &&
             traceIfFalse "publisher must receive tip" (paidToPublisherAda >= amt) &&
             traceIfFalse "must spend article UTxO" (findOwnInput ctx /= Nothing)

{-# INLINABLE mkValidatorUntyped #-}
mkValidatorUntyped :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mkValidatorUntyped d r c =
    let dat = unsafeFromBuiltinData @ArticleDatum d
        red = unsafeFromBuiltinData @ArticleAction r
        ctx = unsafeFromBuiltinData @ScriptContext c
    in if mkArticleValidator dat red ctx then () else error ()

validator :: Validator
validator = mkValidatorScript $$(PlutusTx.compile [|| mkValidatorUntyped ||])

{-# INLINABLE mkEntPolicy #-}
mkEntPolicy :: BuiltinData -> BuiltinData -> ()
mkEntPolicy _ ctxDat =
    let ctx = unsafeFromBuiltinData @ScriptContext ctxDat
        info = scriptContextTxInfo ctx
        vh = plutusValidatorHash validator
        hasArticleInput = findPoolInputByValidatorHash vh info
        minted = txInfoMint info
        nonZeroMint = (flattenValue minted) /= ([] :: [(CurrencySymbol, TokenName, Integer)]) && (txInfoMint info /= mempty)
    in if hasArticleInput && nonZeroMint then () else error ()

lpMintingPolicy :: MintingPolicy
lpMintingPolicy = mkMintingPolicyScript $$(PlutusTx.compile [|| mkEntPolicy ||])

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
    Address (ScriptCredential (plutusValidatorHash validator)) Nothing

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
    writeValidator "article-validator.plutus" validator
    writeCBOR "article-validator.cbor" validator
    let mp      = lpMintingPolicy
        vh      = plutusValidatorHash validator
        onchain = plutusScriptAddress
        bech32  = toBech32ScriptAddress network validator
    putStrLn "\n--- Article Paywall Validator Info ---"
    putStrLn $ "Validator Hash (Plutus): " <> P.show vh
    putStrLn $ "Plutus Script Address:    " <> P.show onchain
    putStrLn $ "Bech32 Script Address:    " <> bech32
    putStrLn "---------------------------------"
    putStrLn "Article paywall validator & entitlement policy generated successfully."
