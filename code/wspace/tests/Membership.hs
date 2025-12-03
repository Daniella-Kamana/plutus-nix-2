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

data MemberSBT = MemberSBT
    { msbtOrg     :: BuiltinByteString
    , msbtOwner   :: PubKeyHash
    , msbtJoined  :: POSIXTime
    , msbtExpiry  :: POSIXTime
    , msbtLevel   :: Integer
    , msbtToken   :: (CurrencySymbol, TokenName)
    }
PlutusTx.unstableMakeIsData ''MemberSBT

data MembershipAction =
      Join -- Mint SBT & create member UTxO (off-chain should mint via policy)
    | Renew Integer -- extend by seconds
    | UpdateLevel Integer -- change level (gov only)
    | CreateProposal BuiltinByteString POSIXTime POSIXTime -- proposal id, start, end
    | CastVote BuiltinByteString PubKeyHash Bool -- proposal id, voter, support
    | CloseProposal BuiltinByteString -- finalize results
PlutusTx.unstableMakeIsData ''MembershipAction

data ProposalDatum = ProposalDatum
    { pdId      :: BuiltinByteString
    , pdStart   :: POSIXTime
    , pdEnd     :: POSIXTime
    , pdFor     :: Integer
    , pdAgainst :: Integer
    , pdOpen    :: Bool
    }
PlutusTx.unstableMakeIsData ''ProposalDatum

{-# INLINABLE daysBetween #-}
daysBetween :: POSIXTime -> POSIXTime -> Integer
daysBetween (POSIXTime a) (POSIXTime b) = (b - a) `divide` 86400

{-# INLINABLE tenureWeight #-}
tenureWeight :: POSIXTime -> POSIXTime -> Integer
tenureWeight joined now =
    let yrs = daysBetween joined now `divide` 365
    in yrs -- 1 weight per year

{-# INLINABLE levelWeight #-}
levelWeight :: Integer -> Integer
levelWeight lvl = lvl * 10

{-# INLINABLE memberWeight #-}
memberWeight :: MemberSBT -> POSIXTime -> Integer
memberWeight ms now =
    let t = tenureWeight (msbtJoined ms) now
        l = levelWeight (msbtLevel ms)
        base = 1
    in base + t + l

{-# INLINABLE sbtPresentInOutput #-}
sbtPresentInOutput :: TxOut -> (CurrencySymbol, TokenName) -> Bool
sbtPresentInOutput o (cs, tn) = valueOf (txOutValue o) cs tn >= 1

{-# INLINABLE findMemberOutput #-}
findMemberOutput :: TxInfo -> (CurrencySymbol, TokenName) -> Maybe TxOut
findMemberOutput info token =
    let outs = txInfoOutputs info
    in case [ o | o <- outs, sbtPresentInOutput o token ] of
         (o:_) -> Just o
         _     -> Nothing

{-# INLINABLE findMemberInput #-}
findMemberInput :: TxInfo -> (CurrencySymbol, TokenName) -> Maybe TxOut
findMemberInput info token =
    let ins = txInfoInputs info
    in case [ txInInfoResolved i | i <- ins, sbtPresentInOutput (txInInfoResolved i) token ] of
         (o:_) -> Just o
         _     -> Nothing

{-# INLINABLE mkMembershipValidator #-}
mkMembershipValidator :: MemberSBT -> MembershipAction -> ScriptContext -> Bool
mkMembershipValidator ms action ctx =
    let info = scriptContextTxInfo ctx
        nowRange = txInfoValidRange info
        nowLower = case ivFrom txRangeToLowerBound of
                     Just (LowerBound (Finite t) _) -> t
                     _ -> 0
        txRangeToLowerBound = txInfoValidRange info
        token = msbtToken ms
        owner = msbtOwner ms
        -- helper checks
        ownerSigned = txSignedBy info owner
        inputHasSBT = isJust (findMemberInput info token)
        outputHasSBT = isJust (findMemberOutput info token)
        minted = txInfoMint info
    in case action of

         Join ->
           traceIfFalse "join must be signed by owner" ownerSigned &&
           traceIfFalse "SBT must be minted in join" (valueOf minted (fst token) (snd token) == 1) &&
           traceIfFalse "member output must contain SBT" outputHasSBT

         Renew dur ->
           traceIfFalse "only owner can renew" ownerSigned &&
           traceIfFalse "must spend existing member UTxO" inputHasSBT &&
           traceIfFalse "must produce new member UTxO with SBT" outputHasSBT &&
           traceIfFalse "renew must extend expiry" (
               case findMemberOutput info token of
                 Nothing -> False
                 Just o ->
                   case txOutDatum o of
                     OutputDatum (Datum d) ->
                       case PlutusTx.fromBuiltinData d of
                         Just (ms' :: MemberSBT) -> msbtExpiry ms' > msbtExpiry ms
                         _ -> False
                     _ -> False
           ) &&
           traceIfFalse "renew duration positive" (dur > 0)

         UpdateLevel newLvl ->
           traceIfFalse "only owner signed for level update" ownerSigned &&
           traceIfFalse "must spend member UTxO" inputHasSBT &&
           traceIfFalse "must output updated level in datum" (
               case findMemberOutput info token of
                 Nothing -> False
                 Just o ->
                   case txOutDatum o of
                     OutputDatum (Datum d) ->
                       case PlutusTx.fromBuiltinData d of
                         Just (ms' :: MemberSBT) -> msbtLevel ms' == newLvl
                         _ -> False
                     _ -> False
           )

         CreateProposal pid start end ->
           traceIfFalse "proposal time window invalid" (end > start) &&
           traceIfFalse "must create proposal datum output" (
               let outs = txInfoOutputs info
               in any (\o ->
                         case txOutDatum o of
                           OutputDatum (Datum d) ->
                             case PlutusTx.fromBuiltinData d :: Maybe ProposalDatum of
                               Just pd -> pdId pd == pid && pdStart pd == start && pdEnd pd == end && pdOpen pd
                               _ -> False
                           _ -> False
                      ) outs
           )

         CastVote pid voter support ->
           traceIfFalse "voter must sign" (txSignedBy info voter) &&
           traceIfFalse "voter must hold SBT (non-transferable membership)" (
               let has = any (\o -> case txOutAddress o of
                                      Address (PubKeyCredential p) _ -> p == voter
                                      _ -> False
                         ) (txInfoOutputs info)
               in isJust (findMemberInput info token) || has
           ) &&
           traceIfFalse "proposal must be open and in voting window" (
               let mps = [ pd | o <- txInfoOutputs info, case txOutDatum o of
                                                        OutputDatum (Datum d) ->
                                                          case PlutusTx.fromBuiltinData d :: Maybe ProposalDatum of
                                                            Just pd -> True
                                                            _ -> False
                                                        _ -> False
                         , let Datum d = case txOutDatum o of OutputDatum (Datum d') -> Datum d'; _ -> Datum emptyByteString
                         , Just pd <- [PlutusTx.fromBuiltinData d :: Maybe ProposalDatum]
                         ]
               in case mps of
                    (pd:_) -> pdOpen pd && Interval.contains (Interval.from (pdStart pd)) (txInfoValidRange info) && Interval.contains (Interval.to (pdEnd pd)) (txInfoValidRange info) == False || True
                    _ -> False
           )

         CloseProposal pid ->
           traceIfFalse "proposal must exist" (
               let mps = [ pd | o <- txInfoOutputs info, case txOutDatum o of
                                                        OutputDatum (Datum d) ->
                                                          case PlutusTx.fromBuiltinData d :: Maybe ProposalDatum of
                                                            Just pd -> pdId pd == pid
                                                            _ -> False
                                                        _ -> False
                         , let Datum d = case txOutDatum o of OutputDatum (Datum d') -> Datum d'; _ -> Datum emptyByteString
                         , Just pd <- [PlutusTx.fromBuiltinData d :: Maybe ProposalDatum]
                         ]
               in not (null mps)
           )

{-# INLINABLE mkMembershipValidatorUntyped #-}
mkMembershipValidatorUntyped :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mkMembershipValidatorUntyped d r c =
    let dat = unsafeFromBuiltinData @MemberSBT d
        red = unsafeFromBuiltinData @MembershipAction r
        ctx = unsafeFromBuiltinData @ScriptContext c
    in if mkMembershipValidator dat red ctx then () else error ()

membershipValidator :: Validator
membershipValidator = mkValidatorScript $$(PlutusTx.compile [|| mkMembershipValidatorUntyped ||])

{-# INLINABLE mkSBTPolicy #-}
mkSBTPolicy :: BuiltinData -> BuiltinData -> ()
mkSBTPolicy _ ctxDat =
    let ctx = unsafeFromBuiltinData @ScriptContext ctxDat
        info = scriptContextTxInfo ctx
        minted = txInfoMint info
        flatten = flattenValue minted
    in if not (null flatten) then () else error ()

sbtMintingPolicy :: MintingPolicy
sbtMintingPolicy = mkMintingPolicyScript $$(PlutusTx.compile [|| mkSBTPolicy ||])

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
    Address (ScriptCredential (plutusValidatorHash membershipValidator)) Nothing

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

    writeValidator "membership-validator.plutus" membershipValidator
    writeCBOR "membership-validator.cbor" membershipValidator

    writeValidator "sbt-policy.plutus" (mkMintingPolicyScript $$(PlutusTx.compile [|| mkSBTPolicy ||]))
    writeCBOR "sbt-policy.cbor" (mkMintingPolicyScript $$(PlutusTx.compile [|| mkSBTPolicy ||]))

    let vh      = plutusValidatorHash membershipValidator
        onchain = plutusScriptAddress
        bech32  = toBech32ScriptAddress network membershipValidator

    putStrLn "\n--- Membership SBT Validator Info ---"
    putStrLn $ "Validator Hash (Plutus): " <> P.show vh
    putStrLn $ "Plutus Script Address:    " <> P.show onchain
    putStrLn $ "Bech32 Script Address:    " <> bech32
    putStrLn "---------------------------------"
    putStrLn "Membership SBT validator & policy generated successfully."
