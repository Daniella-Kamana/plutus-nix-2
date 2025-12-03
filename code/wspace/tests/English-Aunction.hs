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

-- Plutus core
import Plutus.V2.Ledger.Api
import Plutus.V2.Ledger.Contexts
import qualified Plutus.V2.Ledger.Api as PlutusV2
import Plutus.V1.Ledger.Interval as Interval
import Plutus.V1.Ledger.Value (valueOf, adaSymbol, adaToken, singleton)
import PlutusTx
import PlutusTx.Prelude hiding (Semigroup(..), unless)
import qualified PlutusTx.Builtins as Builtins

-- Serialization
import qualified Codec.Serialise as Serialise
import qualified Data.ByteString.Lazy  as LBS
import qualified Data.ByteString.Short as SBS
import qualified Data.ByteString       as BS

-- Cardano API (for Bech32 address)
import qualified Cardano.Api as C
import qualified Cardano.Api.Shelley as CS

------------------------------------------------------------------------
-- Auction Datum and Redeemer
------------------------------------------------------------------------

data AuctionDatum = AuctionDatum
    { adSeller     :: PubKeyHash
    , adCurrency   :: CurrencySymbol
    , adToken      :: TokenName
    , adMinBid     :: Integer
    , adDeadline   :: POSIXTime
    , adTopBid     :: Integer
    , adTopBidder  :: PubKeyHash
    , adBidBondBps :: Integer      -- basis points (e.g., 500 = 5%)
    }
PlutusTx.unstableMakeIsData ''AuctionDatum

data AuctionRedeemer = Bid | Settle | Cancel
PlutusTx.unstableMakeIsData ''AuctionRedeemer

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

{-# INLINABLE scriptInputValue #-}
scriptInputValue :: ScriptContext -> Value
scriptInputValue ctx =
    case findOwnInput ctx of
        Nothing -> traceError "no script input"
        Just i  -> txOutValue (txInInfoResolved i)

{-# INLINABLE bidBond #-}
bidBond :: Integer -> Integer -> Integer
bidBond b bps = divide (b * bps) 10000

------------------------------------------------------------------------
-- Validator Logic
------------------------------------------------------------------------

{-# INLINABLE mkAuctionValidator #-}
mkAuctionValidator :: AuctionDatum -> AuctionRedeemer -> ScriptContext -> Bool
mkAuctionValidator dat red ctx =
    case red of

      ------------------------------------------------------------------
      -- BID LOGIC
      ------------------------------------------------------------------
      Bid ->
           traceIfFalse "too late to bid"       beforeDeadline
        && traceIfFalse "bid too low"          newBidHigher
        && traceIfFalse "bidder signature"     bidderSigned
        && traceIfFalse "missing bond"         correctBondPaid
        && traceIfFalse "refund prev bidder"   refundPrevious
        && traceIfFalse "new datum incorrect"  correctUpdatedDatum

      ------------------------------------------------------------------
      -- SETTLE LOGIC
      ------------------------------------------------------------------
      Settle ->
           traceIfFalse "too early to settle"     afterDeadline
        && traceIfFalse "winner must sign"       winnerSigned
        && traceIfFalse "asset not sent to winner"  winnerGetsAsset
        && traceIfFalse "seller not paid"          sellerGetsFunds
        && traceIfFalse "bonds not refunded"       bondsRefunded

      ------------------------------------------------------------------
      -- CANCEL LOGIC
      ------------------------------------------------------------------
      Cancel ->
           traceIfFalse "too early to cancel"     afterDeadline
        && traceIfFalse "only seller may cancel"  sellerSigned
        && traceIfFalse "cannot cancel with bids" noBids
        && traceIfFalse "seller not get asset"    sellerGetsAsset

  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    txRange :: POSIXTimeRange
    txRange = txInfoValidRange info

    -- Bidding window checks
    beforeDeadline :: Bool
    beforeDeadline = Interval.contains (Interval.to (adDeadline dat - 1)) txRange

    afterDeadline :: Bool
    afterDeadline = Interval.contains (Interval.from (adDeadline dat + 1)) txRange

    bidderSigned :: Bool
    bidderSigned = txSignedBy info newTopBidder

    winnerSigned :: Bool
    winnerSigned = txSignedBy info (adTopBidder dat)

    sellerSigned :: Bool
    sellerSigned = txSignedBy info (adSeller dat)

    noBids :: Bool
    noBids = adTopBid dat == 0

    -------------------------------------------------------
    -- Continuing output and new datum extraction
    -- (Expect exactly 1 continuing output which holds the updated AuctionDatum)
    -------------------------------------------------------
    ownOutput :: TxOut
    ownOutput =
        case getContinuingOutputs ctx of
            [o] -> o
            _   -> traceError "expected exactly 1 continuing output"

    outDatum :: AuctionDatum
    outDatum =
        case txOutDatum ownOutput of
            OutputDatum d -> unsafeFromBuiltinData (getDatum d)
            _             -> traceError "datum must be inline"

    -------------------------------------------------------
    -- BID branch helpers
    -------------------------------------------------------
    newTopBid     = adTopBid outDatum
    newTopBidder  = adTopBidder outDatum
    newBidHigher  = newTopBid > adTopBid dat && newTopBid >= adMinBid dat

    -- Required bond for new bid (sent into script)
    newBondAmount :: Integer
    newBondAmount = bidBond newTopBid (adBidBondBps dat)

    correctBondPaid :: Bool
    correctBondPaid =
        let scriptValBefore = scriptInputValue ctx
            scriptValAfter  = txOutValue ownOutput
            -- difference of ADA locked into script (after - before) should equal bond
            diffAda = valueOf scriptValAfter adaSymbol adaToken - valueOf scriptValBefore adaSymbol adaToken
        in diffAda == newBondAmount

    -- Refund previous bidder their (oldBid + oldBond)
    refundPrevious :: Bool
    refundPrevious =
        if adTopBid dat == 0
           then True  -- no previous bidder to refund
           else
             let refundVal = valuePaidTo info (adTopBidder dat)
                 needed    = adTopBid dat + bidBond (adTopBid dat) (adBidBondBps dat)
             in valueOf refundVal adaSymbol adaToken >= needed

    correctUpdatedDatum :: Bool =
        adSeller dat      == adSeller outDatum      &&
        adCurrency dat    == adCurrency outDatum    &&
        adToken dat       == adToken outDatum       &&
        adDeadline dat    == adDeadline outDatum    &&
        adBidBondBps dat  == adBidBondBps outDatum

    -------------------------------------------------------
    -- SETTLE branch helpers
    -------------------------------------------------------
    asset :: Value
    asset = singleton (adCurrency dat) (adToken dat) 1

    winnerGetsAsset :: Bool =
        let paidToWinner = valuePaidTo info (adTopBidder dat)
        in valueOf paidToWinner (adCurrency dat) (adToken dat) >= 1

    sellerGetsFunds :: Bool =
        let paidToSeller = valuePaidTo info (adSeller dat)
        in valueOf paidToSeller adaSymbol adaToken >= adTopBid dat

    bondsRefunded :: Bool =
        -- For simplicity we require that the winner receives back their bond + their bid is routed accordingly.
        let bond = bidBond (adTopBid dat) (adBidBondBps dat)
            paidToWinner = valuePaidTo info (adTopBidder dat)
            paidToSeller = valuePaidTo info (adSeller dat)
        in (valueOf paidToWinner adaSymbol adaToken >= bond) &&
           (valueOf paidToSeller adaSymbol adaToken >= adTopBid dat)

    -------------------------------------------------------
    -- CANCEL branch helpers
    -------------------------------------------------------
    sellerGetsAsset :: Bool =
        let paidToSeller = valuePaidTo info (adSeller dat)
        in valueOf paidToSeller (adCurrency dat) (adToken dat) >= 1

------------------------------------------------------------------------
-- Untyped wrapper + Validator value
------------------------------------------------------------------------

{-# INLINABLE mkAuctionValidatorUntyped #-}
mkAuctionValidatorUntyped :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mkAuctionValidatorUntyped d r c =
    let dat = unsafeFromBuiltinData @AuctionDatum d
        red = unsafeFromBuiltinData @AuctionRedeemer r
        ctx = unsafeFromBuiltinData @ScriptContext c
    in if mkAuctionValidator dat red ctx then () else error ()

auctionValidator :: Validator
auctionValidator =
    mkValidatorScript $$(PlutusTx.compile [|| mkAuctionValidatorUntyped ||])

------------------------------------------------------------------------
-- On-chain (Plutus) hash and address helpers (same style as your escrow)
------------------------------------------------------------------------

{-# INLINABLE plutusValidatorHash #-}
plutusValidatorHash :: PlutusV2.Validator -> PlutusV2.ValidatorHash
plutusValidatorHash val =
    let bytes    = Serialise.serialise val
        short    = SBS.toShort (LBS.toStrict bytes)
        strictBS = SBS.fromShort short
        builtin  = Builtins.toBuiltin strictBS
    in PlutusV2.ValidatorHash builtin

{-# INLINABLE plutusScriptAddress #-}
plutusScriptAddress :: Address
plutusScriptAddress =
    Address (ScriptCredential (plutusValidatorHash auctionValidator)) Nothing

-- Off-chain (Cardano API) Bech32 address for CLI use
toBech32ScriptAddress :: C.NetworkId -> Validator -> String
toBech32ScriptAddress network val =
    let serialised = SBS.toShort . LBS.toStrict $ Serialise.serialise val
        plutusScript :: C.PlutusScript C.PlutusScriptV2
        plutusScript = CS.PlutusScriptSerialised serialised

        scriptHash = C.hashScript (C.PlutusScript C.PlutusScriptV2 plutusScript)

        -- The type annotation declares it's a Babbage-era address
        shelleyAddr :: C.AddressInEra C.BabbageEra
        shelleyAddr =
            C.makeShelleyAddressInEra
                network
                (C.PaymentCredentialByScript scriptHash)
                C.NoStakeAddress
    in T.unpack (C.serialiseAddress shelleyAddr)

------------------------------------------------------------------------
-- File writing
------------------------------------------------------------------------

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

    writeValidator "auction.plutus" auctionValidator

    let vh      = plutusValidatorHash auctionValidator
        onchain = plutusScriptAddress
        bech32  = toBech32ScriptAddress network auctionValidator

    putStrLn "\n--- English Auction Validator Info ---"
    putStrLn $ "Validator Hash (Plutus): " <> P.show vh
    putStrLn $ "Plutus Script Address:    " <> P.show onchain
    putStrLn $ "Bech32 Script Address:    " <> bech32
    putStrLn "---------------------------------"
    putStrLn "English Auction validator generated successfully."
