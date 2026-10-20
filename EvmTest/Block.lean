import EvmTest.TxSupport

/-!
# Tests for `EvmLean.Block`

Hashing is stubbed; checks that need real Keccak live in `EvmTest/TxIntegration.lean`.
-/

open EvmLean EvmLean.Block EvmTest

namespace EvmTest.BlockTest

/-! ## Decoding the fixture's genesis and block 1 -/

#guard genesisBlock.header.number = 0
#guard genesisBlock.header.baseFeePerGas = 900
#guard genesisBlock.header.gasLimit = 0x016345785d8a0000
#guard genesisBlock.header.timestamp = 0x03b6
#guard genesisBlock.header.coinbase = 0xba5e000000000000000000000000000000000000
#guard genesisBlock.header.extraData == hx "0x42"
#guard genesisBlock.header.nonce == Bytes.zeros 8
#guard genesisBlock.header.prevRandao = 0x20000
#guard genesisBlock.header.stateRoot =
  hw "0x96c7a471e05d95a962c9860f966ebcf96b1e3867321ec408e86ffd3bd50a1c62"
#guard genesisBlock.transactions.isEmpty && genesisBlock.withdrawals.isEmpty &&
  genesisBlock.ommers.isEmpty
#guard (Block.toRlp genesisBlock).encode == hx genesisRlpHex
#guard block1.header.number = 1
#guard block1.header.gasUsed = 0x014820
#guard block1.header.blobGasUsed = 0x020000
#guard block1.header.parentHash =
  hw "0x5eb7f6da0f3e237c62bcae48b7fb5f4506d392616b62890429c8b76b4a1d4104"
-- A pre-Cancun (19-field) header, a 3-field block and a short bloom do not decode.
#guard (Block.decode (Rlp.list [.list (List.replicate 19 (.bytes .empty)), .list [], .list [],
  .list []]).encode).toOption.isNone
#guard (Block.decode (Rlp.list [Block.headerRlp genesisBlock.header, .list [], .list []]).encode).toOption.isNone
#guard (Block.decodeHeader (Block.headerRlp { genesisBlock.header with bloom := Bytes.zeros 255 })).toOption.isNone

/-! ## `calculate_base_fee_per_gas` (EIP-1559) -/

-- At target: unchanged. Full block: +1/8. Empty block: -1/8.
#guard calcBaseFeePerGas 30000000 15000000 1000000000 = 1000000000
#guard calcBaseFeePerGas 30000000 30000000 1000000000 = 1125000000
#guard calcBaseFeePerGas 30000000 0 1000000000 = 875000000
#guard calcBaseFeePerGas 30000000 20000000 1000000000 = 1041666666
#guard calcBaseFeePerGas 30000000 10000000 1000000000 = 958333334
-- An increase is at least 1.
#guard calcBaseFeePerGas 30000000 15000001 7 = 8
-- The fixture: genesis (base fee 900, empty) → block 1 (base fee 0x314 = 788).
#guard calcBaseFeePerGas genesisBlock.header.gasLimit genesisBlock.header.gasUsed
  genesisBlock.header.baseFeePerGas = block1.header.baseFeePerGas

/-! ## `calculate_excess_blob_gas` (EIP-4844) -/

def withBlobs (excess used : Nat) : Header :=
  { genesisBlock.header with excessBlobGas := excess, blobGasUsed := used }

#guard calcExcessBlobGas .cancun (withBlobs 0 0) = 0
#guard calcExcessBlobGas .cancun (withBlobs 0 393216) = 0
#guard calcExcessBlobGas .cancun (withBlobs 0 786432) = 393216
#guard calcExcessBlobGas .cancun (withBlobs 393216 393216) = 393216
#guard calcExcessBlobGas .cancun (withBlobs 100 393216) = 100
#guard calcExcessBlobGas .cancun (withBlobs 393216 0) = 0
#guard calcExcessBlobGas .cancun genesisBlock.header = block1.header.excessBlobGas

/-! ## `check_gas_limit` -/

-- Parent 30M: the adjustment bound is 30M / 1024 = 29296 (exclusive).
#guard checkGasLimit 30000000 30000000
#guard checkGasLimit (30000000 + 29295) 30000000
#guard !checkGasLimit (30000000 + 29296) 30000000
#guard checkGasLimit (30000000 - 29295) 30000000
#guard !checkGasLimit (30000000 - 29296) 30000000
#guard !checkGasLimit 4999 5000
#guard checkGasLimit 5000 5000

/-! ## `validate_header` -/

/-- Fake Keccak that knows the real `EMPTY_OMMER_HASH`, so validation can get past it. -/
def stubKeccak (b : ByteArray) : Word :=
  if b == (Rlp.list []).encode then
    hw "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"
  else fakeKeccak b

/-- Validate a modification of block 1's header against the genesis. -/
def vh (f : Header → Header) : Except HeaderError Unit :=
  validateHeader stubKeccak .cancun genesisBlock.header block1.header.parentHash (f block1.header)

#guard vh id = .ok ()
#guard vh (fun h => { h with number := 0 }) = .error .numberZero
#guard vh (fun h => { h with number := 2 }) = .error .numberMismatch
#guard vh (fun h => { h with excessBlobGas := 1 }) = .error (.excessBlobGasMismatch 0 1)
#guard vh (fun h => { h with gasUsed := h.gasLimit + 1 }) = .error .gasUsedAboveLimit
#guard vh (fun h => { h with gasLimit := h.gasLimit * 2, gasUsed := 0 }) =
  .error (.invalidGasLimit (genesisBlock.header.gasLimit * 2) genesisBlock.header.gasLimit)
#guard vh (fun h => { h with baseFeePerGas := 789 }) = .error (.baseFeeMismatch 788 789)
#guard vh (fun h => { h with timestamp := genesisBlock.header.timestamp }) =
  .error .timestampNotIncreasing
#guard vh (fun h => { h with extraData := Bytes.zeros 33 }) = .error .extraDataTooLong
#guard vh (fun h => { h with extraData := Bytes.zeros 32 }) = .ok ()
#guard vh (fun h => { h with difficulty := 1 }) = .error .nonzeroDifficulty
#guard vh (fun h => { h with nonce := hx "0x0000000000000001" }) = .error .nonzeroNonce
#guard vh (fun h => { h with ommersHash := 0 }) = .error .invalidOmmersHash
#guard vh (fun h => { h with parentHash := 0 }) = .error .parentHashMismatch
-- Without the real empty-ommers hash, validation stops at the ommers hash.
#guard validateHeader fakeKeccak .cancun genesisBlock.header block1.header.parentHash
  block1.header = .error .invalidOmmersHash

/-! ## Blooms and receipts -/

/-- A "hash" whose first three 16-bit words are 1, 2 and 0x0803 (= 3 mod 2048). -/
def bloomHash (_ : ByteArray) : Word := hw "0x0001000208030000000000000000000000000000000000000000000000000000"

#guard bloomBits bloomHash .empty = 0b1110
#guard logsBloom bloomHash #[] == Bytes.zeros 256
#guard logsBloom bloomHash #[{ address := 1, topics := #[5], data := .empty }] ==
  Bytes.zeros 255 ++ ⟨#[0x0e]⟩
#guard (logsBloom fakeKeccak #[{ address := 1, topics := #[5, 6], data := .empty }]).size = 256

def okReceipt : Receipt := { succeeded := true, cumulativeGasUsed := 21000,
                             bloom := Bytes.zeros 256, logs := #[] }

#guard receiptEncode 0 okReceipt ==
  (Rlp.list [.bytes ⟨#[1]⟩, .nat 21000, .bytes (Bytes.zeros 256), .list []]).encode
#guard receiptEncode 2 okReceipt == ⟨#[2]⟩ ++ receiptEncode 0 okReceipt
#guard receiptEncode 0 { okReceipt with succeeded := false } ==
  (Rlp.list [.bytes .empty, .nat 21000, .bytes (Bytes.zeros 256), .list []]).encode
#guard withdrawalEncode { index := 0, validatorIndex := 1, address := 2, amount := 3 } ==
  (Rlp.list [.nat 0, .nat 1, .bytes (Bytes.ofAddress 2), .nat 3]).encode

/-! ## Prague headers, EIP-7918, requests -/

/-- A Prague header (21 fields). -/
def pragueHeader : Header := { genesisBlock.header with requestsHash := some 0x1234 }

#guard (Block.decodeHeader (Block.headerRlp pragueHeader)).toOption = some pragueHeader
#guard (Block.decodeHeader (Block.headerRlp genesisBlock.header)).toOption = some genesisBlock.header
#guard (Block.decodeHeader (.list (List.replicate 22 (.bytes .empty)))).toOption.isNone

-- EIP-7918 (Osaka): with a blob base fee below the execution cost of a blob, the excess grows
-- by `used · 3 / 9` instead of `used − target` (parent base fee 900, blob base fee 1).
#guard calcExcessBlobGas .prague (withBlobs 0 917504) = 131072
#guard calcExcessBlobGas .osaka (withBlobs 0 917504) = 917504 * 3 / 9
#guard calcExcessBlobGas .osaka { withBlobs 0 917504 with baseFeePerGas := 0 } = 131072
#guard calcExcessBlobGas .osaka (withBlobs 0 786431) = 0

def w32 (n : Nat) : ByteArray := Bytes.ofNatBE 32 n

/-- `b` right-padded with zeros to `n` bytes (Solidity ABI). -/
def rpad (b : ByteArray) (n : Nat) : ByteArray := b ++ Bytes.zeros (n - b.size)

/-- An ABI-encoded `DepositEvent` payload. -/
def depositData (pk wc amount sig index : ByteArray) : ByteArray :=
  w32 160 ++ w32 256 ++ w32 320 ++ w32 384 ++ w32 512 ++ w32 48 ++ rpad pk 64 ++ w32 32 ++ wc
    ++ w32 8 ++ rpad amount 32 ++ w32 96 ++ sig ++ w32 8 ++ rpad index 32

def pk : ByteArray := Bytes.ofNatBE 48 1
def wc : ByteArray := Bytes.ofNatBE 32 2
/-- Little-endian gwei in the real contract; opaque here. -/
def amt : ByteArray := Bytes.ofNatBE 8 3
def sig : ByteArray := Bytes.ofNatBE 96 4
def idx : ByteArray := Bytes.ofNatBE 8 5

#guard (depositData pk wc amt sig idx).size = 576
#guard extractDepositData (depositData pk wc amt sig idx) = some (pk ++ wc ++ amt ++ sig ++ idx)
#guard extractDepositData ((depositData pk wc amt sig idx).extract 0 575) = none
#guard extractDepositData (w32 161 ++ (depositData pk wc amt sig idx).extract 32 576) = none

def depositLog (data : ByteArray) (topic : Word := depositEventSignatureHash) : Log :=
  { address := depositContractAddress, topics := #[topic], data }

#guard (parseDepositRequests #[depositLog (depositData pk wc amt sig idx)]).toOption =
  some (pk ++ wc ++ amt ++ sig ++ idx)
-- Other events of the deposit contract are ignored; a malformed deposit invalidates the block.
#guard (parseDepositRequests #[depositLog .empty (topic := 1)]).toOption = some .empty
#guard (parseDepositRequests #[depositLog .empty]).toOption.isNone
-- `sha256` of nothing: the requests hash of a block without requests.
#guard computeRequestsHash Crypto.real.sha256 [] =
  hw "0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

/-! ## Withdrawals (gwei → wei, EIP-161 clean-up) -/

#guard (applyWithdrawals ∅ [{ index := 0, validatorIndex := 0, address := 7, amount := 2 }]).account 7
  = { balance := 2000000000 }
#guard applyWithdrawals ∅ [{ index := 0, validatorIndex := 0, address := 7, amount := 0 }] = ∅

/-! ## Block environment -/

#guard (blockEnv 1 block1.header [5, 4, 3]).blockHashes = [5, 4, 3]
#guard (blockEnv 1 block1.header ((List.range 300).map (BitVec.ofNat 256 ·))).blockHashes.length = 256
#guard (blockEnv 1 block1.header []).baseFee = 788

end EvmTest.BlockTest
