import EvmTest.TxSupport

/-!
Unit tests for `EvmLean.Tx` (intrinsic gas, validation, `check_transaction`, blob fees) and
the RLP decoder / transaction codec. None of these need real hashing.
-/

open EvmLean EvmLean.Tx EvmTest

namespace EvmTest.TxTest

/-! ## RLP decoding: `ethereum/tests` `RLPTests/invalidRLPTest.json` and round trips -/

#guard rlpRejects (hx "0xbf0f000000000000021111")       -- int32Overflow
#guard rlpRejects (hx "0xff0f000000000000021111")       -- int32Overflow2
#guard rlpRejects (hx "0xf80180")                       -- wrongSizeList
#guard rlpRejects (hx "0xf80100")                       -- wrongSizeList2
#guard rlpRejects (hx "0x8100")                         -- bytesShouldBeSingleByte00
#guard rlpRejects (hx "0x8101")                         -- bytesShouldBeSingleByte01
#guard rlpRejects (hx "0x817F")                         -- bytesShouldBeSingleByte7F
#guard rlpRejects (hx "b800")                           -- leadingZerosInLongLengthArray2
#guard rlpRejects (hx "f800")                           -- leadingZerosInLongLengthList2
#guard rlpRejects (hx "b81000112233445566778899aabbccddeeff") -- nonOptimalLongLengthArray1
#guard rlpRejects (hx "b801ff")                         -- nonOptimalLongLengthArray2
#guard rlpRejects (hx "f810000102030405060708090a0b0c0d0e0f") -- nonOptimalLongLengthList1
#guard rlpRejects (hx "f803112233")                     -- nonOptimalLongLengthList2
#guard rlpRejects (hx "")                               -- emptyEncoding
#guard rlpRejects (hx "81")                             -- lessThanShortLengthArray1
#guard rlpRejects (hx "c5010203")                       -- lessThanShortLengthList1
#guard rlpRejects (hx "e201020304050607")               -- lessThanShortLengthList2
#guard rlpRejects (hx "ba010000aabbccddeeff")           -- lessThanLongLengthArray1
#guard rlpRejects (hx "b840ffeeddccbbaa99887766554433221100") -- lessThanLongLengthArray2
#guard rlpRejects (hx "f90180")                         -- lessThanLongLengthList1
#guard rlpRejects (hx "ffffffffffffffffff0001020304050607") -- lessThanLongLengthList2
#guard rlpRejects (hx "0x8080")                         -- trailing bytes

#guard rlpRoundtrips (hx "0x80")
#guard rlpRoundtrips (hx "0x7f")
#guard rlpRoundtrips (hx "0xc0")
#guard rlpRoundtrips (hx "0x83646f67")                  -- "dog"
#guard rlpRoundtrips (hx "0xc88363617483646f67")        -- ["cat", "dog"]
#guard rlpRoundtrips (hx "0xc7c0c1c0c3c0c1c0")          -- set-theoretic 3
#guard rlpRoundtrips (hx "0x820400")                    -- 1024
#guard rlpRoundtrips (hx genesisRlpHex)
#guard rlpRoundtrips (hx block1RlpHex)

-- Integers: leading zeros and over-wide values are rejected by the typed accessors.
#guard (Rlp.asU64 "x" (.bytes (hx "0x0001"))).toOption = none
#guard (Rlp.asU64 "x" (.bytes (hx "0x010000000000000000"))).toOption = none
#guard (Rlp.asU64 "x" (.bytes (hx "0xffffffffffffffff"))).toOption = some (2 ^ 64 - 1)
#guard (Rlp.asU256 "x" (.bytes .empty)).toOption = some 0
#guard (Rlp.asTo "to" (.bytes .empty)).toOption = some none
#guard (Rlp.asTo "to" (.bytes (hx "0x0102"))).toOption = none

/-! ## Transaction codec, on the fixture's block 1 (one transaction of each type) -/

#guard block1.transactions.map Transaction.typeByte = [0, 1, 2, 3]
#guard block1.transactions.map Transaction.nonce = [0, 1, 2, 3]
#guard block1.transactions.map Transaction.value = [1, 3, 5, 7]
#guard block1.transactions.all (·.to = some 0x100000000000000000000000000000000000000a)
#guard block1.transactions.map Transaction.gas = List.replicate 4 0xe8d4a51000
-- Decoding the canonical encoding gives back the same transaction.
#guard block1.transactions.all fun tx => (Transaction.decode tx.encode).toOption = some tx
-- The block re-encodes to the exact fixture bytes.
#guard (Block.toRlp block1).encode == hx block1RlpHex
#guard match block1.transactions with
  | [_, _, _, .eip4844 t] =>
    t.maxFeePerBlobGas = 10 && t.blobVersionedHashes =
      [hw "0x01a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8"]
  | _ => false
-- Unsupported type byte and blob creation are decoding errors.
#guard (Transaction.decode (hx "0x04c0")).toOption = none
#guard (Transaction.decode (hx "0x00c0")).toOption = none

/-! ## Intrinsic gas (`calculate_intrinsic_cost`) -/

/-- A legacy transaction template. -/
def legacyTx (to : Option Address := some 0xaa) (data : ByteArray := .empty) (gas := 100000)
    (gasPrice := 10) (nonce := 0) (value := 0) : Transaction :=
  .legacy { nonce, gasPrice, gas, to, value, data, v := 27, r := 1, s := 1 }

/-- An EIP-1559 transaction template. -/
def feeTx (maxFee maxPrio : Nat) (gas := 100000) (accessList : List AccessListItem := [])
    (chainId := 1) : Transaction :=
  .eip1559 { chainId, nonce := 0, maxPriorityFeePerGas := maxPrio, maxFeePerGas := maxFee, gas,
             to := some 0xaa, value := 0, data := .empty, accessList, yParity := 0, r := 1,
             s := 1 }

/-- A blob transaction template. -/
def blobTx (hashes : List Word) (maxFeePerBlobGas := 10) (gas := 100000) : Transaction :=
  .eip4844 { chainId := 1, nonce := 0, maxPriorityFeePerGas := 1, maxFeePerGas := 1000, gas,
             to := 0xaa, value := 0, data := .empty, accessList := [], maxFeePerBlobGas,
             blobVersionedHashes := hashes, yParity := 0, r := 1, s := 1 }

/-- A valid versioned hash (version byte `0x01`). -/
def vh : Word := hw "0x01a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8"

#guard (intrinsicGas (legacyTx)).regular = 21000
#guard (intrinsicGas (legacyTx (data := hx "0x0001"))).regular = 21000 + 4 + 16
#guard (intrinsicGas (legacyTx (data := hx "0x00000000ff"))).regular = 21000 + 4 * 4 + 16
-- Creation: 32000 plus 2 gas per init-code word (EIP-3860); 33 bytes = 2 words.
#guard (intrinsicGas (legacyTx (to := none) (data := Bytes.zeros 33))).regular = 21000 + 33 * 4 + 32000 + 4
#guard (intrinsicGas (legacyTx (to := none))).regular = 53000
-- Access list: 2400 per address, 1900 per key.
#guard (intrinsicGas (feeTx 10 1 (accessList := [⟨0xbb, [1, 2]⟩, ⟨0xcc, []⟩]))).regular =
  21000 + 2 * 2400 + 2 * 1900
-- EIP-7623 floor: 21000 + 10 per token (4 tokens per non-zero byte).
#guard (intrinsicGas (legacyTx (data := hx "0x0001"))).calldataFloor = 21000 + 10 * 5
#guard validate .prague (legacyTx (data := Bytes.zeros 100 ++ hx "0xff") (gas := 21000 + 416)) =
  .error (.intrinsicGasTooLow (21000 + 10 * 104) (21000 + 416))
#guard (validate .cancun (legacyTx (data := Bytes.zeros 100 ++ hx "0xff") (gas := 21000 + 416))).isOk
-- EIP-7825 (Osaka): gas limit cap 2^24.
#guard validate .osaka (legacyTx (gas := 2 ^ 24 + 1)) = .error (.gasLimitAboveCap (2 ^ 24 + 1))
#guard (validate .osaka (legacyTx (gas := 2 ^ 24))).isOk
#guard (validate .prague (legacyTx (gas := 2 ^ 24 + 1))).isOk
#guard Gas.initCodeCost 0 = 0
#guard Gas.initCodeCost 1 = 2
#guard Gas.initCodeCost 32 = 2
#guard Gas.initCodeCost 33 = 4

/-! ## `validate_transaction` -/

#guard (validate .cancun (legacyTx (gas := 21000))).toOption.map (·.regular) = some 21000
#guard validate .cancun (legacyTx (gas := 20999)) = .error (.intrinsicGasTooLow 21000 20999)
#guard validate .cancun (legacyTx (nonce := 2 ^ 64 - 1)) = .error (.nonceOverflow (2 ^ 64 - 1))
#guard (validate .cancun (legacyTx (nonce := 2 ^ 64 - 2))).toOption.map (·.regular) = some 21000
#guard validate .cancun (feeTx 10 11) = .error (.priorityFeeGreaterThanMaxFee 11 10)
#guard (validate .cancun (feeTx 10 10)).toOption.map (·.regular) = some 21000
-- EIP-3860: init code above 49152 bytes is invalid (gas is checked first).
#guard validate .cancun (legacyTx (to := none) (data := Bytes.zeros 49153) (gas := 10000000)) =
  .error (.initCodeSizeExceeded 49153)
#guard (validate .cancun (legacyTx (to := none) (data := Bytes.zeros 49152) (gas := 10000000))).isOk

/-! ## Signature fields and chain id -/

/-- A legacy transaction with the given signature values. -/
def signedLegacy (v r s : Nat) : Transaction :=
  .legacy { nonce := 0, gasPrice := 0, gas := 0, to := none, value := 0, data := .empty,
            v, r, s }

/-- An EIP-1559 transaction with the given y-parity. -/
def withParity (yParity : Nat) : Transaction :=
  .eip1559 { chainId := 1, nonce := 0, maxPriorityFeePerGas := 0, maxFeePerGas := 0, gas := 0,
             to := none, value := 0, data := .empty, accessList := [], yParity, r := 1, s := 1 }

#guard chainIdOf (legacyTx) = .ok none
#guard chainIdOf (signedLegacy 37 1 1) = .ok (some 1)
#guard chainIdOf (signedLegacy 38 1 1) = .ok (some 1)
#guard chainIdOf (signedLegacy 30 1 1) = .error (.invalidSignature .badV)
#guard recoveryId (signedLegacy 28 1 1) = .ok 1
#guard recoveryId (signedLegacy 38 1 1) = .ok 1
#guard resolveSender fakeCrypto (legacyTx) (some 0x1234) = .ok 0x1234
#guard resolveSender fakeCrypto (signedLegacy 27 0 1) (some 1) = .error (.invalidSignature .badR)
#guard resolveSender fakeCrypto (signedLegacy 27 Secp256k1.n 1) (some 1) =
  .error (.invalidSignature .badR)
#guard resolveSender fakeCrypto (signedLegacy 27 1 (Secp256k1.n / 2 + 1)) (some 1) =
  .error (.invalidSignature .badS)
#guard resolveSender fakeCrypto (signedLegacy 27 1 (Secp256k1.n / 2)) (some 1) = .ok 1
#guard resolveSender fakeCrypto (withParity 2) (some 1) = .error (.invalidSignature .badYParity)
-- Without a hint, recovery goes through `crypto.ecrecover` (which fails here).
#guard resolveSender fakeCrypto (legacyTx) none = .error (.invalidSignature .recoveryFailed)

/-! ## `check_transaction` -/

/-- The test sender. -/
def alice : Address := 0xa11ce

/-- A world where `alice` has `balance` wei and nonce `nonce`. -/
def worldWith (balance : Nat) (nonce := 0) (code : ByteArray := .empty) : World :=
  (∅ : World).insert alice { nonce, balance := BitVec.ofNat 256 balance, code }

/-- Block environment with base fee 7. -/
def env : BlockEnv := { chainId := 1, baseFee := 7, gasLimit := 30000000, coinbase := 0xc0 }

/-- `check` with plenty of block gas and the hint `alice`. -/
def chk (w : World) (tx : Transaction) (gasAvailable := 30000000)
    (blobGasAvailable := 786432) (e : BlockEnv := env) : Except InvalidTx Checked :=
  check fakeCrypto .cancun e gasAvailable blobGasAvailable w tx (some alice)

/-- The effective gas price, if the check passes. -/
def price (r : Except InvalidTx Checked) : Option Nat := r.toOption.map (·.effectiveGasPrice)

#guard price (chk (worldWith (10 ^ 18)) (legacyTx (gasPrice := 10))) = some 10
#guard price (chk (worldWith (10 ^ 18)) (feeTx 100 2)) = some 9      -- base 7 + tip 2
#guard price (chk (worldWith (10 ^ 18)) (feeTx 8 5)) = some 8        -- tip capped at 1
#guard (chk (worldWith (10 ^ 18)) (feeTx 6 1)).toOption.isNone          -- max fee < base fee
#guard chk (worldWith (10 ^ 18)) (feeTx 6 1) = .error (.insufficientMaxFeePerGas 6 7)
#guard chk (worldWith (10 ^ 18)) (legacyTx (gasPrice := 6)) = .error (.gasPriceBelowBaseFee 6 7)
#guard chk (worldWith (10 ^ 18)) (legacyTx) (gasAvailable := 99999) =
  .error (.gasAllowanceExceeded 100000 99999)
#guard chk (worldWith (10 ^ 18)) (feeTx 100 2 (chainId := 5)) = .error (.wrongChainId 1 5)
#guard chk (worldWith (10 ^ 18) (nonce := 1)) (legacyTx) = .error (.nonceTooLow 1 0)
#guard chk (worldWith (10 ^ 18)) (legacyTx (nonce := 1)) = .error (.nonceTooHigh 0 1)
#guard chk (worldWith (10 ^ 18) (code := hx "0x00")) (legacyTx) = .error .senderNotEOA
-- Balance must cover gas * price + value exactly.
#guard (chk (worldWith (100000 * 10 + 5)) (legacyTx (value := 5))).isOk
#guard chk (worldWith (100000 * 10 + 4)) (legacyTx (value := 5)) =
  .error (.insufficientBalance 1000004 1000005)
-- No wrap-around: an astronomically large gas * price is just unaffordable.
#guard chk (worldWith (2 ^ 256 - 1)) (legacyTx (gas := 2 ^ 200) (gasPrice := 2 ^ 100))
  (gasAvailable := 2 ^ 300) = .error (.insufficientBalance (2 ^ 256 - 1) (2 ^ 300))
-- Blob transactions.
#guard (chk (worldWith (10 ^ 18)) (blobTx [vh])).toOption.map (·.blobGasUsed) = some 131072
#guard chk (worldWith (10 ^ 18)) (blobTx []) = .error .noBlobData
#guard chk (worldWith (10 ^ 18)) (blobTx [vh + 2 ^ 248]) = .error .invalidBlobVersionedHash
#guard (chk (worldWith (10 ^ 18)) (blobTx [vh]) (e := { env with excessBlobGas := 2314058 })).isOk
#guard chk (worldWith (10 ^ 18)) (blobTx [vh] (maxFeePerBlobGas := 1))
  (e := { env with excessBlobGas := 2314058 }) = .error (.insufficientMaxFeePerBlobGas 1 2)
#guard chk (worldWith (10 ^ 18)) (blobTx (List.replicate 7 vh)) =
  .error (.blobGasLimitExceeded (7 * 131072) 786432)
#guard chk (worldWith (10 ^ 18)) (blobTx [vh]) (blobGasAvailable := 131071) =
  .error (.blobGasLimitExceeded 131072 131071)
-- The blob fee counts towards the balance requirement: 100000 * 1000 + 131072 * 10.
#guard chk (worldWith (100000 * 1000 + 131072 * 10 - 1)) (blobTx [vh]) =
  .error (.insufficientBalance (100000 * 1000 + 131072 * 10 - 1) (100000 * 1000 + 131072 * 10))

/-! ## Prague and Osaka checks -/

/-- An authorization tuple (only its count matters to the checks below). -/
def someAuth : Authorization :=
  { chainId := 1, address := 0xbb, nonce := 0, yParity := 0, r := 1, s := 1 }

/-- An EIP-7702 transaction template. -/
def setCodeTx (auths : List Authorization) (gas := 100000) : Transaction :=
  .eip7702 { chainId := 1, nonce := 0, maxPriorityFeePerGas := 1, maxFeePerGas := 1000, gas,
             to := 0xaa, value := 0, data := .empty, accessList := [], authorizations := auths,
             yParity := 0, r := 1, s := 1 }

/-- `check` at `fork` with the hint `alice`. -/
def chkAt (fork : Fork) (w : World) (tx : Transaction) : Except InvalidTx Checked :=
  check fakeCrypto fork env 30000000 1179648 w tx (some alice)

-- 25000 per authorization; set-code transactions only from Prague.
#guard (intrinsicGas (setCodeTx [someAuth, someAuth])).regular = 21000 + 2 * 25000
#guard validate .cancun (setCodeTx [someAuth]) = .error (.unsupportedType 4)
#guard (validate .prague (setCodeTx [someAuth])).isOk
#guard chkAt .prague (worldWith (10 ^ 18)) (setCodeTx []) = .error .emptyAuthorizationList
#guard (chkAt .prague (worldWith (10 ^ 18)) (setCodeTx [someAuth])).isOk
-- Codec round trip (`0x04 ‖ rlp(fields)`).
#guard (Transaction.decode (setCodeTx [someAuth]).encode).toOption = some (setCodeTx [someAuth])
#guard (setCodeTx [someAuth]).encode[0]? = some 4
-- EIP-3607 as amended by EIP-7702: a delegated sender is still an EOA.
#guard (chkAt .prague (worldWith (10 ^ 18) (code := Interpreter.delegationCode 0xbb))
  (legacyTx)).isOk
#guard chkAt .cancun (worldWith (10 ^ 18) (code := Interpreter.delegationCode 0xbb)) (legacyTx) =
  .error .senderNotEOA
-- Osaka: at most six blobs per transaction.
#guard chkAt .osaka (worldWith (10 ^ 18)) (blobTx (List.replicate 7 vh)) =
  .error (.blobCountExceeded 7)
#guard (chkAt .prague (worldWith (10 ^ 18)) (blobTx (List.replicate 7 vh))).isOk

/-! ## Blob gas price (`calculate_blob_gas_price`), values from the reference algorithm -/

#guard Gas.blobGasPrice .cancun 0 = 1
#guard Gas.blobGasPrice .cancun 2314057 = 1
#guard Gas.blobGasPrice .cancun 2314058 = 2
#guard Gas.blobGasPrice .cancun 3932160 = 3
#guard Gas.blobGasPrice .cancun 16692385 = 148
#guard Gas.blobGasPrice .cancun 100000000 = 10203769476395
#guard totalBlobGas (blobTx [vh, vh]) = 262144

/-! ## EIP-161 helpers -/

#guard creditBalance ∅ 0xbeef 0 = ∅
#guard (creditBalance ∅ 0xbeef 5).contains 0xbeef
#guard creditBalance ((∅ : World).insert 0xbeef {}) 0xbeef 0 = ∅
#guard destroyTouchedEmpty ((∅ : World).insert 0xbeef {}) ((∅ : AddressSet).insert 0xbeef) = ∅
#guard (destroyTouchedEmpty (worldWith 1) ((∅ : AddressSet).insert alice)).contains alice

end EvmTest.TxTest
