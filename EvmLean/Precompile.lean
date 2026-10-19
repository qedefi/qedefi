import EvmLean.Machine.Types
import EvmLean.Crypto.Secp256k1

/-!
# Precompiled contracts

Addresses `0x01`–`0x0a` (Cancun). Each precompile charges its gas, then either succeeds
with output or fails exceptionally, consuming all gas. Mirrors
`cancun/vm/precompiled_contracts/*.py` in `ethereum/execution-specs`:

| Address | Precompile | Gas | Spec |
|---|---|---|---|
| `0x01` | `ECRECOVER` | `3000` | Yellow Paper App. E |
| `0x02` | `SHA256` | `60 + 12·words` | Yellow Paper App. E |
| `0x03` | `RIPEMD160` | `600 + 120·words` | Yellow Paper App. E |
| `0x04` | `IDENTITY` | `15 + 3·words` | Yellow Paper App. E |
| `0x05` | `MODEXP` | `max(200, ⌊mult·iter/3⌋)` | EIP-198, EIP-2565 |
| `0x06` | `ECADD` | `150` | EIP-196, EIP-1108 |
| `0x07` | `ECMUL` | `6000` | EIP-196, EIP-1108 |
| `0x08` | `ECPAIRING` | `45000 + 34000·k` | EIP-197, EIP-1108 |
| `0x09` | `BLAKE2F` | `rounds` | EIP-152 |
| `0x0a` | `POINT_EVALUATION` | `50000` | EIP-4844 |

All cryptography goes through the `Crypto` record (`crypto.*`), never through a concrete
implementation, so the semantics stays parameterised. `MODEXP` uses plain `Nat` arithmetic
(`Nat.powMod`) with arbitrary-length base, exponent and modulus.

## Forks

`ofAddress` maps `(fork, address)` to a `Kind`, matching exhaustively on `Fork`, so new
precompiles slot in as new `Kind` constructors. Not yet implemented: Prague's BLS12-381
precompiles `0x0b`–`0x11` (EIP-2537) and Osaka's `P256VERIFY` at `0x100` (EIP-7951); for
those forks the Cancun set is returned. Osaka's `MODEXP` changes (EIP-7823 input bounds,
EIP-7883 repricing) are implemented, following `osaka/vm/precompiled_contracts/modexp.py`.
-/

namespace EvmLean.Precompile

/-- Outcome of a precompile call. -/
structure Result where
  /-- `false` on exceptional failure (out of gas or invalid input). -/
  success : Bool
  /-- Gas left (zero on failure). -/
  gasLeft : Nat
  /-- Output (empty on failure). -/
  output : ByteArray
  deriving Inhabited

/-- The precompiled contracts, in address order. -/
inductive Kind where
  /-- `0x01`: secp256k1 signer recovery. -/
  | ecrecover
  /-- `0x02`: SHA-256. -/
  | sha256
  /-- `0x03`: RIPEMD-160. -/
  | ripemd160
  /-- `0x04`: identity (data copy). -/
  | identity
  /-- `0x05`: modular exponentiation (EIP-198). -/
  | modexp
  /-- `0x06`: BN254 point addition (EIP-196). -/
  | ecAdd
  /-- `0x07`: BN254 scalar multiplication (EIP-196). -/
  | ecMul
  /-- `0x08`: BN254 pairing check (EIP-197). -/
  | ecPairing
  /-- `0x09`: BLAKE2b compression `F` (EIP-152). -/
  | blake2f
  /-- `0x0a`: KZG point evaluation (EIP-4844). -/
  | pointEvaluation
  deriving DecidableEq, Repr, Inhabited

/-- The precompiles active since Cancun, by address. -/
def cancunOfNat : Nat → Option Kind
  | 0x01 => some .ecrecover
  | 0x02 => some .sha256
  | 0x03 => some .ripemd160
  | 0x04 => some .identity
  | 0x05 => some .modexp
  | 0x06 => some .ecAdd
  | 0x07 => some .ecMul
  | 0x08 => some .ecPairing
  | 0x09 => some .blake2f
  | 0x0a => some .pointEvaluation
  | _ => none

/-- The precompile at `a` in `fork`, if any. Prague's BLS12-381 precompiles and Osaka's
`P256VERIFY` are not yet implemented, so later forks currently get the Cancun set. -/
def ofAddress (fork : Fork) (a : Address) : Option Kind :=
  match fork with
  | .cancun | .prague | .osaka => cancunOfNat a.toNat

/-- Is `a` a precompile address in `fork`? -/
def isPrecompile (fork : Fork) (a : Address) : Bool := (ofAddress fork a).isSome

/-! ## Helpers -/

/-- Exceptional failure: all gas consumed, no output. -/
def fail : Result := { success := false, gasLeft := 0, output := .empty }

/-- Number of 32-byte words covering `len` bytes (`ceil32(len) / 32`). -/
def wordCount (len : Nat) : Nat := (len + 31) / 32

/-- Left-pad `b` with zeros to 32 bytes (`left_pad_zero_bytes(b, 32)`). -/
def leftPad32 (b : ByteArray) : ByteArray := Bytes.zeros (32 - b.size) ++ b

/-- The big-endian word at `off`, zero-padded (`U256.from_be_bytes(buffer_read(…, 32))`). -/
def readWord (input : ByteArray) (off : Nat) : Nat := Bytes.toNat (Bytes.readPadded input off 32)

/-- Big-endian value of `b[lo, hi)` by balanced splitting, so that long inputs decode in
quasi-linear time (`Bytes.toNat` is quadratic). `fuel` bounds the recursion depth. -/
def natOfSlice (b : ByteArray) : Nat → Nat → Nat → Nat
  | 0, lo, hi => Bytes.toNat (b.extract lo hi)
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 64 then Bytes.toNat (b.extract lo hi)
    else
      let mid := (lo + hi) / 2
      (natOfSlice b fuel lo mid <<< (8 * (hi - mid))) + natOfSlice b fuel mid hi

/-- `Uint.from_be_bytes(buffer_read(b, off, len))`: the big-endian value of `len` bytes of
`b` at `off`, reading zeros past the end. Computed without materialising the padding. -/
def readNat (b : ByteArray) (off len : Nat) : Nat :=
  if off ≥ b.size then 0
  else
    let hi := min b.size (off + len)
    natOfSlice b 64 off hi <<< (8 * (off + len - hi))

/-- `n` as exactly `len` big-endian bytes (high bytes beyond `len` dropped), by balanced
splitting (`Bytes.ofNatBE` is quadratic in `len`). `fuel` bounds the recursion depth. -/
def bytesOfNat : Nat → Nat → Nat → ByteArray
  | 0, len, n => Bytes.ofNatBE len n
  | fuel + 1, len, n =>
    if len ≤ 64 then Bytes.ofNatBE len n
    else
      let lo := len / 2
      bytesOfNat fuel (len - lo) (n >>> (8 * lo)) ++ bytesOfNat fuel lo (n % (1 <<< (8 * lo)))

/-! ## `ECRECOVER`, `SHA256`, `RIPEMD160`, `IDENTITY` -/

/-- `ECRECOVER` (`ecrecover.py`): an invalid signature is a *successful* call with empty
output; the output is the signer address left-padded to 32 bytes. -/
def ecrecover (crypto : Crypto) (input : ByteArray) (gas : Nat) : Result :=
  if gas < 3000 then fail
  else
    let gasLeft := gas - 3000
    let noOutput : Result := { success := true, gasLeft, output := .empty }
    let hash := Bytes.readPadded input 0 32
    let v := readWord input 32
    let r := readWord input 64
    let s := readWord input 96
    if v ≠ 27 && v ≠ 28 then noOutput
    else if r = 0 || r ≥ Secp256k1.n || s = 0 || s ≥ Secp256k1.n then noOutput
    else
      match crypto.ecrecover hash (v - 27) r s with
      | none => noOutput
      | some pub =>
        let addr := (Bytes.ofWord (crypto.keccak256 pub)).extract 12 32
        { success := true, gasLeft, output := leftPad32 addr }

/-- `SHA256` (`sha256.py`). -/
def sha256 (crypto : Crypto) (input : ByteArray) (gas : Nat) : Result :=
  let cost := 60 + 12 * wordCount input.size
  if gas < cost then fail
  else { success := true, gasLeft := gas - cost, output := crypto.sha256 input }

/-- `RIPEMD160` (`ripemd160.py`): the 20-byte digest left-padded to 32 bytes. -/
def ripemd160 (crypto : Crypto) (input : ByteArray) (gas : Nat) : Result :=
  let cost := 600 + 120 * wordCount input.size
  if gas < cost then fail
  else { success := true, gasLeft := gas - cost, output := leftPad32 (crypto.ripemd160 input) }

/-- `IDENTITY` (`identity.py`). -/
def identity (input : ByteArray) (gas : Nat) : Result :=
  let cost := 15 + 3 * wordCount input.size
  if gas < cost then fail
  else { success := true, gasLeft := gas - cost, output := input }

/-! ## `MODEXP` (EIP-198, EIP-2565; EIP-7823 and EIP-7883 from Osaka) -/

/-- `iterations` in `modexp.py`: an estimate of the number of squarings, where
`expHead` is the first (at most) 32 bytes of the exponent. `lengthMultiplier` is `8` before
Osaka and `16` from Osaka (EIP-7883). `Nat.log2 x` is `bit_length(x) − 1` (and `0` for `0`). -/
def modexpIterations (lengthMultiplier expLen expHead : Nat) : Nat :=
  let count :=
    if expLen ≤ 32 then Nat.log2 expHead
    else lengthMultiplier * (expLen - 32) + Nat.log2 expHead
  max count 1

/-- `gas_cost` in `modexp.py` for `fork`. -/
def modexpGas (fork : Fork) (baseLen modLen expLen expHead : Nat) : Nat :=
  let words := (max baseLen modLen + 7) / 8
  if fork ≥ .osaka then
    -- EIP-7883.
    let complexity := if max baseLen modLen > 32 then 2 * words * words else 16
    max 500 (complexity * modexpIterations 16 expLen expHead)
  else
    -- EIP-2565.
    max 200 (words * words * modexpIterations 8 expLen expHead / 3)

/-- `MODEXP` (`modexp.py`): `base ^ exp % modulus` for arbitrary-length operands, output
left-padded to the modulus length (all zeros for a zero modulus). -/
def modexp (fork : Fork) (input : ByteArray) (gas : Nat) : Result :=
  let baseLen := readWord input 0
  let expLen := readWord input 32
  let modLen := readWord input 64
  -- EIP-7823 (Osaka): each length is at most 1024 bytes.
  if fork ≥ .osaka && (baseLen > 1024 || expLen > 1024 || modLen > 1024) then fail
  else
    -- Before Osaka a huge `baseLen` puts the exponent past the end of the input, where it
    -- reads as zero; `readNat` returns `0` for any offset past the end.
    let expHead := readNat input (96 + baseLen) (min 32 expLen)
    let cost := modexpGas fork baseLen modLen expLen expHead
    if gas < cost then fail
    else
      let gasLeft := gas - cost
      if baseLen = 0 && modLen = 0 then { success := true, gasLeft, output := .empty }
      else
        let base := readNat input 96 baseLen
        let exp := readNat input (96 + baseLen) expLen
        let modulus := readNat input (96 + baseLen + expLen) modLen
        let value := if modulus = 0 then 0 else Nat.powMod base exp modulus
        { success := true, gasLeft, output := bytesOfNat 64 modLen value }

/-! ## BN254 (EIP-196, EIP-197) -/

/-- `ECADD` (`alt_bn128_add`). -/
def ecAdd (crypto : Crypto) (input : ByteArray) (gas : Nat) : Result :=
  if gas < 150 then fail
  else
    match crypto.bn254Add input with
    | none => fail
    | some out => { success := true, gasLeft := gas - 150, output := out }

/-- `ECMUL` (`alt_bn128_mul`). -/
def ecMul (crypto : Crypto) (input : ByteArray) (gas : Nat) : Result :=
  if gas < 6000 then fail
  else
    match crypto.bn254Mul input with
    | none => fail
    | some out => { success := true, gasLeft := gas - 6000, output := out }

/-- `ECPAIRING` (`alt_bn128_pairing_check`): gas is charged for `⌊len/192⌋` pairs before
the length is checked; the output is the word `1` or `0`. -/
def ecPairing (crypto : Crypto) (input : ByteArray) (gas : Nat) : Result :=
  let cost := 45000 + 34000 * (input.size / 192)
  if gas < cost then fail
  else if input.size % 192 ≠ 0 then fail
  else
    match crypto.bn254Pairing input with
    | none => fail
    | some ok =>
      { success := true, gasLeft := gas - cost, output := Bytes.ofNatBE 32 (if ok then 1 else 0) }

/-! ## `BLAKE2F` (EIP-152) -/

/-- Byte `i` of `b`, or `0` past the end. -/
def byteAt (b : ByteArray) (i : Nat) : UInt8 := b[i]?.getD 0

/-- Little-endian 64-bit word at `off` (`spit_le_to_uint`). -/
def le64 (b : ByteArray) (off : Nat) : UInt64 :=
  ((List.range 8).foldr (fun i acc => acc * 256 + (byteAt b (off + i)).toNat) 0).toUInt64

/-- Little-endian serialisation of the state words. -/
def le64Bytes (h : Vector UInt64 8) : ByteArray :=
  ⟨(h.toList.flatMap fun w => (List.range 8).map fun j => (w >>> (8 * j).toUInt64).toUInt8).toArray⟩

/-- `BLAKE2F` (`blake2f.py`): exactly 213 bytes `rounds(4, BE) ‖ h(64, LE) ‖ m(128, LE) ‖
t(16, LE) ‖ f(1)`, with `f ∈ {0, 1}`; one gas per round. -/
def blake2f (crypto : Crypto) (input : ByteArray) (gas : Nat) : Result :=
  if input.size ≠ 213 then fail
  else
    let rounds := Bytes.toNat (input.extract 0 4)
    if gas < rounds then fail
    else
      let f := byteAt input 212
      if f > 1 then fail
      else
        let h := Vector.ofFn (n := 8) fun i => le64 input (4 + 8 * i.val)
        let m := Vector.ofFn (n := 16) fun i => le64 input (68 + 8 * i.val)
        let out := crypto.blake2f rounds h m (le64 input 196) (le64 input 204) (f = 1)
        { success := true, gasLeft := gas - rounds, output := le64Bytes out }

/-! ## `POINT_EVALUATION` (EIP-4844) -/

/-- `FIELD_ELEMENTS_PER_BLOB`. -/
def fieldElementsPerBlob : Nat := 4096

/-- `BLS_MODULUS`, the order of the BLS12-381 scalar field. -/
def blsModulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- `VERSIONED_HASH_VERSION_KZG`. -/
def versionedHashVersionKzg : UInt8 := 0x01

/-- `POINT_EVALUATION` (`point_evaluation.py`): input `versioned_hash ‖ z ‖ y ‖ commitment ‖
proof` (192 bytes). The versioned hash must be `0x01 ‖ sha256(commitment)[1:]`, `z` and `y`
canonical field elements (`bytes_to_bls_field` in `verify_kzg_proof`), and the proof valid. -/
def pointEvaluation (crypto : Crypto) (input : ByteArray) (gas : Nat) : Result :=
  if input.size ≠ 192 then fail
  else if gas < 50000 then fail
  else
    let versionedHash := input.extract 0 32
    let z := input.extract 32 64
    let y := input.extract 64 96
    let commitment := input.extract 96 144
    let proof := input.extract 144 192
    let expected := ByteArray.mk #[versionedHashVersionKzg] ++ (crypto.sha256 commitment).extract 1 32
    if versionedHash ≠ expected then fail
    else if Bytes.toNat z ≥ blsModulus || Bytes.toNat y ≥ blsModulus then fail
    else
      match crypto.kzgVerify commitment z y proof with
      | some true =>
        { success := true, gasLeft := gas - 50000,
          output := Bytes.ofNatBE 32 fieldElementsPerBlob ++ Bytes.ofNatBE 32 blsModulus }
      | some false | none => fail

/-! ## Dispatch -/

/-- Run precompile `k` in `fork`. -/
def runKind (crypto : Crypto) (fork : Fork) (k : Kind) (input : ByteArray) (gas : Nat) : Result :=
  match k with
  | .ecrecover => ecrecover crypto input gas
  | .sha256 => sha256 crypto input gas
  | .ripemd160 => ripemd160 crypto input gas
  | .identity => identity input gas
  | .modexp => modexp fork input gas
  | .ecAdd => ecAdd crypto input gas
  | .ecMul => ecMul crypto input gas
  | .ecPairing => ecPairing crypto input gas
  | .blake2f => blake2f crypto input gas
  | .pointEvaluation => pointEvaluation crypto input gas

/-- Run the precompile at `a` on `input` with `gas` available. Callers must first check
`isPrecompile`; a non-precompile address yields `fail`. -/
def run (crypto : Crypto) (fork : Fork) (a : Address) (input : ByteArray) (gas : Nat) : Result :=
  match ofAddress fork a with
  | some k => runKind crypto fork k input gas
  | none => fail

end EvmLean.Precompile
