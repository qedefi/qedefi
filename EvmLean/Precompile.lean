import EvmLean.Machine.Types
import EvmLean.Crypto.Secp256k1

/-!
# Precompiled contracts

Addresses `0x01`–`0x0a` (Cancun), `0x0b`–`0x11` (Prague, EIP-2537) and `0x100` (Osaka,
EIP-7951). Each precompile charges gas, then succeeds with output or fails consuming all gas.
Mirrors `vm/precompiled_contracts/*.py`. Cryptography goes through the `Crypto` record, so the
semantics stays parameterised; `MODEXP` uses plain `Nat` arithmetic.
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
  /-- `0x0b`: BLS12-381 `G1` addition (EIP-2537, Prague). -/
  | blsG1Add
  /-- `0x0c`: BLS12-381 `G1` multi-scalar multiplication (EIP-2537, Prague). -/
  | blsG1Msm
  /-- `0x0d`: BLS12-381 `G2` addition (EIP-2537, Prague). -/
  | blsG2Add
  /-- `0x0e`: BLS12-381 `G2` multi-scalar multiplication (EIP-2537, Prague). -/
  | blsG2Msm
  /-- `0x0f`: BLS12-381 pairing check (EIP-2537, Prague). -/
  | blsPairing
  /-- `0x10`: map an `𝔽ₚ` element to `G1` (EIP-2537, Prague). -/
  | blsMapFpToG1
  /-- `0x11`: map an `𝔽ₚ²` element to `G2` (EIP-2537, Prague). -/
  | blsMapFp2ToG2
  /-- `0x100`: secp256r1 (P-256) signature verification (EIP-7951, Osaka). -/
  | p256Verify
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

/-- The precompiles added in Prague (EIP-2537), by address. -/
def pragueOfNat : Nat → Option Kind
  | 0x0b => some .blsG1Add
  | 0x0c => some .blsG1Msm
  | 0x0d => some .blsG2Add
  | 0x0e => some .blsG2Msm
  | 0x0f => some .blsPairing
  | 0x10 => some .blsMapFpToG1
  | 0x11 => some .blsMapFp2ToG2
  | _ => none

/-- The precompiles added in Osaka (EIP-7951), by address. -/
def osakaOfNat : Nat → Option Kind
  | 0x100 => some .p256Verify
  | _ => none

/-- The precompile at `a` in `fork`, if any (`PRE_COMPILED_CONTRACTS` of the fork). -/
def ofAddress (fork : Fork) (a : Address) : Option Kind :=
  match fork with
  | .cancun => cancunOfNat a.toNat
  | .prague => cancunOfNat a.toNat <|> pragueOfNat a.toNat
  | .osaka => cancunOfNat a.toNat <|> pragueOfNat a.toNat <|> osakaOfNat a.toNat

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

/-- Big-endian value of `b[lo, hi)` by balanced splitting (`Bytes.toNat` is quadratic). -/
def natOfSlice (b : ByteArray) : Nat → Nat → Nat → Nat
  | 0, lo, hi => Bytes.toNat (b.extract lo hi)
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 64 then Bytes.toNat (b.extract lo hi)
    else
      let mid := (lo + hi) / 2
      (natOfSlice b fuel lo mid <<< (8 * (hi - mid))) + natOfSlice b fuel mid hi

/-- `Uint.from_be_bytes(buffer_read(b, off, len))`, without materialising the zero padding. -/
def readNat (b : ByteArray) (off len : Nat) : Nat :=
  if off ≥ b.size then 0
  else
    let hi := min b.size (off + len)
    natOfSlice b 64 off hi <<< (8 * (off + len - hi))

/-- `n` as exactly `len` big-endian bytes by balanced splitting (`Bytes.ofNatBE` is quadratic). -/
def bytesOfNat : Nat → Nat → Nat → ByteArray
  | 0, len, n => Bytes.ofNatBE len n
  | fuel + 1, len, n =>
    if len ≤ 64 then Bytes.ofNatBE len n
    else
      let lo := len / 2
      bytesOfNat fuel (len - lo) (n >>> (8 * lo)) ++ bytesOfNat fuel lo (n % (1 <<< (8 * lo)))

/-! ## `ECRECOVER`, `SHA256`, `RIPEMD160`, `IDENTITY` -/

/-- `ECRECOVER`: an invalid signature is a *successful* call with empty output. -/
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

/-- `iterations` in `modexp.py`; `expHead` is the exponent's first ≤32 bytes, multiplier 8 or 16. -/
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

/-- `MODEXP`: `base ^ exp % modulus`, padded to the modulus length (zeros for a zero modulus). -/
def modexp (fork : Fork) (input : ByteArray) (gas : Nat) : Result :=
  let baseLen := readWord input 0
  let expLen := readWord input 32
  let modLen := readWord input 64
  -- EIP-7823 (Osaka): each length is at most 1024 bytes.
  if fork ≥ .osaka && (baseLen > 1024 || expLen > 1024 || modLen > 1024) then fail
  else
    -- Before Osaka a huge `baseLen` puts the exponent past the input end, where it reads as 0.
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

/-- `ECPAIRING`: gas for `⌊len/192⌋` pairs is charged before the length is checked. -/
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

/-- `BLAKE2F`: 213 bytes `rounds(4,BE) ‖ h(64,LE) ‖ m(128,LE) ‖ t(16,LE) ‖ f(1)`; gas = rounds. -/
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

/-- `POINT_EVALUATION`: 192 bytes `versioned_hash ‖ z ‖ y ‖ commitment ‖ proof`. -/
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

/-! ## BLS12-381 (EIP-2537, Prague) -/

/-- `G1_K_DISCOUNT`: MSM discount (per mille) for `k = 1 … 128` pairs in `G1`. -/
def g1KDiscount : Array Nat := #[
    1000, 949, 848, 797, 764, 750, 738, 728, 719, 712, 705, 698, 692, 687, 682, 677,
    673, 669, 665, 661, 658, 654, 651, 648, 645, 642, 640, 637, 635, 632, 630, 627,
    625, 623, 621, 619, 617, 615, 613, 611, 609, 608, 606, 604, 603, 601, 599, 598,
    596, 595, 593, 592, 591, 589, 588, 586, 585, 584, 582, 581, 580, 579, 577, 576,
    575, 574, 573, 572, 570, 569, 568, 567, 566, 565, 564, 563, 562, 561, 560, 559,
    558, 557, 556, 555, 554, 553, 552, 551, 550, 549, 548, 547, 547, 546, 545, 544,
    543, 542, 541, 540, 540, 539, 538, 537, 536, 536, 535, 534, 533, 532, 532, 531,
    530, 529, 528, 528, 527, 526, 525, 525, 524, 523, 522, 522, 521, 520, 520, 519]

/-- `G2_K_DISCOUNT`: MSM discount (per mille) for `k = 1 … 128` pairs in `G2`. -/
def g2KDiscount : Array Nat := #[
    1000, 1000, 923, 884, 855, 832, 812, 796, 782, 770, 759, 749, 740, 732, 724, 717,
    711, 704, 699, 693, 688, 683, 679, 674, 670, 666, 663, 659, 655, 652, 649, 646,
    643, 640, 637, 634, 632, 629, 627, 624, 622, 620, 618, 615, 613, 611, 609, 607,
    606, 604, 602, 600, 598, 597, 595, 593, 592, 590, 589, 587, 586, 584, 583, 582,
    580, 579, 578, 576, 575, 574, 573, 571, 570, 569, 568, 567, 566, 565, 563, 562,
    561, 560, 559, 558, 557, 556, 555, 554, 553, 552, 552, 551, 550, 549, 548, 547,
    546, 545, 545, 544, 543, 542, 541, 541, 540, 539, 538, 537, 537, 536, 535, 535,
    534, 533, 532, 532, 531, 530, 530, 529, 528, 528, 527, 526, 526, 525, 524, 524]

/-- `G1_MAX_DISCOUNT`: the discount for more than 128 pairs. -/
def g1MaxDiscount : Nat := 519

/-- `G2_MAX_DISCOUNT`: the discount for more than 128 pairs. -/
def g2MaxDiscount : Nat := 524

/-- MSM gas `k · mulCost · discount(k) / 1000`; `maxDiscount` applies above 128 pairs. -/
def msmGas (table : Array Nat) (maxDiscount mulCost k : Nat) : Nat :=
  let discount := if k ≤ 128 then table.getD (k - 1) maxDiscount else maxDiscount
  k * mulCost * discount / 1000

/-- A fixed-gas BLS operation on exactly `len` bytes; the length is checked before gas. -/
def blsFixed (len cost : Nat) (op : ByteArray → Option ByteArray) (input : ByteArray)
    (gas : Nat) : Result :=
  if input.size ≠ len then fail
  else if gas < cost then fail
  else
    match op input with
    | some out => { success := true, gasLeft := gas - cost, output := out }
    | none => fail

/-- An MSM: the input must be a non-empty multiple of `pairLen` bytes; gas by `msmGas`. -/
def blsMsm (pairLen : Nat) (table : Array Nat) (maxDiscount mulCost : Nat)
    (op : ByteArray → Option ByteArray) (input : ByteArray) (gas : Nat) : Result :=
  if input.size = 0 || input.size % pairLen ≠ 0 then fail
  else
    let cost := msmGas table maxDiscount mulCost (input.size / pairLen)
    if gas < cost then fail
    else
      match op input with
      | some out => { success := true, gasLeft := gas - cost, output := out }
      | none => fail

/-- `BLS12_PAIRING_CHECK`: a non-empty multiple of 384-byte `G1 ‖ G2` pairs; outputs `1` or `0`. -/
def blsPairing (crypto : Crypto) (input : ByteArray) (gas : Nat) : Result :=
  if input.size = 0 || input.size % 384 ≠ 0 then fail
  else
    let cost := 32600 * (input.size / 384) + 37700
    if gas < cost then fail
    else
      match crypto.bls12Pairing input with
      | some ok =>
        { success := true, gasLeft := gas - cost, output := Bytes.ofNatBE 32 (if ok then 1 else 0) }
      | none => fail

/-! ## `P256VERIFY` (EIP-7951, Osaka) -/

/-- `P256VERIFY`: a bad length or invalid signature is a *successful* call with empty output. -/
def p256Verify (crypto : Crypto) (input : ByteArray) (gas : Nat) : Result :=
  if gas < 6900 then fail
  else
    let gasLeft := gas - 6900
    if input.size ≠ 160 then { success := true, gasLeft, output := .empty }
    else
      let ok := crypto.p256Verify (input.extract 0 32) (readWord input 32) (readWord input 64)
        (readWord input 96) (readWord input 128)
      { success := true, gasLeft, output := if ok then Bytes.ofNatBE 32 1 else .empty }

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
  | .blsG1Add => blsFixed 256 375 crypto.bls12G1Add input gas
  | .blsG1Msm => blsMsm 160 g1KDiscount g1MaxDiscount 12000 crypto.bls12G1Msm input gas
  | .blsG2Add => blsFixed 512 600 crypto.bls12G2Add input gas
  | .blsG2Msm => blsMsm 288 g2KDiscount g2MaxDiscount 22500 crypto.bls12G2Msm input gas
  | .blsPairing => blsPairing crypto input gas
  | .blsMapFpToG1 => blsFixed 64 5500 crypto.bls12MapFpToG1 input gas
  | .blsMapFp2ToG2 => blsFixed 128 23800 crypto.bls12MapFp2ToG2 input gas
  | .p256Verify => p256Verify crypto input gas

/-- Run the precompile at `a`; a non-precompile address yields `fail`. -/
def run (crypto : Crypto) (fork : Fork) (a : Address) (input : ByteArray) (gas : Nat) : Result :=
  match ofAddress fork a with
  | some k => runKind crypto fork k input gas
  | none => fail

end EvmLean.Precompile
