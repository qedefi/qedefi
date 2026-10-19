import EvmLeanProofs.Bytes
import EvmLeanProofs.Word
import EvmLeanProofs.Solidity.SimpAttr

/-!
# Solidity ABI: calldata and return data of static types

The ABI encoding of a call to an external function with *static* arguments (`uintN`,
`address`, `bool`, `bytes32`, …) is

```
selector (4 bytes) ‖ arg₀ (32 bytes) ‖ arg₁ (32 bytes) ‖ …
```

where the selector is the first four bytes of `keccak256("name(type₀,type₁,…)")` and each
argument is one big-endian word (addresses and `bool`s zero-extended). Return data of static
values is the same without the selector.

## Selectors are data

A selector is a hash, but the compiled dispatcher only compares the first four calldata bytes
with *literals* (`PUSH4 sel EQ`). Selectors are therefore plain numbers here (taken from the
compiler's `--hashes` / `methodIdentifiers` output), never computed with `Crypto.keccak256`:
the semantics is parametric in `Crypto`, so a theorem about "the selector of `transfer`"
would otherwise have to assume something about the hash function. `selector` documents the
intended relation without being used by any proof.

## Main facts

* `size_encodeCall`: `CALLDATASIZE` of an encoded call is `4 + 32 · #args`.
* `calldataload_encodeCall`: `CALLDATALOAD (4 + 32 i)` of an encoded call is argument `i`.
* `shr_calldataload_zero`: `CALLDATALOAD 0 >> 224` (solc's `PUSH0 CALLDATALOAD PUSH1 0xe0
  SHR`) is the big-endian value of the first four calldata bytes, for *any* calldata
  (zero-padded); `selectorOf_encodeCall` computes it for an encoded call.
* `Bytes.toNat_append`, `Bytes.toNat_lt`, `readPadded_add`: the byte-level facts behind them.
-/

namespace EvmLean.Interpreter

/-- The bytes read by `readBytes` have the requested length. -/
theorem size_readBytes (b : ByteArray) (off len : Nat) : (readBytes b off len).size = len := by
  rw [readBytes_eq_readPadded, Bytes.size_readPadded]

end EvmLean.Interpreter

namespace EvmLean.Solidity

open Bytes Interpreter

/-! ## Big-endian values of concatenations -/

/-- Folding bytes big-endian from an accumulator. -/
private theorem foldl_bigEndian (l : List UInt8) (a : Nat) :
    l.foldl (fun acc x => acc * 256 + x.toNat) a =
      a * 256 ^ l.length + l.foldl (fun acc x => acc * 256 + x.toNat) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih, ih x.toNat, Nat.pow_succ]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    rw [Nat.mul_comm 256 (256 ^ xs.length)]

/-- A big-endian fold is below `(a + 1) · 256 ^ length`. -/
private theorem foldl_bigEndian_lt (l : List UInt8) :
    l.foldl (fun acc x => acc * 256 + x.toNat) 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [foldl_bigEndian, Nat.pow_succ]
    have hx := x.toNat_lt
    have : x.toNat * 256 ^ xs.length + 256 ^ xs.length ≤ 256 ^ xs.length * 256 := by
      rw [Nat.mul_comm (256 ^ xs.length) 256, ← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hx
    omega

/-- The big-endian value of a byte array, as a list fold. -/
private theorem toNat_eq_foldl_toList (b : ByteArray) :
    Bytes.toNat b = b.data.toList.foldl (fun acc x => acc * 256 + x.toNat) 0 := by
  rw [toNat_eq_foldl, Array.foldl_toList]

/-- The big-endian value of `x ‖ y`. -/
theorem Bytes.toNat_append (x y : ByteArray) :
    Bytes.toNat (x ++ y) = Bytes.toNat x * 256 ^ y.size + Bytes.toNat y := by
  rw [toNat_eq_foldl_toList, toNat_eq_foldl_toList x, toNat_eq_foldl_toList y,
    ByteArray.data_append, Array.toList_append, List.foldl_append, foldl_bigEndian,
    Array.length_toList]
  rfl

/-- The big-endian value of `n` bytes is below `256 ^ n`. -/
theorem Bytes.toNat_lt (b : ByteArray) : Bytes.toNat b < 256 ^ b.size := by
  rw [toNat_eq_foldl_toList]
  have := foldl_bigEndian_lt b.data.toList
  rwa [Array.length_toList] at this

/-! ## Slicing -/

/-- A padded read splits at any point. -/
theorem readPadded_add (b : ByteArray) (off m n : Nat) :
    readPadded b off (m + n) = readPadded b off m ++ readPadded b (off + m) n := by
  apply ext_getD (by simp [size_readPadded, ByteArray.size_append])
  intro j hj
  rw [size_readPadded] at hj
  rw [getD_append, size_readPadded]
  simp only [getD_readPadded]
  by_cases h : j < m
  · simp [h, show j < m + n by omega]
  · have : off + m + (j - m) = off + j := by omega
    simp [h, hj, show j - m < n by omega, this]

/-- `readBytes` splits at any point. -/
theorem readBytes_add (b : ByteArray) (off m n : Nat) :
    readBytes b off (m + n) = readBytes b off m ++ readBytes b (off + m) n := by
  simp only [readBytes_eq_readPadded, readPadded_add]

/-- Reading past a prefix. -/
theorem readPadded_append_shift (x y : ByteArray) (off len : Nat) :
    readPadded (x ++ y) (x.size + off) len = readPadded y off len := by
  apply ext_getD (by simp [size_readPadded])
  intro j hj
  rw [size_readPadded] at hj
  simp only [getD_readPadded, hj, ↓reduceIte, getD_append]
  have h1 : ¬ x.size + off + j < x.size := by omega
  have h2 : x.size + off + j - x.size = off + j := by omega
  simp only [h1, ↓reduceIte, h2]

/-- Reading inside a prefix. -/
theorem readPadded_append_of_le (x y : ByteArray) (off len : Nat) (h : off + len ≤ x.size) :
    readPadded (x ++ y) off len = readPadded x off len := by
  apply ext_getD (by simp [size_readPadded])
  intro j hj
  rw [size_readPadded] at hj
  simp only [getD_readPadded, hj, ↓reduceIte, getD_append, show off + j < x.size by omega]

/-- `readBytes` past a prefix. -/
theorem readBytes_append_shift (x y : ByteArray) (off len : Nat) :
    readBytes (x ++ y) (x.size + off) len = readBytes y off len := by
  simp only [readBytes_eq_readPadded, readPadded_append_shift]

/-- `readBytes` inside a prefix. -/
theorem readBytes_append_of_le (x y : ByteArray) (off len : Nat) (h : off + len ≤ x.size) :
    readBytes (x ++ y) off len = readBytes x off len := by
  simp only [readBytes_eq_readPadded, readPadded_append_of_le x y off len h]

namespace Abi

/-! ## Encoding -/

/-- The 4 selector bytes (big-endian) of selector `sel`. -/
def selectorBytes (sel : Nat) : ByteArray := Bytes.ofNatBE 4 sel

/-- The ABI encoding of static values: one big-endian word each (also the return data of a
function returning static values). -/
def encodeArgs : List Word → ByteArray
  | [] => .empty
  | a :: as => Bytes.ofWord a ++ encodeArgs as

/-- Calldata of a call to the function with selector `sel` and static arguments `args`. -/
def encodeCall (sel : Nat) (args : List Word) : ByteArray := selectorBytes sel ++ encodeArgs args

/-- The ABI word of a `bool`. -/
def encodeBool (b : Bool) : Word := if b then 1 else 0

/-- The selector `sel` of a function signature: the first four bytes of its Keccak-256
hash. Documentation only (see the module docstring): proofs use selector literals. -/
def selector (crypto : Crypto) (signature : String) : Nat :=
  Bytes.toNat ((Bytes.ofWord (crypto.keccak256 signature.toUTF8)).extract 0 4)

/-- The selector that solc's dispatcher computes from calldata (`CALLDATALOAD 0 >> 224`): the
first four bytes, zero-padded. -/
def selectorOf (data : ByteArray) : Nat := Bytes.toNat (readBytes data 0 4)

/-- `encodeArgs` has one word per argument. -/
theorem size_encodeArgs (as : List Word) : (encodeArgs as).size = 32 * as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [encodeArgs, ByteArray.size_append, size_ofWord, ih, List.length_cons]
    omega

/-- `CALLDATASIZE` of an encoded call. -/
@[sol_norm] theorem size_encodeCall (sel : Nat) (args : List Word) :
    (encodeCall sel args).size = 4 + 32 * args.length := by
  simp only [encodeCall, selectorBytes, ByteArray.size_append, size_ofNatBE, size_encodeArgs]

/-- Word `i` of encoded static values. -/
theorem readBytes_encodeArgs (as : List Word) (i : Nat) (h : i < as.length) :
    readBytes (encodeArgs as) (32 * i) 32 = Bytes.ofWord as[i] := by
  induction as generalizing i with
  | nil => simp at h
  | cons a as ih =>
    cases i with
    | zero =>
      simp only [encodeArgs, Nat.mul_zero, List.getElem_cons_zero]
      have := readBytes_append_left (Bytes.ofWord a) (encodeArgs as)
      rwa [size_ofWord] at this
    | succ i =>
      simp only [List.length_cons] at h
      simp only [encodeArgs, List.getElem_cons_succ]
      have := readBytes_append_shift (Bytes.ofWord a) (encodeArgs as) (32 * i) 32
      rw [size_ofWord, show 32 + 32 * i = 32 * (i + 1) by omega] at this
      rw [this, ih i (by omega)]

/-- **`CALLDATALOAD (4 + 32 i)` of an encoded call is argument `i`.** -/
theorem calldataload_encodeCall (sel : Nat) (args : List Word) (i : Nat) (h : i < args.length) :
    Bytes.toWord (readBytes (encodeCall sel args) (4 + 32 * i) 32) = args[i] := by
  have := readBytes_append_shift (selectorBytes sel) (encodeArgs args) (32 * i) 32
  rw [selectorBytes, size_ofNatBE] at this
  rw [encodeCall, selectorBytes, this, readBytes_encodeArgs args i h, toWord_ofWord]

/-- The first four bytes of an encoded call are the selector. -/
@[sol_norm] theorem selectorOf_encodeCall (sel : Nat) (args : List Word) :
    selectorOf (encodeCall sel args) = sel % 2 ^ 32 := by
  have := readBytes_append_left (selectorBytes sel) (encodeArgs args)
  rw [selectorBytes, size_ofNatBE] at this
  rw [selectorOf, encodeCall, selectorBytes, this, toNat_ofNatBE]

/-- **solc's selector extraction** (`PUSH0 CALLDATALOAD PUSH1 0xe0 SHR`): the first calldata
word shifted right by 224 bits is the big-endian value of the first four calldata bytes. Holds
for all calldata, including calldata shorter than four bytes (zero-padded). -/
@[sol_norm] theorem shr_calldataload_zero (data : ByteArray) :
    Word.shr (BitVec.ofNat 256 224) (Bytes.toWord (readBytes data 0 32)) =
      BitVec.ofNat 256 (selectorOf data) := by
  have hsplit := readBytes_add data 0 4 28
  rw [show 4 + 28 = 32 from rfl, Nat.zero_add] at hsplit
  have ha := Bytes.toNat_lt (readBytes data 0 4)
  have hb := Bytes.toNat_lt (readBytes data 4 28)
  rw [size_readBytes] at ha hb
  apply BitVec.eq_of_toNat_eq
  simp only [Word.shr, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, toWord, hsplit,
    Bytes.toNat_append, size_readBytes, BitVec.toNat_ofNat, selectorOf]
  generalize Bytes.toNat (readBytes data 0 4) = a at ha ⊢
  generalize Bytes.toNat (readBytes data 4 28) = b at hb ⊢
  rw [show 224 % 2 ^ 256 = 224 by decide, Nat.shiftRight_eq_div_pow]
  have hlt : a * 256 ^ 28 + b < 2 ^ 256 := by
    have : a * 256 ^ 28 + b < (a + 1) * 256 ^ 28 := by rw [Nat.succ_mul]; omega
    have h2 : (a + 1) * 256 ^ 28 ≤ 256 ^ 4 * 256 ^ 28 := Nat.mul_le_mul_right _ ha
    have h3 : (256 : Nat) ^ 4 * 256 ^ 28 = 2 ^ 256 := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : a < 2 ^ 256)]
  have h4 : (2 : Nat) ^ 224 = 256 ^ 28 := by decide
  rw [h4, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hb]
  omega

/-- `CALLDATALOAD 4`: the first argument. -/
@[sol_norm] theorem calldataload_encodeCall_0 (sel : Nat) (a : Word) (as : List Word) :
    Bytes.toWord (readBytes (encodeCall sel (a :: as)) 4 32) = a :=
  calldataload_encodeCall sel _ 0 (by simp)

/-- `CALLDATALOAD 36`: the second argument. -/
@[sol_norm] theorem calldataload_encodeCall_1 (sel : Nat) (a b : Word) (as : List Word) :
    Bytes.toWord (readBytes (encodeCall sel (a :: b :: as)) 36 32) = b :=
  calldataload_encodeCall sel _ 1 (by simp)

/-- `CALLDATALOAD 68`: the third argument. -/
@[sol_norm] theorem calldataload_encodeCall_2 (sel : Nat) (a b c : Word) (as : List Word) :
    Bytes.toWord (readBytes (encodeCall sel (a :: b :: c :: as)) 68 32) = c :=
  calldataload_encodeCall sel _ 2 (by simp)

/-- `CALLDATALOAD 100`: the fourth argument. -/
@[sol_norm] theorem calldataload_encodeCall_3 (sel : Nat) (a b c d : Word) (as : List Word) :
    Bytes.toWord (readBytes (encodeCall sel (a :: b :: c :: d :: as)) 100 32) = d :=
  calldataload_encodeCall sel _ 3 (by simp)

end Abi

end EvmLean.Solidity
