import EvmLeanSpecs.Refinement.UnknownSelectors

/-!
# Malformed calldata: definitions

The argument words of calldata (`argWord`), clean `address` arguments (`CleanAddr`), calldata
malformed for a function shape (`Malformed`), the function shapes of the vault and the asset
(`vaultArgShapes`, `assetArgShapes`) and the word facts the decoder proofs use. The theorems are
in `MalformedVault*.lean`, `MalformedAsset.lean` and `MalformedCalldata.lean`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-! ## Argument words -/

/-- Argument word `j` of calldata `d`, as `CALLDATALOAD(4 + 32·j)` reads it. -/
def argWord (d : ByteArray) (j : Nat) : Word := Bytes.toWord (readBytes d (4 + 32 * j) 32)

/-- Argument word `j` is a clean `address`: its high 96 bits are zero. -/
def CleanAddr (d : ByteArray) (j : Nat) : Prop := argWord d j &&& addressMask = argWord d j

/-- Calldata `d` is malformed for a function taking `k` argument words with `address`
arguments at positions `addrs`: fewer than `k` argument words, or a dirty `address` argument
after clean ones. -/
def Malformed (d : ByteArray) (k : Nat) (addrs : List Nat) : Prop :=
  d.size < 4 + 32 * k ∨
    (4 + 32 * k ≤ d.size ∧ ∃ j ∈ addrs, (∀ j' ∈ addrs, j' < j → CleanAddr d j') ∧ ¬ CleanAddr d j)

/-- A clean argument, with the mask as symbolic execution produces it. -/
theorem cleanAddr_lit {d : ByteArray} {j : Nat} (h : CleanAddr d j) :
    argWord d j &&& 1461501637330902918203684832716283019655932542975#256 = argWord d j := by
  rw [← addressMask_eq]; exact h

/-- The address validator fails on a dirty argument. -/
theorem eq_and_mask_zero {d : ByteArray} {j : Nat} (h : ¬ CleanAddr d j) :
    Word.eq (argWord d j)
      (argWord d j &&& 1461501637330902918203684832716283019655932542975#256) = 0 := by
  unfold Word.eq Word.ofBool
  have : (argWord d j == argWord d j &&& 1461501637330902918203684832716283019655932542975#256)
      = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro he
    exact h (by unfold CleanAddr; rw [addressMask_eq]; exact he.symm)
  rw [this]; rfl

/-- The ABI decoder's calldata-length check fails when the calldata is shorter than the
selector and `n` bytes of arguments. -/
theorem iszero_slt_short {size n : Nat} (h1 : 4 ≤ size) (h2 : size < 4 + n) (hn : n < 2 ^ 255) :
    Word.iszero (Word.slt (BitVec.ofNat 256 size - 4#256) (BitVec.ofNat 256 n)) = 0 := by
  have hx : (BitVec.ofNat 256 size - 4#256).toNat = size - 4 := by
    rw [BitVec.toNat_sub_of_le] <;> simp [BitVec.le_def] <;> omega
  simp only [Word.iszero, Word.slt, Word.ofBool, BitVec.slt_eq_ult, BitVec.msb_eq_decide, hx,
    BitVec.ult, BitVec.toNat_ofNat]
  simp (disch := omega) [Nat.mod_eq_of_lt]
  rw [decide_eq_false (by omega), decide_eq_false (by omega), decide_eq_true (by omega)]
  decide

/-! ## Function shapes -/

/-- The vault's functions with arguments: selector, number of argument words, positions of the
`address` arguments. -/
def vaultArgShapes : List (Nat × Nat × List Nat) :=
  [(0xdd62ed3e, 2, [0, 1]), (0x095ea7b3, 2, [0]), (0x70a08231, 1, [0]), (0x07a2d13a, 1, []),
    (0xc6e6f592, 1, []), (0x6e553f65, 2, [1]), (0x402d267d, 1, [0]), (0xc63d75b6, 1, [0]),
    (0xd905777e, 1, [0]), (0xce96cb77, 1, [0]), (0x94bf804d, 2, [1]), (0x7ecebe00, 1, [0]),
    (0xd505accf, 7, [0, 1]), (0xef8b30f7, 1, []), (0xb3d7f6b9, 1, []), (0x4cdad506, 1, []),
    (0x0a28a477, 1, []), (0xba087652, 3, [1, 2]), (0xa9059cbb, 2, [0]), (0x23b872dd, 3, [0, 1]),
    (0xb460af94, 3, [1, 2])]

/-- The asset's functions with arguments: selector, number of argument words, positions of the
`address` arguments. -/
def assetArgShapes : List (Nat × Nat × List Nat) :=
  [(0xdd62ed3e, 2, [0, 1]), (0x095ea7b3, 2, [0]), (0x70a08231, 1, [0]), (0x9dc29fac, 2, [0]),
    (0x40c10f19, 2, [0]), (0x7ecebe00, 1, [0]), (0xd505accf, 7, [0, 1]), (0xa9059cbb, 2, [0]),
    (0x23b872dd, 3, [0, 1])]

end EvmLeanSpecs.Refinement
