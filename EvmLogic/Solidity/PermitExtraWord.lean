import EvmLogic.Word

/-!
# Word identities of solc's storage-string encoder

`abi_encode_t_string_storage` (used by `keccak256(bytes(name))` in Solmate's
`computeDomainSeparator`) advances the memory pointer by `length * iszero(iszero(length))`
and the caller takes the difference of two pointers; these identities let symbolic execution
simplify both.
-/

namespace EvmLean.Word

/-- `x * iszero(iszero(x)) = x`. -/
theorem mul_iszero_iszero (x : Word) : x * Word.iszero (Word.iszero x) = x := by
  by_cases h : x = 0
  · subst h; decide
  · have h1 : Word.iszero x = 0 := by
      unfold Word.iszero Word.ofBool; simp; exact h
    rw [h1]
    have h2 : Word.iszero 0 = 1 := by decide
    rw [h2]; exact BitVec.mul_one x

/-- `a + x - a = x`. -/
theorem add_sub_cancel_left' (a x : Word) : a + x - a = x := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

end EvmLean.Word
