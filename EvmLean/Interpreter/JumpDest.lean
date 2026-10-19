/-!
# Jump destination analysis

`validJumpDests code` is a bitmap marking the `JUMPDEST` (`0x5b`) bytes of `code` that are
real instructions, not immediate data of a `PUSH1`–`PUSH32` (`0x60`–`0x7f`). Mirrors
`get_valid_jump_destinations` in `cancun/vm/runtime.py`.

The scan is fork-independent: every byte outside `0x60`–`0x7f` advances by one (including
undefined opcodes, which the spec skips as one byte as well).

The definition uses explicit structural fuel (`code.size + 1`, which suffices because each
iteration advances `pc` by at least one), so it reduces in the kernel.
-/

namespace EvmLean.Interpreter

/-- Scan `code` from `pc`, marking valid jump destinations in `acc` (`acc.size = code.size`).
`fuel` bounds the number of instructions still to scan. -/
def jumpDestLoop (code : ByteArray) : Nat → Nat → Array Bool → Array Bool
  | 0, _, acc => acc
  | fuel + 1, pc, acc =>
    if h : pc < code.size then
      let b := code[pc]
      if b = 0x5b then jumpDestLoop code fuel (pc + 1) (acc.setIfInBounds pc true)
      else if 0x60 ≤ b ∧ b ≤ 0x7f then
        jumpDestLoop code fuel (pc + 1 + (b.toNat - 0x5f)) acc
      else jumpDestLoop code fuel (pc + 1) acc
    else acc

/-- The valid jump destinations of `code`, as a bitmap of size `code.size`.
Mirrors `get_valid_jump_destinations`. -/
def validJumpDests (code : ByteArray) : Array Bool :=
  jumpDestLoop code (code.size + 1) 0 (Array.replicate code.size false)

/-- Is `dest` a valid jump destination according to the bitmap? Out-of-range destinations
(including ones beyond `2⁶⁴`) are invalid. -/
def isValidJumpDest (bitmap : Array Bool) (dest : Nat) : Bool := bitmap[dest]?.getD false

/-- The scan preserves the bitmap size. -/
theorem size_jumpDestLoop (code : ByteArray) (fuel pc : Nat) (acc : Array Bool) :
    (jumpDestLoop code fuel pc acc).size = acc.size := by
  induction fuel generalizing pc acc with
  | zero => simp [jumpDestLoop]
  | succ n ih =>
    unfold jumpDestLoop
    split
    · simp only []
      split
      · rw [ih]; simp
      · split <;> rw [ih]
    · rfl

/-- The bitmap has one entry per code byte. -/
theorem size_validJumpDests (code : ByteArray) : (validJumpDests code).size = code.size := by
  simp [validJumpDests, size_jumpDestLoop]

/-- A position marked by the scan was marked initially or holds a `JUMPDEST` byte. -/
theorem jumpDestLoop_true (code : ByteArray) (fuel pc : Nat) (acc : Array Bool) (i : Nat)
    (h : (jumpDestLoop code fuel pc acc)[i]? = some true) :
    acc[i]? = some true ∨ code[i]? = some 0x5b := by
  induction fuel generalizing pc acc with
  | zero => exact .inl h
  | succ n ih =>
    unfold jumpDestLoop at h
    split at h
    · rename_i hpc
      simp only [] at h
      split at h
      · rename_i hb
        rcases ih _ _ h with h' | h'
        · rw [Array.getElem?_setIfInBounds] at h'
          split at h'
          · subst_vars
            right
            simp [hpc, hb]
          · exact .inl h'
        · exact .inr h'
      · split at h <;> exact ih _ _ h
    · exact .inl h

/-- Soundness: every valid jump destination is a `JUMPDEST` (`0x5b`) byte of the code.
(That `0x5b` bytes inside `PUSH` data are excluded is checked by `#guard`s in
`EvmLeanTest/Interpreter.lean`.) -/
theorem validJumpDests_true (code : ByteArray) (i : Nat)
    (h : (validJumpDests code)[i]? = some true) : code[i]? = some 0x5b := by
  rcases jumpDestLoop_true code _ _ _ i h with h' | h'
  · simp [Array.getElem?_replicate] at h'
  · exact h'

end EvmLean.Interpreter
