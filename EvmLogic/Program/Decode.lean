import EvmLean

/-!
# Decoding and jump-destination facts

* Decoding is fork-independent except for `0x1e` (`CLZ`, Osaka), and `decode` inverts
  `toByte` in Osaka (in earlier forks except for `CLZ`).
* Valid jump destinations are `JUMPDEST` bytes (`isValidJumpDest_validJumpDests`), and
  never lie past the end of the code.
-/

namespace EvmLean

namespace Opcode

/-- Decoding does not depend on the fork, except for `0x1e` (`CLZ`). -/
theorem decode_eq_decode_cancun (fk : Fork) (b : UInt8) (h : b ≠ 0x1e) :
    decode fk b = decode .cancun b := by
  have key : ∀ i : Fin 256, UInt8.ofNat i.val ≠ 0x1e →
      decode fk (UInt8.ofNat i.val) = decode .cancun (UInt8.ofNat i.val) := by
    cases fk <;> decide +kernel
  have := key ⟨b.toNat, b.toNat_lt⟩ (by simpa using h)
  simpa using this

/-- In Osaka, `decode` inverts `toByte`. -/
theorem decode_toByte_osaka (op : Opcode) : decode .osaka op.toByte = op := by
  cases op
  all_goals first
    | rfl
    | (rename_i n; revert n; decide)

/-- Before Osaka, `decode` inverts `toByte` on every opcode except `CLZ`. -/
theorem decode_toByte (fk : Fork) (op : Opcode) (h : op ≠ .clz) : decode fk op.toByte = op := by
  have hb : op.toByte ≠ 0x1e := by
    cases op
    all_goals first
      | exact absurd rfl h
      | decide
      | (rename_i n; revert n; decide)
  rw [decode_eq_decode_cancun fk _ hb, ← decode_eq_decode_cancun .osaka _ hb]
  exact decode_toByte_osaka op

end Opcode

namespace Interpreter

/-- A valid jump destination is a `JUMPDEST` byte of the code. -/
theorem isValidJumpDest_validJumpDests {code : ByteArray} {d : Nat}
    (h : isValidJumpDest (validJumpDests code) d = true) : code[d]? = some 0x5b := by
  apply validJumpDests_true
  unfold isValidJumpDest at h
  cases h' : (validJumpDests code)[d]? with
  | none => simp [h'] at h
  | some v => simp_all

/-- A valid jump destination lies inside the code. -/
theorem lt_size_of_isValidJumpDest {code : ByteArray} {d : Nat}
    (h : isValidJumpDest (validJumpDests code) d = true) : d < code.size := by
  have := isValidJumpDest_validJumpDests h
  rw [getElem?_eq_some_iff] at this
  exact this.1

end Interpreter

end EvmLean
