import EvmLogic.GasMono.CodeScan
import EvmLogic.GasMono.Pc

/-!
# Gas monotonicity: `CallsFed` over the instruction scan

`CallsFed code n` (`GasMono/Pc.lean`) asks that every `CALL`/`CREATE`-family byte at a boundary
below `n` directly follows a `GAS` at a boundary. `callsFedB n prev l` checks it in one pass over
the scan `insns code` (`GasMono/CodeScan.lean`), comparing each instruction with its
predecessor; `callsFed_of_scan` turns a successful check into `CallsFed`, so that
`decide +kernel` establishes it for a concrete code.
-/

namespace EvmLean.Program.GasMono

/-- `IsCallByte` as a Boolean. -/
def isCallByteB (b : UInt8) : Bool :=
  b == 0xf0 || b == 0xf1 || b == 0xf2 || b == 0xf4 || b == 0xf5 || b == 0xfa

theorem isCallByteB_of {b : UInt8} (h : IsCallByte b) : isCallByteB b = true := by
  unfold IsCallByte at h
  rcases h with h | h | h | h | h | h <;> subst h <;> rfl

/-- One pass over the scan: every call byte below `n` follows a `GAS` (`prev` is the previous
instruction's position and opcode). -/
def callsFedB (n : Nat) : Nat × UInt8 → List (Nat × UInt8 × UInt8) → Bool
  | _, [] => true
  | prev, t :: l =>
    (!(decide (t.1 < n) && isCallByteB t.2.1) || (prev.2 == 0x5a && prev.1 + 1 == t.1)) &&
      callsFedB n (t.1, t.2.1) l

theorem callsFedB_spec {n : Nat} :
    ∀ (l : List (Nat × UInt8 × UInt8)) (prev : Nat × UInt8), callsFedB n prev l = true →
      ∀ t ∈ l, t.1 < n → isCallByteB t.2.1 = true →
        (prev.2 = 0x5a ∧ prev.1 + 1 = t.1) ∨ ∃ t' ∈ l, t'.2.1 = 0x5a ∧ t'.1 + 1 = t.1 := by
  intro l
  induction l with
  | nil => intro _ _ t ht; cases ht
  | cons s l ih =>
    intro prev h t ht hn hc
    simp only [callsFedB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 ht with rfl | ht
    · rcases h1 with (h1 | h1) | h1
      · exact absurd hn h1
      · rw [hc] at h1; cases h1
      · exact .inl h1
    · rcases ih _ h2 t ht hn hc with h3 | ⟨t', ht', h3⟩
      · exact .inr ⟨s, List.mem_cons_self, h3⟩
      · exact .inr ⟨t', List.mem_cons_of_mem _ ht', h3⟩

/-- **`CallsFed` from the scan.** -/
theorem callsFed_of_scan {code : ByteArray} {n : Nat}
    (h : callsFedB n (0, 0) (insns code) = true) : CallsFed code n := by
  intro q hq hqn hb
  have hmem : insnInfo code q ∈ insns code := by
    rw [insns_eq]; exact List.mem_map_of_mem hq
  rcases callsFedB_spec _ _ h _ hmem hqn (isCallByteB_of hb) with h1 | ⟨t', ht', h5, h1⟩
  · simp at h1
  · rw [insns_eq] at ht'
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 ht'
    simp only [insnInfo] at h5 h1
    refine ⟨by omega, ?_, ?_⟩
    · rw [show q - 1 = q' by omega]; exact hq'
    · rw [show q - 1 = q' by omega]; exact h5

end EvmLean.Program.GasMono
