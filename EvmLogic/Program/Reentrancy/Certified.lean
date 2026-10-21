import EvmLogic.Program.Reentrancy.NoWrite
import EvmLogic.Program.Reentrancy.Halts
import EvmLogic.AbsInt.Frame

/-!
# A certified no-write frame keeps the world, for any gas

`noWrite_halts`: a frame whose code is covered by an abstract-interpretation certificate (`Cert`)
all of whose reachable instructions are `WorldSafe` halts with the world unchanged, **whatever
its gas**. The certificate localises the reachable pcs (`absint_frame`/`inCert_within`), so every
executed byte is world-safe and `exec_worldSafe` keeps the world at each step; the strict gas of
each step (`exec_strict`) makes the frame terminate. No gas bound and no lockstep: this is the
any-gas fact the stipend and checks-effects-interactions reasoning needs for a function's tail
after its external call.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested EvmLogic.AbsInt

/-- Every recorded instruction of `t` is world-safe. -/
def WorldSafeCert (code : ByteArray) (t : Tree) : Prop :=
  t.All (fun q _ _ => ∀ b, code[q]? = some b → WorldSafe b = true)

/-- A recorded pc runs a world-safe byte. -/
theorem worldSafe_of_inCert {ρ : Nat → Address} {code : ByteArray} {t : Tree}
    (hw : WorldSafeCert code t) {m : Machine} (h : InCert ρ t m) {b : UInt8}
    (hb : m.frame.code[m.frame.pc]? = some b) (hcode : m.frame.code = code) :
    WorldSafe b = true := by
  obtain ⟨s, ⟨e, imm, ss, hf, -⟩, -⟩ := h
  exact hw.find hf b (by rw [← hcode]; exact hb)

/-- **One step of a certified world-safe frame**: it finishes (its machine's world unchanged), or
continues with strictly less gas and the world unchanged. It never starts a child. -/
theorem step_worldSafe {m : Machine} {b : UInt8} (hb : m.frame.code[m.frame.pc]? = some b)
    (hsafe : WorldSafe b = true) :
    (∃ m' o, step m = finishFrame m' o ∧ InstrFrame m m' ∧ m'.world = m.world) ∨
    (∃ m', step m = .running m' ∧ InstrFrame m m' ∧ m'.frame.gasLeft < m.frame.gasLeft ∧
      m'.world = m.world ∧
      (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m')) := by
  have hpc : m.frame.pc < m.frame.code.size := by
    rw [getElem?_eq_some_iff] at hb; exact hb.1
  have hbd : Opcode.decode m.ctx.fork m.frame.code[m.frame.pc] = Opcode.decode m.ctx.fork b := by
    congr 1; exact (getElem?_eq_some_iff.1 hb).2
  have hw := wp_and (wp_and (exec_frame (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m)
      (exec_strict (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m))
    (by rw [hbd]; exact exec_worldSafe_byte m.ctx.fork b m hsafe)
  unfold step
  simp only [hpc, ↓reduceDIte]
  split
  · exact .inl ⟨m, _, rfl, .refl m, rfl⟩
  · rename_i m' h
    obtain ⟨⟨⟨hf, -⟩, hs, -⟩, -, -, hworld⟩ := hw.of_run h
    exact .inr ⟨m', rfl, hf, hs, hworld, by rw [← hbd]; exact h⟩
  · rename_i out m' h
    obtain ⟨⟨⟨hf, -⟩, -⟩, -, -, hworld⟩ := hw.of_run h
    exact .inl ⟨m', _, rfl, hf, hworld⟩
  · rename_i out m' h
    obtain ⟨⟨⟨hf, -⟩, -⟩, -, -, hworld⟩ := hw.of_run h
    exact .inl ⟨m', _, rfl, hf, hworld⟩
  · rename_i req m' h
    obtain ⟨-, hne, -, -⟩ := hw.of_run h
    exact absurd rfl (hne req)
  · rename_i msg m' h
    obtain ⟨-, -, hne, -⟩ := hw.of_run h
    exact absurd rfl (hne msg)

variable {ρ : Nat → Address} {allowed : AVal → Bool} {code : ByteArray} {init : AStack} {t : Tree}

/-- **A certified world-safe frame halts with its world unchanged, for any gas.** -/
theorem noWrite_halts (hc : Cert ρ allowed code init t) (hw : WorldSafeCert code t)
    {m : Machine} (hcode : m.frame.code = code) (hin : InCert ρ t m) :
    Halts m (fun mf _ => mf.world = m.world) := by
  suffices ∀ n m, m.frame.gasLeft = n → m.frame.code = code → InCert ρ t m →
      Halts m (fun mf _ => mf.world = m.world) from this _ m rfl hcode hin
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hn hcm hin
    by_cases hpc : m.frame.pc < m.frame.code.size
    · have hb := getElem?_pos m.frame.code m.frame.pc hpc
      have hsafe := worldSafe_of_inCert hw hin hb hcm
      rcases step_worldSafe hb hsafe with ⟨m', o, he, hf, hworld⟩ | ⟨m', he, hf, hgas, hworld, hex⟩
      · exact Halts.of_step he hf.same hworld
      · have hwithin : Within m' .next m' := .inl ⟨rfl, rfl⟩
        obtain ⟨hcode', hin'⟩ := inCert_within hc hcm hin hb hex hwithin
        exact (Halts.of_steps (Steps.of_step he hf.same)
          (ih _ (hn ▸ hgas) m' rfl hcode' hin')).mono (fun mf _ _ h => h.trans hworld)
    · refine Halts.of_step (o := .success .empty) ?_ (.refl m) rfl
      unfold step; simp only [hpc, ↓reduceDIte]

end EvmLogic.Program.Reentrancy
