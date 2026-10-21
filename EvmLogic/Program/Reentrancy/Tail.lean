import EvmLogic.Program.Reentrancy.Certified

/-!
# Certified tails: world-safe from a given pc, for any gas

`noWrite_halts` (`EvmLogic.Program.Reentrancy.Certified`) needs a `Cert`, explored from pc `0`,
whose every table entry is world-safe. The tail of a checks-effects-interactions function (the
code after its external call) is reached from the call's `pc + 1`, in code that elsewhere
writes storage and calls. This module certifies such a tail on its own:

* `certifyAt`: the exploration of `explore` from `(q, init)`; `certifyAt_sound` gives a
  `TailCert` (closed, right for the code, containing `(q, init)`).
* `WorldSafeReached`: every instruction **at which a state is recorded** is world-safe (entries
  never reached may be anything); `tailCheck` checks both by evaluation (`tailCheck_sound`).
* `noWrite_halts_tail`: a frame described by a recorded state of such a certificate halts with
  its world unchanged, for any gas.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested EvmLogic.AbsInt

/-! ## Certificates from a given state -/

/-- Explore `code` from pc `q` with the abstract stack `init`. -/
def certifyAt (allowed : AVal → Bool) (code : ByteArray) (syms : List (Nat × Nat)) (q : Nat)
    (init : AStack) (fuel : Nat) : Option Tree :=
  explore allowed fuel (table code syms) [(q, init)]

/-- **A tail certificate**: a closed table, right for the code, containing `(q, init)`. -/
structure TailCert (ρ : Nat → Address) (allowed : AVal → Bool) (code : ByteArray) (q : Nat)
    (init : AStack) (t : Tree) : Prop where
  closed : Closed allowed t
  ins : t.All (InsOk ρ code)
  init : InT t q init

/-- **The tail certificate computed by `certifyAt` is sound.** -/
theorem certifyAt_sound {ρ : Nat → Address} {allowed : AVal → Bool} {code : ByteArray}
    {syms : List (Nat × Nat)} {q : Nat} {init : AStack} {fuel : Nat} {t : Tree}
    (h : certifyAt allowed code syms q init fuel = some t) (hs : SymOk ρ code syms) :
    TailCert ρ allowed code q init t := by
  obtain ⟨hA, hF, -⟩ := Tree.build_ok 64 (ascan code syms).length _ (ascan_ok hs)
  have hI : ExInv allowed (table code syms) [(q, init)] := by
    intro q s ⟨e, imm, ss, hf, hm⟩
    rw [hF.find hf] at hm
    cases hm
  obtain ⟨hc, hm⟩ := explore_sound allowed fuel _ _ t h hI
  exact ⟨hc, explore_all fuel _ _ t h hA, hm q init (.inr List.mem_cons_self)⟩

/-! ## World-safety of the reached instructions -/

/-- Every instruction at which `t` records a state is world-safe. -/
def WorldSafeReached (code : ByteArray) (t : Tree) : Prop :=
  ∀ q e imm ss, t.find q = some (e, imm, ss) → ss ≠ [] → ∀ b, code[q]? = some b →
    WorldSafe b = true

/-- The byte at `q`, if any, is world-safe. -/
def worldSafeAt (code : ByteArray) (q : Nat) : Bool :=
  match code[q]? with
  | some b => WorldSafe b
  | none => true

/-- Boolean check of `WorldSafeReached`. -/
def reachedSafe (code : ByteArray) : Tree → Bool
  | .leaf => true
  | .node l q _ _ ss r => reachedSafe code l && (ss.isEmpty || worldSafeAt code q) &&
      reachedSafe code r

theorem reachedSafe_find {code : ByteArray} : ∀ {t : Tree}, reachedSafe code t = true →
    ∀ {q e imm ss}, t.find q = some (e, imm, ss) → ss ≠ [] → worldSafeAt code q = true
  | .leaf, _, _, _, _, _, h, _ => by simp [Tree.find] at h
  | .node l k e' imm' ss' r, hA, q, e, imm, ss, h, hne => by
    simp only [reachedSafe, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff] at hA
    simp only [Tree.find] at h
    split at h
    · exact reachedSafe_find hA.1.1 h hne
    · split at h
      · exact reachedSafe_find hA.2 h hne
      · cases h
        rename_i h1 h2
        have : q = k := by simp only [Nat.blt_eq] at h1 h2; omega
        subst this
        rcases hA.1.2 with h | h
        · exact absurd h hne
        · exact h

theorem worldSafeReached_of {code : ByteArray} {t : Tree} (h : reachedSafe code t = true) :
    WorldSafeReached code t := by
  intro q e imm ss hf hne b hb
  have := reachedSafe_find h hf hne
  simp only [worldSafeAt, hb] at this
  exact this

/-- Explore from `(q, init)` and check that every reached instruction is world-safe. -/
def tailCheck (allowed : AVal → Bool) (code : ByteArray) (syms : List (Nat × Nat)) (q : Nat)
    (init : AStack) (fuel : Nat) : Bool :=
  match certifyAt allowed code syms q init fuel with
  | some t => reachedSafe code t
  | none => false

/-- **A successful `tailCheck` gives a world-safe tail certificate.** -/
theorem tailCheck_sound {ρ : Nat → Address} {allowed : AVal → Bool} {code : ByteArray}
    {syms : List (Nat × Nat)} {q : Nat} {init : AStack} {fuel : Nat}
    (h : tailCheck allowed code syms q init fuel = true) (hs : SymOk ρ code syms) :
    ∃ t, TailCert ρ allowed code q init t ∧ WorldSafeReached code t := by
  unfold tailCheck at h
  split at h
  · rename_i t ht
    exact ⟨t, certifyAt_sound ht hs, worldSafeReached_of h⟩
  · cases h

/-! ## A certified world-safe tail keeps the world -/

variable {ρ : Nat → Address} {allowed : AVal → Bool} {code : ByteArray} {q : Nat}
  {init : AStack} {t : Tree}

/-- A state of the tail at a world-safe instruction continues to a recorded state. -/
theorem inCert_next_tail (hc : TailCert ρ allowed code q init t) {m m' : Machine} {b : UInt8}
    (hcm : m.frame.code = code) (hQ : InCert ρ t m) (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m')) :
    m'.frame.code = code ∧ InCert ρ t m' := by
  have hif : InstrFrame m m' := ((exec_frame _ m).of_run he).1
  refine ⟨hif.same.code.trans hcm, ?_⟩
  obtain ⟨s, hin, hst⟩ := hQ
  obtain ⟨e, imm, ss, hf, hok, succs, ha, hall⟩ := hc.closed _ _ hin
  obtain ⟨b', hb', he', himm⟩ := hc.ins.find hf
  rw [← hcm, hb] at hb'
  cases hb'
  subst he'
  have himm' : ∀ n, byteEff b = .push n →
      imm.Holds ρ (Bytes.toWord (readBytes m.frame.code (m.frame.pc + 1) n)) := by
    intro n hn; rw [byteEff_push hn, hcm]; exact himm
  have hpost : NextPost (byteEff b) m m' := (exec_eff_byte m.ctx.fork b m).of_run he
  obtain ⟨x, hx, hx1, hx2⟩ := asucc_next hst rfl himm' hpost ha
  exact ⟨x.2, by rw [← hx1]; exact hall x hx, hx2⟩

/-- A recorded state runs a world-safe byte. -/
theorem worldSafe_of_inCert_tail (hw : WorldSafeReached code t) {m : Machine} (h : InCert ρ t m)
    {b : UInt8} (hb : m.frame.code[m.frame.pc]? = some b) (hcode : m.frame.code = code) :
    WorldSafe b = true := by
  obtain ⟨s, ⟨e, imm, ss, hf, hs⟩, -⟩ := h
  exact hw _ _ _ _ hf (List.ne_nil_of_mem hs) b (by rw [← hcode]; exact hb)

/-- **A frame in a certified world-safe tail halts with its world unchanged, for any gas.** -/
theorem noWrite_halts_tail (hc : TailCert ρ allowed code q init t) (hw : WorldSafeReached code t)
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
      have hsafe := worldSafe_of_inCert_tail hw hin hb hcm
      rcases step_worldSafe hb hsafe with ⟨m', o, he, hf, hworld⟩ | ⟨m', he, hf, hgas, hworld, hex⟩
      · exact Halts.of_step he hf.same hworld
      · obtain ⟨hcode', hin'⟩ := inCert_next_tail hc hcm hin hb hex
        exact (Halts.of_steps (Steps.of_step he hf.same)
          (ih _ (hn ▸ hgas) m' rfl hcode' hin')).mono (fun mf _ _ h => h.trans hworld)
    · refine Halts.of_step (o := .success .empty) ?_ (.refl m) rfl
      unfold step; simp only [hpc, ↓reduceDIte]

/-- The entry state of a tail certificate describes a machine at `q` with a matching stack. -/
theorem inCert_of_entry (hc : TailCert ρ allowed code q init t) {m : Machine}
    (hpc : m.frame.pc = q) (hst : StackOk ρ init m.frame.stack) : InCert ρ t m :=
  ⟨init, by rw [hpc]; exact hc.init, hst⟩

end EvmLogic.Program.Reentrancy
