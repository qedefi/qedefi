import EvmLogic.AbsInt.Frame

/-!
# Abstract interpretation from any recorded states

`EvmLogic.AbsInt.Cert` asks for the frame's start (pc `0`) among the recorded states.
`CertT` drops that field, so a table explored from other states (here: the states of the
whole frame's table at some pcs) describes the rest of a frame from any machine those states
describe (`absintT_frame`). `subcert`: such an exploration, from the states of a closed table
at the pcs `Q`, records every state it starts from (`inT_sub`).
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested EvmLogic.GasMono
open EvmLogic.AbsInt

/-- A closed table, right for the code (a `Cert` without its start). -/
structure CertT (ρ : Nat → Address) (allowed : AVal → Bool) (code : ByteArray) (t : Tree) :
    Prop where
  closed : Closed allowed t
  ins : t.All (InsOk ρ code)

variable {ρ : Nat → Address} {allowed : AVal → Bool} {code : ByteArray} {t : Tree}

theorem CertT.of_cert {init : AStack} (h : Cert ρ allowed code init t) : CertT ρ allowed code t :=
  ⟨h.closed, h.ins⟩

theorem inCertT_entry (hc : CertT ρ allowed code t) {m : Machine} (hcode : m.frame.code = code)
    (h : InCert ρ t m) {b : UInt8} (hb : m.frame.code[m.frame.pc]? = some b) :
    ∃ s imm succs, StackOk ρ s m.frame.stack ∧ callOk allowed (byteEff b) s = true ∧
      asucc (byteEff b) imm m.frame.pc s = some succs ∧ (∀ x ∈ succs, InT t x.1 x.2) ∧
      ∀ n, byteEff b = .push n →
        imm.Holds ρ (Bytes.toWord (readBytes m.frame.code (m.frame.pc + 1) n)) := by
  obtain ⟨s, hin, hst⟩ := h
  obtain ⟨e, imm, ss, hf, hok, succs, ha, hall⟩ := hc.closed _ _ hin
  obtain ⟨b', hb', he, himm⟩ := hc.ins.find hf
  rw [← hcode, hb] at hb'
  cases hb'
  subst he
  refine ⟨s, imm, succs, hst, hok, ha, hall, fun n hn => ?_⟩
  rw [byteEff_push hn, hcode]; exact himm

theorem inCertT_resume (hc : CertT ρ allowed code t) {m m' : Machine} {b : UInt8}
    {a : Action} (hcode : m.frame.code = code) (h : InCert ρ t m)
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m'))
    (ha : (∃ req, a = .call req) ∨ ∃ msg, a = .create msg) (M : Machine) (r : ChildResult)
    (hM : M.frame = m'.frame) : InCert ρ t (resume M r) := by
  obtain ⟨s, imm, succs, hst, -, hsucc, hall, -⟩ := inCertT_entry hc hcode h hb
  have hpost := (exec_eff_byte m.ctx.fork b m).of_run he
  have hcp : CallPost (byteEff b) m m' ∨ CreatePost (byteEff b) m m' := by
    rcases ha with ⟨req, rfl⟩ | ⟨msg, rfl⟩
    · exact .inl hpost
    · exact .inr hpost
  have hpc' : m'.frame.pc = m.frame.pc := by
    cases hb' : byteEff b <;> rw [hb'] at hcp <;>
      simp only [CallPost, CreatePost, or_false, false_or] at hcp <;> exact hcp.1
  obtain ⟨hpc, ⟨w, hw⟩, -⟩ := resume_frame M r
  obtain ⟨x, hx, hx1, hx2⟩ := asucc_child hst hcp hsucc w
  refine ⟨x.2, ?_, ?_⟩
  · rw [hpc, hM, hpc', ← hx1]; exact hall x hx
  · rw [hw, hM]; exact hx2

theorem inCertT_within (hc : CertT ρ allowed code t) {m m' m₁ : Machine} {b : UInt8}
    {a : Action} (hcm : m.frame.code = code) (hQ : InCert ρ t m)
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m')) (hw : Within m' a m₁) :
    m₁.frame.code = code ∧ InCert ρ t m₁ := by
  have hif : InstrFrame m m' := ((exec_frame _ m).of_run he).1
  rcases hw with ⟨rfl, hm1⟩ | ⟨req, rfl, hpre, hm1⟩ <;> rw [hm1]
  · refine ⟨hif.same.code.trans hcm, ?_⟩
    obtain ⟨s, imm, succs, hst, -, hsucc, hall, himm⟩ := inCertT_entry hc hcm hQ hb
    have hpost : NextPost (byteEff b) m m' := (exec_eff_byte m.ctx.fork b m).of_run he
    obtain ⟨x, hx, hx1, hx2⟩ := asucc_next hst rfl himm hpost hsucc
    exact ⟨x.2, by rw [← hx1]; exact hall x hx, hx2⟩
  · obtain ⟨w, tr, r, hl, -⟩ := launchCall_some hpre
    rw [hl]
    refine ⟨(resume_frame _ r).2.2.trans (hif.same.code.trans hcm), ?_⟩
    exact inCertT_resume hc hcm hQ hb he (.inl ⟨req, rfl⟩) _ r rfl

theorem inCertT_pushed (hc : CertT ρ allowed code t) {m m' mc : Machine} {b : UInt8}
    {a : Action} (hcm : m.frame.code = code) (hQ : InCert ρ t m)
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m')) (hp : Pushed m' a mc)
    (mfc : Machine) (oc : Outcome) :
    (resumeAfter m'.frame m.parents mfc oc).frame.code = code ∧
      InCert ρ t (resumeAfter m'.frame m.parents mfc oc) := by
  have hif : InstrFrame m m' := ((exec_frame _ m).of_run he).1
  have ha : (∃ req, a = .call req) ∨ ∃ msg, a = .create msg := by
    rcases hp with ⟨req, rfl, -⟩ | ⟨msg, rfl, -⟩
    · exact .inl ⟨req, rfl⟩
    · exact .inr ⟨msg, rfl⟩
  refine ⟨?_, inCertT_resume hc hcm hQ hb he ha _ _ rfl⟩
  exact (resume_frame _ _).2.2.trans (hif.same.code.trans hcm)

/-- **Every machine of the frame from `mh` to its exit is described by `t`.** -/
theorem absintT_frame (hc : CertT ρ allowed code t) {mh mf : Machine} {N : Nat}
    {o : Outcome} (hex : Exit mh N mf o) (hcode : mh.frame.code = code) (h0 : InCert ρ t mh) :
    ∀ k ≤ N, ∀ m, stepN k mh = .running m → SameFrame mh m → InCert ρ t m := by
  intro k hk m hm hs
  refine (exit_frame_ind (fun m => m.frame.code = code ∧ InCert ρ t m) ?_ ?_ N mh mf o hex
    ⟨hcode, h0⟩ k hk m hm hs).2
  · intro m b a m' m₁ ⟨hcm, hQ⟩ hb he hw _
    exact inCertT_within hc hcm hQ hb he hw
  · intro m b a m' mc nc mfc oc ⟨hcm, hQ⟩ hb he hp _ _
    exact inCertT_pushed hc hcm hQ hb he hp mfc oc

/-! ## Explorations from recorded states -/

/-- The recorded states of `t` at the pcs `Q`. -/
def seedsAt (t : Tree) (Q : List Nat) : List (Nat × AStack) :=
  Q.flatMap fun q => match t.find q with
    | some (_, _, ss) => ss.map fun s => (q, s)
    | none => []

theorem mem_seedsAt {t : Tree} {Q : List Nat} {q : Nat} {s : AStack} (h : InT t q s)
    (hq : q ∈ Q) : (q, s) ∈ seedsAt t Q := by
  obtain ⟨e, imm, ss, hf, hs⟩ := h
  simp only [seedsAt, List.mem_flatMap]
  exact ⟨q, hq, by rw [hf]; exact List.mem_map.2 ⟨s, hs, rfl⟩⟩

/-- Explore `code` from the recorded states of `t0` at `Q`, calls to any target allowed. -/
def subcert (code : ByteArray) (t0 : Tree) (Q : List Nat) (fuel : Nat) : Option Tree :=
  explore (fun _ => true) fuel (table code []) (seedsAt t0 Q)

theorem subcert_sound {ρ : Nat → Address} {code : ByteArray} {t0 : Tree} {Q : List Nat}
    {fuel : Nat} {t : Tree} (h : subcert code t0 Q fuel = some t) :
    CertT ρ (fun _ => true) code t ∧ ∀ q s, InT t0 q s → q ∈ Q → InT t q s := by
  have hs : SymOk ρ code [] := fun q k h => by simp [symAt] at h
  obtain ⟨hA, hF, -⟩ := Tree.build_ok 64 (ascan code []).length _ (ascan_ok hs)
  have hI : ExInv (fun _ => true) (table code []) (seedsAt t0 Q) := by
    intro q s ⟨e, imm, ss, hf, hm⟩
    rw [hF.find hf] at hm
    cases hm
  obtain ⟨hc, hm⟩ := explore_sound _ fuel _ _ t h hI
  exact ⟨⟨hc, explore_all fuel _ _ t h hA⟩,
    fun q s hin hq => hm q s (.inr (mem_seedsAt hin hq))⟩

/-! ## Recorded pcs -/

/-- The pcs at which `t` records some state. -/
def recorded : Tree → List Nat
  | .leaf => []
  | .node l q _ _ ss r => recorded l ++ (if ss.isEmpty then [] else [q]) ++ recorded r

theorem find_recorded : ∀ {t : Tree} {q e imm ss s}, t.find q = some (e, imm, ss) → s ∈ ss →
    q ∈ recorded t
  | .leaf, _, _, _, _, _, h, _ => by simp [Tree.find] at h
  | .node l k e' imm' ss' r, q, e, imm, ss, s, h, hs => by
    simp only [Tree.find] at h
    simp only [recorded, List.mem_append]
    split at h
    · exact .inl (.inl (find_recorded h hs))
    · split at h
      · exact .inr (find_recorded h hs)
      · cases h
        rename_i h1 h2
        have : q = k := by simp only [Nat.blt_eq] at h1 h2; omega
        subst this
        refine .inl (.inr ?_)
        cases ss' with
        | nil => cases hs
        | cons _ _ => simp

theorem inT_recorded {t : Tree} {q : Nat} {s : AStack} (h : InT t q s) : q ∈ recorded t := by
  obtain ⟨e, imm, ss, hf, hs⟩ := h
  exact find_recorded hf hs

theorem inCert_recorded {t : Tree} {m : Machine} (h : InCert ρ t m) :
    m.frame.pc ∈ recorded t := by
  obtain ⟨s, hin, -⟩ := h
  exact inT_recorded hin

end Verified.Solmate.ERC20.Spec
