import EvmLogic.AbsInt.Guard.Check
import EvmLogic.AbsInt.Frame
import EvmLogic.Program.Nested.Storage

/-!
# Guarded abstract interpretation: frame invariants

`GInCert ν t m`: the machine's pc and stack are described by a recorded abstract state of the
certificate `t`. This is the frame invariant a relay contract uses in
`EvmLogic.Program.Nested.GuardInv`: it holds at the start of a frame (`ginCert_init`), is kept by
each instruction while the configuration's facts hold (`ginCert_next`), and holds after any child
returns (`ginCert_resume`). It bounds every call target (`ginCert_call`), rules out creations
(`ginCert_no_create`) and bounds every `SSTORE` key (`ginCert_sstore`).
-/

namespace EvmLogic.AbsInt.Guard
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested EvmLogic.AbsInt

/-- The machine is described by a recorded abstract state. -/
def GInCert (ν : Env) (t : GTree) (m : Machine) : Prop :=
  ∃ s, GInT t m.frame.pc s ∧ GStackOk ν s m.frame.stack

variable {ν : Env} {cfg : Cfg} {code : ByteArray} {init : GStack} {t : GTree}

theorem GInCert.entry (hc : GCert ν cfg code init t) {m : Machine} (hcode : m.frame.code = code)
    (h : GInCert ν t m) {b : UInt8} (hb : m.frame.code[m.frame.pc]? = some b) :
    ∃ s imm succs, GStackOk ν s m.frame.stack ∧ gok cfg (gbyteEff b) s = true ∧
      gsucc cfg (gbyteEff b) imm m.frame.pc s = some succs ∧ (∀ x ∈ succs, GInT t x.1 x.2) ∧
      ∀ n, gbyteEff b = .push n →
        imm.Holds ν (Bytes.toWord (readBytes m.frame.code (m.frame.pc + 1) n)) := by
  obtain ⟨s, hin, hst⟩ := h
  obtain ⟨e, imm, ss, hf, hok, succs, ha, hall⟩ := hc.closed _ _ hin
  obtain ⟨b', hb', he, himm⟩ := hc.ins.find hf
  rw [← hcode, hb] at hb'
  cases hb'
  subst he
  refine ⟨s, imm, succs, hst, hok, ha, hall, fun n hn => ?_⟩
  rw [gbyteEff_push hn, hcode]; exact himm

/-- At the start of a frame running `code` (pc `0`, empty stack), from a certificate explored
from the empty stack. -/
theorem ginCert_init (hc : GCert ν cfg code [] t) {m : Machine} (hpc : m.frame.pc = 0)
    (hst : m.frame.stack = []) : GInCert ν t m :=
  ⟨[], by rw [hpc]; exact hc.init, by rw [hst]; trivial⟩

/-- **An instruction continuing the frame keeps the invariant** (while the facts hold). -/
theorem ginCert_next (hc : GCert ν cfg code init t) {m m' : Machine} {b : UInt8}
    (hcode : m.frame.code = code) (h : GInCert ν t m) (henv : EnvOk ν cfg m)
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m')) : GInCert ν t m' := by
  obtain ⟨s, imm, succs, hst, -, hsucc, hall, himm⟩ := h.entry hc hcode hb
  have hpost : GNextPost (gbyteEff b) m m' := (gexec_eff_byte m.ctx.fork b m).of_run he
  obtain ⟨x, hx, hx1, hx2⟩ := gsucc_next henv hst rfl himm hpost hsucc
  exact ⟨x.2, by rw [← hx1]; exact hall x hx, hx2⟩

/-- **The invariant holds after any child returns.** -/
theorem ginCert_resume (hc : GCert ν cfg code init t) {m m' : Machine} {b : UInt8}
    {a : Action} (hcode : m.frame.code = code) (h : GInCert ν t m)
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m'))
    (ha : (∃ req, a = .call req) ∨ ∃ msg, a = .create msg) (M : Machine) (r : ChildResult)
    (hM : M.frame = m'.frame) : GInCert ν t (resume M r) := by
  obtain ⟨s, imm, succs, hst, -, hsucc, hall, -⟩ := h.entry hc hcode hb
  have hpost := (gexec_eff_byte m.ctx.fork b m).of_run he
  have hcp : GCallPost (gbyteEff b) m m' ∨ GCreatePost (gbyteEff b) m m' := by
    rcases ha with ⟨req, rfl⟩ | ⟨msg, rfl⟩
    · exact .inl hpost
    · exact .inr hpost
  have hpc' : m'.frame.pc = m.frame.pc := by
    cases hb' : gbyteEff b <;> rw [hb'] at hcp <;>
      simp only [GCallPost, GCreatePost, or_false, false_or] at hcp <;> exact hcp.1
  obtain ⟨hpc, ⟨w, hw⟩, -⟩ := resume_frame M r
  obtain ⟨x, hx, hx1, hx2⟩ := gsucc_child hst hcp hsucc w
  refine ⟨x.2, ?_, ?_⟩
  · rw [hpc, hM, hpc', ← hx1]; exact hall x hx
  · rw [hw, hM]; exact hx2

/-- **The calls of a described frame** go to allowed targets, running the target's code
(unless it holds an EIP-7702 designator). -/
theorem ginCert_call (hc : GCert ν cfg code init t) {m m' : Machine} {b : UInt8}
    {req : CallRequest} (hcode : m.frame.code = code) (h : GInCert ν t m)
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m')) :
    ∃ tw a, m.frame.stack[1]? = some tw ∧ cfg.callAllowed a = true ∧ a.Holds ν tw ∧
      ((m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress tw)) = none) →
        req.msg.codeAddress = some (Word.toAddress tw) ∧
        req.msg.code = m.world.code (Word.toAddress tw) ∧ req.msg.disablePrecompiles = false) := by
  obtain ⟨s, imm, succs, hst, hok, -, -, -⟩ := h.entry hc hcode hb
  have hpost : GCallPost (gbyteEff b) m m' := (gexec_eff_byte m.ctx.fork b m).of_run he
  obtain ⟨tw, htw, hcall⟩ := (exec_target _ m).of_run he req rfl
  cases hbe : gbyteEff b with
  | call p =>
    rw [hbe] at hok
    obtain ⟨a, ha, hat⟩ := gok_target hok hst htw
    exact ⟨tw, a, htw, ha, hat, hcall⟩
  | _ => rw [hbe] at hpost; exact hpost.elim

/-- **A described frame requests no creation.** -/
theorem ginCert_no_create (hc : GCert ν cfg code init t) {m m' : Machine} {b : UInt8}
    {msg : Message} (hcode : m.frame.code = code) (h : GInCert ν t m)
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.create msg, m')) : False := by
  obtain ⟨s, imm, succs, hst, hok, -, -, -⟩ := h.entry hc hcode hb
  have hpost : GCreatePost (gbyteEff b) m m' := (gexec_eff_byte m.ctx.fork b m).of_run he
  cases hbe : gbyteEff b with
  | create p => rw [hbe] at hok; simp [gok] at hok
  | _ => rw [hbe] at hpost; exact hpost.elim

/-- **The `SSTORE`s of a described frame** write allowed keys. -/
theorem ginCert_sstore (hc : GCert ν cfg code init t) {m m' : Machine} {b : UInt8} {a : Action}
    (hcode : m.frame.code = code) (h : GInCert ν t m) (hb : m.frame.code[m.frame.pc]? = some b)
    (hdec : Opcode.decode m.ctx.fork b = .sstore)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m')) :
    ∃ k v r av, m.frame.stack = k :: v :: r ∧
      m'.world = m.world.sstore m.frame.msg.currentTarget k v ∧
      cfg.sstoreAllowed av = true ∧ av.Holds ν k := by
  obtain ⟨s, imm, succs, hst, hok, -, -, -⟩ := h.entry hc hcode hb
  rw [hdec] at he
  obtain ⟨k, v, r, hstk, hw⟩ := (exec_sstore_world m).of_run he
  have hge : gbyteEff b = .sstore := by
    unfold gbyteEff
    rcases decode_osaka_or_invalid m.ctx.fork b with h' | h'
    · rw [← h', hdec]; rfl
    · rw [hdec] at h'; cases h'
  rw [hge] at hok
  obtain ⟨av, hav, hk⟩ := gok_sstore hok hst hstk
  exact ⟨k, v, r, av, hstk, hw, hav, hk⟩

end EvmLogic.AbsInt.Guard
