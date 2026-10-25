import Verified.OpenZeppelin.ERC20.Spec.Kind
import EvmLogic.GasMono.CodeScan

/-!
# Low gas for code without `GAS`, calls or creations

A frame running code in which no instruction reads the gas or starts a child (`NoGasCode`:
no `GAS`, `CALL*` or `CREATE*` at an instruction boundary) does with less gas what it does
with more, or fails (`lockstep`). Unlike the general lockstep of `EvmLogic/GasMono/` this
needs no hypothesis on the precompiles and no final `INVALID`: execution stays at
instruction boundaries or past the end of the code (`PcIn`), since every jump lands on a
`JUMPDEST`.

The high-gas frame is compared at the top level and as a call (`high`): there a `Halts`
witness determines the frame's return data, world, transient storage and logs on success
(`top_success_inv`), whatever the kind of the low frame. `lift`: a summary of the high frame
whose successes are described by those four transfers to the low frame, with its created
accounts unchanged.
-/

namespace Verified.OpenZeppelin.ERC20.Spec
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested EvmLogic.GasMono

/-! ## The code condition -/

/-- The bytes of `GAS` and of the `CALL` and `CREATE` families. -/
def gasByteB (b : UInt8) : Bool :=
  b == 0x5a || b == 0xf0 || b == 0xf1 || b == 0xf2 || b == 0xf4 || b == 0xf5 || b == 0xfa

/-- No instruction of `code` reads the gas or starts a child. -/
def NoGasCode (code : ByteArray) : Prop := ∀ q ∈ boundaries code, gasByteB (Bytes.getD code q) = false

/-- `NoGasCode` from the fast instruction scan (decided by the kernel). -/
theorem noGasCode_of_scan {code : ByteArray}
    (h : (insns code).all (fun e => !gasByteB e.2.1) = true) : NoGasCode code := by
  intro q hq
  rw [insns_eq, List.all_map, List.all_eq_true] at h
  have := h q hq
  simpa [insnInfo] using this

theorem readsGasB_eq_false {code : ByteArray} (h : NoGasCode code) {q : Nat}
    (hq : q ∈ boundaries code) (fork : Fork) :
    readsGasB (Opcode.decode fork (Bytes.getD code q)) = false := by
  cases hr : readsGasB (Opcode.decode fork (Bytes.getD code q)) with
  | false => rfl
  | true =>
    have hb := h q hq
    rcases readsGas_decode fork _ hr with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;>
      rw [h1] at hb <;> simp [gasByteB] at hb

/-! ## Where the pc goes -/

/-- The pc is an instruction boundary or past the end of the code. -/
def PcIn (code : ByteArray) (pc : Nat) : Prop := pc ∈ boundaries code ∨ code.size ≤ pc

theorem pcIn_zero (code : ByteArray) : PcIn code 0 := by
  by_cases h : code.size = 0
  · exact .inr (by omega)
  · left
    unfold boundaries
    obtain ⟨k, hk⟩ : ∃ k, code.size = k + 1 := ⟨code.size - 1, by omega⟩
    rw [hk, boundariesFrom_succ]
    simp only [show 0 < code.size by omega, ↓reduceIte]
    exact List.mem_cons_self

theorem pcIn_of_exec {code : ByteArray} {m m' : Machine} {b : UInt8}
    (hj : m.frame.jumpDests = validJumpDests code) (hpc : m.frame.pc ∈ boundaries code)
    (hb : b = Bytes.getD code m.frame.pc)
    (h : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m')) :
    PcIn code m'.frame.pc := by
  have hpost := (exec_pc _ m).of_run h
  simp only [PcPost, immOf_decode] at hpost
  rcases hpost with h1 | h1
  · rw [h1, hb]
    by_cases hn : nextPc code m.frame.pc < code.size
    · exact .inl (next_mem_boundaries hpc hn)
    · exact .inr (by unfold nextPc at hn; omega)
  · rw [hj] at h1
    exact .inl (mem_boundaries_of_validJumpDests h1).1

/-! ## The lockstep -/

/-- The high machine: `d` more gas, message gas `x`, parents `ps`, frame kind `k`. -/
def hi (d x : Nat) (ps : List Frame) (k : FrameKind) (m : Machine) : Machine :=
  setKind k (bump d x ps m)

theorem sameFrame_hi {m m' : Machine} (h : SameFrame m m') (d d' x : Nat) (ps : List Frame)
    (k : FrameKind) : SameFrame (hi d x ps k m) (hi d' x ps k m') :=
  ⟨h.ctx, h.precompiles, h.originalWorld, rfl, by simp [hi, setKind, bump, h.msg], h.code,
    h.jumpDests, rfl, h.snapshot⟩

/-- The end of the low frame (from `ml`) against the end of the high one: a failure, or the
same outcome from a machine the high one is a `hi` of, with the created accounts of `ml`. -/
def LPost (ml mfh : Machine) (oh : Outcome) (mfl : Machine) (ol : Outcome) : Prop :=
  Failed ol ∨ (ol = oh ∧ (∃ d x ps k, mfh = hi d x ps k mfl) ∧
    mfl.createdAccounts = ml.createdAccounts)

set_option maxHeartbeats 1000000 in
/-- **The lockstep**: with `NoGasCode`, a frame with less gas fails or ends exactly as its
`hi` version ends (`Exit`). -/
theorem lockstep {code : ByteArray} (hno : NoGasCode code) : ∀ N ml d x ps k mfh oh,
    ml.frame.code = code → ml.frame.jumpDests = validJumpDests code → PcIn code ml.frame.pc →
    Exit (hi d x ps k ml) N mfh oh → Halts ml (LPost ml mfh oh) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro ml d x ps k mfh oh hcode hjd hpc hex
    rcases hpc with hpc | hpc
    · have hlt := lt_size_of_mem_boundaries hpc
      have hlt' : ml.frame.pc < ml.frame.code.size := by rw [hcode]; exact hlt
      have hb : ml.frame.code[ml.frame.pc]? = some (Bytes.getD code ml.frame.pc) := by
        rw [getElem?_eq_some_iff]
        refine ⟨hlt', ?_⟩
        subst hcode
        exact (getD_eq_getElem hlt).symm
      have hbh : (hi d x ps k ml).frame.code[(hi d x ps k ml).frame.pc]? =
          some (Bytes.getD code ml.frame.pc) := hb
      have hrg := readsGasB_eq_false hno hpc ml.ctx.fork
      have hop : ¬ ReadsGas (Opcode.decode ml.ctx.fork (Bytes.getD code ml.frame.pc)) := by
        rw [readsGas_iff, hrg]; simp
      cases hrun : (exec (Opcode.decode ml.ctx.fork (Bytes.getD code ml.frame.pc))).run ml with
      | error e =>
        exact Halts.of_step (step_of_exec_error hb hrun) (.refl ml) (.inl (fun out h => by cases h))
      | ok p =>
        obtain ⟨act, ml'⟩ := p
        have hrunh : (exec (Opcode.decode (hi d x ps k ml).ctx.fork
            (Bytes.getD code ml.frame.pc))).run (hi d x ps k ml) = .ok (act, hi d x ps k ml') :=
          exec_setKind _ hop (exec_bump _ hop hrun d x ps) k
        have hfl := ((exec_frame _ ml).of_run hrun).1
        have hnc := (exec_noChild _ hrg ml).of_run hrun
        cases act with
        | next =>
          have hstepl := step_of_exec_next hb hrun
          have hsteph : step (hi d x ps k ml) = .running (hi d x ps k ml') :=
            step_of_exec_next hbh hrunh
          have hst := sameFrame_hi hfl.same d d x ps k
          obtain ⟨hN, hex'⟩ := hex.next hsteph hst
          have hpc' := pcIn_of_exec hjd hpc rfl hrun
          have hrec := ih (N - 1) (by omega) ml' d x ps k mfh oh (hfl.same.code.trans hcode)
            (hfl.same.jumpDests.trans hjd) hpc' hex'
          refine Halts.of_steps (Steps.of_step hstepl hfl.same) (hrec.mono ?_)
          rintro mfl ol - (hf | ⟨h1, h2, h3⟩)
          · exact .inl hf
          · exact .inr ⟨h1, h2, h3.trans hfl.created⟩
        | stop out =>
          have hxh := (exitOf_of_exec hbh hrunh).1 out rfl
          obtain ⟨-, rfl, rfl⟩ := (exit_zero hxh).unique hex
          exact Halts.of_step (step_of_exec_stop hb hrun) hfl.same
            (.inr ⟨rfl, ⟨d, x, ps, k, rfl⟩, hfl.created⟩)
        | revert out =>
          have hxh := (exitOf_of_exec hbh hrunh).2 out rfl
          obtain ⟨-, rfl, rfl⟩ := (exit_zero hxh).unique hex
          exact Halts.of_step (step_of_exec_revert hb hrun) hfl.same
            (.inr ⟨rfl, ⟨d, x, ps, k, rfl⟩, hfl.created⟩)
        | call req => exact hnc.elim
        | create msg => exact hnc.elim
    · have hge : ¬ ml.frame.pc < ml.frame.code.size := by rw [hcode]; omega
      have hstep : step ml = finishFrame ml (.success .empty) := by
        unfold step; simp only [hge, ↓reduceDIte]
      have hx : exitOf (hi d x ps k ml) = some (hi d x ps k ml, .success .empty) := by
        unfold exitOf
        have : ¬ (hi d x ps k ml).frame.pc < (hi d x ps k ml).frame.code.size := hge
        simp only [this, ↓reduceDIte]
      obtain ⟨-, rfl, rfl⟩ := (exit_zero hx).unique hex
      exact Halts.of_step hstep (.refl ml) (.inr ⟨rfl, ⟨d, x, ps, k, rfl⟩, rfl⟩)

/-! ## Transferring a summary to lower gas -/

/-- The frame `m` with gas `G`, at the top level, as a call. -/
def high (G : Nat) (m : Machine) : Machine := hi (G - m.frame.gasLeft) G [] (.call 0 0) m

@[simp] theorem high_world (G : Nat) (m : Machine) : (high G m).world = m.world := rfl
@[simp] theorem high_transient (G : Nat) (m : Machine) : (high G m).transient = m.transient := rfl
@[simp] theorem high_created (G : Nat) (m : Machine) :
    (high G m).createdAccounts = m.createdAccounts := rfl
@[simp] theorem high_ctx (G : Nat) (m : Machine) : (high G m).ctx = m.ctx := rfl
@[simp] theorem high_logs (G : Nat) (m : Machine) :
    (high G m).frame.sub = m.frame.sub := rfl
@[simp] theorem high_snapshot (G : Nat) (m : Machine) :
    (high G m).frame.snapshot = m.frame.snapshot := rfl
@[simp] theorem high_gasLeft {G : Nat} {m : Machine} (h : m.frame.gasLeft ≤ G) :
    (high G m).frame.gasLeft = G := by
  simp only [high, hi, setKind, bump]; omega

theorem fresh_high {code : ByteArray} {m : Machine} (hf : Fresh code m) {G : Nat}
    (hG : m.frame.gasLeft ≤ G) : Fresh code (high G m) := by
  obtain ⟨msg, kind, snap, hfr, hc⟩ := hf
  refine ⟨{ msg with gas := G }, .call 0 0, snap, ?_, hc⟩
  have hg : m.frame.gasLeft = msg.gas := by rw [hfr]; rfl
  simp only [high, hi, setKind, bump, hfr, Frame.init, Frame.mk.injEq, and_true, true_and]
  rw [hfr] at hG; simp only [Frame.init] at hG; omega

/-- **Two successful ends of a top-level call frame with the same final result** have the
same return data, world, transient storage and logs. -/
theorem top_success_inv {mf mf' : Machine} {out : ByteArray} {o' : Outcome} {ko ks : Nat}
    (hk : mf.frame.kind = .call ko ks) (hk' : mf'.frame.kind = .call ko ks)
    (hp : mf.parents = []) (hp' : mf'.parents = [])
    (ht : mf'.frame.msg = mf.frame.msg)
    (h : finishFrame mf' o' = finishFrame mf (.success out)) :
    o' = .success out ∧ mf'.world = mf.world ∧ mf'.transient = mf.transient ∧
      mf'.frame.sub.logs = mf.frame.sub.logs := by
  rw [finishFrame_of_top _ hp', finishFrame_of_top _ hp, frameResult_success_call hk, ht] at h
  cases o' with
  | success out' =>
    rw [frameResult_success_call hk'] at h
    injection h with h
    simp only [topLevelResult, ChildResult.success, Option.isNone_none, Bool.not_false,
      Bool.and_self, ↓reduceIte, MessageResult.mk.injEq] at h
    obtain ⟨-, -, hl, -, -, -, -, ho, hw, htr⟩ := h
    exact ⟨by rw [ho], hw, htr, hl⟩
  | revert out' =>
    have := congrArg (fun r => match r with | .done r => r.reverted | .running _ => false) h
    simp [topLevelResult, ChildResult.success, frameResult_revert] at this
  | halt e =>
    have := congrArg (fun r => match r with | .done r => r.error | .running _ => none) h
    simp [topLevelResult, ChildResult.success, frameResult_halt] at this

/-- What a successful end may be required to satisfy: the return data, world, transient
storage and logs. -/
abbrev SuccessPost := ByteArray → World → TransientStorage → Array Log → Prop

/-- **A summary transfers to lower gas.** If the frame `m` with gas `G`, at the top
level as a call (`high G m`), fails or succeeds as `Q` says, then so does `m`, also keeping its
created accounts. (Useful for `G` above `m`'s gas; `G` is arbitrary.) -/
theorem lift {code : ByteArray} (hno : NoGasCode code) {m : Machine} (hf : Fresh code m) {G : Nat}
    {Q : SuccessPost}
    (h : Halts (high G m) fun mf o =>
      Failed o ∨ ∃ out, o = .success out ∧ Q out mf.world mf.transient mf.frame.sub.logs) :
    Halts m fun mf o => Failed o ∨ ∃ out, o = .success out ∧
      Q out mf.world mf.transient mf.frame.sub.logs ∧ mf.createdAccounts = m.createdAccounts := by
  obtain ⟨hcode, hjd, hpc0, -⟩ := hf.frame
  obtain ⟨N, mfh, oh, hex, mf', o', hH, hs', hfin⟩ := exit_of_halts_top rfl h
  have hlow := lockstep hno N m _ _ _ _ mfh oh hcode hjd (by rw [hpc0]; exact pcIn_zero _) hex
  refine hlow.mono fun mfl ol _ hpost => ?_
  rcases hpost with hfl | ⟨rfl, ⟨d, x, ps, k, rfl⟩, hcr⟩
  · exact .inl hfl
  · cases ol with
    | success out =>
      right
      have hfh := hex.finish.2
      have hkh : (hi d x ps k mfl).frame.kind = .call 0 0 := hfh.kind
      have hk' : mf'.frame.kind = .call 0 0 := hs'.kind
      obtain ⟨ho, hw, htr, hl⟩ := top_success_inv hkh hk' hfh.parents hs'.parents
        (hs'.msg.trans hfh.msg.symm) hfin
      rcases hH with hF | ⟨out', ho', hQ⟩
      · exact absurd ho (hF out)
      · rw [ho] at ho'
        cases ho'
        refine ⟨out, rfl, ?_, hcr⟩
        rw [hw, htr, hl] at hQ
        exact hQ
    | revert out => exact .inl (fun _ h => by cases h)
    | halt e => exact .inl (fun _ h => by cases h)

end Verified.OpenZeppelin.ERC20.Spec
