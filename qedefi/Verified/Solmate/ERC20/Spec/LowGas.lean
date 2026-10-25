import EvmLogic.GasMono.Lockstep

/-!
# Low gas without calls: a frame summary transfers to any lower gas

The gas lockstep of `EvmLogic.GasMono` asks the children of the high frame to be gas-monotone.
A token's frame that executes no `GAS`, no call and no creation needs none of that, nor the
standard precompiles: `lockstep` runs a low frame against the same frame *lifted* (more gas,
any message gas, any parents, any frame kind: `lift`), up to the lifted frame's exit; the low
frame fails or ends exactly as the lifted one (`LPost`).

`lowGas`: a frame summary of the lifted frame under a dummy parent with empty code (`pin`
makes the summary's witness the real exit) transfers to the low frame: it fails, or succeeds
with the summary's observable post (world, transient storage, created accounts, logs, output).
The frame kind of the lifted frame is a call, whatever the low frame's, so that the parent sees
everything a successful child hands back.
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested EvmLogic.GasMono

/-! ## Changing the frame kind -/

/-- The machine with frame kind `k`. -/
def setKind (k : FrameKind) (m : Machine) : Machine :=
  { m with frame := { m.frame with kind := k } }

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
/-- **No instruction reads the frame kind** (those that read the gas aside). -/
theorem exec_setKind_wp (op : Opcode) (hop : ¬ ReadsGas op) (m : Machine) (k : FrameKind) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = setKind k m') (setKind k m)) m := by
  cases op
  case call | callcode | delegatecall | staticcall | gas | create | create2 =>
    exact absurd trivial hop
  case returndatacopy =>
    simp [exec, memoryExpansion, expandMemory, writeMemory, setKind]
    intros
    simp_all
    intro hz
    simp only [hz] at *
    exact ⟨by omega, by omega, .inl (by omega)⟩
  case dup n =>
    simp [exec, setKind]
    intro _
    split <;> simp_all
  case swap n =>
    simp [exec, setKind]
    intro _
    split <;> simp_all
  case log n =>
    simp [exec, execLog, setKind, memoryExpansion, expandMemory, requireNonStatic, readMemory]
    intros
    subst_vars
    simp_all
  all_goals try (simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    setKind, execSstore, execSelfdestruct, execLog, execCall, execCreate, genericCall,
    setReturnData] <;> intros <;> (try simp_all) <;> done)

theorem exec_setKind (op : Opcode) (hop : ¬ ReadsGas op) {m m' : Machine} {a : Action}
    (h : (exec op).run m = .ok (a, m')) (k : FrameKind) :
    (exec op).run (setKind k m) = .ok (a, setKind k m') := by
  have hw := (exec_setKind_wp op hop m k).of_run h
  unfold Twp at hw
  split at hw
  · rename_i a' m'' he
    obtain ⟨rfl, rfl⟩ := hw
    exact he
  · exact hw.elim

/-! ## Lifted frames -/

/-- The frame of `m` with `d` more gas, message gas `x`, parents `ps` and kind `k`. -/
def lift (d x : Nat) (ps : List Frame) (k : FrameKind) (m : Machine) : Machine :=
  setKind k (bump d x ps m)

theorem exec_lift (op : Opcode) (hop : ¬ ReadsGas op) {m m' : Machine} {a : Action}
    (h : (exec op).run m = .ok (a, m')) (d x : Nat) (ps : List Frame) (k : FrameKind) :
    (exec op).run (lift d x ps k m) = .ok (a, lift d x ps k m') :=
  exec_setKind op hop (exec_bump op hop h d x ps) k

theorem sameFrame_lift {m m' : Machine} (h : SameFrame m m') (d d' x : Nat) (ps : List Frame)
    (k : FrameKind) : SameFrame (lift d x ps k m) (lift d' x ps k m') :=
  ⟨h.ctx, h.precompiles, h.originalWorld, rfl, by simp [lift, setKind, bump, h.msg], h.code,
    h.jumpDests, rfl, h.snapshot⟩

/-- The lifted frame executes no instruction reading the gas (no `GAS`, call or creation) up
to step `N`. -/
def NoGasRead (mh : Machine) (N : Nat) : Prop :=
  ∀ j ≤ N, ∀ m' b, stepN j mh = .running m' → SameFrame mh m' →
    m'.frame.code[m'.frame.pc]? = some b → readsGasB (Opcode.decode m'.ctx.fork b) = false

/-- **The end of a low frame against the end of its lift**: it failed, or ended with the same
outcome from a machine that the lifted one lifts. -/
def LPost (mfh : Machine) (oh : Outcome) (mfl : Machine) (ol : Outcome) : Prop :=
  Failed ol ∨ (ol = oh ∧ ∃ d x ps k, mfh = lift d x ps k mfl)

theorem step_of_pc_ge {m : Machine} (h : ¬ m.frame.pc < m.frame.code.size) :
    step m = finishFrame m (.success .empty) := by
  unfold step; simp only [h, ↓reduceDIte]

theorem exitOf_of_pc_ge {m : Machine} (h : ¬ m.frame.pc < m.frame.code.size) :
    exitOf m = some (m, .success .empty) := by
  unfold exitOf; simp only [h, ↓reduceDIte]

/-- **The lockstep without calls.** -/
theorem lockstep : ∀ N, ∀ ml d x ps k mfh oh, Exit (lift d x ps k ml) N mfh oh →
    NoGasRead (lift d x ps k ml) N → Halts ml (LPost mfh oh) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro ml d x ps k mfh oh hex hng
    cases hb : ml.frame.code[ml.frame.pc]? with
    | none =>
      have hlt : ¬ ml.frame.pc < ml.frame.code.size := by
        intro h; simp [h] at hb
      have hlth : ¬ (lift d x ps k ml).frame.pc < (lift d x ps k ml).frame.code.size := hlt
      obtain ⟨-, rfl, rfl⟩ := (exit_zero (exitOf_of_pc_ge hlth)).unique hex
      exact Halts.of_step (step_of_pc_ge hlt) (.refl ml) (.inr ⟨rfl, d, x, ps, k, rfl⟩)
    | some b =>
      have hbh : (lift d x ps k ml).frame.code[(lift d x ps k ml).frame.pc]? = some b := hb
      have hrg : readsGasB (Opcode.decode ml.ctx.fork b) = false :=
        hng 0 (Nat.zero_le _) (lift d x ps k ml) b rfl (.refl _) hbh
      have hop : ¬ ReadsGas (Opcode.decode ml.ctx.fork b) := by
        rw [readsGas_iff, hrg]; simp
      cases hrun : (exec (Opcode.decode ml.ctx.fork b)).run ml with
      | error e =>
        exact Halts.of_step (step_of_exec_error hb hrun) (.refl ml)
          (.inl (fun out h => by cases h))
      | ok p =>
        obtain ⟨act, ml'⟩ := p
        have hrunh : (exec (Opcode.decode (lift d x ps k ml).ctx.fork b)).run (lift d x ps k ml) =
            .ok (act, lift d x ps k ml') := exec_lift _ hop hrun d x ps k
        have hfl := ((exec_frame _ ml).of_run hrun).1
        have hnc := (exec_noChild _ hrg ml).of_run hrun
        cases act with
        | next =>
          have hstepl := step_of_exec_next hb hrun
          have hsteph : step (lift d x ps k ml) = .running (lift d x ps k ml') :=
            step_of_exec_next hbh hrunh
          have hst := sameFrame_lift hfl.same d d x ps k
          obtain ⟨hN, hex'⟩ := hex.next hsteph hst
          refine Halts.of_steps (Steps.of_step hstepl hfl.same)
            (ih (N - 1) (by omega) ml' d x ps k mfh oh hex' ?_)
          intro j hj m' b' hj' hs' hb'
          refine hng (1 + j) (by omega) m' b' ?_ (hst.trans hs') hb'
          rw [stepN_add_of_running (by rw [stepN_one, hsteph])]; exact hj'
        | stop out =>
          have hxh := (exitOf_of_exec hbh hrunh).1 out rfl
          obtain ⟨-, rfl, rfl⟩ := (exit_zero hxh).unique hex
          exact Halts.of_step (step_of_exec_stop hb hrun) hfl.same
            (.inr ⟨rfl, d, x, ps, k, rfl⟩)
        | revert out =>
          have hxh := (exitOf_of_exec hbh hrunh).2 out rfl
          obtain ⟨-, rfl, rfl⟩ := (exit_zero hxh).unique hex
          exact Halts.of_step (step_of_exec_revert hb hrun) hfl.same
            (.inr ⟨rfl, d, x, ps, k, rfl⟩)
        | call req => exact hnc.elim
        | create msg => exact hnc.elim

/-! ## Pinning a summary to the exit -/

theorem step_resumeAfter_empty {p : Frame} (hc : p.code.size = 0) (mf : Machine) (o : Outcome) :
    ∃ r, step (resumeAfter p [] mf o) = .done r := by
  have hlt : ¬ (resumeAfter p [] mf o).frame.pc < (resumeAfter p [] mf o).frame.code.size := by
    have : (resumeAfter p [] mf o).frame.code = p.code := rfl
    rw [this, hc]; omega
  rw [step_of_pc_ge hlt, finishFrame_of_top _ (by simp [resumeAfter])]
  exact ⟨_, rfl⟩

/-- **A summary of a frame under a parent with empty code describes its exit**: the witness of
`Halts` ends the frame exactly as the exit does, as the parent sees it. -/
theorem pin {mh : Machine} {p0 : Frame} (hp : mh.parents = [p0]) (hc : p0.code.size = 0)
    {H : Machine → Outcome → Prop} (h : Halts mh H) :
    ∃ N mfh oh, Exit mh N mfh oh ∧ ∃ mf' o', H mf' o' ∧ SameFrame mh mf' ∧
      resumeAfter p0 [] mf' o' = resumeAfter p0 [] mfh oh := by
  obtain ⟨n, mf', o', hn, hs', hH⟩ := h
  rw [finishFrame_of_parents o' (hs'.parents.trans hp)] at hn
  have hna : ¬ ∃ m', stepN n mh = .running m' ∧ Above mh m' := by
    rintro ⟨m', h1, h2⟩
    rw [hn] at h1
    cases h1
    have := h2.length_le
    simp [resumeAfter, hp] at this
  obtain ⟨k, hk, mfh, oh, hex⟩ := exit_of_leaves hna
  have hfin := hex.finish
  have hR := hfin.1
  rw [finishFrame_of_parents oh (hfin.2.parents.trans hp)] at hR
  refine ⟨k, mfh, oh, hex, mf', o', hH, hs', ?_⟩
  by_cases hnk : n = k + 1
  · subst hnk; rw [hR] at hn; exact (StepResult.running.inj hn).symm
  · obtain ⟨r, hr⟩ := step_resumeAfter_empty hc mfh oh
    have := stepN_add_of_running hR (n - (k + 1))
    rw [show k + 1 + (n - (k + 1)) = n by omega, hn,
      show n - (k + 1) = (n - (k + 2)) + 1 by omega, stepN_succ_of_done hr] at this
    cases this

/-- **What the parent sees of a successful call frame**: the outcome, world, transient storage,
created accounts and logs. -/
theorem resumeAfter_success {p : Frame} {mf mf' : Machine} {o' : Outcome} {out : ByteArray}
    {a b : Nat} (hk : mf.frame.kind = .call a b) (hk' : mf'.frame.kind = .call a b)
    (h : resumeAfter p [] mf' o' = resumeAfter p [] mf (.success out)) :
    o' = .success out ∧ mf'.world = mf.world ∧ mf'.transient = mf.transient ∧
      mf'.createdAccounts = mf.createdAccounts ∧
      p.sub.logs ++ mf'.frame.sub.logs = p.sub.logs ++ mf.frame.sub.logs := by
  have hst := congrArg (fun M : Machine => M.frame.stack) h
  have hw := congrArg Machine.world h
  have ht := congrArg Machine.transient h
  have hc := congrArg Machine.createdAccounts h
  have hl := congrArg (fun M : Machine => M.frame.sub.logs) h
  have hrd := congrArg (fun M : Machine => M.frame.returnData) h
  cases o' with
  | success out' =>
    simp [resumeAfter, frameResult, resume, hk, hk', ChildResult.success] at hst hw ht hc hl hrd
    exact ⟨by rw [hrd], hw, ht, hc, hl⟩
  | revert out' =>
    simp [resumeAfter, frameResult, resume, hk, hk', ChildResult.success] at hst
  | halt e =>
    simp [resumeAfter, frameResult, resume, hk, hk', ChildResult.success] at hst

/-- **A frame summary transfers to any lower gas**, for a frame that reads no gas: if the frame
lifted under a parent with empty code (as a call frame) succeeds only with a post `P` of its
observables, the frame itself fails or succeeds with `P`. -/
theorem lowGas {ml : Machine} {d x : Nat} {p0 : Frame} (hc : p0.code.size = 0) {a b : Nat}
    {P : ByteArray → Machine → Prop}
    (hP : ∀ out mf mf', mf'.world = mf.world → mf'.transient = mf.transient →
      mf'.createdAccounts = mf.createdAccounts → mf'.frame.sub.logs = mf.frame.sub.logs →
      P out mf → P out mf')
    (hhigh : Halts (lift d x [p0] (.call a b) ml) fun mf o => ∀ out, o = .success out → P out mf)
    (hng : ∀ N mfh oh, Exit (lift d x [p0] (.call a b) ml) N mfh oh →
      NoGasRead (lift d x [p0] (.call a b) ml) N) :
    Halts ml fun mf o => Failed o ∨ ∃ out, o = .success out ∧ P out mf := by
  obtain ⟨N, mfh, oh, hex, mf', o', hH, hs', heq⟩ := pin rfl hc hhigh
  refine (lockstep N ml d x [p0] (.call a b) mfh oh hex (hng N mfh oh hex)).mono
    fun mfl ol _ hpost => ?_
  rcases hpost with hf | ⟨rfl, d', x', ps', k', hmf⟩
  · exact .inl hf
  · cases ol with
    | success out =>
      have hkh : mfh.frame.kind = .call a b := hex.finish.2.kind
      have hk' : mf'.frame.kind = .call a b := hs'.kind
      obtain ⟨rfl, hw, ht, hcr, hl⟩ := resumeAfter_success hkh hk' heq
      have hP' := hP out mf' mfh hw.symm ht.symm hcr.symm ((Array.append_right_inj _).1 hl).symm
        (hH out rfl)
      refine .inr ⟨out, rfl, hP out mfh mfl ?_ ?_ ?_ ?_ hP'⟩ <;> rw [hmf] <;> rfl
    | revert out => exact .inl (fun _ h => by cases h)
    | halt e => exact .inl (fun _ h => by cases h)

end Verified.Solmate.ERC20.Spec
