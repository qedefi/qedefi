import Verified.Solmate.ERC20.Spec.LowGas
import EvmLogic.AbsInt.Frame

/-!
# Running a frame as another kind, under other parents

No instruction reads the frame's kind or its parents (`exec_reframe`), and a call answered by a
precompile resumes the frame in place (`launchCall_reframe`). So a frame whose calls all go to
precompiles and which creates nothing runs in lockstep with the same frame re-kinded and
re-parented (`reframe`), to the same outcome (`lockstepK`). With it, a frame of any kind
(a creation running a token's runtime code included) is handled as a call frame.
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested EvmLogic.GasMono

/-- The machine `m` with frame kind `k` and parents `ps`. -/
def reframe (k : FrameKind) (ps : List Frame) (m : Machine) : Machine :=
  { m with frame := { m.frame with kind := k }, parents := ps }

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
theorem exec_reframe_call (c : CallKind) (m : Machine) (k : FrameKind) (ps : List Frame) :
    Wp (execCall c) (fun a m' => Twp (execCall c)
      (fun a' m'' => a' = a ∧ m'' = reframe k ps m') (reframe k ps m)) m := by
  cases c <;> simp (config := {maxSteps := 4000000}) [execCall, reframe, memoryExpansion,
    expandMemory, readMemory, setReturnData, genericCall, accessDelegation, delegateCode] <;>
    intros <;> (try simp_all) <;> (try split) <;> simp_all

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
theorem exec_reframe_create (b : Bool) (m : Machine) (k : FrameKind) (ps : List Frame) :
    Wp (execCreate b) (fun a m' => Twp (execCreate b)
      (fun a' m'' => a' = a ∧ m'' = reframe k ps m') (reframe k ps m)) m := by
  cases b <;> simp (config := {maxSteps := 4000000}) [execCreate, reframe, memoryExpansion,
    requireNonStatic, expandMemory, readMemory, setReturnData] <;>
    intros <;> (try simp_all) <;> (try split) <;> (try simp_all)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
/-- **No instruction reads the frame's kind or parents.** -/
theorem exec_reframe_wp (op : Opcode) (m : Machine) (k : FrameKind) (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = reframe k ps m') (reframe k ps m)) m := by
  cases op
  case call => exact exec_reframe_call .call m k ps
  case callcode => exact exec_reframe_call .callcode m k ps
  case delegatecall => exact exec_reframe_call .delegatecall m k ps
  case staticcall => exact exec_reframe_call .staticcall m k ps
  case create => exact exec_reframe_create false m k ps
  case create2 => exact exec_reframe_create true m k ps
  case returndatacopy =>
    simp [exec, memoryExpansion, expandMemory, writeMemory, reframe]
    intros
    simp_all
    intro hz
    simp only [hz] at *
    exact ⟨by omega, by omega, .inl (by omega)⟩
  case dup n =>
    simp [exec, reframe]
    intro _
    split <;> simp_all
  case swap n =>
    simp [exec, reframe]
    intro _
    split <;> simp_all
  case log n =>
    simp [exec, execLog, reframe, memoryExpansion, expandMemory, requireNonStatic, readMemory]
    intros
    subst_vars
    simp_all
  all_goals try (simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    reframe, execSstore, execSelfdestruct, execLog, execCall, execCreate, genericCall,
    setReturnData] <;> intros <;> (try simp_all) <;> done)

theorem exec_reframe (op : Opcode) {m m' : Machine} {a : Action}
    (h : (exec op).run m = .ok (a, m')) (k : FrameKind) (ps : List Frame) :
    (exec op).run (reframe k ps m) = .ok (a, reframe k ps m') := by
  have hw := (exec_reframe_wp op m k ps).of_run h
  unfold Twp at hw
  split at hw
  · rename_i a' m'' he
    obtain ⟨rfl, rfl⟩ := hw
    exact he
  · exact hw.elim

/-- **A call answered by a precompile resumes the frame in place**, whatever its kind and
parents. -/
theorem launchCall_reframe {m : Machine} {req : CallRequest}
    (h : precompileOf m.precompiles req.msg ≠ none) (k : FrameKind) (ps : List Frame) :
    launchCall (reframe k ps m) req = reframe k ps (launchCall m req) := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h
  unfold launchCall reframe
  dsimp only
  rw [ha]
  rfl

theorem sameFrame_reframe {m m' : Machine} (h : SameFrame m m') (k : FrameKind)
    (ps : List Frame) : SameFrame (reframe k ps m) (reframe k ps m') :=
  ⟨h.ctx, h.precompiles, h.originalWorld, rfl, h.msg, h.code, h.jumpDests, rfl, h.snapshot⟩

/-- The calls of the frame before step `N` are answered by precompiles, and it creates
nothing. -/
def OnlyPrecompiles (mh : Machine) (N : Nat) : Prop :=
  ∀ j ≤ N, ∀ m' b a m'', stepN j mh = .running m' → SameFrame mh m' →
    m'.frame.code[m'.frame.pc]? = some b →
    (exec (Opcode.decode m'.ctx.fork b)).run m' = .ok (a, m'') →
    (∀ req, a = .call req → precompileOf m''.precompiles req.msg ≠ none) ∧
      (∀ msg, a ≠ .create msg)

/-- How a frame ends against its reframed copy: it failed, or ended as the copy did. -/
def KPost (k : FrameKind) (ps : List Frame) (mfh : Machine) (oh : Outcome) (mfl : Machine)
    (ol : Outcome) : Prop :=
  Failed ol ∨ (ol = oh ∧ mfh = reframe k ps mfl)

theorem sameFrame_launchCall {m : Machine} {req : CallRequest}
    (h : precompileOf m.precompiles req.msg ≠ none) : SameFrame m (launchCall m req) := by
  obtain ⟨w, t, r, hl, -⟩ := EvmLogic.AbsInt.launchCall_some h
  rw [hl]
  exact SameFrame.trans (m₂ := { m with world := w, transient := t })
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (sameFrame_resume _ _)

/-- **The kind-and-parents lockstep.** -/
theorem lockstepK : ∀ N, ∀ ml k ps mfh oh, Exit (reframe k ps ml) N mfh oh →
    OnlyPrecompiles (reframe k ps ml) N → Halts ml (KPost k ps mfh oh) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro ml k ps mfh oh hex hok
    cases hb : ml.frame.code[ml.frame.pc]? with
    | none =>
      have hlt : ¬ ml.frame.pc < ml.frame.code.size := by
        intro h; simp [h] at hb
      have hlth : ¬ (reframe k ps ml).frame.pc < (reframe k ps ml).frame.code.size := hlt
      obtain ⟨-, rfl, rfl⟩ := (exit_zero (exitOf_of_pc_ge hlth)).unique hex
      exact Halts.of_step (step_of_pc_ge hlt) (.refl ml) (.inr ⟨rfl, rfl⟩)
    | some b =>
      have hbh : (reframe k ps ml).frame.code[(reframe k ps ml).frame.pc]? = some b := hb
      cases hrun : (exec (Opcode.decode ml.ctx.fork b)).run ml with
      | error e =>
        exact Halts.of_step (step_of_exec_error hb hrun) (.refl ml)
          (.inl (fun out h => by cases h))
      | ok p =>
        obtain ⟨act, ml'⟩ := p
        have hrunh : (exec (Opcode.decode (reframe k ps ml).ctx.fork b)).run (reframe k ps ml) =
            .ok (act, reframe k ps ml') := exec_reframe _ hrun k ps
        have hfl := ((exec_frame _ ml).of_run hrun).1
        obtain ⟨hpre, hnc⟩ := hok 0 (Nat.zero_le _) _ b _ _ rfl (.refl _) hbh hrunh
        have shift : ∀ (ml₁ : Machine), 1 ≤ N → step (reframe k ps ml) = .running (reframe k ps ml₁) →
            SameFrame (reframe k ps ml) (reframe k ps ml₁) →
            OnlyPrecompiles (reframe k ps ml₁) (N - 1) := by
          intro ml₁ hN1 hst hs j hj m' b' a' m'' hj' hs' hb' hr'
          exact hok (1 + j) (by omega) m' b' a' m''
            (by rw [stepN_add_of_running (by rw [stepN_one, hst])]; exact hj') (hs.trans hs') hb' hr'
        cases act with
        | next =>
          have hstepl := step_of_exec_next hb hrun
          have hsteph : step (reframe k ps ml) = .running (reframe k ps ml') :=
            step_of_exec_next hbh hrunh
          have hst := sameFrame_reframe hfl.same k ps
          obtain ⟨hN, hex'⟩ := hex.next hsteph hst
          exact Halts.of_steps (Steps.of_step hstepl hfl.same)
            (ih (N - 1) (by omega) ml' k ps mfh oh hex' (shift ml' hN hsteph hst))
        | stop out =>
          have hxh := (exitOf_of_exec hbh hrunh).1 out rfl
          obtain ⟨-, rfl, rfl⟩ := (exit_zero hxh).unique hex
          exact Halts.of_step (step_of_exec_stop hb hrun) hfl.same (.inr ⟨rfl, rfl⟩)
        | revert out =>
          have hxh := (exitOf_of_exec hbh hrunh).2 out rfl
          obtain ⟨-, rfl, rfl⟩ := (exit_zero hxh).unique hex
          exact Halts.of_step (step_of_exec_revert hb hrun) hfl.same (.inr ⟨rfl, rfl⟩)
        | call req =>
          have hp : precompileOf ml'.precompiles req.msg ≠ none := hpre req rfl
          have hstepl : step ml = .running (launchCall ml' req) := by
            rw [step_eq_of_code hb, hrun]
          have hsteph : step (reframe k ps ml) = .running (reframe k ps (launchCall ml' req)) := by
            rw [step_eq_of_code hbh, hrunh]
            dsimp only
            rw [launchCall_reframe hp]
          have hsl : SameFrame ml (launchCall ml' req) := hfl.same.trans (sameFrame_launchCall hp)
          have hst := sameFrame_reframe hsl k ps
          obtain ⟨hN, hex'⟩ := hex.next hsteph hst
          exact Halts.of_steps (Steps.of_step hstepl hsl)
            (ih (N - 1) (by omega) _ k ps mfh oh hex' (shift _ hN hsteph hst))
        | create msg => exact absurd rfl (hnc msg)

end Verified.Solmate.ERC20.Spec
