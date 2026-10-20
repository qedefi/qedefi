import EvmLogic.Program.Nested.Frame

/-!
# One step of the machine: frame condition and gas

Lifts the per-instruction frame condition (`exec_frame`) to `step`:

* `step_cases`: a step either stays in the frame (`InstrFrame`), ends the frame from a machine
  related by `InstrFrame` (`finishFrame`), or pushes a child described by `CallOk` /
  `CreateOk`;
* `frameResult_world`: the world a finished frame hands over is its current world, the
  current world with the created code deposited (creations), or its snapshot;
* `step_gas`, `stepN_gas`: the total gas of the frame stack (`gasSum`) never increases, for
  every machine whose precompiles return at most the gas they are given (`PrecompilesOk`; the
  standard ones do, `precompilesOk_standard`).
-/

namespace EvmLogic.Program.Nested
open EvmLean

open EvmLean.Interpreter

/-! ## Precompiles -/

/-- Every standard precompile returns at most the gas it was given. -/
theorem precompile_gasLeft_le (crypto : Crypto) (fork : Fork) (a : Address) (input : ByteArray)
    (gas : Nat) : (Precompile.run crypto fork a input gas).gasLeft ≤ gas := by
  unfold Precompile.run
  split
  · rename_i k _
    cases k <;> simp only [Precompile.runKind, Precompile.ecrecover, Precompile.sha256,
      Precompile.ripemd160, Precompile.identity, Precompile.modexp, Precompile.ecAdd,
      Precompile.ecMul, Precompile.ecPairing, Precompile.blake2f, Precompile.pointEvaluation,
      Precompile.blsFixed, Precompile.blsMsm, Precompile.blsPairing, Precompile.p256Verify] <;>
      repeat' (first | split | (simp only [Precompile.fail]; omega) | omega)
  · simp [Precompile.fail]

/-- The precompiles of a machine return at most the gas they are given. -/
def PrecompilesOk (pre : PrecompileImpl) : Prop := ∀ a d g, (pre.run a d g).gasLeft ≤ g

theorem precompilesOk_standard (ctx : Context) : PrecompilesOk (PrecompileImpl.standard ctx) :=
  fun a d g => precompile_gasLeft_le ctx.crypto ctx.fork a d g

/-! ## Gas of the frame stack -/

/-- The gas held by all frames of the stack. -/
def gasSum (m : Machine) : Nat := m.frame.gasLeft + (m.parents.map Frame.gasLeft).sum

/-- The gas of a step result (a finished message: its gas left). -/
def resultGas : StepResult → Nat
  | .running m => gasSum m
  | .done r => r.gasLeft

/-- Code deposit leaves at most the gas it was given. -/
theorem depositCode_le {fork : Fork} {g g' : Nat} {out : ByteArray}
    (h : depositCode fork g out = .ok g') : g' ≤ g := by
  unfold depositCode at h
  dsimp only at h
  by_cases h1 : out[0]? = some 0xef
  · simp [h1] at h
  · by_cases h2 : g < Gas.codeDepositCost out.size
    · simp [h1, h2] at h
    · by_cases h3 : out.size > Gas.maxCodeSize fork
      · simp [h1, h2, h3] at h
      · simp only [h1, h2, h3, ite_false, Except.ok.injEq] at h
        omega

/-- A finished frame hands over at most its gas. -/
theorem frameResult_gasLeft_le (m : Machine) (o : Outcome) :
    (frameResult m o).1.gasLeft ≤ m.frame.gasLeft := by
  cases o with
  | success out =>
    cases hk : m.frame.kind with
    | call a b => simp [frameResult, hk]
    | create =>
      cases hd : depositCode m.ctx.fork m.frame.gasLeft out with
      | ok g => simp [frameResult, hk, hd]; exact depositCode_le hd
      | error e => simp [frameResult, hk, hd]
  | revert out => simp [frameResult]
  | halt e => simp [frameResult]

/-- What a finished frame hands over: its world, its world with deposited code (a successful
creation), or its rollback snapshot. -/
theorem frameResult_world (m : Machine) (o : Outcome) :
    (frameResult m o).2.1 = m.world ∨
      (m.frame.kind = .create ∧ ∃ out, (frameResult m o).2.1 =
        setCode m.world m.frame.msg.currentTarget out) ∨
      (frameResult m o).2.1 = m.frame.snapshot.1 := by
  cases o with
  | success out =>
    cases hk : m.frame.kind with
    | call a b => simp [frameResult, hk]
    | create =>
      cases hd : depositCode m.ctx.fork m.frame.gasLeft out with
      | ok g => right; left; exact ⟨rfl, out, by simp [frameResult, hk, hd]⟩
      | error e => simp [frameResult, hk, hd]
  | revert out => simp [frameResult]
  | halt e => simp [frameResult]

@[simp] theorem resume_world (M : Machine) (r : ChildResult) : (resume M r).world = M.world := rfl
@[simp] theorem resume_parents (M : Machine) (r : ChildResult) :
    (resume M r).parents = M.parents := rfl
@[simp] theorem resume_gasLeft (M : Machine) (r : ChildResult) :
    (resume M r).frame.gasLeft = M.frame.gasLeft + r.gasLeft := rfl
@[simp] theorem resume_createdAccounts (M : Machine) (r : ChildResult) :
    (resume M r).createdAccounts = M.createdAccounts := rfl

/-- `finishFrame` does not increase the total gas. -/
theorem finishFrame_gas (m : Machine) (o : Outcome) :
    resultGas (finishFrame m o) ≤ gasSum m := by
  rw [finishFrame_eq]
  have h := frameResult_gasLeft_le m o
  cases hp : m.parents with
  | nil =>
    simp only [resultGas, gasSum, hp, List.map_nil, List.sum_nil, Nat.add_zero]
    unfold topLevelResult
    split <;> exact h
  | cons p ps =>
    simp only [resultGas, gasSum, resumeAfter, resume_gasLeft, resume_parents, hp, List.map_cons,
      List.sum_cons]
    omega

/-! ## The shape of a step -/

/-- **How a step goes.** It ends the frame, stays in it, or pushes a child, and in each case
the instruction's frame condition holds. -/
theorem step_cases (m : Machine) :
    (∃ m' o, step m = finishFrame m' o ∧ InstrFrame m m') ∨
    (∃ m', step m = .running m' ∧ InstrFrame m m') ∨
    (∃ m' req, step m = .running (launchCall m' req) ∧ InstrFrame m m' ∧ CallOk m m' req) ∨
    (∃ m' msg, step m = .running (launchCreate m' msg) ∧ InstrFrame m m' ∧ CreateOk m m' msg) := by
  unfold step
  dsimp only
  split
  · rename_i hpc
    have hw := exec_frame (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m
    split
    · exact .inl ⟨m, _, rfl, .refl m⟩
    · rename_i m' h
      exact .inr (.inl ⟨m', rfl, (hw.of_run h).1⟩)
    · rename_i out m' h
      exact .inl ⟨m', _, rfl, (hw.of_run h).1⟩
    · rename_i out m' h
      exact .inl ⟨m', _, rfl, (hw.of_run h).1⟩
    · rename_i req m' h
      exact .inr (.inr (.inl ⟨m', req, rfl, (hw.of_run h).1, (hw.of_run h).2⟩))
    · rename_i msg m' h
      exact .inr (.inr (.inr ⟨m', msg, rfl, (hw.of_run h).1, (hw.of_run h).2⟩))
  · exact .inl ⟨m, _, rfl, .refl m⟩

/-- The machine after a call pushed its child frame. -/
def pushCall (m : Machine) (req : CallRequest) : Machine :=
  { m with
    world := transferValue m.world req.msg
    frame := Frame.init req.msg (.call req.retOffset req.retSize) (m.world, m.transient)
    parents := m.frame :: m.parents }

/-- A requested call either runs a precompile to completion (the world afterwards is the
world after the value transfer or the snapshot) or pushes the child frame. -/
theorem launchCall_cases (m : Machine) (req : CallRequest) :
    (∃ r w t, launchCall m req = resume { m with world := w, transient := t } r ∧
      (w = transferValue m.world req.msg ∨ w = m.world) ∧
      (PrecompilesOk m.precompiles → r.gasLeft ≤ req.msg.gas)) ∨
    launchCall m req = pushCall m req := by
  unfold launchCall
  dsimp only
  split
  · rename_i a _
    left
    unfold runPrecompile
    dsimp only
    split
    · exact ⟨_, _, _, rfl, .inl rfl, fun h => h a _ _⟩
    · exact ⟨_, _, _, rfl, .inr rfl, fun _ => Nat.zero_le _⟩
  · right; rfl

/-- **Gas never increases** over one step. -/
theorem step_gas {m : Machine} (hpre : PrecompilesOk m.precompiles) :
    resultGas (step m) ≤ gasSum m := by
  rcases step_cases m with ⟨m', o, h, hf⟩ | ⟨m', h, hf⟩ | ⟨m', req, h, hf, hc⟩ |
    ⟨m', msg, h, hf, hc⟩
  · rw [h]
    refine Nat.le_trans (finishFrame_gas m' o) ?_
    simp only [gasSum, hf.same.parents]
    have := hf.gas; omega
  · rw [h]
    simp only [resultGas, gasSum, hf.same.parents]
    have := hf.gas; omega
  · rw [h]
    have hg := hc.gas
    have hpre' : PrecompilesOk m'.precompiles := by rw [hf.same.precompiles]; exact hpre
    rcases launchCall_cases m' req with ⟨r, w, t, he, -, hr⟩ | he <;> rw [he]
    · have := hr hpre'
      simp only [resultGas, gasSum, resume_gasLeft, resume_parents, hf.same.parents]
      omega
    · simp only [resultGas, gasSum, pushCall, Frame.init, List.map_cons, List.sum_cons,
        hf.same.parents]
      omega
  · rw [h]
    have hg := hc.gas
    simp only [launchCreate, resultGas, gasSum, Frame.init, List.map_cons, List.sum_cons,
      hf.same.parents]
    omega

/-- The constants of the machine never change. -/
theorem step_consts {m m' : Machine} (h : step m = .running m') :
    m'.ctx = m.ctx ∧ m'.precompiles = m.precompiles := by
  rcases step_cases m with ⟨m₁, o, h', hf⟩ | ⟨m₁, h', hf⟩ | ⟨m₁, req, h', hf, -⟩ |
    ⟨m₁, msg, h', hf, -⟩
  · rw [h', finishFrame_eq] at h
    split at h
    · cases h
    · cases h; exact ⟨hf.same.ctx, hf.same.precompiles⟩
  · rw [h'] at h; cases h; exact ⟨hf.same.ctx, hf.same.precompiles⟩
  · rw [h'] at h; cases h
    rcases launchCall_cases m₁ req with ⟨r, w, t, he, -, -⟩ | he <;> rw [he] <;>
      exact ⟨hf.same.ctx, hf.same.precompiles⟩
  · rw [h'] at h; cases h; exact ⟨hf.same.ctx, hf.same.precompiles⟩

/-- Over any number of steps, gas never increases and the constants stay. -/
theorem stepN_gas {m : Machine} (hpre : PrecompilesOk m.precompiles) :
    ∀ n, resultGas (stepN n m) ≤ gasSum m := by
  intro n
  induction n generalizing m with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [stepN]
    split
    · rename_i r h
      have := step_gas hpre; rw [h] at this; exact this
    · rename_i m' h
      have h1 := step_gas hpre; rw [h] at h1
      have hc := step_consts h
      exact Nat.le_trans (ih (by rw [hc.2]; exact hpre)) h1

end EvmLogic.Program.Nested
