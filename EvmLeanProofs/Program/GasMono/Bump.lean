import EvmLeanProofs.Program.GasMono.Exit
import EvmLeanProofs.Program.NestedExtraGas

/-!
# Gas monotonicity: frames with more gas

The lockstep simulation relates a low-gas machine `m` to the high-gas machine
`bump d x ps m` (`NestedExtraGas`): the executing frame has `d` more gas, its message records
gas `x`, and the suspended parents `ps` are arbitrary; **every other field is equal**. This file
proves that the relation survives the transitions around a call:

* `pushCall_bump`: a child started with more gas (`c ≤ c'`) is the bump of the low child,
  with the high caller's frame as parent.
* `resumeAfter_bump`: resuming a bumped caller after a bumped child of a message call (same
  outcome) is a bump of the low resumption: the gas returned by the child only adds up.
* `PreMono`, `preMono_standard`: **every standard precompile is gas-monotone**: if it succeeds
  with gas `g`, it succeeds with any `g' ≥ g`, with the same output and `g' - g` more gas left
  (each precompile charges a gas-independent cost, then computes a gas-independent result).
* `launchCall_precompile_bump`: hence a precompile call that succeeds with the low gas runs
  identically with the high gas.
* `exec_gas_bump`: `GAS` from a bumped machine pushes the bumped gas (the only difference).
-/

namespace EvmLean.Program.GasMono

open Interpreter Nested

/-- The frame with `d` more gas and message gas `x`. -/
def bumpF (d x : Nat) (f : Frame) : Frame :=
  { f with gasLeft := f.gasLeft + d, msg := { f.msg with gas := x } }

theorem bump_eq (d x : Nat) (ps : List Frame) (m : Machine) :
    bump d x ps m = { m with frame := bumpF d x m.frame, parents := ps } := rfl

@[simp] theorem bump_frame (d x : Nat) (ps : List Frame) (m : Machine) :
    (bump d x ps m).frame = bumpF d x m.frame := rfl

@[simp] theorem bump_parents (d x : Nat) (ps : List Frame) (m : Machine) :
    (bump d x ps m).parents = ps := rfl

/-- Zero extra gas and the same message gas and parents: no change. -/
theorem bump_zero (m : Machine) : bump 0 m.frame.msg.gas m.parents m = m := rfl

/-- A bump of a bump. -/
theorem bump_trans (d₁ x₁ : Nat) (ps₁ : List Frame) (d₂ x₂ : Nat) (ps₂ : List Frame)
    (m : Machine) : bump d₂ x₂ ps₂ (bump d₁ x₁ ps₁ m) = bump (d₁ + d₂) x₂ ps₂ m := by
  simp only [bump, Nat.add_assoc]

/-! ## Children -/

/-- The child message with gas `c`. -/
def _root_.EvmLean.Interpreter.CallRequest.withGas (req : CallRequest) (c : Nat) : CallRequest :=
  { req with msg := { req.msg with gas := c } }

/-- The value transfer does not depend on the message gas. -/
theorem transferValue_withGas (w : World) (msg : Message) (c : Nat) :
    transferValue w { msg with gas := c } = transferValue w msg := rfl

/-- The precompile check does not depend on the message gas. -/
theorem precompileOf_withGas (pre : PrecompileImpl) (msg : Message) (c : Nat) :
    precompileOf pre { msg with gas := c } = precompileOf pre msg := rfl

/-- **A child started with more gas** is the bump of the low child. -/
theorem pushCall_bump {m : Machine} {req : CallRequest} {c' d x : Nat} {ps : List Frame}
    (hc : req.msg.gas ≤ c') :
    pushCall (bump d x ps m) (req.withGas c') =
      bump (c' - req.msg.gas) c' (bumpF d x m.frame :: ps) (pushCall m req) := by
  simp only [pushCall, bump, CallRequest.withGas, transferValue_withGas, Frame.init, bumpF,
    Machine.mk.injEq, Frame.mk.injEq, true_and, and_true]
  omega

/-- **Resuming after a child, with more gas on both sides.** -/
theorem resumeAfter_bump {p : Frame} {ps ps' psf : List Frame} {mf : Machine} {o : Outcome}
    {d dp x xp : Nat} {ko ks : Nat} (hk : mf.frame.kind = .call ko ks) :
    ∃ d', resumeAfter (bumpF dp xp p) ps' (bump d x psf mf) o =
      bump d' xp ps' (resumeAfter p ps mf o) := by
  cases o with
  | success out =>
    refine ⟨dp + d, ?_⟩
    simp only [resumeAfter, frameResult, bump, bumpF, hk, resume, ChildResult.success,
      Machine.mk.injEq, Frame.mk.injEq, true_and, and_true]
    omega
  | revert out =>
    refine ⟨dp + d, ?_⟩
    simp only [resumeAfter, frameResult, bump, bumpF, hk, resume, ChildResult.success,
      Machine.mk.injEq, Frame.mk.injEq, true_and, and_true]
    omega
  | halt e =>
    refine ⟨dp, ?_⟩
    simp only [resumeAfter, frameResult, bump, bumpF, hk, resume, ChildResult.success,
      Machine.mk.injEq, Frame.mk.injEq, true_and, and_true]
    omega

/-! ## Precompiles -/

/-- A precompile function is gas-monotone: success with gas `g` implies success with any
`g' ≥ g`, the same output, and `g' - g` more gas left. -/
def PreMonoFn (run : ByteArray → Nat → Precompile.Result) : Prop :=
  ∀ input g g', g ≤ g' → (run input g).success = true →
    (run input g').success = true ∧ (run input g').output = (run input g).output ∧
    (run input g').gasLeft = (run input g).gasLeft + (g' - g)

/-- The precompiles of a machine are gas-monotone. -/
def PreMono (pre : PrecompileImpl) : Prop := ∀ a, PreMonoFn (pre.run a)

set_option maxHeartbeats 2000000 in
/-- **Every standard precompile is gas-monotone.** -/
theorem runKind_mono (c : Crypto) (fork : Fork) (k : Precompile.Kind) :
    PreMonoFn (Precompile.runKind c fork k) := by
  intro input g g' hle hs
  cases k <;> simp only [Precompile.runKind, Precompile.ecrecover, Precompile.sha256,
      Precompile.ripemd160, Precompile.identity, Precompile.modexp, Precompile.ecAdd,
      Precompile.ecMul, Precompile.ecPairing, Precompile.blake2f, Precompile.pointEvaluation,
      Precompile.blsFixed, Precompile.blsMsm, Precompile.blsPairing, Precompile.p256Verify]
      at hs ⊢ <;>
    (repeat' (first | (split at hs) | split)) <;> simp_all [Precompile.fail] <;> omega

/-- The standard precompiles of a context are gas-monotone. -/
theorem preMono_standard (ctx : Context) : PreMono (PrecompileImpl.standard ctx) := by
  intro a input g g' hle hs
  simp only [PrecompileImpl.standard, Precompile.run] at hs ⊢
  split
  · rename_i k hk
    rw [hk] at hs
    exact runKind_mono _ _ k input g g' hle hs
  · rename_i hk
    rw [hk] at hs
    simp [Precompile.fail] at hs

/-- `ECRECOVER` in particular. -/
theorem ecrecover_mono (c : Crypto) : PreMonoFn (Precompile.ecrecover c) :=
  runKind_mono c .cancun .ecrecover

/-- A precompile call from `m` (precompile `a`). -/
theorem launchCall_precompile {m : Machine} {req : CallRequest} {a : Address}
    (h : precompileOf m.precompiles req.msg = some a) :
    launchCall m req =
      resume { m with
        world := (runPrecompile m.precompiles a req.msg (.call req.retOffset req.retSize)
          (transferValue m.world req.msg) m.transient (m.world, m.transient)).2.1
        transient := (runPrecompile m.precompiles a req.msg (.call req.retOffset req.retSize)
          (transferValue m.world req.msg) m.transient (m.world, m.transient)).2.2 }
        (runPrecompile m.precompiles a req.msg (.call req.retOffset req.retSize)
          (transferValue m.world req.msg) m.transient (m.world, m.transient)).1 := by
  simp only [launchCall, h]

/-- **A precompile that succeeds with the low gas** runs identically with the high gas: the
caller resumes as a bump of the low caller. -/
theorem launchCall_precompile_bump {m : Machine} {req : CallRequest} {a : Address}
    {c' d x : Nat} {ps : List Frame} (hpm : PreMono m.precompiles)
    (h : precompileOf m.precompiles req.msg = some a) (hc : req.msg.gas ≤ c')
    (hs : (m.precompiles.run a req.msg.data req.msg.gas).success = true) :
    ∃ d', launchCall (bump d x ps m) (req.withGas c') = bump d' x ps (launchCall m req) := by
  obtain ⟨hs', ho, hg⟩ := hpm a req.msg.data req.msg.gas c' hc hs
  refine ⟨d + (c' - req.msg.gas), ?_⟩
  have h' : precompileOf (bump d x ps m).precompiles (req.withGas c').msg = some a := h
  rw [launchCall_precompile h', launchCall_precompile h]
  simp only [runPrecompile, bump, CallRequest.withGas, transferValue_withGas] at hs' ho hg ⊢
  simp only [hs, hs', ↓reduceIte, ho, resume, Substate.ofMessage, ChildResult.success,
    Machine.mk.injEq, Frame.mk.injEq, true_and, and_true, hg]
  omega

/-- A failed precompile call: the caller resumes with `0` pushed and the pc advanced. -/
theorem launchCall_precompile_fail {m : Machine} {req : CallRequest} {a : Address}
    (h : precompileOf m.precompiles req.msg = some a)
    (hs : (m.precompiles.run a req.msg.data req.msg.gas).success = false) :
    (launchCall m req).frame.stack = 0 :: m.frame.stack ∧
      (launchCall m req).frame.pc = m.frame.pc + 1 ∧
      SameFrame m (launchCall m req) := by
  rw [launchCall_precompile h]
  simp only [runPrecompile, hs, Bool.false_eq_true, ↓reduceIte]
  refine ⟨?_, rfl, SameFrame.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (sameFrame_resume _ _)⟩
  simp [resume, ChildResult.success]

/-! ## `GAS` -/

/-- The machine with the top of the stack replaced by `b`. -/
def withTop (b : Word) (m : Machine) : Machine :=
  { m with frame := { m.frame with stack := b :: m.frame.stack.tail } }

/-- `GAS` from a bumped machine, as a weakest precondition. -/
theorem exec_gas_bump_wp (m : Machine) (d x : Nat) (ps : List Frame) :
    Wp (exec .gas) (fun a m' => a = .next ∧
      m'.frame.stack = BitVec.ofNat 256 (m.frame.gasLeft - Gas.base) :: m.frame.stack ∧
      m'.frame.gasLeft = m.frame.gasLeft - Gas.base ∧
      Twp (exec .gas) (fun a' m'' => a' = .next ∧
        m'' = withTop (BitVec.ofNat 256 (m.frame.gasLeft + d - Gas.base)) (bump d x ps m'))
        (bump d x ps m)) m := by
  simp [exec, pushValue, bump, withTop, Interpreter.ofNat]
  intros
  omega

/-- **`GAS` from a bumped machine** pushes the bumped gas; nothing else differs. -/
theorem exec_gas_bump {m m' : Machine} {a : Action} (h : (exec .gas).run m = .ok (a, m'))
    (d x : Nat) (ps : List Frame) :
    a = .next ∧ m'.frame.stack = BitVec.ofNat 256 (m.frame.gasLeft - Gas.base) :: m.frame.stack ∧
      m'.frame.gasLeft = m.frame.gasLeft - Gas.base ∧
      (exec .gas).run (bump d x ps m) =
        .ok (.next, withTop (BitVec.ofNat 256 (m.frame.gasLeft + d - Gas.base))
          (bump d x ps m')) := by
  obtain ⟨h1, h2, h3, h4⟩ := (exec_gas_bump_wp m d x ps).of_run h
  refine ⟨h1, h2, h3, ?_⟩
  unfold Twp at h4
  split at h4
  · rename_i a' m'' he
    obtain ⟨rfl, rfl⟩ := h4
    exact he
  · exact h4.elim

end EvmLean.Program.GasMono
