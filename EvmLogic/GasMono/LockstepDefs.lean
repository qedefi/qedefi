import EvmLogic.GasMono.CallStep
import EvmLogic.GasMono.Pc

/-!
# Gas monotonicity: definitions of the lockstep

* `Failed o`: not a successful outcome.
* `Post mfh oh mfl ol`: how the real end `(mfl, ol)` of a low-gas frame relates to the real end
  `(mfh, oh)` of the same frame with more gas: the low frame failed, or it ended the same way
  with a machine of which the high one is a bump (same world, transient storage, substate,
  output; more gas left).
* `MonoFrom S`: **the frames whose high-gas version satisfies `S` are gas-monotone**: for every
  low-gas version (`BumpOf`: the same machine with less frame gas, any message gas, any
  parents), the low frame ends, and `Post` holds of its end and the high frame's exit. This is
  compositional: a frame whose children are gas-monotone is gas-monotone
  (`GasMono/Lockstep.lean`).
* `CallsTo S' mh N`: every child the high frame starts before its exit at step `N` is a
  precompile call or a frame satisfying `S'`.
* `Rel code n ml mh`: the lockstep invariant.
-/

namespace EvmLean.Program.GasMono

open Interpreter Nested

/-- Not a successful outcome. -/
def Failed (o : Outcome) : Prop := ∀ out, o ≠ .success out

/-- **The end of a low-gas frame against the end of the high-gas frame**: the low frame failed,
or it ended with the same outcome from a machine that the high one bumps. -/
def Post (mfh : Machine) (oh : Outcome) (mfl : Machine) (ol : Outcome) : Prop :=
  Failed ol ∨ (ol = oh ∧ ∃ d x ps, mfh = bump d x ps mfl)

/-- **Gas-monotone frames.** Every high-gas frame satisfying `S`, against any version of it with
less gas: the low frame ends, failing or as the high frame does. -/
def MonoFrom (S : Machine → Prop) : Prop :=
  ∀ ml mh N mfh oh, S mh → BumpOf mh.frame.msg.gas mh.parents ml mh → Exit mh N mfh oh →
    Halts ml (Post mfh oh)

/-- The children the high frame `mh` starts before its exit at step `N` are precompile calls or
frames satisfying `S'`. -/
def CallsTo (S' : Machine → Prop) (mh : Machine) (N : Nat) : Prop :=
  ∀ k < N, ∀ m' b req m'', stepN k mh = .running m' → SameFrame mh m' →
    m'.frame.code[m'.frame.pc]? = some b →
    (exec (Opcode.decode m'.ctx.fork b)).run m' = .ok (.call req, m'') →
    precompileOf m''.precompiles req.msg = none → S' (pushCall m'' req)

/-- **The lockstep invariant**: the high machine bumps the low one, which runs `code` at a
boundary of the region `[0, n)`; the high gas fits a word; the precompiles return at most their
gas and are gas-monotone. -/
structure Rel (code : ByteArray) (n : Nat) (ml mh : Machine) : Prop where
  /-- More gas, otherwise equal. -/
  bump : BumpOf mh.frame.msg.gas mh.parents ml mh
  /-- The code. -/
  codeEq : ml.frame.code = code
  /-- Its jump table. -/
  jd : ml.frame.jumpDests = validJumpDests code
  /-- A boundary of the region. -/
  pc : PcOk code n ml.frame.pc
  /-- The high gas fits a word (so `GAS` pushes it exactly). -/
  gasLt : mh.frame.gasLeft < 2 ^ 256
  /-- Precompiles return at most their gas. -/
  preOk : PrecompilesOk mh.precompiles
  /-- Precompiles are gas-monotone. -/
  preMono : PreMono mh.precompiles

/-! ## Basic facts -/

/-- A bump is a `BumpOf`. -/
theorem bumpOf_bump (d x : Nat) (ps : List Frame) (m : Machine) :
    BumpOf x ps m (bump d x ps m) :=
  ⟨by simp [bump], by simp only [bump_frame, bumpF, Nat.add_sub_cancel_left]⟩

/-- `BumpOf` fixes the message gas and the parents. -/
theorem BumpOf.msgGas {x : Nat} {ps : List Frame} {m m' : Machine} (h : BumpOf x ps m m') :
    m'.frame.msg.gas = x ∧ m'.parents = ps := by
  rw [h.2]; exact ⟨rfl, rfl⟩

/-- The fields a bump keeps. -/
theorem BumpOf.fields {x : Nat} {ps : List Frame} {m m' : Machine} (h : BumpOf x ps m m') :
    m'.ctx = m.ctx ∧ m'.precompiles = m.precompiles ∧ m'.world = m.world ∧
      m'.transient = m.transient ∧ m'.frame.code = m.frame.code ∧ m'.frame.pc = m.frame.pc ∧
      m'.frame.stack = m.frame.stack ∧ m'.frame.jumpDests = m.frame.jumpDests := by
  rw [h.2]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Bumps of machines in the same frame are in the same frame. -/
theorem sameFrame_bump {m m' : Machine} (h : SameFrame m m') (d d' x : Nat) (ps : List Frame) :
    SameFrame (bump d x ps m) (bump d' x ps m') :=
  ⟨h.ctx, h.precompiles, h.originalWorld, rfl, by simp [bump, h.msg], h.code,
    h.jumpDests, h.kind, h.snapshot⟩

/-- `withTop` with the current top is the identity. -/
theorem withTop_self {m : Machine} {a : Word} {s : List Word} (h : m.frame.stack = a :: s) :
    withTop a m = m := by
  simp only [withTop, h, List.tail_cons]
  rw [← h]

/-- The children called by a frame, seen from a later machine of the frame. -/
theorem CallsTo.shift {S' : Machine → Prop} {mh mh' : Machine} {N j : Nat}
    (h : CallsTo S' mh N) (hj : stepN j mh = .running mh') (hs : SameFrame mh mh') :
    CallsTo S' mh' (N - j) := by
  intro k hk m' b req m'' hk' hs' hb hx hp
  exact h (j + k) (by omega) m' b req m'' (by rw [stepN_add_of_running hj]; exact hk')
    (hs.trans hs') hb hx hp

/-- The frame's gas never exceeds its gas at an earlier machine of the frame. -/
theorem gas_le_of_stepN {m m' : Machine} {j : Nat} (hpre : PrecompilesOk m.precompiles)
    (hj : stepN j m = .running m') (hp : m'.parents = m.parents) :
    m'.frame.gasLeft ≤ m.frame.gasLeft := by
  have := stepN_gas hpre j
  rw [hj] at this
  simp only [resultGas, gasSum, hp] at this
  omega

/-- After a failed child of a message call, the caller resumes with `0` on the stack. -/
theorem resumeAfter_failed {p : Frame} {ps : List Frame} {mf : Machine} {o : Outcome}
    {ko ks : Nat} (hk : mf.frame.kind = .call ko ks) (hf : Failed o) :
    (resumeAfter p ps mf o).frame.stack = 0 :: p.stack ∧
      (resumeAfter p ps mf o).frame.pc = p.pc + 1 ∧
      (resumeAfter p ps mf o).frame.code = p.code := by
  cases o with
  | success out => exact absurd rfl (hf out)
  | revert out => rw [resumeAfter_revert hk]; exact ⟨rfl, rfl, rfl⟩
  | halt e => rw [resumeAfter_halt hk]; exact ⟨rfl, rfl, rfl⟩

/-- The exit of a `STOP`/`RETURN`/`REVERT` step. -/
theorem exitOf_of_exec {m m' : Machine} {b : UInt8} {a : Action}
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hexec : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m')) :
    (∀ out, a = .stop out → exitOf m = some (m', .success out)) ∧
      (∀ out, a = .revert out → exitOf m = some (m', .revert out)) := by
  rw [getElem?_eq_some_iff] at hcode
  obtain ⟨hlt, hb⟩ := hcode
  unfold exitOf
  simp only [hlt, ↓reduceDIte, hb, hexec]
  refine ⟨fun out h => by subst h; rfl, fun out h => by subst h; rfl⟩

/-- An exit right away. -/
theorem exit_zero {m mf : Machine} {o : Outcome} (h : exitOf m = some (mf, o)) :
    Exit m 0 mf o :=
  ⟨fun k hk => by rw [Nat.le_zero.1 hk]; exact ⟨m, rfl, .of_same (.refl m)⟩,
    m, rfl, .refl m, h⟩

/-- The pc of a frame at a region boundary is inside the code. -/
theorem code_getElem? {code : ByteArray} {n : Nat} {m : Machine} (hc : m.frame.code = code)
    (hpc : PcOk code n m.frame.pc) :
    m.frame.code[m.frame.pc]? = some (Bytes.getD code m.frame.pc) := by
  have hlt := hpc.lt_size
  subst hc
  rw [getElem?_eq_some_iff]
  exact ⟨hlt, (getD_eq_getElem hlt).symm⟩

/-- The region starts at a boundary. -/
theorem pcOk_zero {code : ByteArray} {n : Nat} (h : RegionOk code n) : PcOk code n 0 := by
  have hs := lt_size_of_mem_boundaries h.2.1
  refine ⟨?_, h.1⟩
  unfold boundaries
  obtain ⟨k, hk⟩ : ∃ k, code.size = k + 1 := ⟨code.size - 1, by omega⟩
  rw [hk, boundariesFrom_succ]
  simp only [show 0 < code.size by omega, ↓reduceIte]
  exact List.mem_cons_self

end EvmLean.Program.GasMono
