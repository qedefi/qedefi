import EvmLogic.GasMono.CallStep
import EvmLogic.GasMono.Pc

/-!
# Gas monotonicity: the lockstep theorem

`monoFrom_of_code`: a frame running code that satisfies `CodeOk`, whose children are precompile
calls or gas-monotone frames, is gas-monotone (`MonoFrom`): with less gas it fails or ends exactly
as with more (`Post`). The proof runs both frames in lockstep along the high frame's `Exit`, with
invariant `Rel`. `halts_world_of_mono` transfers frame summaries to any lower gas. See
`docs/proving.md` §6.
-/

section

namespace EvmLogic.GasMono
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested

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
  bump : BumpOf mh.frame.msg.gas mh.parents ml mh
  codeEq : ml.frame.code = code
  jd : ml.frame.jumpDests = validJumpDests code
  pc : PcOk code n ml.frame.pc
  /-- The high gas fits a word (so `GAS` pushes it exactly). -/
  gasLt : mh.frame.gasLeft < 2 ^ 256
  preOk : PrecompilesOk mh.precompiles
  preMono : PreMono mh.precompiles

/-! ## Basic facts -/

theorem bumpOf_bump (d x : Nat) (ps : List Frame) (m : Machine) :
    BumpOf x ps m (bump d x ps m) :=
  ⟨by simp [bump], by simp only [bump_frame, bumpF, Nat.add_sub_cancel_left]⟩

theorem BumpOf.msgGas {x : Nat} {ps : List Frame} {m m' : Machine} (h : BumpOf x ps m m') :
    m'.frame.msg.gas = x ∧ m'.parents = ps := by
  rw [h.2]; exact ⟨rfl, rfl⟩

theorem BumpOf.fields {x : Nat} {ps : List Frame} {m m' : Machine} (h : BumpOf x ps m m') :
    m'.ctx = m.ctx ∧ m'.precompiles = m.precompiles ∧ m'.world = m.world ∧
      m'.transient = m.transient ∧ m'.frame.code = m.frame.code ∧ m'.frame.pc = m.frame.pc ∧
      m'.frame.stack = m.frame.stack ∧ m'.frame.jumpDests = m.frame.jumpDests := by
  rw [h.2]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sameFrame_bump {m m' : Machine} (h : SameFrame m m') (d d' x : Nat) (ps : List Frame) :
    SameFrame (bump d x ps m) (bump d' x ps m') :=
  ⟨h.ctx, h.precompiles, h.originalWorld, rfl, by simp [bump, h.msg], h.code,
    h.jumpDests, h.kind, h.snapshot⟩

theorem withTop_self {m : Machine} {a : Word} {s : List Word} (h : m.frame.stack = a :: s) :
    withTop a m = m := by
  simp only [withTop, h, List.tail_cons]
  rw [← h]

theorem CallsTo.shift {S' : Machine → Prop} {mh mh' : Machine} {N j : Nat}
    (h : CallsTo S' mh N) (hj : stepN j mh = .running mh') (hs : SameFrame mh mh') :
    CallsTo S' mh' (N - j) := by
  intro k hk m' b req m'' hk' hs' hb hx hp
  exact h (j + k) (by omega) m' b req m'' (by rw [stepN_add_of_running hj]; exact hk')
    (hs.trans hs') hb hx hp

theorem gas_le_of_stepN {m m' : Machine} {j : Nat} (hpre : PrecompilesOk m.precompiles)
    (hj : stepN j m = .running m') (hp : m'.parents = m.parents) :
    m'.frame.gasLeft ≤ m.frame.gasLeft := by
  have := stepN_gas hpre j
  rw [hj] at this
  simp only [resultGas, gasSum, hp] at this
  omega

theorem resumeAfter_failed {p : Frame} {ps : List Frame} {mf : Machine} {o : Outcome}
    {ko ks : Nat} (hk : mf.frame.kind = .call ko ks) (hf : Failed o) :
    (resumeAfter p ps mf o).frame.stack = 0 :: p.stack ∧
      (resumeAfter p ps mf o).frame.pc = p.pc + 1 ∧
      (resumeAfter p ps mf o).frame.code = p.code := by
  cases o with
  | success out => exact absurd rfl (hf out)
  | revert out => rw [resumeAfter_revert hk]; exact ⟨rfl, rfl, rfl⟩
  | halt e => rw [resumeAfter_halt hk]; exact ⟨rfl, rfl, rfl⟩

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

theorem exit_zero {m mf : Machine} {o : Outcome} (h : exitOf m = some (mf, o)) :
    Exit m 0 mf o :=
  ⟨fun k hk => by rw [Nat.le_zero.1 hk]; exact ⟨m, rfl, .of_same (.refl m)⟩,
    m, rfl, .refl m, h⟩

theorem code_getElem? {code : ByteArray} {n : Nat} {m : Machine} (hc : m.frame.code = code)
    (hpc : PcOk code n m.frame.pc) :
    m.frame.code[m.frame.pc]? = some (Bytes.getD code m.frame.pc) := by
  have hlt := hpc.lt_size
  subst hc
  rw [getElem?_eq_some_iff]
  exact ⟨hlt, (getD_eq_getElem hlt).symm⟩

theorem pcOk_zero {code : ByteArray} {n : Nat} (h : RegionOk code n) : PcOk code n 0 := by
  have hs := lt_size_of_mem_boundaries h.2.1
  refine ⟨?_, h.1⟩
  unfold boundaries
  obtain ⟨k, hk⟩ : ∃ k, code.size = k + 1 := ⟨code.size - 1, by omega⟩
  rw [hk, boundariesFrom_succ]
  simp only [show 0 < code.size by omega, ↓reduceIte]
  exact List.mem_cons_self

end EvmLogic.GasMono

end

section

/-!
## The lockstep theorem

Cases along the high run: an instruction not reading the gas (`exec_bump`); `GAS` and the call it
feeds; a `CALL`/`STATICCALL`/`DELEGATECALL` (`call_case`) that is not made, runs a precompile, or
starts a child (`Exit.split`, `MonoFrom S'`, `resumeAfter_bump`). A failed low call makes the low
frame fail (`FailureReverts`).
-/

namespace EvmLogic.GasMono
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested

/-- **The code-level conditions** of the lockstep, for the region `[0, n)`. -/
structure CodeOk (code : ByteArray) (n : Nat) : Prop where
  /-- Every `GAS` feeds a `CALL`/`STATICCALL`. -/
  feed : GasFeedsCall code n
  /-- Execution stays in the region. -/
  region : RegionOk code n
  /-- Every `CALL`/`CREATE`-family byte follows a `GAS`. -/
  fed : CallsFed code n
  /-- After every call, failure makes the frame fail. -/
  reverts : ∀ p ∈ callReturnPoints code n, FailureReverts code p

/-- The induction hypothesis of the lockstep, below `N`. -/
def LockIH (code : ByteArray) (n : Nat) (S' : Machine → Prop) (N : Nat) : Prop :=
  ∀ N' < N, ∀ ml mh mfh oh, Rel code n ml mh → Exit mh N' mfh oh → CallsTo S' mh N' →
    Halts ml (Post mfh oh)

theorem pcOk_of_exec' {code : ByteArray} {n : Nat} (hreg : RegionOk code n) {m m' : Machine}
    {b : UInt8} (hc : m.frame.code = code) (hj : m.frame.jumpDests = validJumpDests code)
    (hpc : PcOk code n m.frame.pc) (hb : m.frame.code[m.frame.pc]? = some b)
    (h : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m')) :
    PcOk code n m'.frame.pc := by
  rw [getElem?_eq_some_iff] at hb
  obtain ⟨hlt, hb⟩ := hb
  exact pcOk_of_exec hreg hc hj hpc hlt (by rw [hb]; exact h)

theorem halts_post_of_failed {m : Machine} {mfh : Machine} {oh : Outcome}
    (h : Halts m (fun _ o => ∀ out, o ≠ .success out)) : Halts m (Post mfh oh) :=
  h.mono fun _ _ _ hf => .inl hf

theorem halts_of_failedCall {code : ByteArray} {n : Nat} (hc : CodeOk code n) {R : Machine}
    {mfh : Machine} {oh : Outcome} (hcode : R.frame.code = code)
    (hret : R.frame.pc ∈ callReturnPoints code n) (hs : R.frame.stack.head? = some 0) :
    Halts R (Post mfh oh) :=
  halts_post_of_failed (hc.reverts _ hret R hcode rfl hs)

theorem decode_call (fork : Fork) {b : UInt8} (h : b = 0xf1 ∨ b = 0xfa ∨ b = 0xf4) :
    Opcode.decode fork b = .call ∨ Opcode.decode fork b = .staticcall ∨
      Opcode.decode fork b = .delegatecall := by
  rcases h with rfl | rfl | rfl <;> cases fork <;> simp [Opcode.decode]

theorem launchCall_none {m : Machine} {req : CallRequest}
    (h : precompileOf m.precompiles req.msg = none) : launchCall m req = pushCall m req := by
  simp only [launchCall, h, pushCall]

theorem sameFrame_withTop_bump {ml R : Machine} (h : SameFrame ml R) (b : Word) (d d' x : Nat)
    (ps : List Frame) : SameFrame (withTop b (bump d x ps ml)) (bump d' x ps R) :=
  ⟨h.ctx, h.precompiles, h.originalWorld, rfl, by simp [bump, withTop, h.msg], h.code,
    h.jumpDests, h.kind, h.snapshot⟩

theorem exec_call_mono {fork : Fork} {byte : UInt8}
    (hbyte : byte = 0xf1 ∨ byte = 0xfa ∨ byte = 0xf4)
    (m : Machine) (b : Word) (d x : Nat) (ps : List Frame) (a : Word) (s : List Word)
    (hs : m.frame.stack = a :: s) (hab : a.toNat ≤ b.toNat) (hbd : b.toNat ≤ a.toNat + d) :
    Wp (exec (Opcode.decode fork byte)) (fun act m' => Twp (exec (Opcode.decode fork byte))
      (fun act' m'' => CallRel x ps act act' m' m'') (withTop b (bump d x ps m))) m := by
  rcases decode_call fork hbyte with h | h | h <;> rw [h]
  · exact execCall_call_mono m b d x ps a s hs hab hbd
  · exact execCall_staticcall_mono m b d x ps a s hs hab hbd
  · exact execCall_delegatecall_mono m b d x ps a s hs hab hbd

theorem sameFrame_resumeAfter {ml ml' mfl : Machine} {req : CallRequest} {o : Outcome}
    (hf : SameFrame ml ml') (hs : SameFrame (pushCall ml' req) mfl) :
    SameFrame ml (resumeAfter ml'.frame ml'.parents mfl o) := by
  refine SameFrame.trans ?_ (sameFrame_resume _ _)
  exact ⟨hs.ctx.trans hf.ctx, hs.precompiles.trans hf.precompiles,
    hs.originalWorld.trans hf.originalWorld, hf.parents, hf.msg, hf.code, hf.jumpDests, hf.kind,
    hf.snapshot⟩

set_option maxHeartbeats 1000000 in
/-- **The call macro-step.** From a low machine at a `CALL`/`STATICCALL`/`DELEGATECALL` and the
high machine with `d` more gas and a requested gas `b` with `a ≤ b ≤ a + d` (`a` the low
request), the low frame fails or reaches a machine related to the high frame's, after the call. -/
theorem call_case {code : ByteArray} {n : Nat} (hc : CodeOk code n) {S' : Machine → Prop}
    (hS' : MonoFrom S') {N : Nat} (ih : LockIH code n S' N)
    {ml : Machine} {a b : Word} {s : List Word} {d x : Nat} {ps : List Frame}
    (hstk : ml.frame.stack = a :: s) (hab : a.toNat ≤ b.toNat) (hbd : b.toNat ≤ a.toNat + d)
    (hcode : ml.frame.code = code) (hjd : ml.frame.jumpDests = validJumpDests code)
    (hpc : PcOk code n ml.frame.pc)
    (hbyte : Bytes.getD code ml.frame.pc = 0xf1 ∨ Bytes.getD code ml.frame.pc = 0xfa ∨
      Bytes.getD code ml.frame.pc = 0xf4)
    (hret : ml.frame.pc + 1 ∈ callReturnPoints code n)
    (hgas : ml.frame.gasLeft + d < 2 ^ 256)
    (hpreOk : PrecompilesOk ml.precompiles) (hpreMono : PreMono ml.precompiles)
    {mfh : Machine} {oh : Outcome}
    (hex : Exit (withTop b (bump d x ps ml)) N mfh oh)
    (hcalls : CallsTo S' (withTop b (bump d x ps ml)) N) :
    Halts ml (Post mfh oh) := by
  have hb : ml.frame.code[ml.frame.pc]? = some (Bytes.getD code ml.frame.pc) :=
    code_getElem? hcode hpc
  have hbh : (withTop b (bump d x ps ml)).frame.code[(withTop b (bump d x ps ml)).frame.pc]? =
      some (Bytes.getD code ml.frame.pc) := hb
  have hmono := exec_call_mono (fork := ml.ctx.fork) hbyte ml b d x ps a s hstk hab hbd
  cases hrun : (exec (Opcode.decode ml.ctx.fork (Bytes.getD code ml.frame.pc))).run ml with
  | error e =>
    exact Halts.of_step (step_of_exec_error hb hrun) (.refl ml) (.inl (fun out h => by cases h))
  | ok p =>
    obtain ⟨act, ml'⟩ := p
    have hrel := hmono.of_run hrun
    unfold Twp at hrel
    have hfl := ((exec_frame _ ml).of_run hrun).1
    have hpl := (exec_pc _ ml).of_run hrun
    have hstepl := step_eq_of_code hb
    rw [hrun] at hstepl
    cases hrunh : (exec (Opcode.decode ml.ctx.fork (Bytes.getD code ml.frame.pc))).run
        (withTop b (bump d x ps ml)) with
    | error e => rw [hrunh] at hrel; exact hrel.elim
    | ok q =>
      obtain ⟨act', mh'⟩ := q
      rw [hrunh] at hrel
      have hfh := ((exec_frame _ (withTop b (bump d x ps ml))).of_run hrunh).1
      have hsteph : step (withTop b (bump d x ps ml)) =
          match (exec (Opcode.decode ml.ctx.fork (Bytes.getD code ml.frame.pc))).run
            (withTop b (bump d x ps ml)) with
          | .error e => finishFrame (withTop b (bump d x ps ml)) (.halt e)
          | .ok (.next, m') => .running m'
          | .ok (.stop out, m') => finishFrame m' (.success out)
          | .ok (.revert out, m') => finishFrame m' (.revert out)
          | .ok (.call req, m') => .running (launchCall m' req)
          | .ok (.create msg, m') => .running (launchCreate m' msg) := step_eq_of_code hbh
      rw [hrunh] at hsteph
      have hmhgas : (withTop b (bump d x ps ml)).frame.gasLeft = ml.frame.gasLeft + d := rfl
      have hsameh : ∀ {R : Machine}, SameFrame ml R → ∀ d', SameFrame
          (withTop b (bump d x ps ml)) (bump d' x ps R) :=
        fun h d' => sameFrame_withTop_bump h b d d' x ps
      have hretOk : PcOk code n (ml.frame.pc + 1) := pcOk_return hc.region hpc hbyte
      cases act <;> cases act' <;> simp only [CallRel] at hrel
      · -- the call is not made: both continue
        dsimp only at hstepl hsteph
        obtain ⟨hle, hmh'⟩ := hrel
        rw [hmh'] at hsteph
        have hst := hsameh hfl.same (mh'.frame.gasLeft - ml'.frame.gasLeft)
        obtain ⟨hN, hex'⟩ := hex.next hsteph hst
        refine Halts.of_steps (Steps.of_step hstepl hfl.same) (ih (N - 1) (by omega) ml' _ mfh oh
          ⟨bumpOf_bump _ _ _ _, hfl.same.code.trans hcode, hfl.same.jumpDests.trans hjd,
            pcOk_of_exec' hc.region hcode hjd hpc hb hrun, ?_,
            by show PrecompilesOk ml'.precompiles; rw [hfl.same.precompiles]; exact hpreOk,
            by show PreMono ml'.precompiles; rw [hfl.same.precompiles]; exact hpreMono⟩ hex'
          (hcalls.shift (by rw [stepN_one, hsteph]) hst))
        have := hfh.gas
        rw [hmh'] at this
        exact Nat.lt_of_le_of_lt this (by rw [hmhgas]; exact hgas)
      · -- a call
        rename_i req req'
        dsimp only at hstepl hsteph
        obtain ⟨hcg, hreq, hle, hmh'⟩ := hrel
        have hpc' : ml'.frame.pc = ml.frame.pc := hpl
        generalize hd2 : mh'.frame.gasLeft - ml'.frame.gasLeft = d2 at hmh'
        generalize hc' : req'.msg.gas = c' at hreq hcg
        subst hmh' hreq
        have hpm : ml'.precompiles = ml.precompiles := hfl.same.precompiles
        cases hpo : precompileOf ml'.precompiles req.msg with
        | some pa =>
          cases hsucc : (ml'.precompiles.run pa req.msg.data req.msg.gas).success with
          | true =>
            obtain ⟨d3, hd3⟩ := launchCall_precompile_bump (d := d2) (x := x) (ps := ps)
              (by rw [hpm]; exact hpreMono) hpo hcg hsucc
            rw [hd3] at hsteph
            have hsl : SameFrame ml (launchCall ml' req) := by
              refine hfl.same.trans ?_
              rw [launchCall_precompile hpo]
              exact SameFrame.trans (m₂ := { ml' with
                world := (runPrecompile ml'.precompiles pa req.msg (.call req.retOffset req.retSize)
                  (transferValue ml'.world req.msg) ml'.transient (ml'.world, ml'.transient)).2.1
                transient := (runPrecompile ml'.precompiles pa req.msg
                  (.call req.retOffset req.retSize) (transferValue ml'.world req.msg)
                  ml'.transient (ml'.world, ml'.transient)).2.2 })
                ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (sameFrame_resume _ _)
            have hpcR : (launchCall ml' req).frame.pc = ml.frame.pc + 1 := by
              rw [launchCall_precompile hpo, ← hpc']; rfl
            have hst := hsameh hsl d3
            obtain ⟨hN, hex'⟩ := hex.next hsteph hst
            refine Halts.of_steps (Steps.of_step hstepl hsl) (ih (N - 1) (by omega) _ _ mfh oh
              ⟨bumpOf_bump _ _ _ _, hsl.code.trans hcode, hsl.jumpDests.trans hjd,
                by rw [hpcR]; exact hretOk, ?_,
                by show PrecompilesOk (launchCall ml' req).precompiles
                   rw [hsl.precompiles]; exact hpreOk,
                by show PreMono (launchCall ml' req).precompiles
                   rw [hsl.precompiles]; exact hpreMono⟩ hex'
              (hcalls.shift (mh' := bump d3 x ps (launchCall ml' req)) (j := 1)
                (by rw [stepN_one, hsteph]) hst))
            have := gas_le_of_stepN (m := withTop b (bump d x ps ml))
              (m' := bump d3 x ps (launchCall ml' req)) hpreOk
              (j := 1) (by rw [stepN_one, hsteph]) rfl
            exact Nat.lt_of_le_of_lt this (by rw [hmhgas]; exact hgas)
          | false =>
            obtain ⟨hstk', hpcR, hsl⟩ := launchCall_precompile_fail hpo hsucc
            have hsl' := hfl.same.trans hsl
            refine Halts.of_steps (Steps.of_step hstepl hsl')
              (halts_of_failedCall hc (hsl'.code.trans hcode) (by rw [hpcR, hpc']; exact hret)
                (by rw [hstk']; rfl))
        | none =>
          have hpoh : precompileOf (bump d2 x ps ml').precompiles (req.withGas c').msg = none :=
            hpo
          rw [launchCall_none hpo] at hstepl
          rw [launchCall_none hpoh, pushCall_bump hcg] at hsteph
          have hparc : (bump (c' - req.msg.gas) c' (bumpF d2 x ml'.frame :: ps)
              (pushCall ml' req)).parents = (bump d2 x ps ml').frame ::
                (withTop b (bump d x ps ml)).parents := rfl
          obtain ⟨nc, mfc, oc, hexc, hle2, hstepR, hsameR, hexR⟩ := hex.split hsteph hparc
            ⟨by simp [bump, withTop, hfl.same.msg], hfl.same.code, hfl.same.jumpDests,
              hfl.same.kind, hfl.same.snapshot⟩ hfl.same.ctx hfl.same.precompiles
              hfl.same.originalWorld
          have hS'c : S' (pushCall (bump d2 x ps ml') (req.withGas c')) :=
            hcalls 0 (by omega) _ _ _ _ rfl (.refl _) hbh hrunh hpoh
          rw [pushCall_bump hcg] at hS'c
          obtain ⟨nl, mfl, ol, hnl, hsl, hpost⟩ := hS' _ _ nc mfc oc hS'c (bumpOf_bump _ _ _ _) hexc
          have hkl : mfl.frame.kind = .call req.retOffset req.retSize := hsl.kind
          have hparl : mfl.parents = ml'.frame :: ml'.parents := hsl.parents
          have hstepRl : stepN (1 + nl) ml = .running (resumeAfter ml'.frame ml'.parents mfl ol) := by
            rw [stepN_add_of_running (by rw [stepN_one, hstepl]), hnl,
              finishFrame_of_parents ol hparl]
          have hsameRl := sameFrame_resumeAfter (o := ol) hfl.same hsl
          have hpcRl : (resumeAfter ml'.frame ml'.parents mfl ol).frame.pc = ml.frame.pc + 1 := by
            rw [← hpc']; rfl
          rcases hpost with hfail | ⟨rfl, dd, xx, pp, hmfc⟩
          · obtain ⟨hstk', -, -⟩ := resumeAfter_failed (p := ml'.frame) (ps := ml'.parents) hkl hfail
            exact Halts.of_steps ⟨_, hstepRl, hsameRl⟩
              (halts_of_failedCall hc (hsameRl.code.trans hcode) (by rw [hpcRl]; exact hret)
                (by rw [hstk']; rfl))
          · subst hmfc
            obtain ⟨d', hd'⟩ := resumeAfter_bump (p := ml'.frame) (ps := ml'.parents)
              (ps' := (withTop b (bump d x ps ml)).parents) (dp := d2) (xp := x) (o := ol) hkl
            have hR : resumeAfter (bump d2 x ps ml').frame (withTop b (bump d x ps ml)).parents
                (bump dd xx pp mfl) ol = bump d' x ps (resumeAfter ml'.frame ml'.parents mfl ol) :=
              hd'
            rw [hR] at hstepR hsameR hexR
            refine Halts.of_steps ⟨_, hstepRl, hsameRl⟩ (ih _ (by omega) _ _ mfh oh
              ⟨bumpOf_bump _ _ _ _, hsameRl.code.trans hcode, hsameRl.jumpDests.trans hjd,
                by rw [hpcRl]; exact hretOk, ?_,
                by show PrecompilesOk (resumeAfter ml'.frame ml'.parents mfl ol).precompiles
                   rw [hsameRl.precompiles]; exact hpreOk,
                by show PreMono (resumeAfter ml'.frame ml'.parents mfl ol).precompiles
                   rw [hsameRl.precompiles]; exact hpreMono⟩ hexR
              (hcalls.shift hstepR hsameR))
            have := gas_le_of_stepN (m := withTop b (bump d x ps ml)) hpreOk hstepR rfl
            exact Nat.lt_of_le_of_lt this (by rw [hmhgas]; exact hgas)

set_option maxHeartbeats 1000000 in
/-- **The lockstep.** -/
theorem lockstep {code : ByteArray} {n : Nat} (hc : CodeOk code n) {S' : Machine → Prop}
    (hS' : MonoFrom S') : ∀ N, ∀ ml mh mfh oh, Rel code n ml mh → Exit mh N mfh oh →
      CallsTo S' mh N → Halts ml (Post mfh oh) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro ml mh mfh oh hr hex hcalls
    obtain ⟨hbo, hcode, hjd, hpc, hgas, hpreOk, hpreMono⟩ := hr
    have hmh : mh = bump (mh.frame.gasLeft - ml.frame.gasLeft) mh.frame.msg.gas mh.parents ml :=
      hbo.2
    generalize hd : mh.frame.gasLeft - ml.frame.gasLeft = d at hmh
    generalize hx : mh.frame.msg.gas = x at hmh
    generalize hps : mh.parents = ps at hmh
    subst hmh
    have hb : ml.frame.code[ml.frame.pc]? = some (Bytes.getD code ml.frame.pc) :=
      code_getElem? hcode hpc
    have hbh : (bump d x ps ml).frame.code[(bump d x ps ml).frame.pc]? =
        some (Bytes.getD code ml.frame.pc) := hb
    have hpreOk' : PrecompilesOk ml.precompiles := hpreOk
    have hpreMono' : PreMono ml.precompiles := hpreMono
    have hmhgas : (bump d x ps ml).frame.gasLeft = ml.frame.gasLeft + d := rfl
    have hgas' : ml.frame.gasLeft + d < 2 ^ 256 := hgas
    have ih' : LockIH code n S' N := fun N' hN' => ih N' hN'
    cases hrg : readsGasB (Opcode.decode ml.ctx.fork (Bytes.getD code ml.frame.pc)) with
    | false =>
      have hop : ¬ ReadsGas (Opcode.decode ml.ctx.fork (Bytes.getD code ml.frame.pc)) := by
        rw [readsGas_iff, hrg]; simp
      cases hrun : (exec (Opcode.decode ml.ctx.fork (Bytes.getD code ml.frame.pc))).run ml with
      | error e =>
        exact Halts.of_step (step_of_exec_error hb hrun) (.refl ml) (.inl (fun out h => by cases h))
      | ok p =>
        obtain ⟨act, ml'⟩ := p
        have hrunh := exec_bump _ hop hrun d x ps
        have hfl := ((exec_frame _ ml).of_run hrun).1
        have hnc := (exec_noChild _ hrg ml).of_run hrun
        cases act with
        | next =>
          have hstepl := step_of_exec_next hb hrun
          have hsteph : step (bump d x ps ml) = .running (bump d x ps ml') :=
            step_of_exec_next hbh hrunh
          have hst := sameFrame_bump hfl.same d d x ps
          obtain ⟨hN, hex'⟩ := hex.next hsteph hst
          refine Halts.of_steps (Steps.of_step hstepl hfl.same) (ih (N - 1) (by omega) ml' _ mfh oh
            ⟨bumpOf_bump _ _ _ _, hfl.same.code.trans hcode, hfl.same.jumpDests.trans hjd,
              pcOk_of_exec' hc.region hcode hjd hpc hb hrun, ?_,
              by show PrecompilesOk ml'.precompiles; rw [hfl.same.precompiles]; exact hpreOk,
              by show PreMono ml'.precompiles; rw [hfl.same.precompiles]; exact hpreMono⟩ hex'
            (hcalls.shift (by rw [stepN_one, hsteph]) hst))
          have := hfl.gas
          show ml'.frame.gasLeft + d < 2 ^ 256
          omega
        | stop out =>
          have hxl := (exitOf_of_exec hb hrun).1 out rfl
          have hxh := (exitOf_of_exec hbh hrunh).1 out rfl
          obtain ⟨-, rfl, rfl⟩ := (exit_zero hxh).unique hex
          exact Halts.of_step (step_of_exec_stop hb hrun) hfl.same (.inr ⟨rfl, d, x, ps, rfl⟩)
        | revert out =>
          have hxh := (exitOf_of_exec hbh hrunh).2 out rfl
          obtain ⟨-, rfl, rfl⟩ := (exit_zero hxh).unique hex
          exact Halts.of_step (step_of_exec_revert hb hrun) hfl.same (.inr ⟨rfl, d, x, ps, rfl⟩)
        | call req => exact hnc.elim
        | create msg => exact hnc.elim
    | true =>
      have hbyte := readsGas_decode _ _ hrg
      rcases hbyte with h5a | hother
      · -- `GAS`, then the call it feeds
        have hfeed := hc.feed _ hpc.1 hpc.2 h5a
        rw [h5a] at hb hbh
        have hgasop : Opcode.decode ml.ctx.fork 0x5a = .gas := by cases ml.ctx.fork <;> rfl
        cases hrun : (exec (Opcode.decode ml.ctx.fork 0x5a)).run ml with
        | error e =>
          exact Halts.of_step (step_of_exec_error hb hrun) (.refl ml) (.inl (fun out h => by cases h))
        | ok p =>
          obtain ⟨act, ml1⟩ := p
          have hrun' : (exec .gas).run ml = .ok (act, ml1) := by rw [← hgasop]; exact hrun
          obtain ⟨rfl, hstk1, hg1, hrunh'⟩ := exec_gas_bump hrun' d x ps
          have hrunh : (exec (Opcode.decode ml.ctx.fork 0x5a)).run (bump d x ps ml) =
              .ok (.next, withTop (BitVec.ofNat 256 (ml.frame.gasLeft + d - Gas.base))
                (bump d x ps ml1)) := by rw [hgasop]; exact hrunh'
          have hfl := ((exec_frame _ ml).of_run hrun).1
          have hstepl := step_of_exec_next hb hrun
          have hsteph := step_of_exec_next hbh hrunh
          have hst : SameFrame (bump d x ps ml) (withTop (BitVec.ofNat 256
              (ml.frame.gasLeft + d - Gas.base)) (bump d x ps ml1)) :=
            ⟨hfl.same.ctx, hfl.same.precompiles, hfl.same.originalWorld, rfl,
              by simp [bump, withTop, hfl.same.msg], hfl.same.code, hfl.same.jumpDests,
              hfl.same.kind, hfl.same.snapshot⟩
          obtain ⟨hN, hex'⟩ := hex.next hsteph hst
          have hpc1 : ml1.frame.pc = ml.frame.pc + 1 := by
            have hw : Wp (exec .gas) (fun _ m' => m'.frame.pc = ml.frame.pc + 1) ml := by
              simp [exec, pushValue]
            exact hw.of_run hrun'
          have hpcOk1 : PcOk code n ml1.frame.pc :=
            pcOk_of_exec' hc.region hcode hjd hpc hb hrun
          have hret : ml1.frame.pc + 1 ∈ callReturnPoints code n := by
            rw [hpc1]
            unfold callReturnPoints
            rw [List.mem_filterMap]
            exact ⟨ml.frame.pc, hpc.1, by simp [hpc.2, h5a]⟩
          refine Halts.of_steps (Steps.of_step hstepl hfl.same) (call_case hc hS'
            (N := N - 1) (fun N' hN' => ih N' (by omega)) hstk1 ?_ ?_
            (hfl.same.code.trans hcode) (hfl.same.jumpDests.trans hjd) hpcOk1
            (by rw [hpc1]; exact hfeed) hret ?_
            (by show PrecompilesOk ml1.precompiles; rw [hfl.same.precompiles]; exact hpreOk)
            (by show PreMono ml1.precompiles; rw [hfl.same.precompiles]; exact hpreMono) hex'
            (hcalls.shift (by rw [stepN_one, hsteph]) hst))
          · simp only [BitVec.toNat_ofNat, Gas.base]
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            omega
          · simp only [BitVec.toNat_ofNat, Gas.base]
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            omega
          · rw [hg1]; simp only [Gas.base]; omega
      · -- a member of the `CALL` or `CREATE` family: `CALL`, `STATICCALL` or `DELEGATECALL`
        obtain ⟨hcall, hret⟩ := callsFed_call hc.feed hc.fed hpc.1 hpc.2 hother
        cases hstk : ml.frame.stack with
        | nil =>
          have hw : Wp (exec (Opcode.decode ml.ctx.fork (Bytes.getD code ml.frame.pc)))
              (fun _ _ => False) ml := by
            rcases decode_call ml.ctx.fork hcall with h | h | h <;> rw [h] <;>
              simp [exec, execCall, hstk]
          cases hrun : (exec (Opcode.decode ml.ctx.fork (Bytes.getD code ml.frame.pc))).run ml with
          | error e =>
            exact Halts.of_step (step_of_exec_error hb hrun) (.refl ml)
              (.inl (fun out h => by cases h))
          | ok p => exact (hw.of_run hrun).elim
        | cons a s =>
          have hself : withTop a (bump d x ps ml) = bump d x ps ml := withTop_self hstk
          exact call_case hc hS' ih' hstk (Nat.le_refl _) (Nat.le_add_right _ _) hcode hjd hpc
            hcall hret hgas' hpreOk hpreMono (by rw [hself]; exact hex)
            (by rw [hself]; exact hcalls)

/-- **Gas monotonicity of a code** (the main theorem). Let `code` satisfy the code-level
conditions on the region `[0, n)` (`CodeOk`). Let `S` describe high-gas frames running `code`
from a boundary of the region, with gas below `2²⁵⁶` and gas-monotone precompiles that return at
most their gas, and whose children are precompile calls or frames satisfying `S'`, gas-monotone
(`MonoFrom S'`). Then `S` is gas-monotone. -/
theorem monoFrom_of_code {code : ByteArray} {n : Nat} (hc : CodeOk code n)
    {S S' : Machine → Prop} (hS' : MonoFrom S')
    (hS : ∀ mh, S mh → mh.frame.code = code ∧ mh.frame.jumpDests = validJumpDests code ∧
      PcOk code n mh.frame.pc ∧ mh.frame.gasLeft < 2 ^ 256 ∧ PrecompilesOk mh.precompiles ∧
      PreMono mh.precompiles)
    (hcalls : ∀ mh N mfh oh, S mh → Exit mh N mfh oh → CallsTo S' mh N) : MonoFrom S := by
  intro ml mh N mfh oh hSm hbo hex
  obtain ⟨hcode, hjd, hpc, hgas, hpo, hpm⟩ := hS mh hSm
  obtain ⟨-, -, -, -, hfc, hfpc, -, hfjd⟩ := hbo.fields
  exact lockstep hc hS' N ml mh mfh oh
    ⟨hbo, hfc.symm.trans hcode, hfjd.symm.trans hjd, hfpc ▸ hpc, hgas, hpo, hpm⟩ hex
    (hcalls mh N mfh oh hSm hex)

end EvmLogic.GasMono

end

section

/-!
## Frame summaries for any gas

The high frame is taken at the top level (`topBump`) on purpose: there a `Halts` witness
determines the frame's end (`exit_of_halts_top`), while a nested witness may describe a later
point at which the parent happens to look like a resumption.
-/

namespace EvmLogic.GasMono
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested

/-- The frame of `m` with gas `G` (frame and message), at the top level. -/
def topBump (G : Nat) (m : Machine) : Machine := bump (G - m.frame.gasLeft) G [] m

/-- The callee condition of a frame that only calls precompiles. -/
theorem monoFrom_false : MonoFrom (fun _ => False) := fun _ _ _ _ _ h => h.elim

theorem bumpOf_topBump (G : Nat) (m : Machine) :
    BumpOf (topBump G m).frame.msg.gas (topBump G m).parents m (topBump G m) :=
  bumpOf_bump _ _ _ _

theorem topLevelResult_frameResult_success {target : Option Address} {mf mf' : Machine}
    {out : ByteArray} {o' : Outcome} {ko ks : Nat} (hk : mf.frame.kind = .call ko ks)
    (hk' : mf'.frame.kind = .call ko ks)
    (h : topLevelResult target (frameResult mf' o').2.1 (frameResult mf' o').2.2
        (frameResult mf' o').1 =
      topLevelResult target (frameResult mf (.success out)).2.1
        (frameResult mf (.success out)).2.2 (frameResult mf (.success out)).1) :
    ∃ out', o' = .success out' ∧ mf'.world = mf.world := by
  rw [frameResult_success_call hk] at h
  cases o' with
  | success out' =>
    rw [frameResult_success_call hk'] at h
    refine ⟨out', rfl, ?_⟩
    have := congrArg MessageResult.world h
    simpa [topLevelResult, ChildResult.success] using this
  | revert out' =>
    have := congrArg MessageResult.reverted h
    simp [topLevelResult, ChildResult.success, frameResult_revert] at this
  | halt e =>
    have := congrArg MessageResult.error h
    simp [topLevelResult, ChildResult.success, frameResult_halt] at this

/-- **A frame summary transfers to any lower gas**: if `topBump G ml` satisfies a gas-monotone
`S` and its successful ends have worlds satisfying `P`, then `ml` ends, and so do its. -/
theorem halts_world_of_mono {S : Machine → Prop} (hmono : MonoFrom S) {ml : Machine} {G : Nat}
    {ko ks : Nat} (hk : ml.frame.kind = .call ko ks) (hS : S (topBump G ml))
    {P : World → Prop}
    (h : Halts (topBump G ml) (fun mf o => ∀ out, o = .success out → P mf.world)) :
    Halts ml (fun mf o => ∀ out, o = .success out → P mf.world) := by
  obtain ⟨N, mfh, oh, hex, mf', o', hH, hs', hfin⟩ := exit_of_halts_top rfl h
  have hlow := hmono ml (topBump G ml) N mfh oh hS (bumpOf_topBump G ml) hex
  refine hlow.mono fun mfl ol _ hpost out hol => ?_
  rcases hpost with hf | ⟨rfl, dd, xx, pp, hmf⟩
  · exact absurd hol (hf out)
  · subst hol
    have hfh := hex.finish
    have hph : mfh.parents = [] := hfh.2.parents
    have hp' : mf'.parents = [] := hs'.parents
    have hkh : mfh.frame.kind = .call ko ks := hfh.2.kind.trans hk
    have hk' : mf'.frame.kind = .call ko ks := hs'.kind.trans hk
    rw [finishFrame_of_top _ hp', finishFrame_of_top _ hph, hs'.msg, hfh.2.msg] at hfin
    injection hfin with hfin
    obtain ⟨out', ho', hw⟩ := topLevelResult_frameResult_success hkh hk' hfin
    have := hH out' ho'
    rw [hw, hmf] at this
    exact this

end EvmLogic.GasMono

end
