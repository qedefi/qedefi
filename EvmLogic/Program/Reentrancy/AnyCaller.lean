import EvmLogic.Program.Reentrancy.PrefixCall
import EvmLogic.Program.Reentrancy.PrefixEnv
import EvmLogic.Program.Reentrancy.Tail

/-!
# Calls out of a protected frame: any target, `STATICCALL`, `DELEGATECALL`

`pwp_call_v` (`EvmLogic.Program.Reentrancy.PrefixCall`) takes a `CALL` from a protected frame to an
**unprotected** account: the callee is a frame of arbitrary code that the havoc theorem covers.
Three call sites of real protected code fall outside it:

* a `CALL` whose target is itself protected, e.g. an aToken's `rescueTokens(token, …)` with
  `token` the aToken itself, or one protected contract calling another. The child is then a
  dangerous frame whose **caller is protected**, which `DangerStart`/`DStartV` exclude (a
  dangerous frame reached by the havoc theorem always has an unprotected caller). `DStartA` and
  `CoversA` are the dangerous starts and summaries **with any caller**; `CoversA` gives `CoversV`
  (`CoversA.coversV`) and is proved by induction on gas the same way (`coversA_of_lt`).
  **`pwp_call_any`** is `pwp_call_v` for any target under `CoversA`.
* **`pwp_staticcall`**: a `STATICCALL`, any target (precompiles included), any gas, any outcome:
  the caller resumes in some `Gc` world.
* **`pwp_delegatecall`**: a `DELEGATECALL` to trusted code (a proxy's forwarding into its
  implementation): the child runs that code **inside the protected frame** (same address, caller,
  value), so it is no dangerous *start* and no `Covers` applies; the caller supplies a summary of
  the child in `FailOk` form (`DelegateStart`: any child of this call, any gas), and resumes at
  `pc + 1` in some `Gc` world, with any flag.

All three take every outcome of the instruction: out of gas, soft failure (depth, balance), a
precompile, an EIP-7702 designator, or the child.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested EvmLogic.AbsInt

/-! ## What `CALL`, `STATICCALL`, `DELEGATECALL` request -/

/-- What a requested call of kind `k` from `m` looks like (beyond `CallShape`): for `CALL`, from
the executing account to the second stack word with the third as value, transferring it, static
as `m`, running the target's code (unless the target holds an EIP-7702 designator); for
`STATICCALL`, to the second stack word, static, without value; for `DELEGATECALL`, at the executing
account, with `m`'s caller, value and static flag, no transfer, running the second stack word's
code. -/
def ReqShape : CallKind → Machine → CallRequest → Prop
  | .call, m, req => ∃ t v, m.frame.stack[1]? = some t ∧ m.frame.stack[2]? = some v ∧
      req.msg.currentTarget = Word.toAddress t ∧ req.msg.value = v ∧
      req.msg.caller = m.frame.msg.currentTarget ∧ req.msg.shouldTransferValue = true ∧
      req.msg.isStatic = m.frame.msg.isStatic ∧
      (delegatedAddress? (m.world.code (Word.toAddress t)) = none →
        req.msg.code = m.world.code (Word.toAddress t) ∧
        req.msg.codeAddress = some (Word.toAddress t))
  | .staticcall, m, req => ∃ t, m.frame.stack[1]? = some t ∧
      req.msg.currentTarget = Word.toAddress t ∧ req.msg.value = 0 ∧
      req.msg.caller = m.frame.msg.currentTarget ∧ req.msg.isStatic = true
  | .delegatecall, m, req => ∃ t, m.frame.stack[1]? = some t ∧
      req.msg.currentTarget = m.frame.msg.currentTarget ∧ req.msg.caller = m.frame.msg.caller ∧
      req.msg.value = m.frame.msg.value ∧ req.msg.shouldTransferValue = false ∧
      req.msg.isStatic = m.frame.msg.isStatic ∧
      (delegatedAddress? (m.world.code (Word.toAddress t)) = none →
        req.msg.code = m.world.code (Word.toAddress t))
  | .callcode, _, _ => True

/-- The world is unchanged by the instruction itself, and a request has `ReqShape`. -/
def KindShape (k : CallKind) (m : Machine) : Action → Machine → Prop
  | .next, m' => m'.world = m.world
  | .call req, m' => m'.world = m.world ∧ ReqShape k m req
  | _, _ => False

set_option maxHeartbeats 4000000 in
/-- **What `CALL` requests.** -/
theorem execCall_kind_call (m : Machine) : Wp (execCall .call) (KindShape .call m) m := by
  simp [KindShape, ReqShape, execCall, memoryExpansion, expandMemory, readMemory, setReturnData,
    genericCall] <;> intros <;> subst_vars <;> simp_all

set_option maxHeartbeats 4000000 in
/-- **What `STATICCALL` requests.** -/
theorem execCall_kind_static (m : Machine) :
    Wp (execCall .staticcall) (KindShape .staticcall m) m := by
  simp [KindShape, ReqShape, execCall, memoryExpansion, expandMemory, readMemory, setReturnData,
    genericCall] <;> intros <;> subst_vars <;> simp_all

set_option maxHeartbeats 4000000 in
/-- **What `DELEGATECALL` requests.** -/
theorem execCall_kind_delegate (m : Machine) :
    Wp (execCall .delegatecall) (KindShape .delegatecall m) m := by
  simp [KindShape, ReqShape, execCall, memoryExpansion, expandMemory, readMemory, setReturnData,
    genericCall] <;> intros <;> subst_vars <;> simp_all


/-- A stack of shape `Shape 6 1` over `_ :: … :: rest` (six words) is one word on `rest`. -/
theorem shape_call6 {a b c d e f : Word} {rest st' : List Word}
    (h : Shape 6 1 (a :: b :: c :: d :: e :: f :: rest) st') : ∃ x, st' = x :: rest := by
  obtain ⟨-, hl, hd⟩ := h
  match st', hl, hd with
  | x :: r, _, hd => exact ⟨x, by simpa using hd⟩
  | [], hl, _ => simp at hl

theorem transferValue_of_false {w : World} {msg : Message}
    (h : msg.shouldTransferValue = false) : transferValue w msg = w := by
  unfold transferValue; simp [h]

/-- **The callee-summary rule with the gas of the return** (`WP.call`): the caller resumes with at
most its gas at the call plus the child's initial gas (the gas of the whole stack never
increases, `stepN_gas`). -/
theorem WP.call_le {m mc : Machine} {p : Frame} {Q : Machine → Prop}
    {H Hc : Machine → Outcome → Prop}
    (hstep : step m = .running mc) (hpar : mc.parents = p :: m.parents)
    (hp : SameFrame m { mc with frame := p, parents := m.parents })
    (hpre : PrecompilesOk mc.precompiles) (hcallee : Halts mc Hc)
    (k : ∀ mf o, SameFrame mc mf → Hc mf o →
      (resumeAfter p m.parents mf o).frame.gasLeft ≤ p.gasLeft + mc.frame.gasLeft →
      WP (resumeAfter p m.parents mf o) Q H) :
    WP m Q H := by
  obtain ⟨n, mf, o, hH, hs, hn⟩ := hcallee.resume hpar
  have hsame : SameFrame m (resumeAfter p m.parents mf o) := by
    refine SameFrame.trans ?_ (sameFrame_resume _ _)
    exact ⟨hs.ctx.trans hp.ctx, hs.precompiles.trans hp.precompiles,
      hs.originalWorld.trans hp.originalWorld, rfl, hp.msg, hp.code, hp.jumpDests, hp.kind,
      hp.snapshot⟩
  have hg := stepN_gas hpre n
  rw [hn] at hg
  simp only [resultGas, gasSum, resumeAfter, resume_gasLeft, resume_parents, hpar,
    List.map_cons, List.sum_cons] at hg
  refine WP.of_steps ⟨n + 1, ?_, hsame⟩ (k mf o hs hH ?_)
  · rw [show n + 1 = 1 + n by omega, stepN_add_of_running (by rw [stepN_one, hstep]), hn]
  · simp only [resumeAfter, resume_gasLeft]; omega

/-! ## Dangerous starts and summaries with any caller -/

variable {P : Address → Prop} {Good Gc : World → Prop} {C : Context → Prop} {Q : Machine → Prop}
  {m : Machine}

/-- **A dangerous frame start with any caller**: a fresh message-call frame, non-static, at a
protected account, running that account's code, from a `Good` snapshot into a `Good` world, in a
context satisfying `C`. Unlike `DangerStart`/`DStartV`, the caller may be protected (a protected
contract calling itself or another protected one). -/
structure DStartA (P : Address → Prop) (Good : World → Prop) (C : Context → Prop) (G : Nat)
    (m : Machine) : Prop where
  /-- A fresh message-call frame. -/
  fresh : ∃ o s, m.frame = Frame.init m.frame.msg (.call o s) m.frame.snapshot
  danger : Danger P m.frame
  /-- The world before the call (the rollback snapshot) is `Good`. -/
  snapshot : Good m.frame.snapshot.1
  /-- The world the frame starts in (after any value transfer) is `Good`. -/
  world : Good m.world
  /-- The protected account's own code runs. -/
  code : m.frame.msg.code = m.world.code m.frame.msg.currentTarget
  target : m.frame.msg.target = some m.frame.msg.currentTarget
  codeAddress : m.frame.msg.codeAddress = some m.frame.msg.currentTarget
  gas : m.frame.msg.gas ≤ G
  depth : m.frame.msg.depth ≤ Gas.stackDepthLimit
  /-- Standard precompiles. -/
  pre : m.precompiles = PrecompileImpl.standard m.ctx
  /-- The transaction's context. -/
  context : C m.ctx

/-- **Summaries of the protected code for any caller**: every `DStartA` frame with at most `G`
gas ends in a `Good` world. -/
def CoversA (P : Address → Prop) (Good : World → Prop) (C : Context → Prop) (G : Nat) : Prop :=
  ∀ m, DStartA P Good C G m → Halts m (FailOk Good)

/-- `CoversA` by induction on gas: reentrant frames have less gas than their ancestors. -/
theorem coversA_of_lt (h : ∀ G, (∀ G' < G, CoversA P Good C G') → CoversA P Good C G)
    (G : Nat) : CoversA P Good C G := by
  induction G using Nat.strongRecOn with
  | ind G ih => exact h G ih

/-- `CoversA` for more gas gives `CoversA` for less. -/
theorem CoversA.mono {G G' : Nat} (h : CoversA P Good C G) (hle : G' ≤ G) :
    CoversA P Good C G' :=
  fun m hd => h m { hd with gas := Nat.le_trans hd.gas hle }

/-- **`CoversA` gives `CoversV`**: a `DStartV` frame (unprotected caller, value moved) is a
`DStartA` frame, its world `Good` since the transfer came from an unprotected account. -/
theorem CoversA.coversV (S : GoodOps P Good) {G : Nat} (h : CoversA P Good C G) :
    CoversV P Good C G := by
  intro m hd
  refine h m ⟨hd.fresh, hd.danger, hd.snapshot, ?_, hd.code, hd.target, hd.codeAddress, hd.gas,
    hd.depth, hd.pre, hd.context⟩
  rw [hd.world_eq]
  exact S.transfer hd.snapshot fun h1 h2 => ⟨hd.afford h1 h2, .inl hd.caller⟩

/-! ## `CALL` to any account -/

/-- **A `CALL` of a prefix to any account, any gas, any outcome.** As `pwp_call_v`, but the
target may be protected: then the child is a `DStartA` frame (its caller, the executing account,
may be protected), covered by `CoversA` below the caller's gas; otherwise it is a frame of
arbitrary code, covered by the havoc theorem. -/
theorem pwp_call_any (S : GoodOps P Gc) (hC : C m.ctx)
    (hcov : ∀ g < m.frame.gasLeft, CoversA P Gc C g)
    {gas toW value inOff inSize outOff outSize : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hI0 : Gc m.world)
    (hI : value ≠ 0 → value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat →
      Gc (moveEther m.world m.frame.msg.currentTarget (Word.toAddress toW) value))
    (k : ∀ m'', SameFrame m m'' → m''.frame.pc = m.frame.pc + 1 →
      (∃ x, m''.frame.stack = x :: rest) → Gc m''.world → m''.frame.gasLeft ≤ m.frame.gasLeft →
      WP m'' Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  have hdec : Opcode.decode m.ctx.fork 0xf1 = .call := by cases m.ctx.fork <;> rfl
  have hw := wp_and (wp_and (wp_and (wp_and (exec_frame .call m) (exec_strict .call m))
    (exec_world .call m)) (execCall_kind_call m)) (exec_eff .call m)
  cases he : (exec (Opcode.decode m.ctx.fork 0xf1)).run m with
  | error e => exact wp_fail_of_error hsnap hcode he
  | ok p =>
    obtain ⟨a, m'⟩ := p
    have he' := he
    rw [hdec] at he'
    obtain ⟨⟨⟨⟨⟨hf, hok⟩, hs, -⟩, -, ht⟩, hsh⟩, heff⟩ := hw.of_run he'
    cases a with
    | next =>
      have hst := step_of_exec_next hcode he
      have hgood' : Gc m'.world := (show m'.world = m.world from hsh) ▸ hI0
      obtain ⟨hpc, hsh⟩ := heff
      rw [hstk] at hsh
      exact WP.of_step hst hf.same (k m' hf.same hpc (shape_call hsh) hgood' hf.gas)
    | stop out => exact hsh.elim
    | revert out => exact hsh.elim
    | create msg => exact hsh.elim
    | call req =>
      have hst : step m = .running (launchCall m' req) := by rw [step_eq_of_code hcode, he]
      have hs' : m'.frame.gasLeft + req.msg.gas < m.frame.gasLeft := hs
      obtain ⟨hwm, t, v, ht1, hv1, htgt, hval, hcaller, hstv, hstat, hcd⟩ := hsh
      have hgood' : Gc m'.world := hwm ▸ hI0
      obtain ⟨hpc', -, hstk'⟩ := heff
      rw [hstk] at hstk'
      simp only [List.drop_succ_cons, List.drop_zero] at hstk'
      rw [hstk] at ht1 hv1
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ht1 hv1
      subst ht1 hv1
      have htv : Gc (transferValue m'.world req.msg) := by
        unfold transferValue
        split
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨-, hb, -⟩ := ht hc.1 hc.2
          rw [hwm, hcaller, htgt, hval]
          rw [hwm, hcaller, hval] at hb
          exact hI (hval ▸ hc.2) hb
        · exact hgood'
      have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
        rw [hf.same.precompiles, hf.same.ctx]; exact hstd
      rcases launchCall_cases m' req with ⟨r, w, t, hl, hw', hrg⟩ | hl <;> rw [hl] at hst
      · have hsf : SameFrame m (resume { m' with world := w, transient := t } r) :=
          (hf.same.trans (show SameFrame m' { m' with world := w, transient := t } from
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)).trans (sameFrame_resume _ _)
        obtain ⟨hrpc, ⟨x, hrst⟩, -⟩ := resume_frame { m' with world := w, transient := t } r
        have hrg' := hrg (by rw [hpre']; exact precompilesOk_standard _)
        refine WP.of_step hst hsf (k _ hsf ?_ ⟨x, ?_⟩ ?_ (by simp only [resume_gasLeft]; omega))
        · rw [hrpc]; exact congrArg (· + 1) hpc'
        · rw [hrst]; exact congrArg (x :: ·) hstk'
        · rw [resume_world]
          rcases hw' with rfl | rfl
          · exact htv
          · exact hgood'
      · have hpar : (pushCall m' req).parents = m'.frame :: m.parents := by
          simp only [pushCall, hf.same.parents]
        have hp : SameFrame m { pushCall m' req with frame := m'.frame, parents := m.parents } :=
          ⟨hf.same.ctx, hf.same.precompiles, hf.same.originalWorld, rfl, hf.same.msg,
            hf.same.code, hf.same.jumpDests, hf.same.kind, hf.same.snapshot⟩
        have hlt : req.msg.gas < m.frame.gasLeft := by omega
        have hcallee : Halts (pushCall m' req) (FailOk Gc) := by
          by_cases hd : P req.msg.currentTarget ∧ req.msg.isStatic = false
          · have hdel : delegatedAddress? (m.world.code (Word.toAddress toW)) = none :=
              S.deleg _ hI0 _ (htgt ▸ hd.1)
            obtain ⟨hcode', hca⟩ := hcd hdel
            have hsize : (m'.world.code req.msg.currentTarget).size ≠ 0 :=
              S.code _ hgood' _ hd.1
            refine hcov _ hlt _ ⟨⟨_, _, rfl⟩, hd, hgood', htv, ?_, hok.target, ?_, Nat.le_refl _,
              hok.depthLe, by simp only [pushCall]; exact hpre',
              by simp only [pushCall]; rw [hf.same.ctx]; exact hC⟩
            · show req.msg.code = (transferValue m'.world req.msg).code req.msg.currentTarget
              rw [(keep_transferValue hsize).code, hwm, htgt]; exact hcode'
            · show req.msg.codeAddress = some req.msg.currentTarget
              rw [htgt]; exact hca
          · exact halts_inv_v S (CoversA.coversV S (hcov _ hlt)) _
              (show C m'.ctx by rw [hf.same.ctx]; exact hC)
              (Nat.le_of_eq (pushCall_gasLeft _ _))
              ⟨htv, ⟨hgood', hd, fun hk => by cases hk⟩, by simp only [pushCall]; exact hpre'⟩
        refine WP.call_le hst hpar hp
          (by simp only [pushCall]; rw [hpre']; exact precompilesOk_standard _) hcallee ?_
        intro mf o hsf hgood hgas
        have hsame : SameFrame m (resumeAfter m'.frame m.parents mf o) := by
          refine SameFrame.trans ?_ (sameFrame_resume _ _)
          exact ⟨hsf.ctx.trans hp.ctx, hsf.precompiles.trans hp.precompiles,
            hsf.originalWorld.trans hp.originalWorld, rfl, hp.msg, hp.code, hp.jumpDests, hp.kind,
            hp.snapshot⟩
        obtain ⟨hrpc, ⟨x, hrst⟩, -⟩ := resume_frame
          { mf with frame := m'.frame, parents := m.parents, world := (frameResult mf o).2.1,
                    transient := (frameResult mf o).2.2 } (frameResult mf o).1
        refine k _ hsame ?_ ⟨x, ?_⟩ hgood ?_
        · show (resume _ _).frame.pc = _
          rw [hrpc]; exact congrArg (· + 1) hpc'
        · show (resume _ _).frame.stack = _
          rw [hrst]; exact congrArg (x :: ·) hstk'
        · rw [pushCall_gasLeft] at hgas; omega


/-! ## `STATICCALL` -/

/-- **A `STATICCALL` of a prefix, any target, any gas, any outcome.** From a `Gc` world (a
`GoodOps` invariant), the caller continues at `pc + 1` with one word pushed on `rest`, in some
`Gc` world: the child and all its descendants are static, hence never dangerous (the summaries
`CoversA` are only passed on to the havoc theorem). A failure of the instruction itself hands back
the `Good` snapshot. -/
theorem pwp_staticcall (S : GoodOps P Gc) (hC : C m.ctx)
    (hcov : ∀ g < m.frame.gasLeft, CoversA P Gc C g)
    {gas toW inOff inSize outOff outSize : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack = gas :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hI0 : Gc m.world)
    (k : ∀ m'', SameFrame m m'' → m''.frame.pc = m.frame.pc + 1 →
      (∃ x, m''.frame.stack = x :: rest) → Gc m''.world → m''.frame.gasLeft ≤ m.frame.gasLeft →
      WP m'' Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  have hdec : Opcode.decode m.ctx.fork 0xfa = .staticcall := by cases m.ctx.fork <;> rfl
  have hw := wp_and (wp_and (wp_and (exec_frame .staticcall m) (exec_strict .staticcall m))
    (execCall_kind_static m)) (exec_eff .staticcall m)
  cases he : (exec (Opcode.decode m.ctx.fork 0xfa)).run m with
  | error e => exact wp_fail_of_error hsnap hcode he
  | ok p =>
    obtain ⟨a, m'⟩ := p
    have he' := he
    rw [hdec] at he'
    obtain ⟨⟨⟨⟨hf, hok⟩, hs, -⟩, hsh⟩, heff⟩ := hw.of_run he'
    cases a with
    | next =>
      have hst := step_of_exec_next hcode he
      have hgood' : Gc m'.world := (show m'.world = m.world from hsh) ▸ hI0
      obtain ⟨hpc, hsh⟩ := heff
      rw [hstk] at hsh
      exact WP.of_step hst hf.same (k m' hf.same hpc (shape_call6 hsh) hgood' hf.gas)
    | stop out => exact hsh.elim
    | revert out => exact hsh.elim
    | create msg => exact hsh.elim
    | call req =>
      have hst : step m = .running (launchCall m' req) := by rw [step_eq_of_code hcode, he]
      have hs' : m'.frame.gasLeft + req.msg.gas < m.frame.gasLeft := hs
      obtain ⟨hwm, t, -, -, hval, -, hstat⟩ := hsh
      have hgood' : Gc m'.world := hwm ▸ hI0
      obtain ⟨hpc', -, hstk'⟩ := heff
      rw [hstk] at hstk'
      simp only [List.drop_succ_cons, List.drop_zero] at hstk'
      have htv : Gc (transferValue m'.world req.msg) := by
        rw [transferValue_zero _ _ hval]; exact hgood'
      have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
        rw [hf.same.precompiles, hf.same.ctx]; exact hstd
      rcases launchCall_cases m' req with ⟨r, w, t, hl, hw', hrg⟩ | hl <;> rw [hl] at hst
      · have hsf : SameFrame m (resume { m' with world := w, transient := t } r) :=
          (hf.same.trans (show SameFrame m' { m' with world := w, transient := t } from
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)).trans (sameFrame_resume _ _)
        obtain ⟨hrpc, ⟨x, hrst⟩, -⟩ := resume_frame { m' with world := w, transient := t } r
        have hrg' := hrg (by rw [hpre']; exact precompilesOk_standard _)
        refine WP.of_step hst hsf (k _ hsf ?_ ⟨x, ?_⟩ ?_ (by simp only [resume_gasLeft]; omega))
        · rw [hrpc]; exact congrArg (· + 1) hpc'
        · rw [hrst]; exact congrArg (x :: ·) hstk'
        · rw [resume_world]
          rcases hw' with rfl | rfl
          · exact htv
          · exact hgood'
      · have hpar : (pushCall m' req).parents = m'.frame :: m.parents := by
          simp only [pushCall, hf.same.parents]
        have hp : SameFrame m { pushCall m' req with frame := m'.frame, parents := m.parents } :=
          ⟨hf.same.ctx, hf.same.precompiles, hf.same.originalWorld, rfl, hf.same.msg,
            hf.same.code, hf.same.jumpDests, hf.same.kind, hf.same.snapshot⟩
        have hlt : req.msg.gas < m.frame.gasLeft := by omega
        have hnd : ¬ Danger P (pushCall m' req).frame := by
          intro hd
          have : req.msg.isStatic = false := hd.2
          rw [hstat] at this; cases this
        have hcallee : Halts (pushCall m' req) (FailOk Gc) :=
          halts_inv_v S (CoversA.coversV S (hcov _ hlt)) _
            (show C m'.ctx by rw [hf.same.ctx]; exact hC)
            (Nat.le_of_eq (pushCall_gasLeft _ _))
            ⟨htv, ⟨hgood', hnd, fun hk => by cases hk⟩, by simp only [pushCall]; exact hpre'⟩
        refine WP.call_le hst hpar hp
          (by simp only [pushCall]; rw [hpre']; exact precompilesOk_standard _) hcallee ?_
        intro mf o hsf hgood hgas
        have hsame : SameFrame m (resumeAfter m'.frame m.parents mf o) := by
          refine SameFrame.trans ?_ (sameFrame_resume _ _)
          exact ⟨hsf.ctx.trans hp.ctx, hsf.precompiles.trans hp.precompiles,
            hsf.originalWorld.trans hp.originalWorld, rfl, hp.msg, hp.code, hp.jumpDests, hp.kind,
            hp.snapshot⟩
        obtain ⟨hrpc, ⟨x, hrst⟩, -⟩ := resume_frame
          { mf with frame := m'.frame, parents := m.parents, world := (frameResult mf o).2.1,
                    transient := (frameResult mf o).2.2 } (frameResult mf o).1
        refine k _ hsame ?_ ⟨x, ?_⟩ hgood ?_
        · show (resume _ _).frame.pc = _
          rw [hrpc]; exact congrArg (· + 1) hpc'
        · show (resume _ _).frame.stack = _
          rw [hrst]; exact congrArg (x :: ·) hstk'
        · rw [pushCall_gasLeft] at hgas; omega

/-! ## `DELEGATECALL` to trusted code -/

/-- **The child of a `DELEGATECALL`** from `m` to `toW`: a fresh message-call frame started from
`m`'s world (its snapshot) in that world, in `m`'s context, running at `m`'s account with `m`'s
caller, value and static flag, with less gas than `m` has, moving no value, and running the code
of `toW` (unless it holds an EIP-7702 designator). -/
structure DelegateStart (m : Machine) (toW : Word) (mc : Machine) : Prop where
  fresh : ∃ o s t, mc.frame = Frame.init mc.frame.msg (.call o s) (m.world, t)
  world : mc.world = m.world
  ctx : mc.ctx = m.ctx
  pre : mc.precompiles = m.precompiles
  target : mc.frame.msg.currentTarget = m.frame.msg.currentTarget
  caller : mc.frame.msg.caller = m.frame.msg.caller
  value : mc.frame.msg.value = m.frame.msg.value
  isStatic : mc.frame.msg.isStatic = m.frame.msg.isStatic
  transfers : mc.frame.msg.shouldTransferValue = false
  gas : mc.frame.msg.gas < m.frame.gasLeft
  code : delegatedAddress? (m.world.code (Word.toAddress toW)) = none →
    mc.frame.msg.code = m.world.code (Word.toAddress toW)

/-- **A `DELEGATECALL` of a prefix to trusted code, any gas, any outcome.** If every child of the
call (`DelegateStart`) halts handing back a `Gc` world (`FailOk Gc`: its own on success, its
snapshot, the caller's world, otherwise), and the world at the call is `Gc`, the caller continues
at `pc + 1` with one word pushed on `rest`, in some `Gc` world. The child runs **in** the caller's
frame's account: it is the caller's own proof obligation, not a `Covers` one. A failure of the
instruction itself hands back the `Good` snapshot. -/
theorem pwp_delegatecall {gas toW inOff inSize outOff outSize : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0xf4)
    (hstk : m.frame.stack = gas :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx) (hI0 : Gc m.world)
    (hchild : ∀ mc, DelegateStart m toW mc → Halts mc (FailOk Gc))
    (k : ∀ m'', SameFrame m m'' → m''.frame.pc = m.frame.pc + 1 →
      (∃ x, m''.frame.stack = x :: rest) → Gc m''.world → m''.frame.gasLeft ≤ m.frame.gasLeft →
      WP m'' Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  have hdec : Opcode.decode m.ctx.fork 0xf4 = .delegatecall := by cases m.ctx.fork <;> rfl
  have hw := wp_and (wp_and (wp_and (exec_frame .delegatecall m) (exec_strict .delegatecall m))
    (execCall_kind_delegate m)) (exec_eff .delegatecall m)
  cases he : (exec (Opcode.decode m.ctx.fork 0xf4)).run m with
  | error e => exact wp_fail_of_error hsnap hcode he
  | ok p =>
    obtain ⟨a, m'⟩ := p
    have he' := he
    rw [hdec] at he'
    obtain ⟨⟨⟨⟨hf, hok⟩, hs, -⟩, hsh⟩, heff⟩ := hw.of_run he'
    cases a with
    | next =>
      have hst := step_of_exec_next hcode he
      have hgood' : Gc m'.world := (show m'.world = m.world from hsh) ▸ hI0
      obtain ⟨hpc, hsh⟩ := heff
      rw [hstk] at hsh
      exact WP.of_step hst hf.same (k m' hf.same hpc (shape_call6 hsh) hgood' hf.gas)
    | stop out => exact hsh.elim
    | revert out => exact hsh.elim
    | create msg => exact hsh.elim
    | call req =>
      have hst : step m = .running (launchCall m' req) := by rw [step_eq_of_code hcode, he]
      have hs' : m'.frame.gasLeft + req.msg.gas < m.frame.gasLeft := hs
      obtain ⟨hwm, t, ht1, htgt, hcaller, hval, hstv, hstat, hcd⟩ := hsh
      have hgood' : Gc m'.world := hwm ▸ hI0
      obtain ⟨hpc', -, hstk'⟩ := heff
      rw [hstk] at hstk' ht1
      simp only [List.drop_succ_cons, List.drop_zero] at hstk'
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ht1
      subst ht1
      have htv : transferValue m'.world req.msg = m'.world := transferValue_of_false hstv
      have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
        rw [hf.same.precompiles, hf.same.ctx]; exact hstd
      rcases launchCall_cases m' req with ⟨r, w, t, hl, hw', hrg⟩ | hl <;> rw [hl] at hst
      · have hsf : SameFrame m (resume { m' with world := w, transient := t } r) :=
          (hf.same.trans (show SameFrame m' { m' with world := w, transient := t } from
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)).trans (sameFrame_resume _ _)
        obtain ⟨hrpc, ⟨x, hrst⟩, -⟩ := resume_frame { m' with world := w, transient := t } r
        have hrg' := hrg (by rw [hpre']; exact precompilesOk_standard _)
        refine WP.of_step hst hsf (k _ hsf ?_ ⟨x, ?_⟩ ?_ (by simp only [resume_gasLeft]; omega))
        · rw [hrpc]; exact congrArg (· + 1) hpc'
        · rw [hrst]; exact congrArg (x :: ·) hstk'
        · rw [resume_world]
          rcases hw' with rfl | rfl
          · rw [htv]; exact hgood'
          · exact hgood'
      · have hpar : (pushCall m' req).parents = m'.frame :: m.parents := by
          simp only [pushCall, hf.same.parents]
        have hp : SameFrame m { pushCall m' req with frame := m'.frame, parents := m.parents } :=
          ⟨hf.same.ctx, hf.same.precompiles, hf.same.originalWorld, rfl, hf.same.msg,
            hf.same.code, hf.same.jumpDests, hf.same.kind, hf.same.snapshot⟩
        have hcallee : Halts (pushCall m' req) (FailOk Gc) := by
          refine hchild _ ⟨⟨req.retOffset, req.retSize, m'.transient, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hstv, ?_, ?_⟩
          · show Frame.init req.msg _ (m'.world, m'.transient) = _
            rw [hwm]; rfl
          · show transferValue m'.world req.msg = m.world
            rw [htv, hwm]
          · exact hf.same.ctx
          · exact hf.same.precompiles
          · show req.msg.currentTarget = _; exact htgt
          · show req.msg.caller = _; exact hcaller
          · show req.msg.value = _; exact hval
          · show req.msg.isStatic = _; exact hstat
          · show req.msg.gas < _; omega
          · exact hcd
        refine WP.call_le hst hpar hp
          (by simp only [pushCall]; rw [hpre']; exact precompilesOk_standard _) hcallee ?_
        intro mf o hsf hgood hgas
        have hsame : SameFrame m (resumeAfter m'.frame m.parents mf o) := by
          refine SameFrame.trans ?_ (sameFrame_resume _ _)
          exact ⟨hsf.ctx.trans hp.ctx, hsf.precompiles.trans hp.precompiles,
            hsf.originalWorld.trans hp.originalWorld, rfl, hp.msg, hp.code, hp.jumpDests, hp.kind,
            hp.snapshot⟩
        obtain ⟨hrpc, ⟨x, hrst⟩, -⟩ := resume_frame
          { mf with frame := m'.frame, parents := m.parents, world := (frameResult mf o).2.1,
                    transient := (frameResult mf o).2.2 } (frameResult mf o).1
        refine k _ hsame ?_ ⟨x, ?_⟩ hgood ?_
        · show (resume _ _).frame.pc = _
          rw [hrpc]; exact congrArg (· + 1) hpc'
        · show (resume _ _).frame.stack = _
          rw [hrst]; exact congrArg (x :: ·) hstk'
        · rw [pushCall_gasLeft] at hgas; omega


/-! ## Continuing after a call or a world-safe instruction -/

/-- **The continuation of a call rule in literal form**: to continue from every machine the call
rules hand over (same frame, `pc + 1`, one word on `rest`, a `Gc` world, at most the gas at the
call), it suffices to continue from the machine at the call with these fields replaced by
arbitrary values (world, transient storage, created accounts, the pushed word, memory, gas, return
data, substate). -/
theorem wp_of_resume {m : Machine} {rest : List Word} {H : Machine → Outcome → Prop}
    (h : ∀ (w : World) (tr : TransientStorage) (cr : AddressSet) (x : Word) (mem : Memory)
      (g : Nat) (rd : ByteArray) (sub : Substate), Gc w → g ≤ m.frame.gasLeft →
      WP { m with world := w, transient := tr, createdAccounts := cr, frame := { m.frame with
        pc := m.frame.pc + 1, stack := x :: rest, memory := mem, gasLeft := g, returnData := rd,
        sub := sub } } Q H) :
    ∀ m'', SameFrame m m'' → m''.frame.pc = m.frame.pc + 1 → (∃ x, m''.frame.stack = x :: rest) →
      Gc m''.world → m''.frame.gasLeft ≤ m.frame.gasLeft → WP m'' Q H := by
  intro m'' hs hpc ⟨x, hx⟩ hw hg
  obtain ⟨c, p, w, t, o, cr, ⟨msg, code, jd, pc, st, mem, g, rd, sub, snap, kind⟩, par⟩ := m''
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 hpc hx hw hg
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 hpc hx
  exact h w t cr x mem g rd sub hw hg

/-- **A world-safe instruction that only pops** (`LOG*`), as `pwp_safe`, keeping that the gas
after it is at most the gas before (the bound later call rules need). -/
theorem pwp_safe_le {b : UInt8} {p ko ks : Nat} (hsnap : Good m.frame.snapshot.1)
    (hw : Good m.world) (hkind : m.frame.kind = .call ko ks)
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hsafe : WorldSafe b = true) (heff : byteEff b = .gen p 0)
    (hrec : ∀ (t : TransientStorage) (c : AddressSet) (mem : Memory) (g : Nat) (rd : ByteArray)
      (sub : Substate), g ≤ m.frame.gasLeft → WP { m with
        transient := t, createdAccounts := c, frame := { m.frame with
          pc := m.frame.pc + 1, stack := m.frame.stack.drop p, memory := mem, gasLeft := g,
          returnData := rd, sub := sub } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  rcases step_worldSafe hcode hsafe with ⟨m', o, he, hf, hworld⟩ | ⟨m', he, hf, hlt, hworld, hex⟩
  · refine WP.halt_of_step he hf.same ?_
    show Good (frameResult m' o).2.1
    rcases frameResult_world m' o with h1 | ⟨hk', -⟩ | h1
    · rw [h1, hworld]; exact hw
    · rw [hf.same.kind, hkind] at hk'; cases hk'
    · rw [h1, hf.same.snapshot]; exact hsnap
  · have hpost : NextPost (byteEff b) m m' := (exec_eff_byte m.ctx.fork b m).of_run hex
    rw [heff] at hpost
    obtain ⟨hpc, -, hl, hd⟩ := hpost
    simp only [List.drop_zero] at hd
    refine WP.of_step he hf.same ?_
    have hs := hf.same
    have hle : m'.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_of_lt hlt
    obtain ⟨c', p', w', t', o', cr', ⟨msg', code', jd', pc', st', mem', g', rd', sub', snap',
      kind'⟩, par'⟩ := m'
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs
    dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 hpc hd hworld hle
    subst h1 h2 h3 h4 h5 h6 h7 h8 h9 hpc hd hworld
    exact hrec t' cr' mem' g' rd' sub' hle

end EvmLogic.Program.Reentrancy
