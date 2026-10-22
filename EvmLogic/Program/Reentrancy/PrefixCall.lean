import EvmLogic.Program.Reentrancy.Value
import EvmLogic.Program.Reentrancy.PrefixOps
import EvmLogic.AbsInt.Frame
import EvmLogic.Program.Reentrancy.Halts

/-!
# The untrusted `CALL` of a prefix, for any gas and any outcome

`WP.call_havoc_e` takes the call when every side condition of `step_call` holds. A prefix runs
under symbolic gas, so its call may also run out of gas, fail softly (depth, balance: the
caller continues with `0` and the world unchanged), go to a precompile, or hit an EIP-7702
designator. `pwp_call_v` covers all of them at once: if the call-site invariant `Gc` holds of the
world before and after the value transfer, the callee is not protected and the protected code
`CoversV` `Gc` below the caller's gas, then the caller continues at `pc + 1` with `rest` under one
pushed word, in the same frame, in **some** world satisfying `Gc` — or ends with a failure, which
hands back the `Good` snapshot.

`pwp_call_stipend` is the same for a callee given at most the 2300-gas stipend, with no
invariant and no summaries (`halts_low`): the caller continues with the success flag `x` and the
world exactly as before the call (`x = 0`) or after the value transfer (`x ≠ 0`).
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested EvmLogic.AbsInt

/-! ## What `CALL` does -/

/-- The world is unchanged, and a requested call goes from the executing account to the second
stack word with the third as value, transferring it. -/
def CallShape (m : Machine) : Action → Machine → Prop
  | .next, m' => m'.world = m.world
  | .call req, m' => m'.world = m.world ∧
    (∃ t v, m.frame.stack[1]? = some t ∧ m.frame.stack[2]? = some v ∧
      req.msg.currentTarget = Word.toAddress t ∧ req.msg.value = v) ∧
    req.msg.caller = m.frame.msg.currentTarget ∧ req.msg.shouldTransferValue = true
  | _, _ => False

set_option maxHeartbeats 1000000 in
/-- **What `CALL` does to the world and asks for.** -/
theorem execCall_shape (m : Machine) : Wp (execCall .call) (CallShape m) m := by
  simp [CallShape, execCall, memoryExpansion, expandMemory, readMemory, setReturnData,
    genericCall] <;> intros <;> subst_vars <;> simp_all

/-- A stack of shape `Shape 7 1` over `_ :: … :: rest` (seven words) is one word on `rest`. -/
theorem shape_call {a b c d e f g : Word} {rest st' : List Word}
    (h : Shape 7 1 (a :: b :: c :: d :: e :: f :: g :: rest) st') : ∃ x, st' = x :: rest := by
  obtain ⟨-, hl, hd⟩ := h
  match st', hl, hd with
  | x :: r, _, hd => exact ⟨x, by simpa using hd⟩
  | [], hl, _ => simp at hl

/-! ## The rule -/

variable {P : Address → Prop} {Good Gc : World → Prop} {C : Context → Prop} {Q : Machine → Prop}
  {m : Machine}

/-- **The untrusted `CALL` of a prefix, any gas, any outcome.** At a `CALL` to an unprotected
account from any frame, if the call-site invariant `Gc` (a `GoodOps` invariant) holds of the
world and of the world after an affordable value transfer to the callee, and the protected code
`CoversV` `Gc` (in contexts satisfying `C`, which `m`'s does) for every gas below the caller's,
then the caller continues from every machine
of its frame at `pc + 1` with one word pushed on `rest`, in a world satisfying `Gc`; a failure
of the instruction itself hands back the `Good` snapshot. -/
theorem pwp_call_v (S : GoodOps P Gc) (hC : C m.ctx)
    (hcov : ∀ g < m.frame.gasLeft, CoversV P Gc C g)
    {gas toW value inOff inSize outOff outSize : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx) (hto : ¬ P (Word.toAddress toW))
    (hI0 : Gc m.world)
    (hI : value ≠ 0 → value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat →
      Gc (moveEther m.world m.frame.msg.currentTarget (Word.toAddress toW) value))
    (k : ∀ m'', SameFrame m m'' → m''.frame.pc = m.frame.pc + 1 →
      (∃ x, m''.frame.stack = x :: rest) → Gc m''.world → WP m'' Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  have hdec : Opcode.decode m.ctx.fork 0xf1 = .call := by cases m.ctx.fork <;> rfl
  have hw := wp_and (wp_and (wp_and (wp_and (exec_frame .call m) (exec_strict .call m))
    (exec_world .call m)) (execCall_shape m)) (exec_eff .call m)
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
      exact WP.of_step hst hf.same (k m' hf.same hpc (shape_call hsh) hgood')
    | stop out => exact hsh.elim
    | revert out => exact hsh.elim
    | create msg => exact hsh.elim
    | call req =>
      have hst : step m = .running (launchCall m' req) := by rw [step_eq_of_code hcode, he]
      have hs' : m'.frame.gasLeft + req.msg.gas < m.frame.gasLeft := hs
      obtain ⟨hwm, ⟨t, v, ht1, hv1, htgt, hval⟩, hcaller, hstv⟩ := hsh
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
      rcases launchCall_cases m' req with ⟨r, w, t, hl, hw', -⟩ | hl <;> rw [hl] at hst
      · have hsf : SameFrame m (resume { m' with world := w, transient := t } r) :=
          (hf.same.trans (show SameFrame m' { m' with world := w, transient := t } from
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)).trans (sameFrame_resume _ _)
        obtain ⟨hrpc, ⟨x, hrst⟩, -⟩ := resume_frame { m' with world := w, transient := t } r
        refine WP.of_step hst hsf (k _ hsf ?_ ⟨x, ?_⟩ ?_)
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
        have hinv : Inv P Gc (pushCall m' req) := by
          refine ⟨htv, ⟨hgood', ?_, fun hk => by cases hk⟩, hpre'⟩
          intro hd
          exact hto (by rw [← htgt]; exact hd.1)
        have hlt : req.msg.gas < m.frame.gasLeft := by omega
        refine WP.call hst hpar hp
          (halts_inv_v S (hcov _ hlt) _ (show C m'.ctx by rw [hf.same.ctx]; exact hC)
            (Nat.le_of_eq (pushCall_gasLeft _ _)) hinv) ?_
        intro mf o hsf hgood
        have hsame : SameFrame m (resumeAfter m'.frame m.parents mf o) := by
          refine SameFrame.trans ?_ (sameFrame_resume _ _)
          exact ⟨hsf.ctx.trans hp.ctx, hsf.precompiles.trans hp.precompiles,
            hsf.originalWorld.trans hp.originalWorld, rfl, hp.msg, hp.code, hp.jumpDests, hp.kind,
            hp.snapshot⟩
        obtain ⟨hrpc, ⟨x, hrst⟩, -⟩ := resume_frame
          { mf with frame := m'.frame, parents := m.parents, world := (frameResult mf o).2.1,
                    transient := (frameResult mf o).2.2 } (frameResult mf o).1
        refine k _ hsame ?_ ⟨x, ?_⟩ hgood
        · show (resume _ _).frame.pc = _
          rw [hrpc]; exact congrArg (· + 1) hpc'
        · show (resume _ _).frame.stack = _
          rw [hrst]; exact congrArg (x :: ·) hstk'

/-! ## A stipend call, any outcome -/

theorem subCall_le (v g L mc e : Nat) :
    (Gas.messageCallGas v g L mc e).subCall ≤ g + (if v = 0 then 0 else Gas.callStipend) := by
  unfold Gas.messageCallGas
  dsimp only
  split
  · exact Nat.le_refl _
  · exact Nat.add_le_add_right (Nat.min_le_left _ _) _

set_option maxHeartbeats 1000000 in
/-- `CALL` pushes `0` when it fails softly, and gives the child at most its gas argument plus the
stipend when value moves. -/
theorem execCall_gas (m : Machine) : Wp (execCall .call) (fun a m' =>
    (a = .next → m'.frame.stack.head? = some 0) ∧
    ∀ req, a = .call req → ∃ g v, m.frame.stack[0]? = some g ∧ m.frame.stack[2]? = some v ∧
      req.msg.gas ≤ g.toNat + (if v.toNat = 0 then 0 else Gas.callStipend)) m := by
  simp [execCall, memoryExpansion, expandMemory, readMemory, setReturnData,
    genericCall] <;> intros <;> subst_vars <;> simp_all [subCall_le]

/-- A call answered by a precompile: the world after the transfer on success, before it on
failure. -/
theorem launchCall_precompile {m : Machine} {req : CallRequest} {a : Address}
    (h : precompileOf m.precompiles req.msg = some a) :
    ∃ r w t, launchCall m req = resume { m with world := w, transient := t } r ∧
      r.kind = .call req.retOffset req.retSize ∧
      (r.success = true → w = transferValue m.world req.msg) ∧
      (r.success = false → w = m.world) := by
  unfold launchCall runPrecompile
  simp only [h]
  split <;> refine ⟨_, _, _, rfl, rfl, ?_, ?_⟩ <;> intro hs <;>
    first | rfl | simp [ChildResult.success] at hs

/-- The flag a call pushes. -/
theorem resume_stack_call {M : Machine} {r : ChildResult} {o s : Nat} (hk : r.kind = .call o s) :
    (resume M r).frame.stack = (if r.success then 1 else 0) :: M.frame.stack := by
  unfold resume
  simp only [hk]

/-- The world a caller resumes in after a stipend call, by the flag `x` it finds. -/
def StipendWorld (m : Machine) (toW value x : Word) (w : World) : Prop :=
  (x = 0 → w = m.world) ∧
  (x ≠ 0 → value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat ∧
    w = if value = 0 then m.world
      else moveEther m.world m.frame.msg.currentTarget (Word.toAddress toW) value)

/-- **A stipend `CALL` of a prefix, any gas, any outcome.** At a `CALL` (any target, any code)
whose gas argument plus the stipend for a value transfer is at most `Gas.callStipend`, the caller
continues at `pc + 1` with a flag `x` on `rest`, in the world before the call (`x = 0`) or after
the affordable value transfer (`x ≠ 0`): the callee, and every frame it starts, changes no
world state. A failure of the instruction itself hands back the `Good` snapshot. -/
theorem pwp_call_stipend {gas toW value inOff inSize outOff outSize : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hlow : gas.toNat + (if value.toNat = 0 then 0 else Gas.callStipend) ≤ Gas.callStipend)
    (k : ∀ m'' x, SameFrame m m'' → m''.frame.pc = m.frame.pc + 1 →
      m''.frame.stack = x :: rest → StipendWorld m toW value x m''.world →
      WP m'' Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  have hdec : Opcode.decode m.ctx.fork 0xf1 = .call := by cases m.ctx.fork <;> rfl
  have hw := wp_and (wp_and (wp_and (wp_and (exec_frame .call m) (exec_world .call m))
    (execCall_shape m)) (exec_eff .call m)) (execCall_gas m)
  cases he : (exec (Opcode.decode m.ctx.fork 0xf1)).run m with
  | error e => exact wp_fail_of_error hsnap hcode he
  | ok p =>
    obtain ⟨a, m'⟩ := p
    have he' := he
    rw [hdec] at he'
    obtain ⟨⟨⟨⟨⟨hf, -⟩, -, ht⟩, hsh⟩, heff⟩, h0, hgreq⟩ := hw.of_run he'
    cases a with
    | next =>
      have hst := step_of_exec_next hcode he
      have hwm : m'.world = m.world := hsh
      obtain ⟨hpc, hshape⟩ := heff
      rw [hstk] at hshape
      obtain ⟨x, hx⟩ := shape_call hshape
      have hx0 : x = 0 := by have := h0 rfl; rw [hx] at this; simpa using this
      subst hx0
      exact WP.of_step hst hf.same (k m' 0 hf.same hpc hx
        ⟨fun _ => hwm, fun h => absurd rfl h⟩)
    | stop out => exact hsh.elim
    | revert out => exact hsh.elim
    | create msg => exact hsh.elim
    | call req =>
      have hst : step m = .running (launchCall m' req) := by rw [step_eq_of_code hcode, he]
      obtain ⟨hwm, ⟨t, v, ht1, hv1, htgt, hval⟩, hcaller, hstv⟩ := hsh
      obtain ⟨hpc', -, hstk'⟩ := heff
      obtain ⟨g, v', hg1, hv1', hgas⟩ := hgreq req rfl
      rw [hstk] at hstk' ht1 hv1 hg1 hv1'
      simp only [List.drop_succ_cons, List.drop_zero] at hstk'
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at ht1 hv1 hg1 hv1'
      subst ht1 hv1 hg1 hv1'
      have hlow' : req.msg.gas ≤ Gas.callStipend := Nat.le_trans hgas hlow
      -- the world after the value transfer, and its affordability
      have htv : transferValue m'.world req.msg =
          if value = 0 then m.world
          else moveEther m.world m.frame.msg.currentTarget (Word.toAddress toW) value := by
        unfold transferValue
        rw [hstv, hval, hwm, hcaller, htgt]
        by_cases hv : value = 0 <;> simp [hv]
      have haff : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat := by
        by_cases hv : value = 0
        · subst hv; exact Nat.zero_le _
        · have := (ht (by rw [hstv]) (by rw [hval]; exact hv)).2.1
          rwa [hwm, hcaller, hval] at this
      have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
        rw [hf.same.precompiles, hf.same.ctx]; exact hstd
      cases hpo : precompileOf m'.precompiles req.msg with
      | some pa =>
        obtain ⟨r, w, tr, hl, hk, hsucc, hfail⟩ := launchCall_precompile hpo
        rw [hl] at hst
        have hsf : SameFrame m (resume { m' with world := w, transient := tr } r) :=
          (hf.same.trans (show SameFrame m' { m' with world := w, transient := tr } from
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)).trans (sameFrame_resume _ _)
        obtain ⟨hrpc, -, -⟩ := resume_frame { m' with world := w, transient := tr } r
        refine WP.of_step hst hsf (k _ (if r.success then 1 else 0) hsf ?_ ?_ ?_)
        · rw [hrpc]; exact congrArg (· + 1) hpc'
        · rw [resume_stack_call hk]; exact congrArg _ hstk'
        · rw [resume_world]
          cases hs : r.success
          · exact ⟨fun _ => by rw [hfail hs, hwm], fun h => absurd rfl h⟩
          · exact ⟨fun h => absurd h (by decide), fun _ => ⟨haff, by rw [hsucc hs, htv]⟩⟩
      | none =>
        rw [EvmLogic.GasMono.launchCall_none hpo] at hst
        have hpar : (pushCall m' req).parents = m'.frame :: m.parents := by
          simp only [pushCall, hf.same.parents]
        have hp : SameFrame m { pushCall m' req with frame := m'.frame, parents := m.parents } :=
          ⟨hf.same.ctx, hf.same.precompiles, hf.same.originalWorld, rfl, hf.same.msg,
            hf.same.code, hf.same.jumpDests, hf.same.kind, hf.same.snapshot⟩
        refine WP.call hst hpar hp (halts_low _ hlow' (by simp only [pushCall]; exact hpre')) ?_
        intro mf o hsf hmf
        have hsame : SameFrame m (resumeAfter m'.frame m.parents mf o) := by
          refine SameFrame.trans ?_ (sameFrame_resume _ _)
          exact ⟨hsf.ctx.trans hp.ctx, hsf.precompiles.trans hp.precompiles,
            hsf.originalWorld.trans hp.originalWorld, rfl, hp.msg, hp.code, hp.jumpDests, hp.kind,
            hp.snapshot⟩
        have hkind : mf.frame.kind = .call req.retOffset req.retSize := hsf.kind
        obtain ⟨hrpc, -, -⟩ := resume_frame
          { mf with frame := m'.frame, parents := m.parents, world := (frameResult mf o).2.1,
                    transient := (frameResult mf o).2.2 } (frameResult mf o).1
        have hrk : (frameResult mf o).1.kind = .call req.retOffset req.retSize := by
          cases o <;> simp [frameResult, hkind]
        refine k _ (if (frameResult mf o).1.success then 1 else 0) hsame ?_ ?_ ?_
        · show (resume _ _).frame.pc = _
          rw [hrpc]; exact congrArg (· + 1) hpc'
        · show (resume _ _).frame.stack = _
          rw [resume_stack_call hrk]; exact congrArg _ hstk'
        · show StipendWorld m toW value _ (frameResult mf o).2.1
          cases o with
          | success out =>
            rw [frameResult_success_call hkind]
            refine ⟨fun h => absurd h (by simp [ChildResult.success]), fun _ => ⟨haff, ?_⟩⟩
            rw [hmf, ← htv]; rfl
          | revert out =>
            rw [frameResult_revert]
            refine ⟨fun _ => ?_, fun h => absurd (by simp [ChildResult.success]) h⟩
            rw [hsf.snapshot]; exact hwm
          | halt e =>
            rw [frameResult_halt]
            refine ⟨fun _ => ?_, fun h => absurd (by simp [ChildResult.success]) h⟩
            rw [hsf.snapshot]; exact hwm

end EvmLogic.Program.Reentrancy
