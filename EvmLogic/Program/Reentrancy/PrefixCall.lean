import EvmLogic.Program.Reentrancy.Value
import EvmLogic.Program.Reentrancy.PrefixOps
import EvmLogic.AbsInt.Frame

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

end EvmLogic.Program.Reentrancy
