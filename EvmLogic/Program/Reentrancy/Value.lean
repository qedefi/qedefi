import EvmLogic.Program.Reentrancy.Ether
import EvmLogic.AbsInt.Effect

/-!
# Dangerous frames that received their value

`DStart` (`EvmLogic.Program.Reentrancy.Ether`) records the value transfer that started a
dangerous frame, but not that the transfer happened: a message with `shouldTransferValue = false`
(a `DELEGATECALL`'s) carries a `CALLVALUE` that moved no ether. A payable function that credits
`msg.value` (a bank's `deposit()`) is only correct when the ether arrived. This module adds that
fact:

* `exec_value`: a requested child that runs at another account than its caller's frame, and is
  not static, moves its value (`shouldTransferValue = true`): only `CALL` does that.
* `DStartV`, `CoversV`: dangerous frame starts whose value moved, and their summaries.
* `halts_inv_v`: the havoc theorem with `CoversV` summaries.
* `processMessageCall_good_v`: any top-level message call that transfers its value keeps a
  `GoodOps` invariant when the protected code `CoversV` it.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested EvmLogic.AbsInt

variable {P : Address → Prop} {Good : World → Prop}

/-! ## Calls to another account move their value -/

/-- A requested non-static child running at another account than the requesting frame's
transfers its value. -/
def CallValue (m : Machine) (req : CallRequest) : Prop :=
  req.msg.isStatic = false → req.msg.currentTarget ≠ m.frame.msg.currentTarget →
    req.msg.shouldTransferValue = true

set_option maxHeartbeats 1000000 in
/-- `exec_value` for the `CALL` family. -/
theorem execCall_value (k : CallKind) (m : Machine) :
    Wp (execCall k) (fun a _ => ∀ req, a = .call req → CallValue m req) m := by
  cases k <;> simp [CallValue, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall] <;> intros <;> simp_all

/-- **Every requested call to another account transfers its value.** -/
theorem exec_value (op : Opcode) (m : Machine) :
    Wp (exec op) (fun a _ => ∀ req, a = .call req → CallValue m req) m := by
  cases op
  case call => exact execCall_value .call m
  case callcode => exact execCall_value .callcode m
  case delegatecall => exact execCall_value .delegatecall m
  case staticcall => exact execCall_value .staticcall m
  all_goals exact (exec_eff _ m).mono fun a m' h req ha =>
    False.elim (absurd (ha ▸ h) (by simp [EffPost, CallPost, effOf]))

/-- `step_full` with `CallValue` for a requested call. -/
theorem step_value (m : Machine) :
    (∃ m' o, step m = finishFrame m' o ∧ InstrFrame m m' ∧ WorldStep m m'.world) ∨
    (∃ m', step m = .running m' ∧ InstrFrame m m' ∧ m'.frame.gasLeft < m.frame.gasLeft ∧
      WorldStep m m'.world) ∨
    (∃ m' req, step m = .running (launchCall m' req) ∧ InstrFrame m m' ∧ CallOk m m' req ∧
      m'.frame.gasLeft + req.msg.gas < m.frame.gasLeft ∧ WorldStep m m'.world ∧
      TransferOk m (.call req) m' ∧ CallValue m req) ∨
    (∃ m' msg, step m = .running (launchCreate m' msg) ∧ InstrFrame m m' ∧ CreateOk m m' msg ∧
      m'.frame.gasLeft + msg.gas < m.frame.gasLeft ∧ m.frame.msg.isStatic = false ∧
      TransferOk m (.create msg) m') := by
  unfold step
  dsimp only
  split
  · have hw := wp_and (wp_and (wp_and (exec_frame (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m)
      (exec_strict (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m))
      (exec_world (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m))
      (exec_value (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m)
    split
    · exact .inl ⟨m, _, rfl, .refl m, .inl rfl⟩
    · rename_i m' h
      obtain ⟨⟨⟨⟨hf, -⟩, hs, -⟩, hw, -⟩, -⟩ := hw.of_run h
      exact .inr (.inl ⟨m', rfl, hf, hs, hw⟩)
    · rename_i out m' h
      obtain ⟨⟨⟨⟨hf, -⟩, -, -⟩, hw, -⟩, -⟩ := hw.of_run h
      exact .inl ⟨m', _, rfl, hf, hw⟩
    · rename_i out m' h
      obtain ⟨⟨⟨⟨hf, -⟩, -, -⟩, hw, -⟩, -⟩ := hw.of_run h
      exact .inl ⟨m', _, rfl, hf, hw⟩
    · rename_i req m' h
      obtain ⟨⟨⟨⟨hf, hc⟩, hs, -⟩, hw, ht⟩, hv⟩ := hw.of_run h
      exact .inr (.inr (.inl ⟨m', req, rfl, hf, hc, hs, hw, ht, hv req rfl⟩))
    · rename_i msg m' h
      obtain ⟨⟨⟨⟨hf, hc⟩, ⟨hs, hst⟩, -⟩, -, ht⟩, -⟩ := hw.of_run h
      exact .inr (.inr (.inr ⟨m', msg, rfl, hf, hc, hs, hst, ht⟩))
  · exact .inl ⟨m, _, rfl, .refl m, .inl rfl⟩

/-! ## Dangerous frames whose value moved -/

/-- A dangerous frame start (`DStart`) whose message transferred its value. -/
structure DStartV (P : Address → Prop) (Good : World → Prop) (G : Nat) (m : Machine) : Prop
    extends DStart P Good G m where
  /-- The value moved (`CALL` or a value-transferring top-level message). -/
  transfers : m.frame.msg.shouldTransferValue = true

/-- **Frame summaries for dangerous frames whose value moved**: every such frame with at most
`G` gas, started from a `Good` snapshot with any parents, ends in a `Good` world. -/
def CoversV (P : Address → Prop) (Good : World → Prop) (G : Nat) : Prop :=
  ∀ m, DStartV P Good G m → Halts m (fun mf o => Good (frameResult mf o).2.1)

/-- `CoversV` by induction on gas: reentrant frames have less gas than their ancestors. -/
theorem coversV_of_lt (h : ∀ G, (∀ G' < G, CoversV P Good G') → CoversV P Good G) (G : Nat) :
    CoversV P Good G := by
  induction G using Nat.strongRecOn with
  | ind G ih => exact h G ih

/-- `CoversV` for more gas gives `CoversV` for less. -/
theorem CoversV.mono {G G' : Nat} (h : CoversV P Good G) (hle : G' ≤ G) : CoversV P Good G' :=
  fun m hd => h m { hd with gas := Nat.le_trans hd.gas hle }

/-- `CoversE` gives `CoversV`. -/
theorem CoversE.coversV {G : Nat} (h : CoversE P Good G) : CoversV P Good G :=
  fun m hd => h m hd.toDStart

/-- The child of a call requested by a frame satisfying `Inv`: a `DStartV` or an `Inv` frame. -/
theorem child_cases_v (S : GoodOps P Good) {G : Nat} {m m' : Machine} {req : CallRequest}
    (h : Inv P Good m) (hf : InstrFrame m m') (hc : CallOk m m' req) (hw' : Good m'.world)
    (ht : TransferOk m (.call req) m') (hv : CallValue m req) (hg : req.msg.gas ≤ G) :
    DStartV P Good G (pushCall m' req) ∨ Inv P Good (pushCall m' req) := by
  rcases child_cases_e S h hf hc hw' ht hg with hd | hi
  · refine .inl ⟨hd, ?_⟩
    show req.msg.shouldTransferValue = true
    have hd' := hd.danger
    have hst : req.msg.isStatic = false := hd'.2
    have hne : req.msg.currentTarget ≠ m.frame.msg.currentTarget := by
      rintro he
      exact h.frame.safe ⟨he ▸ hd'.1, (hc.nonstatic hst).1⟩
    exact hv hst hne
  · exact .inr hi

/-! ## The havoc theorem -/

/-- **The havoc theorem with `CoversV` summaries.** Under `CoversV` for its gas, a frame
satisfying `Inv` halts in a `Good` world, whatever code it and its descendants run. -/
theorem halts_inv_v (S : GoodOps P Good) {G : Nat} (hcov : CoversV P Good G) :
    ∀ m, m.frame.gasLeft ≤ G → Inv P Good m →
      Halts m (fun mf o => Good (frameResult mf o).2.1) := by
  suffices ∀ n m, m.frame.gasLeft = n → n ≤ G → Inv P Good m →
      Halts m (fun mf o => Good (frameResult mf o).2.1) from fun m hg h => this _ m rfl hg h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hn hG h
    have ih' : ∀ m'', m''.frame.gasLeft < m.frame.gasLeft → Inv P Good m'' →
        Halts m'' (fun mf o => Good (frameResult mf o).2.1) :=
      fun m'' hlt hi => ih _ (hn ▸ hlt) m'' rfl (by omega) hi
    rcases step_value m with ⟨m', o, he, hf, hws⟩ | ⟨m', he, hf, hs, hws⟩ |
      ⟨m', req, he, hf, hc, hs, hws, ht, hv⟩ | ⟨m', msg, he, hf, hc, hs, hst, ht⟩
    · exact Halts.of_step he hf.same
        (S.frameResult (h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind)
          (S.step h.world h.frame.safe hws) o)
    · refine Halts.of_steps (Steps.of_step he hf.same) (ih' m' hs ?_)
      exact ⟨S.step h.world h.frame.safe hws,
        h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind,
        by rw [hf.same.precompiles, hf.same.ctx]; exact h.pre⟩
    · have hw' := S.step h.world h.frame.safe hws
      have hfr' := h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind
      have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
        rw [hf.same.precompiles, hf.same.ctx]; exact h.pre
      rcases launchCall_cases m' req with ⟨r, w, t, hl, hw, hr⟩ | hl <;> rw [hl] at he
      · have hr' := hr (by rw [hpre']; exact precompilesOk_standard _)
        have hsf : SameFrame m (resume { m' with world := w, transient := t } r) :=
          (hf.same.trans (show SameFrame m' { m' with world := w, transient := t } from
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)).trans (sameFrame_resume _ _)
        refine Halts.of_steps (Steps.of_step he hsf) (ih' _ ?_ ?_)
        · simp only [resume_gasLeft]; omega
        · refine ⟨?_, hfr'.of_same rfl rfl rfl, hpre'⟩
          rcases hw with rfl | rfl
          · exact transfer_of_ok S h hw' ht
          · exact hw'
      · have hpar : (pushCall m' req).parents = m'.frame :: m.parents := by
          simp only [pushCall, hf.same.parents]
        have hcallee : Halts (pushCall m' req) (fun mf o => Good (frameResult mf o).2.1) := by
          rcases child_cases_v (G := G) S h hf hc hw' ht hv (by omega) with hd | hi
          · exact hcov _ hd
          · exact ih' _ (by rw [pushCall_gasLeft]; omega) hi
        refine halts_resume he hpar ⟨hf.same.ctx, hf.same.precompiles, hf.same.originalWorld,
          rfl, hf.same.msg, hf.same.code, hf.same.jumpDests, hf.same.kind, hf.same.snapshot⟩
          (by simp only [pushCall]; rw [hpre']; exact precompilesOk_standard _) hcallee ?_
        intro mf o hsf hgood hgas
        refine ih' _ ?_ (Inv.of_resume hfr' hgood ?_)
        · rw [pushCall_gasLeft] at hgas; omega
        · rw [hsf.precompiles, hsf.ctx]; exact hpre'
    · obtain ⟨hcaller, hbal, hw0⟩ := ht
      have hnp : ¬ P m.frame.msg.currentTarget := fun hp => h.frame.safe ⟨hp, hst⟩
      have hw' : Good m'.world := by rw [hw0]; exact S.nonce _ _ h.world
      have hfr' := h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind
      have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
        rw [hf.same.precompiles, hf.same.ctx]; exact h.pre
      have hnpc : ¬ P msg.currentTarget := fun hp => S.code _ hw' _ hp hc.code
      have hpar : (launchCreate m' msg).parents = m'.frame :: m.parents := by
        simp only [launchCreate, hf.same.parents]
      have hcallee : Halts (launchCreate m' msg) (fun mf o => Good (frameResult mf o).2.1) := by
        refine ih' _ (by rw [launchCreate_gasLeft]; omega) ⟨?_, ⟨hw', ?_, ?_⟩, ?_⟩
        · simp only [launchCreate, beginCreate]
          refine S.transfer (S.nonce _ _ hw') fun _ _ => ⟨?_, .inl (hcaller ▸ hnp)⟩
          rw [balance_incrementNonce, hw0, balance_incrementNonce, hcaller]
          rw [hcaller] at hbal; exact hbal
        · exact fun hd => hnpc hd.1
        · exact fun _ => hnpc
        · simp only [launchCreate]; exact hpre'
      refine halts_resume he hpar ⟨hf.same.ctx, hf.same.precompiles, hf.same.originalWorld,
        rfl, hf.same.msg, hf.same.code, hf.same.jumpDests, hf.same.kind, hf.same.snapshot⟩
        (by simp only [launchCreate]; rw [hpre']; exact precompilesOk_standard _) hcallee ?_
      intro mf o hsf hgood hgas
      refine ih' _ ?_ (Inv.of_resume hfr' hgood ?_)
      · rw [launchCreate_gasLeft] at hgas; omega
      · rw [hsf.precompiles, hsf.ctx]; exact hpre'

/-! ## Any transaction -/

/-- `applyTopLevelDelegation` keeps whether the message transfers its value. -/
theorem applyTopLevelDelegation_transfers (ctx : Context) (isPre : Address → Bool) (w : World)
    (msg : Message) :
    (applyTopLevelDelegation ctx isPre w msg).2.1.shouldTransferValue =
      msg.shouldTransferValue := by
  unfold applyTopLevelDelegation
  split
  · rfl
  · split
    · rfl
    · rfl
    · dsimp only
      split <;> dsimp only <;> split <;> rfl

/-- A machine started by `initMachine` runs the message it was given. -/
theorem initMachine_msg {pre : PrecompileImpl} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {m₀ : Machine}
    (h : initMachine pre ctx w tr msg = .inr m₀) : m₀.frame.msg = msg := by
  unfold initMachine at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    · cases h; rfl
  · split at h
    · cases h
    · cases h; rfl

/-- **Any top-level message call that transfers its value keeps a `GoodOps` invariant** when
the protected code `CoversV` it for its gas (callbacks at any depth included): from a `Good`
world, a `TopOk` message with `shouldTransferValue = true` (any code, value, calldata; an
unprotected caller), before Prague or without EIP-7702 authorizations. -/
theorem processMessageCall_good_v (S : GoodOps P Good) {fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult} (hw : Good w)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hmsg : TopOk P w msg)
    (hv : msg.shouldTransferValue = true) (hcov : CoversV P Good msg.gas)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Good r.world := by
  obtain ⟨msg', hd, hcur, hcaller, htarget, hdepth, hstatic, hgas, hsame⟩ :=
    applyTopLevelDelegation_spec (isPre := (PrecompileImpl.standard ctx).isPrecompile) (w := w)
      (msg := msg) hdeleg
  have hv' : msg'.shouldTransferValue = true := by
    have := applyTopLevelDelegation_transfers ctx (PrecompileImpl.standard ctx).isPrecompile w msg
    rw [hd] at this; rw [this]; exact hv
  have hmsg' : TopOk P w msg' := by
    refine ⟨hdepth.trans hmsg.depth, hcaller ▸ hmsg.caller, ?_, fun hp ht => ?_⟩
    · rw [htarget, hcur]; exact hmsg.target
    · rw [hcur] at hp ht ⊢
      rw [htarget] at ht
      obtain ⟨hc, hca⟩ := hmsg.code hp ht
      have := hsame (by rw [hc]; exact S.deleg w hw _ hp)
      subst this
      exact ⟨hc, hca⟩
  unfold processMessageCall processMessageCallWith at hr
  rw [hd] at hr
  dsimp only at hr
  rcases initMachine_out_e (ctx := ctx) (tr := tr) S hw hmsg' with
    ⟨r', hi, hg⟩ | ⟨m₀, hi, hpar, hg0, hm⟩ <;> rw [hi] at hr <;> dsimp only at hr
  · cases hr; exact hg
  · have hH : Halts m₀ (fun mf o => Good (frameResult mf o).2.1) := by
      rcases hm with hm | hm
      · exact halts_inv_v S (hcov.mono (Nat.le_of_eq hgas)) _
          (by rw [hg0]; exact Nat.le_refl _) hm
      · refine hcov _ ⟨by rw [← hgas]; exact hm, ?_⟩
        rw [initMachine_msg hi]; exact hv'
    obtain ⟨n, mf, o, hgood, hsf, hrun⟩ := hH.run hpar
    cases hrun' : run fuel m₀ with
    | error e => rw [hrun'] at hr; cases hr
    | ok r' =>
      rw [hrun'] at hr
      cases hr
      have h1 := run_mono hrun' (Nat.le_max_left fuel n)
      rw [hrun (max fuel n) (Nat.le_max_right fuel n)] at h1
      cases h1
      show Good (topLevelResult _ _ _ _).world
      unfold topLevelResult; split <;> exact hgood

end EvmLogic.Program.Reentrancy
