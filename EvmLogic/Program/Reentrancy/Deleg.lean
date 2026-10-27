import EvmLogic.Program.Reentrancy.Value
import EvmLogic.Program.Nested.Deleg

/-!
# The havoc theorems for any transaction, EIP-7702 authorizations included

`processMessageCall_covers`, `processMessageCall_good_e` and `processMessageCall_good_v` assume
`ctx.fork < .prague ∨ ctx.tx.authorizations = []`. Their `_7702` versions here drop it. An
authorization sets the code of an account holding empty code or a designator, then bumps its
nonce (`EvmLogic.Program.Delegation`); a `GoodOps` invariant is closed under both, since such an
account is not protected (`GoodOps.deleg_world`). The message keeps every field the simulation
reads, and a call to a protected account still runs its own code (`TopOk.delegate`).
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested EvmLogic.AbsInt

variable {P : Address → Prop} {Good : World → Prop} {C : Context → Prop}

/-- An account an authorization may rewrite is not protected in a `GoodOps` world. -/
theorem GoodOps.not_delegable (S : GoodOps P Good) {w : World} (hw : Good w) {a : Address}
    (ha : Delegable (w.code a)) : ¬ P a := fun hp => by
  rcases ha with ha | ha
  · exact S.code w hw a hp ha
  · rw [delegatedAddress?_eq_none.1 (S.deleg w hw a hp)] at ha; cases ha

/-- **A `GoodOps` invariant holds of the delegated world.** -/
theorem GoodOps.deleg_world (S : GoodOps P Good) (ctx : Context) (isPre : Address → Bool)
    {w : World} (msg : Message) (hw : Good w) :
    Good (applyTopLevelDelegation ctx isPre w msg).1 :=
  applyTopLevelDelegation_induct ctx isPre msg Good
    (fun _ _ _ hw ha _ => S.nonce _ _ (S.setCode _ _ _ hw (S.not_delegable hw ha))) hw

/-- `processMessageCall_covers` for any transaction: no restriction on the fork or on EIP-7702
authorizations. -/
theorem processMessageCall_covers_7702 (S : GoodOk P Good) {fuel : Nat} {ctx : Context}
    {w : World} {tr : TransientStorage} {msg : Message} {r : MessageResult} (hw : Good w)
    (hmsg : TopOk P w msg) (hcov : Covers P Good msg.gas)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Good r.world :=
  processMessageCall_good_7702 S hw hmsg (Nat.le_refl _) (fun m _ hd _ => hcov m hd) hr

/-- **Any top-level message call of any transaction keeps a `GoodOps` invariant** when the
protected code `CoversE` it for its gas: `processMessageCall_good_e` without
`ctx.fork < .prague ∨ ctx.tx.authorizations = []`. -/
theorem processMessageCall_good_e_7702 (S : GoodOps P Good) {fuel : Nat} {ctx : Context}
    {w : World} {tr : TransientStorage} {msg : Message} {r : MessageResult} (hw : Good w)
    (hmsg : TopOk P w msg) (hcov : CoversE P Good msg.gas)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Good r.world := by
  have hw' := S.deleg_world ctx (PrecompileImpl.standard ctx).isPrecompile msg hw
  have hmsg' := hmsg.delegate (ctx := ctx) (isPre := (PrecompileImpl.standard ctx).isPrecompile)
    (fun p hp => S.deleg _ hw' p hp)
  have hgas := (applyTopLevelDelegation_frame ctx (PrecompileImpl.standard ctx).isPrecompile w
    msg).2.2.2.2.2.2.1
  unfold processMessageCall processMessageCallWith at hr
  generalize applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg = d
    at hw' hmsg' hgas hr
  obtain ⟨w', msg', refund⟩ := d
  dsimp only at hw' hmsg' hgas hr
  rcases initMachine_out_e (ctx := ctx) (tr := tr) S hw' hmsg' with
    ⟨r', hi, hg⟩ | ⟨m₀, hi, hpar, hg0, hm⟩ <;> rw [hi] at hr <;> dsimp only at hr
  · cases hr; exact hg
  · have hH : Halts m₀ (fun mf o => Good (frameResult mf o).2.1) := by
      rcases hm with hm | hm
      · exact halts_inv_e S hcov _ (by rw [hg0, hgas]; exact Nat.le_refl _) hm
      · exact hcov _ (by rw [← hgas]; exact hm)
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

/-- **Any top-level message call of any transaction that transfers its value keeps a `GoodOps`
invariant** when the protected code `CoversV` it for its gas: `processMessageCall_good_v`
without `ctx.fork < .prague ∨ ctx.tx.authorizations = []`. -/
theorem processMessageCall_good_v_7702 (S : GoodOps P Good) {fuel : Nat} {ctx : Context}
    {w : World} {tr : TransientStorage} {msg : Message} {r : MessageResult} (hw : Good w)
    (hmsg : TopOk P w msg) (hv : msg.shouldTransferValue = true) (hC : C ctx)
    (hcov : CoversV P Good C msg.gas)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Good r.world := by
  have hw' := S.deleg_world ctx (PrecompileImpl.standard ctx).isPrecompile msg hw
  have hmsg' := hmsg.delegate (ctx := ctx) (isPre := (PrecompileImpl.standard ctx).isPrecompile)
    (fun p hp => S.deleg _ hw' p hp)
  have hF := applyTopLevelDelegation_frame ctx (PrecompileImpl.standard ctx).isPrecompile w msg
  have hgas := hF.2.2.2.2.2.2.1
  have hv' := hF.2.2.2.2.2.2.2.2.1.trans hv
  unfold processMessageCall processMessageCallWith at hr
  generalize applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg = d
    at hw' hmsg' hgas hv' hr
  obtain ⟨w', msg', refund⟩ := d
  dsimp only at hw' hmsg' hgas hv' hr
  rcases initMachine_out_e (ctx := ctx) (tr := tr) S hw' hmsg' with
    ⟨r', hi, hg⟩ | ⟨m₀, hi, hpar, hg0, hm⟩ <;> rw [hi] at hr <;> dsimp only at hr
  · cases hr; exact hg
  · have hH : Halts m₀ (fun mf o => Good (frameResult mf o).2.1) := by
      rcases hm with hm | hm
      · exact halts_inv_v S (hcov.mono (Nat.le_of_eq hgas)) _
          (by rw [(initMachine_msg hi).2]; exact hC) (by rw [hg0]; exact Nat.le_refl _) hm
      · refine hcov _ ⟨by rw [← hgas]; exact hm, ?_, ?_⟩
        · rw [(initMachine_msg hi).1]; exact hv'
        · rw [(initMachine_msg hi).2]; exact hC
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
