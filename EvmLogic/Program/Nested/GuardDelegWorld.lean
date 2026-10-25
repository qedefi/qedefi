import EvmLogic.Program.Nested.GuardDeleg

/-!
# Guarded calls of any transaction keep their own hypotheses, and create no idle account

To chain guarded message calls of transactions with EIP-7702 authorizations, two facts are added
to `GuardDeleg.lean`:

* `processMessageCall_guardD_world_7702`: a guarded call with doomed frames
  (`EvmLogic.Program.Nested.Sandbox`) ends in a world satisfying `GuardWorld`: the world
  invariant, the relays' code and the idleness of the idle accounts (as
  `processMessageCall_guard_world_7702` for `GuardInv`). Both come from `SandCommon`, which every
  machine of the simulation satisfies, doomed regions included.
* `reaches_createIdle_7702`, `reaches_createIdleD_7702`: no creation frame of any machine the call
  reaches is at an idle account (`GuardTxInv.createIdle`, `SandCommon.createIdle`). With
  `EvmLogic.Tx.processMessageCall_not_deleted`, the call then schedules no idle account for
  deletion, so the transaction's suffix keeps it idle.
-/

namespace EvmLogic.Program.Nested
open EvmLean EvmLean.Interpreter EvmLogic.AbsInt EvmLogic.GasMono EvmLogic.Program

variable {Rl : Address → Prop} {C : Address → ByteArray} {X : Address → Prop} {G : World → Prop}
  {Iss : Address → Machine → Message → Prop} {J : Address → Machine → Prop} {K : Context → Prop}
  {R : Machine → Prop} {Dm : Address → Machine → Prop}

/-! ## Doomed frames: the world hypotheses -/

/-- **The last step**, with doomed frames: a finished top-level frame leaves a world satisfying
`GuardWorld`. -/
theorem sandInv_done_world (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvD K Rl C X G R Iss (Dm r) r (J r)) {m : Machine}
    {r : MessageResult} (h : SandInv K Rl C X G J m) (hR : R m) (hst : step m = .done r) :
    GuardWorld Rl C X G r.world := by
  refine ⟨sandInv_done hC hG hJ h hR hst, ?_⟩
  have hcm := h.common
  cases hx : exitOf m with
  | none =>
    rcases step_of_exitOf_none hx with ⟨m', hs, -⟩ | ⟨m', req, hs, -⟩ | ⟨m', msg, hs, -⟩ <;>
      rw [hs] at hst <;> cases hst
  | some p =>
    obtain ⟨mf, o⟩ := p
    obtain ⟨hst', hif⟩ := step_of_exitOf hx
    have hmf : RelayCode Rl C mf.world ∧ IdleW X mf.world := by
      rcases exitOf_cases hx with rfl | ⟨b, a, hb, he⟩
      · exact ⟨hcm.world, hcm.idle.1⟩
      · have hcode : SameCode m.world mf.world := (exec_code _ m).of_run he
        have hn : NonceLe m.world mf.world := (exec_nonce _ m).of_run he
        exact ⟨hcm.world.congr hcode, hcm.idle.1.congr hcode hn⟩
    have hcr : mf.frame.kind = .create → ¬ Rl mf.frame.msg.currentTarget := by
      rw [hif.same.kind, hif.same.msg]; exact hcm.create _ List.mem_cons_self
    have hcx : mf.frame.kind = .create → ¬ X mf.frame.msg.currentTarget := by
      rw [hif.same.kind, hif.same.msg]; exact hcm.createIdle _ List.mem_cons_self
    have hsnap : RelayCode Rl C m.frame.snapshot.1 ∧ IdleW X m.frame.snapshot.1 :=
      ⟨hcm.snapshots _ List.mem_cons_self, hcm.idle.2 _ List.mem_cons_self⟩
    have hgr : RelayCode Rl C (Program.frameResult mf o).2.1 ∧
        IdleW X (Program.frameResult mf o).2.1 :=
      frameResult_P (P := fun w => RelayCode Rl C w ∧ IdleW X w) o hmf
        (hif.same.snapshot ▸ hsnap) fun out hk =>
        ⟨fun r hr => by
            have hne : r ≠ mf.frame.msg.currentTarget := fun he => hcr hk (he ▸ hr)
            rw [code_setCode_ne (Ne.symm hne)]; exact hmf.1 r hr,
          hmf.2.setCode (hcx hk)⟩
    rw [hst', finishFrame_eq] at hst
    split at hst
    · cases hst
      unfold topLevelResult
      split <;> exact hgr
    · cases hst

/-- From a machine satisfying the invariant, a finished run whose machines satisfy `R` ends in
a world satisfying `GuardWorld`. -/
theorem sandInv_run_world (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvD K Rl C X G R Iss (Dm r) r (J r)) {m₀ : Machine}
    (hR : ∀ n m, stepN n m₀ = .running m → R m) :
    ∀ (fuel n : Nat) {m : Machine} {r : MessageResult}, stepN n m₀ = .running m →
      SandInv K Rl C X G J m → run fuel m = .ok r → GuardWorld Rl C X G r.world
  | 0, _, _, _, _, _, hr => by cases hr
  | fuel + 1, n, m, r, hn, h, hr => by
    simp only [run] at hr
    cases hs : step m with
    | done r' => rw [hs] at hr; cases hr; exact sandInv_done_world hC hG hJ h (hR n m hn) hs
    | running m' =>
      rw [hs] at hr
      refine sandInv_run_world hC hG hJ hR fuel (n + 1) ?_
        (sandInv_step hC hG hJ h (hR n m hn) hs) hr
      rw [stepN_add_of_running hn 1, stepN_one, hs]

/-- Every machine reached from a machine satisfying the invariant, through machines satisfying
`R`, satisfies it. -/
theorem sandInv_stepN (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvD K Rl C X G R Iss (Dm r) r (J r)) {m₀ : Machine}
    (h₀ : SandInv K Rl C X G J m₀) (hR : ∀ n m, stepN n m₀ = .running m → R m) :
    ∀ (n : Nat) {m : Machine}, stepN n m₀ = .running m → SandInv K Rl C X G J m
  | 0, m, hn => by simp only [stepN_zero, StepResult.running.injEq] at hn; exact hn ▸ h₀
  | n + 1, m, hn => by
    rw [stepN_succ'] at hn
    cases hs : stepN n m₀ with
    | done r => rw [hs] at hn; cases hn
    | running m' =>
      rw [hs] at hn
      exact sandInv_step hC hG hJ (sandInv_stepN hC hG hJ h₀ hR n hs) (hR n m' hs) hn

/-- **A guarded message call with doomed frames, of any transaction, keeps its world
hypotheses**: `processMessageCall_guardD_7702` with the relays' code and the idleness of idle
accounts in the world it ends in. -/
theorem processMessageCall_guardD_world_7702 (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvD K Rl C X G R Iss (Dm r) r (J r))
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    (hw : GuardWorld Rl C X G w) (hauth : IdleNoAuth X ctx)
    (hca : X msg.currentTarget → msg.target = some msg.currentTarget →
      msg.codeAddress = some msg.currentTarget)
    (hmsg : GuardTop Rl X w msg) (hR : ∀ m, Reaches ctx w tr msg m → R m) {fuel : Nat}
    {r : MessageResult} (hr : processMessageCall fuel ctx w tr msg = .ok r)
    (hK : K ctx := by trivial) : GuardWorld Rl C X G r.world := by
  obtain ⟨hg, hrc, hi⟩ := hw
  have S := goodC_ok hC hG
  have hw' := hrc.deleg hC ctx (PrecompileImpl.standard ctx).isPrecompile msg
  have hg' := (S.deleg_world ctx (PrecompileImpl.standard ctx).isPrecompile msg ⟨hg, hrc⟩).1
  have hi' := hi.deleg hauth (PrecompileImpl.standard ctx).isPrecompile msg
  have hmsg' := guardTop_delegation_7702 (isPre := (PrecompileImpl.standard ctx).isPrecompile)
    hC hrc hi hauth hca hmsg
  have hst : ∀ m₀, initMachine (PrecompileImpl.standard ctx) ctx
      (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).1 tr
      (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).2.1 =
        .inr m₀ → StartsAt ctx w tr msg m₀ := fun _ h => h
  unfold processMessageCall processMessageCallWith at hr
  generalize applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg = d
    at hw' hg' hi' hmsg' hst hr
  obtain ⟨w', msg', refund⟩ := d
  dsimp only at hw' hg' hi' hmsg' hst hr
  cases hin : initMachine (PrecompileImpl.standard ctx) ctx w' tr msg' with
  | inl r' =>
    rw [hin] at hr
    cases hr
    show GuardWorld Rl C X G r'.world
    rcases initMachine_inl_world hin with he | he <;> rw [he]
    · exact ⟨hg', hw', hi'⟩
    · exact ⟨(S.transferValue ⟨hg', hw'⟩ msg').1,
        hw'.congr (code_transferValue _ _),
        hi'.congr (code_transferValue _ _) (nonce_transferValue _ _)⟩
  | inr m₀ =>
    rw [hin] at hr
    dsimp only at hr
    cases hrun : run fuel m₀ with
    | error e => rw [hrun] at hr; cases hr
    | ok r' =>
      rw [hrun] at hr
      cases hr
      show GuardWorld Rl C X G r'.world
      have hs := hst m₀ hin
      exact sandInv_run_world hC hG hJ (fun n m hn => hR m ⟨m₀, n, hs, hn⟩) fuel 0 rfl
        (sandInv_start hC hG hJ hw' hg' hi' hmsg' hin hK) hrun

/-! ## No creation at an idle account -/

/-- **No creation frame of a guarded call of any transaction is at an idle account**: every
machine the call reaches satisfies `GuardTxInv`, whose `createIdle` says so. -/
theorem reaches_createIdle_7702 (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w') (hJ : ∀ r, Rl r → GuardInvK K Rl C X G Iss r (J r))
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} (hw : RelayCode Rl C w)
    (hg : G w) (hi : IdleW X w) (hauth : IdleNoAuth X ctx)
    (hca : X msg.currentTarget → msg.target = some msg.currentTarget →
      msg.codeAddress = some msg.currentTarget)
    (hmsg : GuardTop Rl X w msg) (hK : K ctx := by trivial) {m : Machine}
    (hm : Reaches ctx w tr msg m) :
    ∀ f ∈ m.frame :: m.parents, f.kind = .create → ¬ X f.msg.currentTarget := by
  have S := goodC_ok hC hG
  have hw' := hw.deleg hC ctx (PrecompileImpl.standard ctx).isPrecompile msg
  have hg' := (S.deleg_world ctx (PrecompileImpl.standard ctx).isPrecompile msg ⟨hg, hw⟩).1
  have hi' := hi.deleg hauth (PrecompileImpl.standard ctx).isPrecompile msg
  have hmsg' := guardTop_delegation_7702 (isPre := (PrecompileImpl.standard ctx).isPrecompile)
    hC hw hi hauth hca hmsg
  obtain ⟨m₀, n, hs, hn⟩ := hm
  unfold StartsAt at hs
  exact (guardTxInv_stepN hC hG hJ n (guardTxInv_start hC hG hJ hw' hg' hi' hmsg' hs hK)
    hn).createIdle

/-- **No creation frame of a guarded call with doomed frames, of any transaction, is at an idle
account**: every machine the call reaches satisfies `SandInv`, whose `SandCommon.createIdle`
says so. -/
theorem reaches_createIdleD_7702 (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvD K Rl C X G R Iss (Dm r) r (J r))
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} (hw : RelayCode Rl C w)
    (hg : G w) (hi : IdleW X w) (hauth : IdleNoAuth X ctx)
    (hca : X msg.currentTarget → msg.target = some msg.currentTarget →
      msg.codeAddress = some msg.currentTarget)
    (hmsg : GuardTop Rl X w msg) (hR : ∀ m, Reaches ctx w tr msg m → R m)
    (hK : K ctx := by trivial) {m : Machine} (hm : Reaches ctx w tr msg m) :
    ∀ f ∈ m.frame :: m.parents, f.kind = .create → ¬ X f.msg.currentTarget := by
  have S := goodC_ok hC hG
  have hw' := hw.deleg hC ctx (PrecompileImpl.standard ctx).isPrecompile msg
  have hg' := (S.deleg_world ctx (PrecompileImpl.standard ctx).isPrecompile msg ⟨hg, hw⟩).1
  have hi' := hi.deleg hauth (PrecompileImpl.standard ctx).isPrecompile msg
  have hmsg' := guardTop_delegation_7702 (isPre := (PrecompileImpl.standard ctx).isPrecompile)
    hC hw hi hauth hca hmsg
  obtain ⟨m₀, n, hs, hn⟩ := hm
  have hs' := hs
  unfold StartsAt at hs'
  exact (sandInv_stepN hC hG hJ (sandInv_start hC hG hJ hw' hg' hi' hmsg' hs' hK)
    (fun k m hk => hR m ⟨m₀, k, hs, hk⟩) n hn).common.createIdle

end EvmLogic.Program.Nested
