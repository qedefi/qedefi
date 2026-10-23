import EvmLogic.Program.Nested.Guard

/-!
# Guarded message calls keep their own hypotheses

`processMessageCall_guard` concludes only the world invariant `G`. To chain guarded calls along
a sequence of transactions, the world a call leaves must again satisfy the call's other world
hypotheses: the relays hold their code and the idle accounts are idle (`GuardWorld`).
`processMessageCall_guard_world` adds both, from the same simulation invariant: every world and
rollback snapshot of every machine satisfies them, and a creation never deposits code at a relay
or at an idle account.
-/

namespace EvmLogic.Program.Nested
open EvmLean EvmLean.Interpreter EvmLogic.AbsInt EvmLogic.GasMono

/-- **The world hypotheses of a guarded call**: the world invariant, the relays' code, and idle
accounts idle. -/
def GuardWorld (Rl : Address → Prop) (C : Address → ByteArray) (X : Address → Prop)
    (G : World → Prop) (w : World) : Prop :=
  G w ∧ RelayCode Rl C w ∧ IdleW X w

variable {Rl : Address → Prop} {C : Address → ByteArray} {X : Address → Prop} {G : World → Prop}
  {Iss : Address → Machine → Message → Prop} {J : Address → Machine → Prop}

/-- **The last step**: a finished top-level frame leaves a world satisfying `GuardWorld`. -/
theorem guardTxInv_done_world (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w') (hJ : ∀ r, Rl r → GuardInv Rl C X G Iss r (J r))
    {m : Machine} {r : MessageResult} (h : GuardTxInv Rl C X G J m) (hst : step m = .done r) :
    GuardWorld Rl C X G r.world := by
  cases hx : exitOf m with
  | none =>
    rcases step_of_exitOf_none hx with ⟨m', hs, -⟩ | ⟨m', req, hs, -⟩ | ⟨m', msg, hs, -⟩ <;>
      rw [hs] at hst <;> cases hst
  | some p =>
    obtain ⟨mf, o⟩ := p
    obtain ⟨hst', hif⟩ := step_of_exitOf hx
    have hmf : GuardWorld Rl C X G mf.world := by
      rcases exitOf_cases hx with rfl | ⟨b, a, hb, he⟩
      · exact ⟨h.good.1, h.relay.world, h.idle.1⟩
      · exact instr_good hC hG hJ h hb he
    have hcr : mf.frame.kind = .create → ¬ Rl mf.frame.msg.currentTarget := by
      rw [hif.same.kind, hif.same.msg]; exact h.relay.create _ List.mem_cons_self
    have hcx : mf.frame.kind = .create → ¬ X mf.frame.msg.currentTarget := by
      rw [hif.same.kind, hif.same.msg]; exact h.createIdle _ List.mem_cons_self
    have hsnap : GuardWorld Rl C X G m.frame.snapshot.1 :=
      ⟨h.good.2 _ List.mem_cons_self, h.relay.snapshots _ List.mem_cons_self,
        h.idle.2 _ List.mem_cons_self⟩
    have hgr : GuardWorld Rl C X G (Program.frameResult mf o).2.1 :=
      frameResult_P o hmf (hif.same.snapshot ▸ hsnap) fun out hk =>
        ⟨hG _ _ hmf.1 fun r hr => keep_setCode fun he => hcr hk (he ▸ hr),
          fun r hr => by
            have hne : r ≠ mf.frame.msg.currentTarget := fun he => hcr hk (he ▸ hr)
            rw [code_setCode_ne (Ne.symm hne)]; exact hmf.2.1 r hr,
          hmf.2.2.setCode (hcx hk)⟩
    rw [hst', finishFrame_eq] at hst
    split at hst
    · cases hst
      unfold topLevelResult
      split <;> exact hgr
    · cases hst

/-- From a machine satisfying the invariant, every finished run ends in a world satisfying
`GuardWorld`. -/
theorem guard_run_world (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInv Rl C X G Iss r (J r)) :
    ∀ (fuel : Nat) {m : Machine} {r : MessageResult}, GuardTxInv Rl C X G J m →
      run fuel m = .ok r → GuardWorld Rl C X G r.world
  | 0, _, _, _, hr => by cases hr
  | fuel + 1, m, r, h, hr => by
    simp only [run] at hr
    cases hs : step m with
    | done r' => rw [hs] at hr; cases hr; exact guardTxInv_done_world hC hG hJ h hs
    | running m' =>
      rw [hs] at hr; exact guard_run_world hC hG hJ fuel (guardTxInv_step hC hG hJ h hs) hr

/-- A top-level message call that runs no code leaves its world, or its world after the value
transfer. -/
theorem initMachine_inl_world {pre : PrecompileImpl} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (h : initMachine pre ctx w tr msg = .inl r) : r.world = w ∨ r.world = transferValue w msg := by
  unfold initMachine at h
  dsimp only at h
  split at h
  · cases h; exact .inl rfl
  split at h
  · cases h; exact .inl rfl
  split at h
  · split at h
    · cases h; exact .inl rfl
    · cases h
  · split at h
    · cases h
      unfold runPrecompile
      dsimp only
      split <;> unfold topLevelResult <;> split <;> simp
    · cases h

/-- **A guarded message call keeps its world hypotheses**: `processMessageCall_guard`, with the
relays' code and the idleness of idle accounts in the world it ends in. -/
theorem processMessageCall_guard_world (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w') (hJ : ∀ r, Rl r → GuardInv Rl C X G Iss r (J r))
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    (hw : GuardWorld Rl C X G w) (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : GuardTop Rl X w msg) {fuel : Nat} {r : MessageResult}
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : GuardWorld Rl C X G r.world := by
  obtain ⟨hg, hrc, hi⟩ := hw
  obtain ⟨msg', hdl, hmsg'⟩ := guardTop_delegation
    (isPre := (PrecompileImpl.standard ctx).isPrecompile) hC hrc hdeleg hmsg
  unfold processMessageCall processMessageCallWith at hr
  rw [hdl] at hr
  dsimp only at hr
  cases hin : initMachine (PrecompileImpl.standard ctx) ctx w tr msg' with
  | inl r' =>
    rw [hin] at hr
    cases hr
    show GuardWorld Rl C X G r'.world
    rcases initMachine_inl_world hin with he | he <;> rw [he]
    · exact ⟨hg, hrc, hi⟩
    · exact ⟨((goodC_ok hC hG).transferValue ⟨hg, hrc⟩ msg').1,
        hrc.congr (code_transferValue _ _),
        hi.congr (code_transferValue _ _) (nonce_transferValue _ _)⟩
  | inr m₀ =>
    rw [hin] at hr
    dsimp only at hr
    cases hrun : run fuel m₀ with
    | error e => rw [hrun] at hr; cases hr
    | ok r' =>
      rw [hrun] at hr
      cases hr
      show GuardWorld Rl C X G r'.world
      exact guard_run_world hC hG hJ fuel (guardTxInv_start hC hG hJ hrc hg hi hmsg' hin) hrun

end EvmLogic.Program.Nested
