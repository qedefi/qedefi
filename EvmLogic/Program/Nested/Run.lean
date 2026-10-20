import EvmLogic.Program.Nested.Step

/-!
# Nested calls into protected accounts: a machine-level simulation

Only a *dangerous* frame (`Danger`: non-static, at a protected account in `P`) can write
protected storage. `processMessageCall_good`: if every dangerous frame that starts during a
top-level message call ends in a `Good` world (`hsum`, frame summaries), the call ends in a
`Good` world. The invariant `MInv` keeps every rollback snapshot `Good`, so a revert of any
enclosing frame restores a `Good` world (`docs/proving.md` §5).
-/

namespace EvmLogic.Program.Nested
open EvmLean EvmLean.Interpreter

variable {P : Address → Prop} {Good : World → Prop}

/-- Storage and code of every protected account are unchanged. -/
def KeepP (P : Address → Prop) (w w' : World) : Prop := ∀ p, P p → Keep p w w'

/-- What the simulation needs of `Good`. -/
structure GoodOk (P : Address → Prop) (Good : World → Prop) : Prop where
  /-- `Good` depends only on the storage and code of the protected accounts. -/
  keep : ∀ w w', Good w → KeepP P w w' → Good w'
  /-- Protected accounts hold code. -/
  code : ∀ w, Good w → ∀ p, P p → (w.code p).size ≠ 0
  /-- Their code is not an EIP-7702 delegation designator. -/
  deleg : ∀ w, Good w → ∀ p, P p → delegatedAddress? (w.code p) = none

/-- A frame that may write protected storage: non-static, at a protected account. -/
def Danger (P : Address → Prop) (f : Frame) : Prop := P f.msg.currentTarget ∧ f.msg.isStatic = false

/-- The invariant of every frame on the stack. -/
structure FrameInv (P : Address → Prop) (Good : World → Prop) (f : Frame) : Prop where
  /-- Its rollback snapshot is `Good`. -/
  snapshot : Good f.snapshot.1
  /-- It cannot write protected storage. -/
  safe : ¬ Danger P f
  /-- A creation frame does not create a protected account. -/
  create : f.kind = .create → ¬ P f.msg.currentTarget

/-- **The simulation invariant** of a machine whose executing frame is not dangerous. -/
structure MInv (P : Address → Prop) (Good : World → Prop) (G : Nat) (m : Machine) : Prop where
  /-- The current world is `Good`. -/
  world : Good m.world
  frame : FrameInv P Good m.frame
  parents : ∀ f ∈ m.parents, FrameInv P Good f
  gas : gasSum m ≤ G
  pre : m.precompiles = PrecompileImpl.standard m.ctx

/-- A machine that has just started a dangerous frame: what a frame summary may assume. -/
structure DangerStart (P : Address → Prop) (Good : World → Prop) (G : Nat) (m : Machine) :
    Prop where
  /-- A fresh message-call frame. -/
  fresh : ∃ o s, m.frame = Frame.init m.frame.msg (.call o s) m.frame.snapshot
  danger : Danger P m.frame
  /-- The world before the call (the rollback snapshot) is `Good`. -/
  snapshot : Good m.frame.snapshot.1
  /-- The current world differs from it only by a value transfer. -/
  keep : KeepP P m.frame.snapshot.1 m.world
  /-- The protected account's own code runs. -/
  code : m.frame.msg.code = m.world.code m.frame.msg.currentTarget
  target : m.frame.msg.target = some m.frame.msg.currentTarget
  codeAddress : m.frame.msg.codeAddress = some m.frame.msg.currentTarget
  /-- The caller is not protected. -/
  caller : ¬ P m.frame.msg.caller
  gas : m.frame.msg.gas ≤ G
  depth : m.frame.msg.depth ≤ Gas.stackDepthLimit
  /-- Standard precompiles. -/
  pre : m.precompiles = PrecompileImpl.standard m.ctx

/-! ## Worlds -/

theorem KeepP.trans {w₁ w₂ w₃ : World} (h₁ : KeepP P w₁ w₂) (h₂ : KeepP P w₂ w₃) :
    KeepP P w₁ w₃ := fun p hp => (h₁ p hp).trans (h₂ p hp)

theorem keepP_refl (w : World) : KeepP P w w := fun _ _ => keep_refl _ _

theorem GoodOk.transferValue (S : GoodOk P Good) {w : World} (hw : Good w) (msg : Message) :
    Good (Interpreter.transferValue w msg) :=
  S.keep _ _ hw fun p hp => keep_transferValue (S.code w hw p hp)

theorem keep_setCode {w : World} {a p : Address} {c : ByteArray} (h : p ≠ a) : Keep p w (setCode w a c) := by
  unfold setCode modifyState
  dsimp only
  split
  · refine ⟨?_, ?_⟩ <;> simp [World.account, Std.ExtTreeMap.getD_erase, Ne.symm h]
  · refine ⟨?_, ?_⟩ <;> simp [World.account, Std.ExtTreeMap.getD_insert, Ne.symm h]

theorem InstrFrame.good (S : GoodOk P Good) {m m' : Machine} (h : InstrFrame m m')
    (hsafe : ¬ Danger P m.frame) (hw : Good m.world) : Good m'.world :=
  S.keep _ _ hw fun p hp => h.keep p (S.code _ hw p hp) fun ⟨he, hs⟩ => hsafe ⟨he ▸ hp, hs⟩

theorem frameResult_good (S : GoodOk P Good) {m : Machine} (hf : FrameInv P Good m.frame)
    (hw : Good m.world) (o : Outcome) : Good (frameResult m o).2.1 := by
  rcases frameResult_world m o with h | ⟨hk, out, h⟩ | h <;> rw [h]
  · exact hw
  · refine S.keep _ _ hw fun p hp => keep_setCode ?_
    rintro rfl; exact hf.create hk hp
  · exact hf.snapshot

/-! ## One step -/

theorem FrameInv.of_same {f f' : Frame} (h : FrameInv P Good f) (hm : f'.msg = f.msg)
    (hs : f'.snapshot = f.snapshot) (hk : f'.kind = f.kind) : FrameInv P Good f' where
  snapshot := hs ▸ h.snapshot
  safe := by unfold Danger; rw [hm]; exact h.safe
  create := by rw [hk, hm]; exact h.create

/-- The outcome of one step from a machine satisfying the invariant. -/
inductive StepOut (P : Address → Prop) (Good : World → Prop) (G : Nat) : StepResult → Prop
  /-- The message finished in a `Good` world. -/
  | done {r : MessageResult} : Good r.world → StepOut P Good G (.done r)
  /-- Execution continues with the invariant. -/
  | inv {m : Machine} : MInv P Good G m → StepOut P Good G (.running m)
  /-- A dangerous frame was pushed on top of frames satisfying the invariant. -/
  | danger {m : Machine} {p : Frame} {ps : List Frame} : DangerStart P Good G m →
      m.parents = p :: ps → FrameInv P Good p → (∀ f ∈ ps, FrameInv P Good f) →
      gasSum m ≤ G → StepOut P Good G (.running m)

theorem finishFrame_out (S : GoodOk P Good) {G : Nat} {m : Machine} (hf : FrameInv P Good m.frame)
    (hps : ∀ f ∈ m.parents, FrameInv P Good f) (hw : Good m.world) (hgas : gasSum m ≤ G)
    (hpre : m.precompiles = PrecompileImpl.standard m.ctx) (o : Outcome) :
    StepOut P Good G (finishFrame m o) := by
  have hgood := frameResult_good S hf hw o
  have hg := finishFrame_gas m o
  rw [finishFrame_eq] at hg ⊢
  split
  · exact .done (by unfold topLevelResult; split <;> exact hgood)
  · rename_i p ps hp
    rw [hp] at hps hg
    refine .inv ⟨hgood, ?_, fun f hf' => hps f (List.mem_cons_of_mem _ hf'), ?_, hpre⟩
    · exact (hps p (List.mem_cons_self ..)).of_same rfl rfl rfl
    · exact Nat.le_trans hg hgas

/-- **One step preserves the simulation invariant**, or pushes a dangerous frame. -/
theorem minv_step (S : GoodOk P Good) {G : Nat} {m : Machine} (h : MInv P Good G m) :
    StepOut P Good G (step m) := by
  have hgas := step_gas (m := m) (by rw [h.pre]; exact precompilesOk_standard _)
  rcases step_cases m with ⟨m', o, he, hf⟩ | ⟨m', he, hf⟩ | ⟨m', req, he, hf, hc⟩ |
    ⟨m', msg, he, hf, hc⟩
  · rw [he] at hgas ⊢
    refine finishFrame_out S (h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind)
      (by rw [hf.same.parents]; exact h.parents) (hf.good S h.frame.safe h.world) ?_
      (by rw [hf.same.precompiles, hf.same.ctx]; exact h.pre) o
    have := hf.gas
    have hG := h.gas
    simp only [gasSum, hf.same.parents] at hG ⊢
    omega
  · rw [he] at hgas ⊢
    exact .inv ⟨hf.good S h.frame.safe h.world,
      h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind,
      by rw [hf.same.parents]; exact h.parents, Nat.le_trans hgas h.gas,
      by rw [hf.same.precompiles, hf.same.ctx]; exact h.pre⟩
  · rw [he] at hgas ⊢
    have hw' := hf.good S h.frame.safe h.world
    have hfr' := h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind
    have hps' : ∀ f ∈ m'.parents, FrameInv P Good f := by rw [hf.same.parents]; exact h.parents
    have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
      rw [hf.same.precompiles, hf.same.ctx]; exact h.pre
    rcases launchCall_cases m' req with ⟨r, w, t, hl, hw, -⟩ | hl <;> rw [hl] at hgas ⊢
    · refine .inv ⟨?_, ?_, hps', Nat.le_trans hgas h.gas, hpre'⟩
      · rcases hw with rfl | rfl
        · exact S.transferValue hw' _
        · exact hw'
      · exact hfr'.of_same rfl rfl rfl
    · have hg' : req.msg.gas ≤ G := by
        have h1 := h.gas
        unfold gasSum at h1
        simp only [resultGas, gasSum, pushCall, Frame.init, List.map_cons, List.sum_cons] at hgas
        omega
      by_cases hd : P req.msg.currentTarget ∧ req.msg.isStatic = false
      · obtain ⟨hst, hcur⟩ := hc.nonstatic hd.2
        have hne : req.msg.currentTarget ≠ m.frame.msg.currentTarget := by
          rintro he; exact h.frame.safe ⟨he ▸ hd.1, hst⟩
        obtain ⟨hcaller, hcode⟩ := hcur.resolve_left hne
        have hdel := S.deleg _ h.world _ hd.1
        obtain ⟨hcode, hca, -⟩ := hcode hdel
        have hkeep := hf.keep _ (S.code _ h.world _ hd.1) fun hwr => hne hwr.1
        refine .danger ⟨⟨_, _, rfl⟩, hd, hw', fun p hp => keep_transferValue (S.code _ hw' p hp),
          ?_, hc.target, hca, ?_, hg', hc.depthLe, hpre'⟩ rfl hfr' hps' (Nat.le_trans hgas h.gas)
        · show req.msg.code = (transferValue m'.world req.msg).code req.msg.currentTarget
          rw [(keep_transferValue (S.code _ hw' _ hd.1)).code, hkeep.code]; exact hcode
        · show ¬ P req.msg.caller
          rw [hcaller]; intro hp; exact h.frame.safe ⟨hp, hst⟩
      · refine .inv ⟨S.transferValue hw' _, ⟨hw', hd, fun hk => by cases hk⟩, ?_, Nat.le_trans hgas h.gas,
          by simp only [pushCall]; exact hpre'⟩
        intro f hf'
        rcases List.mem_cons.1 hf' with rfl | hf'
        · exact hfr'
        · exact hps' f hf'
  · rw [he] at hgas ⊢
    have hw' := hf.good S h.frame.safe h.world
    have hnp : ¬ P msg.currentTarget := fun hp => S.code _ hw' _ hp hc.code
    refine .inv ⟨?_, ⟨hw', fun hd => hnp hd.1, fun _ => hnp⟩, ?_, Nat.le_trans hgas h.gas, ?_⟩
    · simp only [launchCreate, beginCreate]
      refine S.keep _ _ hw' fun p hp => ?_
      have h1 := keep_incrementNonce (a := msg.currentTarget) (S.code _ hw' p hp)
      exact h1.trans (keep_transferValue (by rw [h1.code]; exact S.code _ hw' p hp))
    · intro f hf'
      simp only [launchCreate] at hf'
      rcases List.mem_cons.1 hf' with rfl | hf'
      · exact h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind
      · rw [hf.same.parents] at hf'; exact h.parents f hf'
    · simp only [launchCreate]; rw [hf.same.precompiles, hf.same.ctx]; exact h.pre

/-! ## Runs -/

theorem run_of_stepN_running {m m' : Machine} {n fuel : Nat} {r : MessageResult}
    (h : stepN n m = .running m') (hr : run fuel m = .ok r) :
    n < fuel ∧ run (fuel - n) m' = .ok r := by
  by_cases hle : fuel ≤ n
  · have hd := run_eq_ok_iff.1 hr
    have := stepN_add_of_done hd (n - fuel)
    rw [show fuel + (n - fuel) = n by omega, h] at this
    cases this
  · refine ⟨by omega, ?_⟩
    rw [← run_add_of_stepN h (fuel - n), show n + (fuel - n) = fuel by omega]
    exact hr

theorem run_of_stepN_done {m : Machine} {n fuel : Nat} {r r' : MessageResult}
    (h : stepN n m = .done r') (hr : run fuel m = .ok r) : r = r' := by
  have h1 := stepN_add_of_done (run_eq_ok_iff.1 hr) n
  have h2 := stepN_add_of_done h fuel
  rw [Nat.add_comm] at h2
  rw [h1] at h2
  cases h2; rfl

/-- **The simulation, for runs.** From a machine satisfying `MInv` reached from `m₀`, if every
dangerous frame reached with no dangerous parent ends in a `Good` world (`hsum`), every finished
run ends in a `Good` world. -/
theorem run_good (S : GoodOk P Good) {G : Nat} {m₀ : Machine}
    (hsum : ∀ n m, stepN n m₀ = .running m → DangerStart P Good G m →
      (∀ f ∈ m.parents, ¬ Danger P f) → Halts m (fun mf o => Good (frameResult mf o).2.1)) :
    ∀ fuel k m r, stepN k m₀ = .running m → MInv P Good G m → run fuel m = .ok r →
      Good r.world := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro k m r hk hm hr
    cases fuel with
    | zero => cases hr
    | succ f =>
      have hk1 : ∀ m', step m = .running m' → stepN (k + 1) m₀ = .running m' := fun m' hs => by
        rw [stepN_add_of_running hk 1, stepN_one, hs]
      have hout := minv_step S hm
      simp only [run] at hr
      revert hk1 hout hr
      cases hs : step m with
      | done r' =>
        intro hr _ hout
        cases hr
        cases hout with
        | done hg => exact hg
      | running m' =>
        intro hr hk1 hout
        cases hout with
        | inv hm' => exact ih f (by omega) (k + 1) m' r (hk1 m' rfl) hm' hr
        | danger hd hpar hp hps hgas =>
          have hsafe : ∀ f ∈ m'.parents, ¬ Danger P f := by
            rw [hpar]; intro f hf
            rcases List.mem_cons.1 hf with rfl | hf
            · exact hp.safe
            · exact (hps f hf).safe
          obtain ⟨n, mf, o, hH, hsf, hn⟩ := (hsum (k + 1) m' (hk1 m' rfl) hd hsafe).resume hpar
          obtain ⟨hlt, hr'⟩ := run_of_stepN_running hn hr
          have hgas' := stepN_gas (m := m') (by rw [hd.pre]; exact precompilesOk_standard _) n
          rw [hn] at hgas'
          refine ih (f - n) (by omega) (k + 1 + n) _ r ?_ ?_ hr'
          · rw [stepN_add_of_running (hk1 m' rfl) n, hn]
          · refine ⟨hH, hp.of_same rfl rfl rfl, hps, Nat.le_trans hgas' hgas, ?_⟩
            show mf.precompiles = PrecompileImpl.standard mf.ctx
            rw [hsf.precompiles, hsf.ctx]; exact hd.pre

/-- **The simulation, from a dangerous top-level frame.** -/
theorem run_good_top {m₀ : Machine} (hp : m₀.parents = [])
    (hH : Halts m₀ (fun mf o => Good (frameResult mf o).2.1)) {fuel : Nat} {r : MessageResult}
    (hr : run fuel m₀ = .ok r) : Good r.world := by
  obtain ⟨n, mf, o, hn, hsf, hg⟩ := hH
  rw [finishFrame_of_top o (hsf.parents.trans hp)] at hn
  rw [run_of_stepN_done hn hr]
  unfold topLevelResult
  split <;> exact hg

/-! ## Top-level message calls -/

theorem applyTopLevelDelegation_spec {ctx : Context} {isPre : Address → Bool} {w : World}
    {msg : Message} (h : ctx.fork < .prague ∨ ctx.tx.authorizations = []) :
    ∃ msg', applyTopLevelDelegation ctx isPre w msg = (w, msg', 0) ∧
      msg'.currentTarget = msg.currentTarget ∧ msg'.caller = msg.caller ∧
      msg'.target = msg.target ∧ msg'.depth = msg.depth ∧ msg'.isStatic = msg.isStatic ∧
      msg'.gas = msg.gas ∧ (delegatedAddress? msg.code = none → msg' = msg) := by
  unfold applyTopLevelDelegation
  split
  · exact ⟨msg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  · rename_i hf
    have hauth : ctx.tx.authorizations = [] := h.resolve_left hf
    split
    · exact ⟨msg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    · exact ⟨msg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    · simp only [hauth, List.isEmpty_nil, ite_true]
      split
      · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
      · rename_i d hd
        exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun h' => by rw [h'] at hd; cases hd⟩

/-- A top-level message the simulation covers: depth zero, an unprotected caller (a sender holds
no code, EIP-3607), a call or creation of `currentTarget`, running a protected account's own
code when calling one. -/
structure TopOk (P : Address → Prop) (w : World) (msg : Message) : Prop where
  depth : msg.depth = 0
  /-- The caller is not protected. -/
  caller : ¬ P msg.caller
  /-- A call to `currentTarget`, or a creation. -/
  target : msg.target = some msg.currentTarget ∨ msg.target = none
  /-- A call to a protected account runs its code. -/
  code : P msg.currentTarget → msg.target = some msg.currentTarget →
    msg.code = w.code msg.currentTarget ∧ msg.codeAddress = some msg.currentTarget

/-- The machine a top-level message call starts (after delegation and `initMachine`). -/
def StartsAt (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message)
    (m₀ : Machine) : Prop :=
  initMachine (PrecompileImpl.standard ctx) ctx (applyTopLevelDelegation ctx
    (PrecompileImpl.standard ctx).isPrecompile w msg).1 tr
    (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).2.1 = .inr m₀

/-- The machines reached by a top-level message call. -/
def Reaches (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) (m : Machine) :
    Prop :=
  ∃ m₀ n, StartsAt ctx w tr msg m₀ ∧ stepN n m₀ = .running m

theorem initMachine_out (S : GoodOk P Good) {G : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} (hw : Good w) (hmsg : TopOk P w msg)
    (hG : msg.gas ≤ G) :
    (∃ r, initMachine (PrecompileImpl.standard ctx) ctx w tr msg = .inl r ∧ Good r.world) ∨
    (∃ m₀, initMachine (PrecompileImpl.standard ctx) ctx w tr msg = .inr m₀ ∧
      (MInv P Good G m₀ ∨ (DangerStart P Good G m₀ ∧ m₀.parents = []))) := by
  unfold initMachine
  dsimp only
  split
  · exact .inl ⟨_, rfl, hw⟩
  split
  · exact .inl ⟨_, rfl, hw⟩
  split
  · rename_i hnone
    split
    · exact .inl ⟨_, rfl, hw⟩
    · rename_i hdep
      have hdep' : accountDeployable w msg.currentTarget = true := by simpa using hdep
      have hnp : ¬ P msg.currentTarget := fun hp =>
        S.code w hw _ hp (size_code_of_deployable hdep')
      refine .inr ⟨_, rfl, .inl ⟨?_, ⟨hw, fun hd => hnp hd.1, fun _ => hnp⟩, by simp, ?_, rfl⟩⟩
      · simp only [beginCreate]
        refine S.keep _ _ hw fun p hp => ?_
        have h1 := keep_incrementNonce (a := msg.currentTarget) (S.code _ hw p hp)
        exact h1.trans (keep_transferValue (by rw [h1.code]; exact S.code _ hw p hp))
      · simp [gasSum, Frame.init]; exact hG
  · rename_i a hsome
    have htgt : msg.target = some msg.currentTarget := by
      rcases hmsg.target with h | h
      · exact h
      · rw [hsome] at h; cases h
    split
    · rename_i pa _
      unfold runPrecompile
      dsimp only
      split
      · refine .inl ⟨_, rfl, ?_⟩
        unfold topLevelResult; split <;> exact S.transferValue hw _
      · refine .inl ⟨_, rfl, ?_⟩
        unfold topLevelResult; split <;> exact hw
    · by_cases hd : P msg.currentTarget ∧ msg.isStatic = false
      · obtain ⟨hcode, hca⟩ := hmsg.code hd.1 htgt
        refine .inr ⟨_, rfl, .inr ⟨⟨⟨0, 0, rfl⟩, hd, hw, fun p hp =>
          keep_transferValue (S.code _ hw p hp), ?_, htgt, hca, hmsg.caller, hG,
          by show msg.depth ≤ _; rw [hmsg.depth]; decide, rfl⟩, rfl⟩⟩
        show msg.code = (transferValue w msg).code msg.currentTarget
        rw [(keep_transferValue (S.code _ hw _ hd.1)).code]; exact hcode
      · refine .inr ⟨_, rfl, .inl ⟨S.transferValue hw _, ⟨hw, hd, fun h => by cases h⟩,
          by simp, by simp [gasSum, Frame.init]; exact hG, rfl⟩⟩

theorem stepN_consts {m m' : Machine} : ∀ {n}, stepN n m = .running m' →
    m'.ctx = m.ctx ∧ m'.precompiles = m.precompiles
  | 0, h => by cases h; exact ⟨rfl, rfl⟩
  | n + 1, h => by
    simp only [stepN] at h
    split at h
    · cases h
    · rename_i m₁ h₁
      have h2 := step_consts h₁
      have h3 := stepN_consts h
      exact ⟨h3.1.trans h2.1, h3.2.trans h2.2⟩

theorem Reaches.ctx {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    {m : Machine} (h : Reaches ctx w tr msg m) : m.ctx = ctx := by
  obtain ⟨m₀, n, hs, hn⟩ := h
  rw [(stepN_consts hn).1]
  unfold StartsAt initMachine at hs
  dsimp only at hs
  split at hs
  · cases hs
  split at hs
  · cases hs
  split at hs
  · split at hs
    · cases hs
    · cases hs; rfl
  · split at hs
    · cases hs
    · cases hs; rfl

/-- The bottom frame of the stack: the frame of the top-level message. -/
def bottom (m : Machine) : Frame := m.parents.getLast?.getD m.frame

theorem getLast?_cons_getD {α : Type} (a : α) (l : List α) (x : α) :
    (a :: l).getLast?.getD x = l.getLast?.getD a := by
  cases l with
  | nil => rfl
  | cons b l => simp [List.getLast?_cons]

theorem step_bottom {m m' : Machine} (h : step m = .running m') :
    (bottom m').msg = (bottom m).msg := by
  rcases step_cases m with ⟨m₁, o, he, hf⟩ | ⟨m₁, he, hf⟩ | ⟨m₁, req, he, hf, -⟩ |
    ⟨m₁, msg, he, hf, -⟩
  · rw [he, finishFrame_eq] at h
    split at h
    · cases h
    · rename_i p ps hp
      cases h
      have hpar : m.parents = p :: ps := hf.same.parents ▸ hp
      simp only [bottom, resumeAfter, resume_parents, hpar, getLast?_cons_getD]
      cases ps with
      | nil => rfl
      | cons q qs => rfl
  · rw [he] at h; cases h
    simp only [bottom, hf.same.parents]
    cases m.parents with
    | nil => exact hf.same.msg
    | cons q qs => rfl
  · rw [he] at h; cases h
    rcases launchCall_cases m₁ req with ⟨r, w, t, hl, -, -⟩ | hl <;> rw [hl]
    · simp only [bottom, resume_parents, hf.same.parents]
      cases hq : m.parents with
      | nil => exact hf.same.msg
      | cons q qs => rfl
    · simp only [bottom, pushCall, getLast?_cons_getD, hf.same.parents]
      cases m.parents with
      | nil => exact hf.same.msg
      | cons q qs => rfl
  · rw [he] at h; cases h
    simp only [bottom, launchCreate, getLast?_cons_getD, hf.same.parents]
    cases m.parents with
    | nil => exact hf.same.msg
    | cons q qs => rfl

theorem stepN_bottom {m m' : Machine} : ∀ {n}, stepN n m = .running m' →
    (bottom m').msg = (bottom m).msg
  | 0, h => by cases h; rfl
  | n + 1, h => by
    simp only [stepN] at h
    split at h
    · cases h
    · rename_i m₁ h₁
      exact (stepN_bottom h).trans (step_bottom h₁)

theorem Reaches.bottom {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    {m : Machine} (h : Reaches ctx w tr msg m) :
    (bottom m).msg =
      (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).2.1 := by
  obtain ⟨m₀, n, hs, hn⟩ := h
  rw [stepN_bottom hn]
  unfold StartsAt initMachine at hs
  dsimp only at hs
  split at hs
  · cases hs
  split at hs
  · cases hs
  split at hs
  · split at hs
    · cases hs
    · cases hs; rfl
  · split at hs
    · cases hs
    · cases hs; rfl

/-- **The simulation, for a top-level message call.** From a `Good` world, a `TopOk` message with
at most `G` gas, before Prague or without EIP-7702 authorizations, ends in a `Good` world,
provided every dangerous frame reached with no dangerous parent ends in a `Good` world (`hsum`). -/
theorem processMessageCall_good (S : GoodOk P Good) {G fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult} (hw : Good w)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hmsg : TopOk P w msg)
    (hG : msg.gas ≤ G)
    (hsum : ∀ m, Reaches ctx w tr msg m → DangerStart P Good G m →
      (∀ f ∈ m.parents, ¬ Danger P f) → Halts m (fun mf o => Good (frameResult mf o).2.1))
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Good r.world := by
  obtain ⟨msg', hd, hcur, hcaller, htarget, hdepth, hstatic, hgas, hsame⟩ :=
    applyTopLevelDelegation_spec (isPre := (PrecompileImpl.standard ctx).isPrecompile) (w := w)
      (msg := msg) hdeleg
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
  rcases initMachine_out (ctx := ctx) (tr := tr) S hw hmsg' (hgas ▸ hG) with
    ⟨r', hi, hg⟩ | ⟨m₀, hi, hm⟩ <;> rw [hi] at hr <;> dsimp only at hr
  · cases hr; exact hg
  · have hst : StartsAt ctx w tr msg m₀ := by unfold StartsAt; rw [hd]; exact hi
    cases hrun : run fuel m₀ with
    | error e => rw [hrun] at hr; cases hr
    | ok r' =>
      rw [hrun] at hr
      cases hr
      show Good r'.world
      rcases hm with hm | ⟨hm, hp⟩
      · exact run_good S (fun n m hn hd hs => hsum m ⟨m₀, n, hst, hn⟩ hd hs) fuel 0 m₀ r' rfl hm
          hrun
      · exact run_good_top hp (hsum m₀ ⟨m₀, 0, hst, rfl⟩ hm (by rw [hp]; simp)) hrun

end EvmLogic.Program.Nested
