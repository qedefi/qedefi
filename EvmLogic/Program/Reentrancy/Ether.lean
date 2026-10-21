import EvmLogic.Program.Reentrancy.World
import EvmLogic.Program.Reentrancy.Havoc
import EvmLogic.State

/-!
# The havoc theorem for invariants that mention ether balances

`halts_inv` needs `GoodOk`: `Good` may only depend on protected storage and code. An invariant
such as a bank's solvency (`Σ balances ≤ address(this).balance`) also depends on ether balances,
which arbitrary code changes (it can send ether to the bank). `GoodOps` replaces `GoodOk` by
closure under every world change a non-dangerous frame can make (`exec_world`): a storage write
at an unprotected account, a nonce increment, an affordable ether transfer out of an unprotected
account (or from an account to itself), zeroing an unprotected account's balance, code deposited
at an unprotected account. Dangerous frames start with `DStart`, which also records the value
transfer that started them.

* `halts_inv_e`: the havoc theorem for `GoodOps` (frame summaries `CoversE`).
* `WP.call_havoc_e`: the rely–guarantee rule at an untrusted `CALL`.
* `processMessageCall_good_e`: any top-level message call keeps `Good`.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested

variable {P : Address → Prop} {Good : World → Prop}

/-! ## Balances -/

theorem balance_incrementNonce (w : World) (a b : Address) :
    (incrementNonce w a).balance b = w.balance b := by
  unfold incrementNonce
  rw [balance_modifyState]
  split
  · subst_vars; rfl
  · rfl

/-! ## Closure under the world changes of arbitrary code -/

/-- **What the ether-aware simulation needs of `Good`**: protected accounts hold code that is no
EIP-7702 delegation, and `Good` is closed under every world change a frame that is not dangerous
can make. -/
structure GoodOps (P : Address → Prop) (Good : World → Prop) : Prop where
  /-- Protected accounts hold code. -/
  code : ∀ w, Good w → ∀ p, P p → (w.code p).size ≠ 0
  /-- Their code is not an EIP-7702 delegation designator. -/
  deleg : ∀ w, Good w → ∀ p, P p → delegatedAddress? (w.code p) = none
  /-- A storage write at an unprotected account. -/
  sstore : ∀ w a k v, Good w → ¬ P a → Good (w.sstore a k v)
  /-- A nonce increment. -/
  nonce : ∀ w a, Good w → Good (incrementNonce w a)
  /-- An affordable ether transfer out of an unprotected account, or to itself. -/
  move : ∀ w src dst v, Good w → v.toNat ≤ (w.balance src).toNat → (¬ P src ∨ dst = src) →
    Good (moveEther w src dst v)
  /-- Zeroing an unprotected account's balance (`SELFDESTRUCT` of an account created in the
  transaction, after its ether moved). -/
  burn : ∀ w a, Good w → ¬ P a → Good (setAccountBalance w a 0)
  /-- Code deposited at an unprotected account. -/
  setCode : ∀ w a c, Good w → ¬ P a → Good (setCode w a c)

/-- A `GoodOps` invariant is closed under a value transfer that `TransferOk` allows. -/
theorem GoodOps.transfer (S : GoodOps P Good) {w : World} {msg : Message} (hw : Good w)
    (h : msg.shouldTransferValue = true → msg.value ≠ 0 →
      msg.value.toNat ≤ (w.balance msg.caller).toNat ∧
      (¬ P msg.caller ∨ msg.currentTarget = msg.caller)) :
    Good (transferValue w msg) := by
  unfold transferValue
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hb, hp⟩ := h hc.1 hc.2
    exact S.move _ _ _ _ hw hb hp
  · exact hw

/-- One instruction of a frame that is not dangerous keeps a `GoodOps` invariant. -/
theorem GoodOps.step (S : GoodOps P Good) {m : Machine} {w' : World} (hw : Good m.world)
    (hsafe : ¬ Danger P m.frame) (h : WorldStep m w') : Good w' := by
  rcases h with rfl | ⟨hst, h⟩
  · exact hw
  have hnp : ¬ P m.frame.msg.currentTarget := fun hp => hsafe ⟨hp, hst⟩
  rcases h with ⟨k, v, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact S.sstore _ _ _ _ hw hnp
  · exact S.nonce _ _ hw
  · exact S.move _ _ _ _ hw (Nat.le_refl _) (.inl hnp)
  · exact S.burn _ _ (S.move _ _ _ _ hw (Nat.le_refl _) (.inl hnp)) hnp

/-- The end of a frame keeps a `GoodOps` invariant. -/
theorem GoodOps.frameResult (S : GoodOps P Good) {m : Machine} (hf : FrameInv P Good m.frame)
    (hw : Good m.world) (o : Outcome) : Good (frameResult m o).2.1 := by
  rcases frameResult_world m o with h | ⟨hk, out, h⟩ | h <;> rw [h]
  · exact hw
  · exact S.setCode _ _ _ hw (hf.create hk)
  · exact hf.snapshot

/-! ## One step, with strict gas and world effects -/

/-- `step_strict` with the world effects of `exec_world`. -/
theorem step_full (m : Machine) :
    (∃ m' o, step m = finishFrame m' o ∧ InstrFrame m m' ∧ WorldStep m m'.world) ∨
    (∃ m', step m = .running m' ∧ InstrFrame m m' ∧ m'.frame.gasLeft < m.frame.gasLeft ∧
      WorldStep m m'.world) ∨
    (∃ m' req, step m = .running (launchCall m' req) ∧ InstrFrame m m' ∧ CallOk m m' req ∧
      m'.frame.gasLeft + req.msg.gas < m.frame.gasLeft ∧ WorldStep m m'.world ∧
      TransferOk m (.call req) m') ∨
    (∃ m' msg, step m = .running (launchCreate m' msg) ∧ InstrFrame m m' ∧ CreateOk m m' msg ∧
      m'.frame.gasLeft + msg.gas < m.frame.gasLeft ∧ m.frame.msg.isStatic = false ∧
      TransferOk m (.create msg) m') := by
  unfold step
  dsimp only
  split
  · have hw := wp_and (wp_and (exec_frame (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m)
      (exec_strict (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m))
      (exec_world (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m)
    split
    · exact .inl ⟨m, _, rfl, .refl m, .inl rfl⟩
    · rename_i m' h
      obtain ⟨⟨⟨hf, -⟩, hs, -⟩, hw, -⟩ := hw.of_run h
      exact .inr (.inl ⟨m', rfl, hf, hs, hw⟩)
    · rename_i out m' h
      obtain ⟨⟨⟨hf, -⟩, -, -⟩, hw, -⟩ := hw.of_run h
      exact .inl ⟨m', _, rfl, hf, hw⟩
    · rename_i out m' h
      obtain ⟨⟨⟨hf, -⟩, -, -⟩, hw, -⟩ := hw.of_run h
      exact .inl ⟨m', _, rfl, hf, hw⟩
    · rename_i req m' h
      obtain ⟨⟨⟨hf, hc⟩, hs, -⟩, hw, ht⟩ := hw.of_run h
      exact .inr (.inr (.inl ⟨m', req, rfl, hf, hc, hs, hw, ht⟩))
    · rename_i msg m' h
      obtain ⟨⟨⟨hf, hc⟩, ⟨hs, hst⟩, -⟩, -, ht⟩ := hw.of_run h
      exact .inr (.inr (.inr ⟨m', msg, rfl, hf, hc, hs, hst, ht⟩))
  · exact .inl ⟨m, _, rfl, .refl m, .inl rfl⟩

/-! ## Dangerous frames and their summaries -/

/-- A dangerous frame start that also records the value transfer that started it: the world is
the snapshot after `transferValue`, which was affordable. -/
structure DStart (P : Address → Prop) (Good : World → Prop) (G : Nat) (m : Machine) : Prop
    extends DangerStart P Good G m where
  /-- The world is the snapshot after the value transfer. -/
  world_eq : m.world = transferValue m.frame.snapshot.1 m.frame.msg
  /-- The value transfer was affordable. -/
  afford : m.frame.msg.shouldTransferValue = true → m.frame.msg.value ≠ 0 →
    m.frame.msg.value.toNat ≤ (m.frame.snapshot.1.balance m.frame.msg.caller).toNat

/-- **Frame summaries for `GoodOps` invariants**: every dangerous frame with at most `G` gas,
started (`DStart`) from a `Good` snapshot with any parents, ends in a `Good` world. -/
def CoversE (P : Address → Prop) (Good : World → Prop) (G : Nat) : Prop :=
  ∀ m, DStart P Good G m → Halts m (fun mf o => Good (frameResult mf o).2.1)

/-- `CoversE` by induction on gas: reentrant frames have less gas than their ancestors. -/
theorem coversE_of_lt (h : ∀ G, (∀ G' < G, CoversE P Good G') → CoversE P Good G) (G : Nat) :
    CoversE P Good G := by
  induction G using Nat.strongRecOn with
  | ind G ih => exact h G ih

/-- `CoversE` for more gas gives `CoversE` for less. -/
theorem CoversE.mono {G G' : Nat} (h : CoversE P Good G) (hle : G' ≤ G) : CoversE P Good G' :=
  fun m hd => h m { hd with gas := Nat.le_trans hd.gas hle }

/-- The value transfer of a call requested by a frame satisfying `Inv` keeps a `GoodOps`
invariant. -/
theorem transfer_of_ok (S : GoodOps P Good) {m m' : Machine} {req : CallRequest}
    (h : Inv P Good m) (hw' : Good m'.world) (ht : TransferOk m (.call req) m') :
    Good (transferValue m'.world req.msg) := by
  refine S.transfer hw' fun h1 h2 => ?_
  obtain ⟨hcaller, hb, hst⟩ := ht h1 h2
  refine ⟨hb, ?_⟩
  rcases hst with hst | hst
  · left; rw [hcaller]; exact fun hp => h.frame.safe ⟨hp, hst⟩
  · right; exact hst

/-- The child of a call requested by a frame satisfying `Inv`: a `DStart` or an `Inv` frame. -/
theorem child_cases_e (S : GoodOps P Good) {G : Nat} {m m' : Machine} {req : CallRequest}
    (h : Inv P Good m) (hf : InstrFrame m m') (hc : CallOk m m' req) (hw' : Good m'.world)
    (ht : TransferOk m (.call req) m') (hg : req.msg.gas ≤ G) :
    DStart P Good G (pushCall m' req) ∨ Inv P Good (pushCall m' req) := by
  have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
    rw [hf.same.precompiles, hf.same.ctx]; exact h.pre
  have htr := transfer_of_ok S h hw' ht
  by_cases hd : P req.msg.currentTarget ∧ req.msg.isStatic = false
  · obtain ⟨hst, hcur⟩ := hc.nonstatic hd.2
    have hne : req.msg.currentTarget ≠ m.frame.msg.currentTarget := by
      rintro he; exact h.frame.safe ⟨he ▸ hd.1, hst⟩
    obtain ⟨hcaller, hcode⟩ := hcur.resolve_left hne
    have hdel := S.deleg _ h.world _ hd.1
    obtain ⟨hcode, hca, -⟩ := hcode hdel
    have hcodeP : ∀ p, P p → (m'.world.code p).size ≠ 0 := fun p hp => S.code _ hw' p hp
    have hkeep : Keep req.msg.currentTarget m.world m'.world :=
      hf.keep _ (S.code _ h.world _ hd.1) fun hwr => hne hwr.1
    refine .inl ⟨⟨⟨_, _, rfl⟩, hd, hw', fun p hp => keep_transferValue (hcodeP p hp),
      ?_, hc.target, hca, ?_, hg, hc.depthLe, hpre'⟩, rfl, fun h1 h2 => (ht h1 h2).2.1⟩
    · show req.msg.code = (transferValue m'.world req.msg).code req.msg.currentTarget
      rw [(keep_transferValue (hcodeP _ hd.1)).code, hkeep.code]; exact hcode
    · show ¬ P req.msg.caller
      rw [hcaller]; intro hp; exact h.frame.safe ⟨hp, hst⟩
  · exact .inr ⟨htr, ⟨hw', hd, fun hk => by cases hk⟩, hpre'⟩

/-! ## The havoc theorem -/

/-- **The havoc theorem for `GoodOps` invariants.** Under `CoversE` for its gas, a frame satisfying
`Inv` halts in a `Good` world, whatever code it and its descendants run. -/
theorem halts_inv_e (S : GoodOps P Good) {G : Nat} (hcov : CoversE P Good G) :
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
    rcases step_full m with ⟨m', o, he, hf, hws⟩ | ⟨m', he, hf, hs, hws⟩ |
      ⟨m', req, he, hf, hc, hs, hws, ht⟩ | ⟨m', msg, he, hf, hc, hs, hst, ht⟩
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
          rcases child_cases_e (G := G) S h hf hc hw' ht (by omega) with hd | hi
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

/-! ## The rule at an untrusted `CALL` -/

/-- **Rely–guarantee at an untrusted `CALL`, for `GoodOps` invariants.** At a `CALL` to an
unprotected account (any code, any affordable value) from a protected frame, in a world
satisfying the call-site invariant `Good`, with `CoversE` for the child's gas, the caller
continues from every return whose world is `Good`. -/
theorem WP.call_havoc_e (S : GoodOps P Good) {G : Nat} (hcov : CoversE P Good G)
    {m : Machine} {gas toW value inOff inSize outOff outSize : Word} {rest : List Word}
    {Q : Machine → Prop} {H : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas value (Word.toAddress toW) (createCost m.world value (Word.toAddress toW))
      (transferCost value) inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hstatic : m.frame.msg.isStatic = false ∨ value = 0)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hto : ¬ P (Word.toAddress toW))
    (hI : Good (moveEther m.world m.frame.msg.currentTarget (Word.toAddress toW) value))
    (hI0 : Good m.world)
    (hG : (callChild m gas toW value inOff inSize outOff outSize rest).frame.gasLeft ≤ G)
    (k : ∀ mf o, SameFrame (callChild m gas toW value inOff inSize outOff outSize rest) mf →
      Good (frameResult mf o).2.1 →
      WP (resumeAfter (callCaller m gas toW value inOff inSize outOff outSize rest) m.parents mf o)
        Q H) :
    WP m Q H := by
  refine WP.call (step_callChild hcode hstk hdel hgas hstatic hbal hdepth hpre) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (halts_inv_e S hcov _ hG ⟨?_, ⟨hI0, fun hd => hto hd.1, fun hk => by cases hk⟩, hstd⟩) k
  show Good (transferValue m.world _)
  unfold transferValue
  split
  · exact hI
  · exact hI0

/-! ## Any transaction -/

/-- The start of a top-level message for a `GoodOps` invariant: a result in a `Good` world, or a
machine satisfying `Inv`, or a top-level `DStart`. -/
theorem initMachine_out_e (S : GoodOps P Good) {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} (hw : Good w) (hmsg : TopOk P w msg) :
    (∃ r, initMachine (PrecompileImpl.standard ctx) ctx w tr msg = .inl r ∧ Good r.world) ∨
    (∃ m₀, initMachine (PrecompileImpl.standard ctx) ctx w tr msg = .inr m₀ ∧ m₀.parents = [] ∧
      m₀.frame.gasLeft = msg.gas ∧ (Inv P Good m₀ ∨ DStart P Good msg.gas m₀)) := by
  unfold initMachine
  dsimp only
  split
  · exact .inl ⟨_, rfl, hw⟩
  rename_i hdep
  split
  · exact .inl ⟨_, rfl, hw⟩
  rename_i hfund
  have hafford : msg.shouldTransferValue = true → msg.value ≠ 0 →
      msg.value.toNat ≤ (w.balance msg.caller).toNat ∧
      (¬ P msg.caller ∨ msg.currentTarget = msg.caller) := fun h1 _ => by
    refine ⟨?_, .inl hmsg.caller⟩
    simp only [h1, Bool.true_and, decide_eq_true_eq] at hfund
    omega
  split
  · rename_i hnone
    split
    · exact .inl ⟨_, rfl, hw⟩
    · rename_i hd
      have hd' : accountDeployable w msg.currentTarget = true := by simpa using hd
      have hnp : ¬ P msg.currentTarget := fun hp => S.code w hw _ hp (size_code_of_deployable hd')
      refine .inr ⟨_, rfl, rfl, rfl, .inl ⟨?_, ⟨hw, fun hd => hnp hd.1, fun _ => hnp⟩, rfl⟩⟩
      simp only [beginCreate]
      refine S.transfer (S.nonce _ _ hw) fun h1 h2 => ?_
      rw [balance_incrementNonce]; exact hafford h1 h2
  · rename_i a hsome
    have htgt : msg.target = some msg.currentTarget := by
      rcases hmsg.target with h | h
      · exact h
      · rw [hsome] at h; cases h
    have htr : Good (transferValue w msg) := S.transfer hw hafford
    split
    · rename_i pa _
      unfold runPrecompile
      dsimp only
      split
      · refine .inl ⟨_, rfl, ?_⟩
        unfold topLevelResult; split <;> exact htr
      · refine .inl ⟨_, rfl, ?_⟩
        unfold topLevelResult; split <;> exact hw
    · by_cases hd : P msg.currentTarget ∧ msg.isStatic = false
      · obtain ⟨hcode, hca⟩ := hmsg.code hd.1 htgt
        refine .inr ⟨_, rfl, rfl, rfl, .inr ⟨⟨⟨0, 0, rfl⟩, hd, hw, fun p hp =>
          keep_transferValue (S.code _ hw p hp), ?_, htgt, hca, hmsg.caller, Nat.le_refl _,
          by show msg.depth ≤ _; rw [hmsg.depth]; decide, rfl⟩, rfl,
          fun h1 h2 => (hafford h1 h2).1⟩⟩
        show msg.code = (transferValue w msg).code msg.currentTarget
        rw [(keep_transferValue (S.code _ hw _ hd.1)).code]; exact hcode
      · exact .inr ⟨_, rfl, rfl, rfl, .inl ⟨htr, ⟨hw, hd, fun h => by cases h⟩, rfl⟩⟩

/-- **Any top-level message call keeps a `GoodOps` invariant** when the protected code `CoversE`
it for its gas (callbacks at any depth included): from a `Good` world, a `TopOk` message (any
code, value, calldata; an unprotected caller), before Prague or without EIP-7702
authorizations. -/
theorem processMessageCall_good_e (S : GoodOps P Good) {fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult} (hw : Good w)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hmsg : TopOk P w msg)
    (hcov : CoversE P Good msg.gas)
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
  rcases initMachine_out_e (ctx := ctx) (tr := tr) S hw hmsg' with
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

end EvmLogic.Program.Reentrancy
