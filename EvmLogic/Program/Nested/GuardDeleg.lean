import EvmLogic.Program.Nested.Sandbox
import EvmLogic.Program.Nested.GuardTrace
import EvmLogic.Program.Nested.Deleg

/-!
# Relays and guards for any transaction, EIP-7702 authorizations included

The relay and guard theorems (`processMessageCall_issues`, `processMessageCall_guard`,
`processMessageCall_guardD`, `processMessageCall_guard_world`) assume
`ctx.fork < .prague ∨ ctx.tx.authorizations = []`. Their `_7702` versions drop it.

* Relays hold real code (`RelayCodeOk`), which no authorization rewrites (`RelayCode.deleg`), so
  `processMessageCall_issues_7702` needs nothing more.
* Idle principals are accounts without code that do not act. Signing an authorization is acting:
  it installs a designator at the signer's account, whose code then runs as that account. So the
  guard theorems assume that no idle account signed one of the transaction's authorizations
  (`IdleNoAuth`), and keep idleness through the authorizations (`IdleW.deleg`). They also assume
  that a top-level call to an idle account runs the code at that account
  (`codeAddress = currentTarget`), as the message of every transaction does: an authorization may
  change the code at the message's `codeAddress`, and the message's code is reloaded from there.
-/

namespace EvmLogic.Program.Nested
open EvmLean EvmLean.Interpreter EvmLogic.AbsInt EvmLogic.GasMono EvmLogic.Program

variable {Rl : Address → Prop} {C : Address → ByteArray} {X : Address → Prop} {G : World → Prop}
  {Iss : Address → Machine → Message → Prop} {J : Address → Machine → Prop} {K : Context → Prop}
  {R : Machine → Prop} {Dm : Address → Machine → Prop}

/-- No idle account signed an authorization of the transaction (an idle principal does not
act). -/
def IdleNoAuth (X : Address → Prop) (ctx : Context) : Prop :=
  ∀ auth ∈ ctx.tx.authorizations, ∀ a, recoverAuthority ctx.crypto auth = some a → ¬ X a

theorem eq_empty_of_size_eq_zero {c : ByteArray} (h : c.size = 0) : c = .empty :=
  Classical.byContradiction fun hne => size_ne_zero_of_ne_empty hne h

theorem delegatedAddress?_of_size_eq_zero {c : ByteArray} (h : c.size = 0) :
    delegatedAddress? c = none := by
  cases hd : delegatedAddress? c with
  | none => rfl
  | some d => exact absurd h (delegated_size hd)

/-- **The relays keep their code through top-level delegation.** -/
theorem RelayCode.deleg (hC : RelayCodeOk Rl C) {w : World} (hw : RelayCode Rl C w)
    (ctx : Context) (isPre : Address → Bool) (msg : Message) :
    RelayCode Rl C (applyTopLevelDelegation ctx isPre w msg).1 := fun r hr => by
  have he := (applyTopLevelDelegation_frame ctx isPre w msg).1.account_eq
    (a := r) (by rw [hw r hr]; exact hC.size r hr) (by rw [hw r hr]; exact hC.deleg r hr)
  show ((applyTopLevelDelegation ctx isPre w msg).1.account r).code = C r
  rw [he]; exact hw r hr

/-- **Idle accounts stay idle through top-level delegation** when none of them signed an
authorization. -/
theorem IdleW.deleg {w : World} (hi : IdleW X w) {ctx : Context} (hauth : IdleNoAuth X ctx)
    (isPre : Address → Bool) (msg : Message) :
    IdleW X (applyTopLevelDelegation ctx isPre w msg).1 :=
  applyTopLevelDelegation_induct_by ctx isPre msg (IdleW X) (fun a => ¬ X a) hauth
    (fun w a c hi ha _ _ x hx => by
      have hne : x ≠ a := fun e => ha (e ▸ hx)
      have he := account_delegate_ne w c hne
      exact ⟨by simp only [World.code, he]; exact (hi x hx).1, by rw [he]; exact (hi x hx).2⟩)
    hi

/-- **`GuardTop` survives top-level delegation, for any transaction**: when no idle account
signed an authorization, and a call to an idle account runs the code at that account. -/
theorem guardTop_delegation_7702 (hC : RelayCodeOk Rl C) {ctx : Context}
    {isPre : Address → Bool} {w : World} {msg : Message} (hw : RelayCode Rl C w)
    (hi : IdleW X w) (hauth : IdleNoAuth X ctx)
    (hca : X msg.currentTarget → msg.target = some msg.currentTarget →
      msg.codeAddress = some msg.currentTarget)
    (hmsg : GuardTop Rl X w msg) :
    GuardTop Rl X (applyTopLevelDelegation ctx isPre w msg).1
      (applyTopLevelDelegation ctx isPre w msg).2.1 := by
  have hw' := hw.deleg hC ctx isPre msg
  have hi' := hi.deleg hauth isPre msg
  obtain ⟨hfr, hcur, hcaller, htarget, -, -, -, -, -, -, hcode⟩ :=
    applyTopLevelDelegation_frame ctx isPre w msg
  refine ⟨hmsg.top.delegate fun p hp => by rw [hw' p hp]; exact hC.deleg p hp,
    hcaller ▸ hmsg.caller, fun hx ht => ?_⟩
  rw [hcur] at hx
  rw [htarget, hcur] at ht
  have h0 := hmsg.idle hx ht
  have hc : msg.code = w.code msg.currentTarget := by
    rw [eq_empty_of_size_eq_zero h0, eq_empty_of_size_eq_zero (hi _ hx).1]
  have h0' := (hi' _ hx).1
  rw [((hcode _ hc (hca hx ht)).1 (delegatedAddress?_of_size_eq_zero h0')).1]
  exact h0'

/-- **Relays issue only what their predicates allow, in a top-level message call of any
transaction**: `processMessageCall_issues` without
`ctx.fork < .prague ∨ ctx.tx.authorizations = []`. -/
theorem processMessageCall_issues_7702 (hC : RelayCodeOk Rl C)
    (hJ : ∀ r, Rl r → RelayInv Rl C Iss r (J r)) {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} (hw : RelayCode Rl C w) (hmsg : TopOk Rl w msg)
    {m : Machine} (hm : Reaches ctx w tr msg m) (hd : Danger Rl m.frame) {c : Message}
    (hc : Requests m c) : Iss m.frame.msg.currentTarget m c := by
  have hw' := hw.deleg hC ctx (PrecompileImpl.standard ctx).isPrecompile msg
  have hmsg' := hmsg.delegate (ctx := ctx) (isPre := (PrecompileImpl.standard ctx).isPrecompile)
    fun p hp => by rw [hw' p hp]; exact hC.deleg p hp
  obtain ⟨m₀, n, hs, hn⟩ := hm
  unfold StartsAt at hs
  have h := relayTxInv_stepN hC hJ n (relayTxInv_start hC hJ hw' hmsg' hs) hn
  exact (hJ _ hd.1).issue m c (h.cur hd) h.world hc

/-- **The non-static calls a relay issues, for any transaction**:
`processMessageCall_issues_call` without `ctx.fork < .prague ∨ ctx.tx.authorizations = []`. -/
theorem processMessageCall_issues_call_7702 (hC : RelayCodeOk Rl C)
    (hJ : ∀ r, Rl r → RelayInv Rl C Iss r (J r)) {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} (hw : RelayCode Rl C w) (hmsg : TopOk Rl w msg)
    {m : Machine} (hm : Reaches ctx w tr msg m) (hr : Rl m.frame.msg.currentTarget)
    {b : UInt8} {req : CallRequest} {m' : Machine} (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m'))
    (hst : req.msg.isStatic = false) : Iss m.frame.msg.currentTarget m req.msg := by
  have hcall : CallOk m m' req := ((exec_frame _ m).of_run he).2
  exact processMessageCall_issues_7702 hC hJ hw hmsg hm ⟨hr, (hcall.nonstatic hst).1⟩
    ⟨b, _, m', hb, he, .inl ⟨req, rfl, rfl⟩⟩

/-- **A guarded message call of any transaction keeps the world invariant**:
`processMessageCall_guard` with, instead of `ctx.fork < .prague ∨ ctx.tx.authorizations = []`,
the assumptions that no idle account signed an authorization of the transaction (`hauth`: an
idle principal does not act) and that a call to an idle account runs the code at that account
(`hca`, true of every transaction's message). -/
theorem processMessageCall_guard_7702 (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w') (hJ : ∀ r, Rl r → GuardInvK K Rl C X G Iss r (J r))
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} (hw : RelayCode Rl C w)
    (hg : G w) (hi : IdleW X w) (hauth : IdleNoAuth X ctx)
    (hca : X msg.currentTarget → msg.target = some msg.currentTarget →
      msg.codeAddress = some msg.currentTarget)
    (hmsg : GuardTop Rl X w msg) {fuel : Nat} {r : MessageResult}
    (hr : processMessageCall fuel ctx w tr msg = .ok r) (hK : K ctx := by trivial) :
    G r.world := by
  have S := goodC_ok hC hG
  have hw' := hw.deleg hC ctx (PrecompileImpl.standard ctx).isPrecompile msg
  have hg' := (S.deleg_world ctx (PrecompileImpl.standard ctx).isPrecompile msg ⟨hg, hw⟩).1
  have hi' := hi.deleg hauth (PrecompileImpl.standard ctx).isPrecompile msg
  have hmsg' := guardTop_delegation_7702 (isPre := (PrecompileImpl.standard ctx).isPrecompile)
    hC hw hi hauth hca hmsg
  unfold processMessageCall processMessageCallWith at hr
  generalize applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg = d
    at hw' hg' hi' hmsg' hr
  obtain ⟨w', msg', refund⟩ := d
  dsimp only at hw' hg' hi' hmsg' hr
  rcases initMachine_out (ctx := ctx) (tr := tr) S ⟨hg', hw'⟩ hmsg'.top (Nat.le_refl _) with
    ⟨r', hin, hgr⟩ | ⟨m₀, hin, -⟩ <;> rw [hin] at hr <;> dsimp only at hr
  · cases hr; exact hgr.1
  · cases hrun : run fuel m₀ with
    | error e => rw [hrun] at hr; cases hr
    | ok r' =>
      rw [hrun] at hr
      cases hr
      show G r'.world
      exact guard_run hC hG hJ fuel (guardTxInv_start hC hG hJ hw' hg' hi' hmsg' hin hK) hrun

/-- **What guarded relays issue, for any transaction**: `processMessageCall_guard_issues` with
`hauth` and `hca` (as in `processMessageCall_guard_7702`) instead of
`ctx.fork < .prague ∨ ctx.tx.authorizations = []`. -/
theorem processMessageCall_guard_issues_7702 (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w') (hJ : ∀ r, Rl r → GuardInvK K Rl C X G Iss r (J r))
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} (hw : RelayCode Rl C w)
    (hg : G w) (hi : IdleW X w) (hauth : IdleNoAuth X ctx)
    (hca : X msg.currentTarget → msg.target = some msg.currentTarget →
      msg.codeAddress = some msg.currentTarget)
    (hmsg : GuardTop Rl X w msg) {m : Machine} (hm : Reaches ctx w tr msg m)
    (hd : Danger Rl m.frame) {c : Message} (hc : Requests m c) (hK : K ctx := by trivial) :
    Iss m.frame.msg.currentTarget m c := by
  have S := goodC_ok hC hG
  have hw' := hw.deleg hC ctx (PrecompileImpl.standard ctx).isPrecompile msg
  have hg' := (S.deleg_world ctx (PrecompileImpl.standard ctx).isPrecompile msg ⟨hg, hw⟩).1
  have hi' := hi.deleg hauth (PrecompileImpl.standard ctx).isPrecompile msg
  have hmsg' := guardTop_delegation_7702 (isPre := (PrecompileImpl.standard ctx).isPrecompile)
    hC hw hi hauth hca hmsg
  obtain ⟨m₀, n, hs, hn⟩ := hm
  unfold StartsAt at hs
  have h := guardTxInv_stepN hC hG hJ n (guardTxInv_start hC hG hJ hw' hg' hi' hmsg' hs hK) hn
  exact (hJ _ hd.1).issue m c (h.relay.cur hd) h.good.1 h.relay.world hc

/-- **A guarded message call with doomed frames, of any transaction, keeps the world
invariant**: `processMessageCall_guardD` with `hauth` and `hca` (as in
`processMessageCall_guard_7702`) instead of `ctx.fork < .prague ∨ ctx.tx.authorizations = []`. -/
theorem processMessageCall_guardD_7702 (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvD K Rl C X G R Iss (Dm r) r (J r))
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} (hw : RelayCode Rl C w)
    (hg : G w) (hi : IdleW X w) (hauth : IdleNoAuth X ctx)
    (hca : X msg.currentTarget → msg.target = some msg.currentTarget →
      msg.codeAddress = some msg.currentTarget)
    (hmsg : GuardTop Rl X w msg) (hR : ∀ m, Reaches ctx w tr msg m → R m) {fuel : Nat}
    {r : MessageResult} (hr : processMessageCall fuel ctx w tr msg = .ok r)
    (hK : K ctx := by trivial) : G r.world := by
  have S := goodC_ok hC hG
  have hw' := hw.deleg hC ctx (PrecompileImpl.standard ctx).isPrecompile msg
  have hg' := (S.deleg_world ctx (PrecompileImpl.standard ctx).isPrecompile msg ⟨hg, hw⟩).1
  have hi' := hi.deleg hauth (PrecompileImpl.standard ctx).isPrecompile msg
  have hmsg' := guardTop_delegation_7702 (isPre := (PrecompileImpl.standard ctx).isPrecompile)
    hC hw hi hauth hca hmsg
  have hst : ∀ m₀, initMachine (PrecompileImpl.standard ctx) ctx
      (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).1 tr
      (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).2.1 =
        .inr m₀ → StartsAt ctx w tr msg m₀ := fun _ h => h
  unfold processMessageCall processMessageCallWith at hr
  generalize applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg = d
    at hw' hg' hi' hmsg' hst hr
  obtain ⟨w', msg', refund⟩ := d
  dsimp only at hw' hg' hi' hmsg' hst hr
  rcases initMachine_out (ctx := ctx) (tr := tr) S ⟨hg', hw'⟩ hmsg'.top (Nat.le_refl _) with
    ⟨r', hin, hgr⟩ | ⟨m₀, hin, -⟩ <;> rw [hin] at hr <;> dsimp only at hr
  · cases hr; exact hgr.1
  · cases hrun : run fuel m₀ with
    | error e => rw [hrun] at hr; cases hr
    | ok r' =>
      rw [hrun] at hr
      cases hr
      show G r'.world
      have hs := hst m₀ hin
      exact sandInv_run hC hG hJ (fun n m hn => hR m ⟨m₀, n, hs, hn⟩) fuel 0 rfl
        (sandInv_start hC hG hJ hw' hg' hi' hmsg' hin hK) hrun

/-- **A guarded message call of any transaction keeps its world hypotheses**:
`processMessageCall_guard_world` with `hauth` and `hca` (as in `processMessageCall_guard_7702`)
instead of `ctx.fork < .prague ∨ ctx.tx.authorizations = []`. -/
theorem processMessageCall_guard_world_7702 (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w') (hJ : ∀ r, Rl r → GuardInv Rl C X G Iss r (J r))
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    (hw : GuardWorld Rl C X G w) (hauth : IdleNoAuth X ctx)
    (hca : X msg.currentTarget → msg.target = some msg.currentTarget →
      msg.codeAddress = some msg.currentTarget)
    (hmsg : GuardTop Rl X w msg) {fuel : Nat} {r : MessageResult}
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : GuardWorld Rl C X G r.world := by
  obtain ⟨hg, hrc, hi⟩ := hw
  have S := goodC_ok hC hG
  have hw' := hrc.deleg hC ctx (PrecompileImpl.standard ctx).isPrecompile msg
  have hg' := (S.deleg_world ctx (PrecompileImpl.standard ctx).isPrecompile msg ⟨hg, hrc⟩).1
  have hi' := hi.deleg hauth (PrecompileImpl.standard ctx).isPrecompile msg
  have hmsg' := guardTop_delegation_7702 (isPre := (PrecompileImpl.standard ctx).isPrecompile)
    hC hrc hi hauth hca hmsg
  unfold processMessageCall processMessageCallWith at hr
  generalize applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg = d
    at hw' hg' hi' hmsg' hr
  obtain ⟨w', msg', refund⟩ := d
  dsimp only at hw' hg' hi' hmsg' hr
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
      exact guard_run_world hC hG hJ fuel (guardTxInv_start hC hG hJ hw' hg' hi' hmsg' hin) hrun

end EvmLogic.Program.Nested
