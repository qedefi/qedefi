module

public import QEDefi.ERC20.Spec.Instances.YAMV2

/-!
# GUSD as a token model

GUSD is three contracts linked by `CALL` (no `DELEGATECALL`):

* the **token address**, `ERC20Proxy` (solc 0.4.21): every ERC-20 call is forwarded to
  `erc20Impl` with `msg.sender` as an extra argument (`transferWithSender(sender, to, v)`, …);
  it reverts (without bubbling the revert data) if the forwarded call fails, and returns its
  `bool`; `emitTransfer`/`emitApproval` emit the events, callable only by `erc20Impl`;
* the **implementation**, `ERC20Impl` (solc 0.8.30, the one pinned in this repository): its
  `erc20Proxy` and `erc20Store` are immutables; it checks, then writes the ledger through the
  store's setters, then asks the proxy to emit the event;
* the **store**, `ERC20Store` (solc 0.4.21): `totalSupply`, `balances`, `allowed`, written only
  by its own `erc20Impl` (`setBalance`, `addBalance` (unchecked), `setAllowance`,
  `setTotalSupply`).

Each contract has its own `custodian`, who replaces the proxy's or the store's `erc20Impl`, or
the custodian itself, by confirming a request anyone can make (`requestImplChange(new)` with
`new ≠ 0`, then `confirmImplChange(lockId)` by the custodian).

**The model** is the system as seen at the token address. Its state (`State`) is the store's
ledger, as a `VState` (`bal`, `supply`, `allowance`; the other fields are unused), and the
wiring: the two `erc20Impl` pointers and the three custodians (`Ctl`). Its ERC-20 calls are the
record `variant` (2 decimals; `transfer`/`transferFrom` reject the recipient `0`, `approve`
rejects the spender `0`, every allowance is spent, everything returns `true`, every failure
reverts; the unchecked `addBalance` cannot wrap under the supply invariant `Variant.WF`).
`transferFrom` emits only `Transfer`. The other operations (`Op`) are the implementation's
entry points (holder and custodian `burn`, `print` by the custodian, `batchTransfer`,
`increaseApproval`/`decreaseApproval`) and the custodians' replacements. The request/confirm
protocol is abstracted to its effect: since anyone can request any nonzero address, a
custodian can set its pointer to any nonzero address (`confirmPrint` likewise executes a print
that anyone requested, so `print` is any print the implementation's custodian confirms).

**The invariant** `wf impl` is the record's supply invariant together with the wiring: both
`erc20Impl` pointers are the pinned implementation `impl` (whose immutables point at this proxy
and store). It is *not* invariant (`not_wfInvariant`): a custodian can point the proxy or the
store at other code, after which the model says nothing. Every other call and operation keeps
it (`wf_call`, `wf_op`).

`gusd_laws`: every standard law but `WFInvariant` holds.
-/

@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.GUSD
open QEDefi.Math Finsupp QEDefi.ERC20 QEDefi.ERC20.Token QEDefi.ERC20.Spec.YAMV2

/-- The wiring of the three contracts. -/
structure Ctl (A : Type) where
  /-- `ERC20Proxy.erc20Impl`. -/
  proxyImpl : A
  /-- `ERC20Store.erc20Impl`. -/
  storeImpl : A
  /-- `ERC20Proxy.custodian`. -/
  proxyCustodian : A
  /-- `ERC20Impl.custodian`. -/
  implCustodian : A
  /-- `ERC20Store.custodian`. -/
  storeCustodian : A

/-- The state of the system: the store's ledger and the wiring. -/
abbrev State (A : Type) := VState A × Ctl A

/-- Which contract's custodian. -/
inductive Which
  /-- `ERC20Proxy`. -/
  | proxy
  /-- `ERC20Impl`. -/
  | impl
  /-- `ERC20Store`. -/
  | store

/-- The other operations of the system. -/
inductive Op (A : Type) where
  /-- `ERC20Proxy.increaseApproval(sp, x)` by `caller`. -/
  | increaseApproval (caller sp : A) (x : ℕ)
  /-- `ERC20Proxy.decreaseApproval(sp, x)` by `caller`. -/
  | decreaseApproval (caller sp : A) (x : ℕ)
  /-- `ERC20Impl.burn(v)` by `caller`, from its own balance. -/
  | burn (caller : A) (v : ℕ)
  /-- `ERC20Impl.burn(owner, v)` by `caller` (custodian only). -/
  | custodianBurn (caller owner : A) (v : ℕ)
  /-- `ERC20Impl.executePrint(dst, v)`, or the confirmation of a requested print, by `caller`
  (custodian only). -/
  | print (caller dst : A) (v : ℕ)
  /-- `ERC20Impl.batchTransfer(tos, values)` by `caller`. -/
  | batchTransfer (caller : A) (xs : List (A × ℕ))
  /-- A confirmed change of the proxy's `erc20Impl` to `new`. -/
  | setProxyImpl (caller new : A)
  /-- A confirmed change of the store's `erc20Impl` to `new`. -/
  | setStoreImpl (caller new : A)
  /-- A confirmed change of a contract's custodian to `new`. -/
  | setCustodian (w : Which) (caller new : A)

variable {A : Type} [DecidableEq A] [Zero A]

/-- **GUSD's ERC-20 calls as a policy record**: recipient `0` rejected by transfers, spender `0`
by approvals, every allowance spent, no `permit`. `mintAuth`, `burnAuth` and `helpers` are the
open forms that `stepOp` gates. -/
def variant : Variant A :=
  { Variant.standard with zero := ⟨false, true, false, true⟩, infinite := .none,
                          mintAuth := .anyone, burnAuth := .anyone, helpers := .checked,
                          permitRule := .none }

/-- **GUSD's events**, emitted by the token address: `Transfer` for both transfers (no
`Approval` from `transferFrom`), `Approval` for `approve`. -/
def events (_s : State A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => [.transfer caller dst v]
  | .transferFrom src dst v => [.transfer src dst v]
  | .approve sp v => [.approval caller sp v]
  | .other _ => []
  | .permit .. => []

/-- A result of the ledger, with the wiring `w` unchanged. -/
def lift (w : Ctl A) : Result (VState A) → Result (State A)
  | .ok s r => .ok (s, w) r
  | .halt h => .halt h

/-- The custodian of a contract. -/
def Ctl.custodian (w : Ctl A) : Which → A
  | .proxy => w.proxyCustodian
  | .impl => w.implCustodian
  | .store => w.storeCustodian

/-- Replace the custodian of a contract. -/
def Ctl.setCustodian (w : Ctl A) : Which → A → Ctl A
  | .proxy, a => { w with proxyCustodian := a }
  | .impl, a => { w with implCustodian := a }
  | .store, a => { w with storeCustodian := a }

/-- The other operations. -/
def stepOp (t : State A) : Op A → Option (State A)
  | .increaseApproval c sp x => ((variant : Variant A).adjustAllowance t.1 c sp true x).map (·, t.2)
  | .decreaseApproval c sp x => ((variant : Variant A).adjustAllowance t.1 c sp false x).map (·, t.2)
  | .burn c v => ((variant : Variant A).burn t.1 c c v).map (·, t.2)
  | .custodianBurn c o v =>
    if c = t.2.implCustodian then ((variant : Variant A).burn t.1 c o v).map (·, t.2) else none
  | .print c d v =>
    if c = t.2.implCustodian ∧ d ≠ 0 then
      -- `_executePrint` does nothing (and does not fail) when the supply would overflow
      some (((variant : Variant A).mint t.1 c d v).getD t.1, t.2)
    else none
  | .batchTransfer c xs =>
    (xs.foldlM (fun s (x : A × ℕ) => (variant : Variant A).transfer s c x.1 x.2) t.1).map (·, t.2)
  | .setProxyImpl c a =>
    if c = t.2.proxyCustodian ∧ a ≠ 0 then some (t.1, { t.2 with proxyImpl := a }) else none
  | .setStoreImpl c a =>
    if c = t.2.storeCustodian ∧ a ≠ 0 then some (t.1, { t.2 with storeImpl := a }) else none
  | .setCustodian w c a =>
    if c = t.2.custodian w ∧ a ≠ 0 then some (t.1, t.2.setCustodian w a) else none

/-- The invariant: the supply invariant of the ledger, and both `erc20Impl` pointers at the
pinned implementation `impl`. -/
def WF (impl : A) (t : State A) : Prop :=
  (variant : Variant A).WF t.1 ∧ t.2.proxyImpl = impl ∧ t.2.storeImpl = impl

/-- **The GUSD model**, for the pinned implementation at `impl`. -/
def model (impl : A) : TokenModel (State A) A (Op A) where
  balanceOf t := (variant : Variant A).balanceOf t.1
  totalSupply t := (variant : Variant A).totalSupply t.1
  allowance t := (variant : Variant A).allowanceOf t.1
  call t c op := lift t.2 ((variant : Variant A).call t.1 c op)
  events := events
  op := stepOp
  wf := WF impl

/-! ## Laws -/

omit [DecidableEq A] [Zero A] in
theorem lift_eq_ok {w : Ctl A} {R : Result (VState A)} {t : State A} {r : RetData} :
    lift w R = .ok t r ↔ R = .ok t.1 r ∧ t.2 = w := by
  cases R <;> simp [lift, Prod.ext_iff, eq_comm, and_comm, and_assoc]

omit [DecidableEq A] [Zero A] in
theorem lift_eq_halt {w : Ctl A} {R : Result (VState A)} {h : Halt} :
    lift w R = .halt h ↔ R = .halt h := by
  cases R <;> simp [lift]

omit [DecidableEq A] [Zero A] in
theorem plain : Plain (variant : Variant A) := by constructor <;> rfl

omit [DecidableEq A] [Zero A] in
theorem sane : (variant : Variant A).Sane := by
  constructor <;> simp [variant, Variant.standard]

/-- The record's events on the ledger (to reuse the laws of plain variants). -/
def vevents (s : VState A) (c : A) (op : Call A) : List (Event A) :=
  events (s, (⟨0, 0, 0, 0, 0⟩ : Ctl A)) c op

theorem call_ok {impl : A} {t t' : State A} {c : A} {op : Call A} {r : RetData}
    (h : (model impl).call t c op = .ok t' r) :
    (Variant.model (variant : Variant A) vevents).call t.1 c op = .ok t'.1 r ∧ t'.2 = t.2 :=
  lift_eq_ok.1 h

theorem failKind_eq (s : VState A) (c : A) (op : Call A) :
    (variant : Variant A).failKind s c op = .revert := by
  unfold Variant.failKind
  have : (variant : Variant A).overflows s c op = false := by
    cases op <;> simp [Variant.overflows, Variant.feeOverflow, variant, Variant.standard]
  rw [this]
  split_ifs <;> first | rfl | contradiction

theorem call_eq (s : VState A) (c : A) (op : Call A) :
    (variant : Variant A).call s c op =
      match (variant : Variant A).step s c op with
      | some s' => .ok s' ((variant : Variant A).retData op)
      | none => .halt .revert := by
  simp only [Variant.call, failKind_eq]; rfl

theorem returnsTrue (impl : A) : (model impl).ReturnsTrue := by
  intro t caller c t' r hc h
  obtain ⟨-, rfl⟩ := step_of_call (V := (variant : Variant A))
    (by simp [variant, Variant.standard]) (by simp [variant, Variant.standard]) (call_ok h).1
  cases c <;> simp_all [Call.returnsBool, Variant.retData, variant, Variant.standard]

theorem noFalseReturn (impl : A) : (model impl).NoFalseReturn := by
  intro t caller c t' h
  obtain ⟨-, hr⟩ := step_of_call (V := (variant : Variant A))
    (by simp [variant, Variant.standard]) (by simp [variant, Variant.standard]) (call_ok h).1
  cases c <;> simp [Variant.retData, variant, Variant.standard] at hr

theorem revertsOnly (impl : A) : (model impl).RevertsOnly := by
  intro t caller c hh h
  have h := lift_eq_halt.1 h
  simp only [call_eq] at h
  split at h <;> cases h
  rfl

theorem exactMoves (impl : A) (P : State A → Prop) : (model impl).ExactMoves P := by
  have H := (plain (A := A)).exactMoves vevents (fun _ => True)
  constructor
  · intro t caller dst v t' r _ hne h hr
    exact H.1 t.1 caller dst v t'.1 r trivial hne (call_ok h).1 hr
  · intro t caller src dst v t' r _ hne h hr
    exact H.2 t.1 caller src dst v t'.1 r trivial hne (call_ok h).1 hr

theorem supplyFixed (impl : A) : (model impl).SupplyFixed := fun t caller c t' r hc h =>
  (plain (A := A)).supplyFixed vevents t.1 caller c t'.1 r hc (call_ok h).1

theorem debitAuth (impl : A) : (model impl).DebitAuth := fun t caller c t' r o h =>
  (plain (A := A)).debitAuth vevents t.1 caller c t'.1 r o (call_ok h).1

theorem allowanceAuth (impl : A) : (model impl).AllowanceAuth := fun t caller c t' r o sp h =>
  (plain (A := A)).allowanceAuth vevents t.1 caller c t'.1 r o sp (call_ok h).1

/-- Every successful call keeps the invariant. -/
theorem wf_call (impl : A) {t t' : State A} {c : A} {op : Call A} {r : RetData}
    (hw : (model impl).wf t) (h : (model impl).call t c op = .ok t' r) : (model impl).wf t' := by
  obtain ⟨h, h2⟩ := call_ok h
  simp only [Variant.model_call, call_eq] at h
  split at h <;> cases h
  obtain ⟨hw, hp, hs⟩ := hw
  exact ⟨Variant.WF_step _ sane hw ‹_›, h2 ▸ hp, h2 ▸ hs⟩

theorem WF_batch {c : A} {s s' : VState A} {xs : List (A × ℕ)} (hw : (variant : Variant A).WF s)
    (h : xs.foldlM (fun s (x : A × ℕ) => (variant : Variant A).transfer s c x.1 x.2) s = some s') :
    (variant : Variant A).WF s' := by
  induction xs generalizing s with
  | nil => simp at h; exact h ▸ hw
  | cons x xs ih =>
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨s1, h1, h2⟩ := h
    exact ih (Variant.WF_transfer _ sane hw h1) h2

/-- Every operation but a custodian's replacement of an `erc20Impl` pointer keeps the
invariant. -/
theorem wf_op (impl : A) {t t' : State A} {e : Op A} (hw : (model impl).wf t)
    (he : ∀ c a, e ≠ .setProxyImpl c a ∧ e ≠ .setStoreImpl c a)
    (h : (model impl).op t e = some t') : (model impl).wf t' := by
  obtain ⟨hw, hp, hs⟩ := hw
  simp only [model] at h
  cases e with
  | increaseApproval c sp x =>
    obtain ⟨s1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨Variant.WF_adjustAllowance _ hw h1, hp, hs⟩
  | decreaseApproval c sp x =>
    obtain ⟨s1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨Variant.WF_adjustAllowance _ hw h1, hp, hs⟩
  | burn c v =>
    obtain ⟨s1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨Variant.WF_burn _ sane hw h1, hp, hs⟩
  | custodianBurn c o v =>
    simp only [stepOp] at h; split_ifs at h
    obtain ⟨s1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨Variant.WF_burn _ sane hw h1, hp, hs⟩
  | print c d v =>
    simp only [stepOp] at h; split_ifs at h; cases h
    refine ⟨?_, hp, hs⟩
    cases hm : (variant : Variant A).mint t.1 c d v with
    | none => exact hw
    | some s1 => exact Variant.WF_mint _ sane hw hm
  | batchTransfer c xs =>
    obtain ⟨s1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨WF_batch hw h1, hp, hs⟩
  | setProxyImpl c a => exact absurd rfl (he c a).1
  | setStoreImpl c a => exact absurd rfl (he c a).2
  | setCustodian w c a =>
    simp only [stepOp] at h; split_ifs at h; cases h
    refine ⟨hw, ?_, ?_⟩ <;> cases w <;> assumption

/-- **The invariant is not invariant**: from any `wf` state whose proxy custodian is `c`, the
custodian can point the proxy at any other nonzero address `a`. -/
theorem not_wf_setProxyImpl {impl a : A} {t : State A} (ha : a ≠ 0) (hai : a ≠ impl) :
    ∃ t', (model impl).op t (.setProxyImpl t.2.proxyCustodian a) = some t' ∧
      ¬ (model impl).wf t' :=
  ⟨(t.1, { t.2 with proxyImpl := a }), by simp [model, stepOp, ha],
    fun h => hai h.2.1⟩

/-- The empty ledger with both pointers at `impl` and custodian `0`: a `wf` state. -/
def wired (impl : A) : State A := (VState.ofToken ⟨0, 0, fun _ _ => 0⟩ 0 0, ⟨impl, impl, 0, 0, 0⟩)

theorem wf_wired (impl : A) : (model impl).wf (wired impl) := by
  refine ⟨?_, rfl, rfl⟩
  simp [Variant.WF, variant, Variant.standard, wired, VState.ofToken, total]

theorem not_wfInvariant {impl a : A} (ha : a ≠ 0) (hai : a ≠ impl) :
    ¬ (model impl).WFInvariant := by
  intro h
  obtain ⟨t', h1, h2⟩ := not_wf_setProxyImpl (t := wired impl) ha hai
  exact h2 (h.2 _ _ _ (wf_wired impl) h1)

/-- **GUSD's laws**: every standard law holds except `WFInvariant` (refuted whenever there is a
nonzero address other than the implementation: a custodian can replace the implementation). -/
theorem gusd_laws (impl : A) :
    (model impl).ReturnsTrue ∧ (model impl).NoFalseReturn ∧ (model impl).RevertsOnly ∧
    (model impl).ExactMoves (fun _ => True) ∧ (model impl).SupplyFixed ∧
    (model impl).DebitAuth ∧ (model impl).AllowanceAuth ∧
    (∀ a : A, a ≠ 0 → a ≠ impl → ¬ (model impl).WFInvariant) :=
  ⟨returnsTrue impl, noFalseReturn impl, revertsOnly impl, exactMoves impl _, supplyFixed impl,
    debitAuth impl, allowanceAuth impl, fun _ ha hai => not_wfInvariant ha hai⟩

end QEDefi.ERC20.Spec.GUSD
