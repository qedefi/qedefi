module

public import QEDefi.ERC20.Spec.Instances.YAMV2

/-!
# LEND as a token model

LEND (`contracts/mainnet/LEND/source/EthLendToken.sol`, solc 0.4.16, `EthLendToken`) is a
token with its ICO built in. Its quirks:

* **The sale gate.** `transfer`, `transferFrom` and `approve` `require(enableTransfers)`; the
  flag is set exactly when the token manager moves `currentState` to `ICOFinished` (5), after
  which `setState` refuses every change: the state is final. Mainnet LEND is in it.
* **Zero values.** `transfer`/`transferFrom` `require(balances[to] + v > balances[to])`
  (wrapping): this fails for `v = 0` (self-transfers included) and on overflow. With
  `balances[to] < 2²⁵⁶` and `v < 2²⁵⁶` it is `0 < v ∧ balances[to] + v ≤ MAX`, the form used here.
* **The USDT approve guard**: `approve(sp, v)` requires `v = 0` or a zero current allowance,
  and returns `true`. Every allowance is spent, `2²⁵⁶ − 1` included.
* Every failure is a `require` (`REVERT`); the SafeMath `assert`s after the requires never
  fail. Everything returns `true`.
* **The sale.** The payable fallback is `buyTokens()`: in `PresaleRunning` (2) at least
  1 ether, `30000` tokens per wei, capped by `presaleSoldTokens + n ≤ 6·10²⁵`; in `ICORunning`
  (4) at least `10¹⁶` wei at `27500`/`26250`/`25000` tokens per wei by `icoSoldTokens` tier,
  capped by `totalSoldTokens + n ≤ 10²⁷`. All of this arithmetic is unchecked (wraps modulo
  `2²⁵⁶`); the model wraps the same way. A purchase emits `LogBuy` (not an ERC-20 event).
* Other entry points: `buyTokensPresale`, `buyTokensICO`, `setState`, `setTokenManager`,
  `withdrawEther` (sends the whole ether balance to `escrow`).

The record `Variant` cannot express the gate on `approve`, the failing zero-value transfer
next to a succeeding zero-value approval, or the sale, so `model` is a `TokenModel` of its own.

**Invariant.** `wf` is the final state: `currentState = ICOFinished` and `enableTransfers`.
It is invariant (`setState` refuses to leave it) and it is mainnet LEND's state. The sale states
are modelled (`call`, `stepOp`) but excluded by `wf`, because `ERC20Spec` could not hold in
them: a purchase through the fallback emits `LogBuy`, and `FallbackSpec` demands that the logs
be exactly the model's `Event`s, which have no such constructor.

`lend_laws`: every standard law holds; moves are exact in every state.
-/

@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.LEND
open QEDefi.Math Finsupp QEDefi.ERC20 QEDefi.ERC20.Token QEDefi.ERC20.Spec.YAMV2

/-- The storage of LEND that its entry points read or write (`escrow`, never written, is not
part of the state; `teamTokenBonus`, never written, is, because it shares slot 3 with the
state flags). -/
structure State (A : Type) where
  /-- `balances`. -/
  bal : A →₀ ℕ
  /-- `supply` (what `totalSupply()` returns). -/
  supply : ℕ
  /-- `allowed[owner][spender]`. -/
  allowance : A → A → ℕ
  /-- `currentState`: `Init`, `Paused`, `PresaleRunning`, `PresaleFinished`, `ICORunning`,
  `ICOFinished` as `0 … 5`. -/
  phase : ℕ
  /-- `enableTransfers`. -/
  enabled : Bool
  /-- `teamTokenBonus` (read only). -/
  team : A
  /-- `tokenManager`. -/
  manager : A
  /-- `presaleSoldTokens`. -/
  presaleSold : ℕ
  /-- `icoSoldTokens`. -/
  icoSold : ℕ
  /-- `totalSoldTokens`. -/
  totalSold : ℕ

/-- Unknown selectors (and `permit`) reach the fallback, `buyTokens()`. -/
inductive Op (A : Type) where
  /-- `buyTokens()` (and the fallback) with `value` wei. -/
  | buyTokens (caller : A) (value : ℕ)
  /-- `buyTokensPresale()` with `value` wei. -/
  | buyTokensPresale (caller : A) (value : ℕ)
  /-- `buyTokensICO()` with `value` wei. -/
  | buyTokensICO (caller : A) (value : ℕ)
  /-- `setState(x)`. -/
  | setState (caller : A) (x : ℕ)
  /-- `setTokenManager(mgr)`. -/
  | setTokenManager (caller mgr : A)
  /-- `withdrawEther()`: `sendOk` is whether the balance is zero or `escrow` accepts it (the
  ether itself is not part of the state). -/
  | withdrawEther (caller : A) (sendOk : Bool)

namespace State

variable {A : Type} [DecidableEq A]

/-- `allowed[o][sp] = v`. -/
def setAllowance (s : State A) (o sp : A) (v : ℕ) : State A :=
  { s with allowance := Function.update s.allowance o (Function.update (s.allowance o) sp v) }

end State

variable {A : Type} [DecidableEq A]

/-! ## The ERC-20 calls -/

/-- `require(balances[from] ≥ v)` and `require(balances[to] + v > balances[to])`, then the move. -/
def move (s : State A) (src dst : A) (v : ℕ) : Option (State A) :=
  if v ≤ s.bal src ∧ 0 < v ∧ s.bal dst + v ≤ MAX then
    some { s with bal := s.bal - single src v + single dst v }
  else none

/-- `transfer(dst, v)` by `c`. -/
def transfer (s : State A) (c dst : A) (v : ℕ) : Option (State A) :=
  if s.enabled then move s c dst v else none

/-- `transferFrom(src, dst, v)` by `c`: the allowance is always spent. -/
def transferFrom (s : State A) (c src dst : A) (v : ℕ) : Option (State A) :=
  if s.enabled ∧ v ≤ s.allowance src c then
    (move s src dst v).map fun s' => s'.setAllowance src c (s.allowance src c - v)
  else none

/-- `approve(sp, v)` by `c`: the race guard. -/
def approve (s : State A) (c sp : A) (v : ℕ) : Option (State A) :=
  if s.enabled ∧ (v = 0 ∨ s.allowance c sp = 0) then some (s.setAllowance c sp v) else none

/-- `getPrice()` in `ICORunning`. -/
def icoPrice (s : State A) : ℕ :=
  if s.icoSold < 200000000 * 10 ^ 18 then 27500
  else if s.icoSold < 300000000 * 10 ^ 18 then 26250
  else 25000

/-- The purchase of `n` tokens by `c`, with LEND's unchecked additions. -/
def credit (s : State A) (c : A) (n : ℕ) : State A :=
  { s with bal := s.bal.update c ((s.bal c + n) % U256), supply := (s.supply + n) % U256,
           totalSold := (s.totalSold + n) % U256 }

/-- `buyTokensPresale()` with `value` wei by `c`. -/
def buyPresale (s : State A) (c : A) (value : ℕ) : Option (State A) :=
  let n := value * 30000 % U256
  if s.phase = 2 ∧ 10 ^ 18 ≤ value ∧ (s.presaleSold + n) % U256 ≤ 60000000 * 10 ^ 18 then
    some { credit s c n with presaleSold := (s.presaleSold + n) % U256 }
  else none

/-- `buyTokensICO()` with `value` wei by `c`. -/
def buyICO (s : State A) (c : A) (value : ℕ) : Option (State A) :=
  let n := value * icoPrice s % U256
  if s.phase = 4 ∧ 10 ^ 16 ≤ value ∧ (s.totalSold + n) % U256 ≤ 10 ^ 27 then
    some { credit s c n with icoSold := (s.icoSold + n) % U256 }
  else none

/-- `buyTokens()` (the fallback). -/
def buy (s : State A) (c : A) (value : ℕ) : Option (State A) :=
  if s.phase = 2 then buyPresale s c value
  else if s.phase = 4 then buyICO s c value
  else none

/-- The state change of a call. -/
def step (s : State A) (c : A) : Call A → Option (State A)
  | .transfer dst v => transfer s c dst v
  | .transferFrom src dst v => transferFrom s c src dst v
  | .approve sp v => approve s c sp v
  | .other value => buy s c value
  | .permit .. => buy s c 0

/-- What a successful call returns. -/
def retData : Call A → RetData
  | .transfer .. | .transferFrom .. | .approve .. => .word true
  | .other _ | .permit .. => .empty

/-- The outcome of a call: every failure reverts. -/
def call (s : State A) (c : A) (op : Call A) : Result (State A) :=
  match step s c op with
  | some s' => .ok s' (retData op)
  | none => .halt .revert

/-- **LEND's events**: `Transfer` for the transfers (no `Approval` from `transferFrom`),
`Approval` for `approve`. A purchase emits `LogBuy`, which is not an ERC-20 event (see the
module docstring). -/
def events (_s : State A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => [.transfer caller dst v]
  | .transferFrom src dst v => [.transfer src dst v]
  | .approve sp v => [.approval caller sp v]
  | .other _ => []
  | .permit .. => []

/-! ## The other entry points -/

/-- The other entry points. `setState(x)`: the manager, from any state but `ICOFinished`, to a
valid state `x < 6`; `enableTransfers` becomes `x = ICOFinished`. -/
def stepOp (s : State A) : Op A → Option (State A)
  | .buyTokens c v => buy s c v
  | .buyTokensPresale c v => buyPresale s c v
  | .buyTokensICO c v => buyICO s c v
  | .setState c x =>
    if c = s.manager ∧ s.phase ≠ 5 ∧ x < 6 then some { s with phase := x, enabled := decide (x = 5) }
    else none
  | .setTokenManager c m => if c = s.manager then some { s with manager := m } else none
  | .withdrawEther c ok => if c = s.manager ∧ ok then some s else none

/-- The final state: `currentState = ICOFinished` with transfers enabled. -/
def WF (s : State A) : Prop := s.phase = 5 ∧ s.enabled = true

/-- **The LEND model.** -/
def model : TokenModel (State A) A (Op A) where
  balanceOf s a := s.bal a
  totalSupply s := s.supply
  allowance s := s.allowance
  call := call
  events := events
  op := stepOp
  wf := WF

/-! ## Quirks -/

/-- A zero-value transfer reverts, a self-transfer included. -/
theorem call_transfer_zero (s : State A) (c d : A) :
    (model : TokenModel (State A) A (Op A)).call s c (.transfer d 0) = .halt .revert := by
  simp [model, call, step, transfer, move]

/-- So does a zero-value `transferFrom`. -/
theorem call_transferFrom_zero (s : State A) (c src d : A) :
    (model : TokenModel (State A) A (Op A)).call s c (.transferFrom src d 0) = .halt .revert := by
  simp [model, call, step, transferFrom, move]

/-- Before the sale is over (transfers disabled), every transfer and approval reverts. -/
theorem call_gated {s : State A} (h : s.enabled = false) (c : A) (op : Call A)
    (hop : op.returnsBool) :
    (model : TokenModel (State A) A (Op A)).call s c op = .halt .revert := by
  cases op <;> simp_all [model, call, step, transfer, transferFrom, approve, Call.returnsBool]

/-- The approve race guard: `approve(sp, v)` (enabled) succeeds iff `v = 0` or the allowance
is `0`. -/
theorem approve_isSome_iff {s : State A} (h : s.enabled = true) (c sp : A) (v : ℕ) :
    (approve s c sp v).isSome ↔ v = 0 ∨ s.allowance c sp = 0 := by
  unfold approve; split_ifs with h1 <;> simp_all

/-! ## Laws -/

theorem step_of_call {s s' : State A} {c : A} {op : Call A} {r : RetData}
    (h : call s c op = .ok s' r) : step s c op = some s' ∧ r = retData op := by
  unfold call at h
  split at h <;> cases h
  exact ⟨‹_›, rfl⟩

omit [DecidableEq A] in
theorem move_eq_some {s s' : State A} {src dst : A} {v : ℕ} (h : move s src dst v = some s') :
    v ≤ s.bal src ∧ s'.bal = s.bal - single src v + single dst v ∧ s'.supply = s.supply ∧
      s'.allowance = s.allowance ∧ s'.phase = s.phase ∧ s'.enabled = s.enabled := by
  unfold move at h
  split_ifs at h with h1
  cases h
  exact ⟨h1.1, rfl, rfl, rfl, rfl, rfl⟩

theorem transferFrom_eq_some {s s' : State A} {c src dst : A} {v : ℕ}
    (h : transferFrom s c src dst v = some s') :
    v ≤ s.bal src ∧ s'.bal = s.bal - single src v + single dst v ∧ s'.supply = s.supply ∧
      s'.allowance = Function.update s.allowance src
        (Function.update (s.allowance src) c (s.allowance src c - v)) ∧
      s'.phase = s.phase ∧ s'.enabled = s.enabled := by
  unfold transferFrom at h
  split_ifs at h
  obtain ⟨s1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := move_eq_some h1
  refine ⟨m1, m2, m3, ?_, m5, m6⟩
  simp only [State.setAllowance, m4]

omit [DecidableEq A] in
theorem buyPresale_phase {s s' : State A} {c : A} {v : ℕ} (h : buyPresale s c v = some s') :
    s.phase = 2 := by
  dsimp only [buyPresale] at h; split_ifs at h with h1; exact h1.1

omit [DecidableEq A] in
theorem buyICO_phase {s s' : State A} {c : A} {v : ℕ} (h : buyICO s c v = some s') :
    s.phase = 4 := by
  dsimp only [buyICO] at h; split_ifs at h with h1; exact h1.1

omit [DecidableEq A] in
theorem buy_phase {s s' : State A} {c : A} {v : ℕ} (h : buy s c v = some s') :
    s.phase = 2 ∨ s.phase = 4 := by
  unfold buy at h; split_ifs at h with h1 h2
  · exact Or.inl h1
  · exact Or.inr h2

/-- A purchase changes only the buyer's balance and the allowances not at all. -/
theorem buy_eq_some {s s' : State A} {c : A} {v : ℕ} (h : buy s c v = some s') :
    (∀ o, o ≠ c → s'.bal o = s.bal o) ∧ s'.allowance = s.allowance := by
  have key : ∀ n (t : State A), (t = { credit s c n with presaleSold := (s.presaleSold + n) % U256 } ∨
      t = { credit s c n with icoSold := (s.icoSold + n) % U256 }) →
      (∀ o, o ≠ c → t.bal o = s.bal o) ∧ t.allowance = s.allowance := by
    rintro n t (rfl | rfl) <;>
      exact ⟨fun o ho => by simp [credit, Finsupp.update_apply, ho], rfl⟩
  unfold buy at h
  split_ifs at h
  · dsimp only [buyPresale] at h; split_ifs at h; cases h; exact key _ _ (Or.inl rfl)
  · dsimp only [buyICO] at h; split_ifs at h; cases h; exact key _ _ (Or.inr rfl)

theorem returnsTrue : (model : TokenModel (State A) A (Op A)).ReturnsTrue := by
  intro s caller c s' r hc h
  obtain ⟨-, rfl⟩ := step_of_call h
  cases c <;> simp_all [retData, Call.returnsBool]

theorem noFalseReturn : (model : TokenModel (State A) A (Op A)).NoFalseReturn := by
  intro s caller c s' h
  obtain ⟨-, hr⟩ := step_of_call h
  cases c <;> simp [retData] at hr

theorem revertsOnly : (model : TokenModel (State A) A (Op A)).RevertsOnly := by
  intro s caller c hh h
  simp only [model, call] at h
  split at h <;> cases h
  rfl

theorem exactMoves (P : State A → Prop) : (model : TokenModel (State A) A (Op A)).ExactMoves P := by
  constructor
  · intro s caller dst v s' r _ hne h _
    obtain ⟨h, -⟩ := step_of_call h
    simp only [step, transfer] at h
    split_ifs at h
    obtain ⟨h1, h2, -⟩ := move_eq_some h
    exact moves_of_bal (s := VState.ofToken ⟨s.bal, 0, fun _ _ => 0⟩ caller caller)
      (s' := VState.ofToken ⟨s'.bal, 0, fun _ _ => 0⟩ caller caller) hne h1 h2
  · intro s caller src dst v s' r _ hne h _
    obtain ⟨h, -⟩ := step_of_call h
    obtain ⟨h1, h2, -⟩ := transferFrom_eq_some h
    exact moves_of_bal (s := VState.ofToken ⟨s.bal, 0, fun _ _ => 0⟩ caller caller)
      (s' := VState.ofToken ⟨s'.bal, 0, fun _ _ => 0⟩ caller caller) hne h1 h2

theorem supplyFixed : (model : TokenModel (State A) A (Op A)).SupplyFixed := by
  intro s caller c s' r hc h
  obtain ⟨h, -⟩ := step_of_call h
  cases c with
  | transfer d v =>
    simp only [step, transfer] at h; split_ifs at h; exact (move_eq_some h).2.2.1
  | transferFrom src d v => exact (transferFrom_eq_some h).2.2.1
  | approve sp v =>
    simp only [step, approve] at h; split_ifs at h; cases h; rfl
  | other _ => simp [Call.returnsBool] at hc
  | permit o' sp' v' l' r' => simp [Call.returnsBool] at hc

/-- The balances of a state as a `VState` (to reuse the move lemmas). -/
def asV (s : State A) (a : A) : VState A := VState.ofToken ⟨s.bal, 0, fun _ _ => 0⟩ a a

theorem debitAuth : (model : TokenModel (State A) A (Op A)).DebitAuth := by
  intro s caller c s' r o h ho hlt
  obtain ⟨h, -⟩ := step_of_call h
  simp only [model] at hlt
  cases c with
  | transfer d v =>
    simp only [step, transfer] at h; split_ifs at h
    obtain ⟨-, h2, -⟩ := move_eq_some h
    exact absurd (bal_ge_of_move (s := asV s o) (s' := asV s' o) ho h2) (not_le.2 hlt)
  | transferFrom src d v =>
    by_cases hs : o = src
    · exact ⟨d, v, hs ▸ rfl⟩
    · obtain ⟨-, h2, -⟩ := transferFrom_eq_some h
      exact absurd (bal_ge_of_move (s := asV s o) (s' := asV s' o) hs h2) (not_le.2 hlt)
  | approve sp v =>
    simp only [step, approve] at h; split_ifs at h; cases h; exact absurd hlt (lt_irrefl _)
  | other value => rw [(buy_eq_some h).1 o ho] at hlt; exact absurd hlt (lt_irrefl _)
  | permit o' sp' v' l' r' => rw [(buy_eq_some h).1 o ho] at hlt; exact absurd hlt (lt_irrefl _)

/-- `AllowanceAuth` (it names the zero address, the failed recovery of a `permit`: `[Zero A]`). -/
theorem allowanceAuth [Zero A] : (model : TokenModel (State A) A (Op A)).AllowanceAuth := by
  intro s caller c s' r o sp h ho hne
  obtain ⟨h, -⟩ := step_of_call h
  simp only [model] at hne
  cases c with
  | transfer d v =>
    simp only [step, transfer] at h; split_ifs at h
    exact absurd (by rw [(move_eq_some h).2.2.2.1]) hne
  | transferFrom src d v =>
    obtain ⟨-, -, -, h4, -⟩ := transferFrom_eq_some h
    rw [h4] at hne
    left
    by_cases hs : o = src
    · subst hs
      by_cases hc : sp = caller
      · exact ⟨hc, d, v, rfl⟩
      · simp [Function.update_of_ne hc] at hne
    · simp [Function.update_of_ne hs] at hne
  | approve sp' v =>
    simp only [step, approve] at h; split_ifs at h; cases h
    simp [State.setAllowance, Function.update_of_ne ho] at hne
  | other value => exact absurd (by rw [(buy_eq_some h).2]) hne
  | permit o' sp' v' l' r' => exact absurd (by rw [(buy_eq_some h).2]) hne

theorem wfInvariant : (model : TokenModel (State A) A (Op A)).WFInvariant := by
  constructor
  · intro s caller c s' r hw h
    obtain ⟨h, -⟩ := step_of_call h
    obtain ⟨hp, he⟩ := hw
    cases c with
    | transfer d v =>
      simp only [step, transfer] at h; split_ifs at h
      obtain ⟨-, -, -, -, h5, h6⟩ := move_eq_some h
      exact ⟨h5 ▸ hp, h6 ▸ he⟩
    | transferFrom src d v =>
      obtain ⟨-, -, -, -, h5, h6⟩ := transferFrom_eq_some h
      exact ⟨h5 ▸ hp, h6 ▸ he⟩
    | approve sp v =>
      simp only [step, approve] at h; split_ifs at h; cases h; exact ⟨hp, he⟩
    | other value => rcases buy_phase h with h | h <;> omega
    | permit o' sp' v' l' r' => rcases buy_phase h with h | h <;> omega
  · intro s e s' hw h
    obtain ⟨hp, he⟩ := hw
    cases e with
    | buyTokens c v => rcases buy_phase h with h | h <;> omega
    | buyTokensPresale c v => have := buyPresale_phase h; omega
    | buyTokensICO c v => have := buyICO_phase h; omega
    | setState c x =>
      simp only [model, stepOp] at h; split_ifs at h with h1; exact absurd hp h1.2.1
    | setTokenManager c m =>
      simp only [model, stepOp] at h; split_ifs at h; cases h; exact ⟨hp, he⟩
    | withdrawEther c ok =>
      simp only [model, stepOp] at h; split_ifs at h; cases h; exact ⟨hp, he⟩

/-- **LEND satisfies every standard law** (moves exact in every state). -/
theorem lend_laws [Zero A] : (model : TokenModel (State A) A (Op A)).Standard fun _ => True where
  returnsTrue := returnsTrue
  noFalseReturn := noFalseReturn
  revertsOnly := revertsOnly
  exactMoves := exactMoves _
  supplyFixed := supplyFixed
  debitAuth := debitAuth
  allowanceAuth := allowanceAuth
  wfInvariant := wfInvariant

end QEDefi.ERC20.Spec.LEND
