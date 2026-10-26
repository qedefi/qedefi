module

public import QEDefi.ERC20.Spec.Model

/-!
# Laws of token models

Each law is a proposition about a `TokenModel`, proved or refuted per token, never part of a
token's spec. Together they are what "a standard ERC-20" means; a contract that holds tokens
assumes only the laws it needs (a vault's no-dilution needs `ExactMoves`, not `ReturnsTrue`).

| Law | Says | Fails for |
|---|---|---|
| `ReturnsTrue` | successful `transfer`/`transferFrom`/`approve` return `true` | USDT, BNB `transfer` (no return data) |
| `NoFalseReturn` | failure is never reported by returning `false` | ZRX |
| `RevertsOnly` | a failing call reverts, never `INVALID` | USDT (`INVALID` on short balance) |
| `ExactMoves P` | a transfer of `v` between distinct accounts moves exactly `v` (in states `P`) | USDT with a fee, STA |
| `SupplyFixed` | transfers and approvals leave `totalSupply` | STA (burns the fee) |
| `DebitAuth` | only `transferFrom` lowers another account's balance | |
| `AllowanceAuth` | another account's allowance changes only by its spender's `transferFrom` or its `permit` signature (never a failed recovery: the owner is not `0`) | AMPL (zero-owner `permit`) |
| `WFInvariant` | the model's invariant survives every call and operation | |

`Standard M P` bundles them. The ERC-20 events are not a law: each model states its own
(`TokenModel.events`), and the bytecode spec checks them.
-/
@[expose] public noncomputable section

namespace QEDefi.ERC20

/-- The calls the standard says return a `bool`. -/
def Call.returnsBool {A : Type} : Call A → Bool
  | .transfer .. | .transferFrom .. | .approve .. => true
  | .other .. | .permit .. => false

namespace TokenModel

variable {σ A E : Type} (M : TokenModel σ A E)

/-- **Successful `transfer`, `transferFrom` and `approve` return `true`.** -/
def ReturnsTrue : Prop :=
  ∀ s caller (c : Call A) s' r, c.returnsBool → M.call s caller c = .ok s' r → r = .word true

/-- **No call reports failure by returning `false`.** -/
def NoFalseReturn : Prop :=
  ∀ s caller (c : Call A) s', M.call s caller c ≠ .ok s' (.word false)

/-- **A failing call reverts**: it never ends with `INVALID` (which consumes all the gas the
caller forwarded). -/
def RevertsOnly : Prop :=
  ∀ s caller (c : Call A) h, M.call s caller c = .halt h → h = .revert

/-- A successful move of `v` from `src` to `dst ≠ src` changes the `balanceOf` view by exactly
`v` at the two accounts and nowhere else. -/
def MovesExactly (s s' : σ) (src dst : A) (v : ℕ) : Prop :=
  M.balanceOf s' src + v = M.balanceOf s src ∧ M.balanceOf s' dst = M.balanceOf s dst + v ∧
    ∀ a, a ≠ src → a ≠ dst → M.balanceOf s' a = M.balanceOf s a

/-- **Transfers are exact** in states satisfying `P`: a successful `transfer` or `transferFrom`
(not one reporting failure by `false`) of `v` between distinct accounts moves exactly `v`. -/
def ExactMoves (P : σ → Prop) : Prop :=
  (∀ s caller dst v s' r, P s → caller ≠ dst →
    M.call s caller (.transfer dst v) = .ok s' r → r ≠ .word false →
    M.MovesExactly s s' caller dst v) ∧
  (∀ s caller src dst v s' r, P s → src ≠ dst →
    M.call s caller (.transferFrom src dst v) = .ok s' r → r ≠ .word false →
    M.MovesExactly s s' src dst v)

/-- **Transfers and approvals leave the supply.** -/
def SupplyFixed : Prop :=
  ∀ s caller (c : Call A) s' r, c.returnsBool → M.call s caller c = .ok s' r →
    M.totalSupply s' = M.totalSupply s

/-- **Only `transferFrom` lowers another account's balance**: a successful call by `caller`
that lowers the balance of `o ≠ caller` is a `transferFrom` from `o`. -/
def DebitAuth : Prop :=
  ∀ s caller (c : Call A) s' r o, M.call s caller c = .ok s' r → o ≠ caller →
    M.balanceOf s' o < M.balanceOf s o → ∃ dst v, c = .transferFrom o dst v

/-- **Allowances change only with their owner's consent**: a successful call by `caller` that
changes `allowance(o, sp)` for `o ≠ caller` is the spender `sp = caller` spending it by
`transferFrom` from `o`, or a `permit` for `(o, sp)` whose signature recovers to `o ≠ 0`.

`ecrecover` returns `0` when recovery fails (`Call.permit`'s `rec`), so a failed recovery
"recovers to" the owner `0`: the permit branch requires `o ≠ 0`, so that a failed recovery never
authorises (AMPL's `permit`, without a zero check, lets anyone set `allowance(0, sp)`). Hence
the `[Zero A]`: the address `0` is the recovery's failure value. -/
def AllowanceAuth [Zero A] : Prop :=
  ∀ s caller (c : Call A) s' r o sp, M.call s caller c = .ok s' r → o ≠ caller →
    M.allowance s' o sp ≠ M.allowance s o sp →
      (sp = caller ∧ ∃ dst v, c = .transferFrom o dst v) ∨
      (∃ v live rec n, c = .permit o sp v live rec ∧ rec n = o ∧ o ≠ 0)

/-- **The model's invariant is an invariant**: every successful call and every operation
keeps `wf`. -/
def WFInvariant : Prop :=
  (∀ s caller (c : Call A) s' r, M.wf s → M.call s caller c = .ok s' r → M.wf s') ∧
  (∀ s (e : E) s', M.wf s → M.op s e = some s' → M.wf s')

/-- **The standard laws**, in states satisfying `P` (`[Zero A]` for `AllowanceAuth`). -/
structure Standard [Zero A] (P : σ → Prop) : Prop where
  returnsTrue : M.ReturnsTrue
  noFalseReturn : M.NoFalseReturn
  revertsOnly : M.RevertsOnly
  exactMoves : M.ExactMoves P
  supplyFixed : M.SupplyFixed
  debitAuth : M.DebitAuth
  allowanceAuth : M.AllowanceAuth
  wfInvariant : M.WFInvariant

/-! ## Executions -/

/-- One step of an execution: an ERC-20 call or another operation. -/
inductive Action (A E : Type) where
  /-- An ERC-20 call by `caller`. -/
  | call (caller : A) (c : Call A)
  /-- Another operation. -/
  | op (e : E)

/-- The state after an action; a failed action leaves the state (the transaction reverts). -/
def act (s : σ) : Action A E → σ
  | .call caller c => match M.call s caller c with
    | .ok s' _ => s'
    | .halt _ => s
  | .op e => (M.op s e).getD s

/-- The state after a sequence of actions. -/
def exec (s : σ) (as : List (Action A E)) : σ := as.foldl M.act s

/-- **The invariant holds after any execution.** -/
theorem WFInvariant.exec {M : TokenModel σ A E} (h : M.WFInvariant) {s : σ} (hs : M.wf s)
    (as : List (Action A E)) : M.wf (M.exec s as) := by
  induction as generalizing s with
  | nil => exact hs
  | cons a as ih =>
    apply ih
    cases a with
    | call caller c =>
      simp only [act]
      split
      · exact h.1 _ _ _ _ _ hs ‹_›
      · exact hs
    | op e =>
      simp only [act]
      cases he : M.op s e with
      | none => exact hs
      | some s' => exact h.2 _ _ _ hs he

end TokenModel

end QEDefi.ERC20
