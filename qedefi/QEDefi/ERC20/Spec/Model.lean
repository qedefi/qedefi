module

public import QEDefi.ERC20.VariantProps

/-!
# Token models

A `TokenModel σ A E` is what a token does, as its holders and the contracts calling it see it:
the three ERC-20 views, the outcome of each ERC-20 call (`Call`: state change, return data and
how a failure ends, `Result`), the events of a successful call, every other entry point or
environment event (`E`: mint, burn, admin operations, rebases, ether arriving), and the
model's own invariant `wf`.

It is the single interface between the two halves of the ERC-20 layer:

* **tokens** are proved to *be* a model on their bytecode (`QEDefi.ERC20.Spec.Bytecode`:
  `ERC20Spec code abs M`), whatever the model is: an instance of the policy record `Variant`
  (`Variant.model`, for the known deviations: fees, rebasing, missing return data, `INVALID`
  failures, blacklists, …) or a model of its own for a token the record does not fit;
* **laws** (`QEDefi.ERC20.Spec.Laws`) are separate propositions about a model (`ReturnsTrue`,
  `ExactMoves`, `SupplyFixed`, …), proved or refuted per token; contracts that hold tokens
  assume only the laws they need.

The spec of a token never says that it is a standard ERC-20; it says exactly what it does, and
the laws say how that differs from the standard.

Not in the interface yet: callbacks into other contracts during a call (ERC-777 hooks,
ERC-1363 `transferAndCall`); no token pinned in this repository has them. They need an
outcome that calls out and continues, and frame summaries with untrusted callees
(`EvmLogic/Program/Reentrancy/`).
-/
@[expose] public noncomputable section

namespace QEDefi.ERC20

/-- An event of the ERC-20 interface, with `ℕ` amounts. -/
inductive Event (A : Type) where
  /-- `Transfer(src, dst, v)`. -/
  | transfer (src dst : A) (v : ℕ)
  /-- `Approval(owner, spender, v)`. -/
  | approval (owner spender : A) (v : ℕ)
  deriving DecidableEq

/-- **A token model**: states `σ`, accounts `A`, other operations `E`. -/
structure TokenModel (σ A E : Type) where
  /-- `balanceOf(a)`. -/
  balanceOf : σ → A → ℕ
  /-- `totalSupply()`. -/
  totalSupply : σ → ℕ
  /-- `allowance(owner, spender)`. -/
  allowance : σ → A → A → ℕ
  /-- The outcome of an ERC-20 call by `caller` in state `s`. -/
  call : σ → A → Call A → Result σ
  /-- The events a successful call by `caller` in state `s` emits, in order. -/
  events : σ → A → Call A → List (Event A)
  /-- Every other operation (other entry points, environment events); `none`: it fails. -/
  op : σ → E → Option σ
  /-- The model's invariant (the states a deployment can reach). -/
  wf : σ → Prop

namespace TokenModel

variable {σ A E : Type} (M : TokenModel σ A E)

/-- The state after a call, if it succeeds. -/
def step (s : σ) (caller : A) (c : Call A) : Option σ :=
  match M.call s caller c with
  | .ok s' _ => some s'
  | .halt _ => none

theorem step_eq_some {s s' : σ} {caller : A} {c : Call A} :
    M.step s caller c = some s' ↔ ∃ r, M.call s caller c = .ok s' r := by
  unfold step
  split <;> simp_all

end TokenModel

/-! ## The variants as token models -/

namespace Variant

variable {A : Type} [DecidableEq A] [Zero A]

/-- `Transfer(src, dst, v)` for a move of `v` (the amount the caller asked for). -/
def moveEvents (src dst : A) (v : ℕ) : List (Event A) := [.transfer src dst v]

/-- **A variant as a token model**, with its event policy `ev` (the record does not model
events: each token's are stated with its instance). -/
def model (V : Variant A) (ev : VState A → A → Call A → List (Event A)) :
    TokenModel (VState A) A (Op A) where
  balanceOf := V.balanceOf
  totalSupply := V.totalSupply
  allowance := V.allowanceOf
  call := V.call
  events := ev
  op := V.stepOp
  wf := V.WF

variable (V : Variant A) (ev : VState A → A → Call A → List (Event A))

@[simp] theorem model_call : (V.model ev).call = V.call := rfl
@[simp] theorem model_op : (V.model ev).op = V.stepOp := rfl
@[simp] theorem model_wf : (V.model ev).wf = V.WF := rfl
@[simp] theorem model_balanceOf : (V.model ev).balanceOf = V.balanceOf := rfl
@[simp] theorem model_totalSupply : (V.model ev).totalSupply = V.totalSupply := rfl
@[simp] theorem model_allowance : (V.model ev).allowance = V.allowanceOf := rfl
@[simp] theorem model_events : (V.model ev).events = ev := rfl

end Variant

end QEDefi.ERC20
