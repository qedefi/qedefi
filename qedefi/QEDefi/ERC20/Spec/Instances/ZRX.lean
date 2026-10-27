module

public import QEDefi.ERC20.Spec.Instances.YAMV2

/-!
# ZRX as a token model

ZRX (`contracts/mainnet/ZRX/source/ZRXToken.sol`, solc 0.4.11, `UnlimitedAllowanceToken`):

* `transfer(dst, v)` succeeds iff `balances[caller] ≥ v` and `balances[dst] + v` does not wrap;
  otherwise it **returns `false`**: success status, no state change, no event.
  `transferFrom(src, dst, v)` likewise with `allowed[src][caller] ≥ v`; an allowance of
  `2²⁵⁶ − 1` is not spent. Both emit only `Transfer`. `approve` always succeeds, emits
  `Approval`, and returns `true`.
* Nothing reverts: there is no `require` or `throw` in the token functions. The dispatcher's
  fallthrough (unknown selector, `permit`, short calldata) and the non-payable checks end with
  the `INVALID` opcode (solc 0.4.11 compiles `throw` to `INVALID`).
* `ZRXToken` redeclares `totalSupply`: `StandardToken.totalSupply` (slot 2) is shadowed and
  never written; the getter reads slot 3. No mint, burn or other entry point.

The model is the record `variant` (`Variant.model variant events`, with no other operations
and a strengthened invariant). The record has no receiver-overflow check; the invariant `wf`
excludes the states where it matters: `Σ bal ≤ supply ≤ MAX` over the balances in the state
(`SubSupply`: the actors' view of the supply invariant) and `2 · supply ≤ MAX`. Then
`bal dst + v ≤ supply ≤ MAX` for distinct accounts and `bal c + v ≤ 2 · bal c ≤ MAX` for a
self-transfer, so the check never fails. ZRX's supply is fixed at `10²⁷ < MAX / 2` by its
constructor and nothing changes it, so every reachable state, seen by any set of actors with
distinct rows, satisfies `wf`.

`zrx_laws`: `ReturnsTrue` and `NoFalseReturn` fail (a short balance returns `false`),
`RevertsOnly` fails (unknown selectors end in `INVALID`); the other laws hold.
-/

@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.ZRX
open QEDefi.Math Finsupp QEDefi.ERC20 QEDefi.ERC20.Token QEDefi.ERC20.Spec.YAMV2

variable {A : Type} [DecidableEq A] [Zero A]

/-- **ZRX as a policy record**: failures of the balance and allowance checks return `false`
(`arithFail`); the only other failure, the dispatcher's fallthrough, is `INVALID`
(`guardFail`, which the record uses for unknown selectors and `permit`); an allowance of
exactly `MAX` is not spent (`eqMax`); no address checks, mint, burn or `permit`. -/
def variant : Variant A :=
  { Variant.standard with guardFail := .invalid, arithFail := .returnFalse, infinite := .eqMax,
                          mintAuth := .nobody, burnAuth := .nobody, permitRule := .none }

/-- **ZRX's events**: a successful transfer emits `Transfer`, `approve` emits `Approval`; a
transfer that returns `false` emits nothing. -/
def events (s : VState A) (caller : A) (c : Call A) : List (Event A) :=
  if ((variant : Variant A).step s caller c).isSome then
    match c with
    | .transfer dst v => [.transfer caller dst v]
    | .transferFrom src dst v => [.transfer src dst v]
    | .approve sp v => [.approval caller sp v]
    | .other _ => []
    | .permit .. => []
  else []

/-- The invariant: the supply bound as the actors see it (`SubSupply`), and `2 · supply ≤ MAX` (ZRX's fixed
supply is `10²⁷`), under which the receiver-overflow check of `transfer`/`transferFrom` never
fails. -/
def WF (s : VState A) : Prop := SubSupply s ∧ 2 * s.supply ≤ MAX

/-- **The ZRX model**: the record's calls with ZRX's events, no other operations, invariant
`WF`. -/
def model : TokenModel (VState A) A Empty :=
  { Variant.model (variant : Variant A) events with op := fun _ e => e.elim, wf := WF }

omit [DecidableEq A] [Zero A] in
theorem plain : Plain (variant : Variant A) := by constructor <;> rfl

omit [DecidableEq A] [Zero A] in
theorem sane : (variant : Variant A).Sane := by
  constructor <;> simp [variant, Variant.standard]

/-! ## Failures return `false` -/

/-- The account `0` holding nothing: a witness state. -/
def empty : VState A := VState.ofToken ⟨0, 0, fun _ _ => 0⟩ 0 0

/-- A transfer of `1` from an empty account returns `false`. -/
theorem call_short : (model : TokenModel (VState A) A Empty).call empty 0 (.transfer 0 1) =
    .ok empty (.word false) := by
  simp [model, Variant.model, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
    Variant.move, Variant.units, variant, Variant.standard, empty, VState.ofToken,
    Variant.failKind, Variant.guardOk, Variant.overflows, Variant.failWith]

/-- An unknown selector ends in `INVALID`. -/
theorem call_other (s : VState A) (c : A) (value : ℕ) :
    (model : TokenModel (VState A) A Empty).call s c (.other value) = .halt .invalid := by
  simp [model, Variant.model, Variant.call, Variant.step, Variant.fallbackCall, variant,
    Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]

theorem not_returnsTrue : ¬ (model : TokenModel (VState A) A Empty).ReturnsTrue := by
  intro h
  have := h _ _ _ _ _ rfl call_short
  simp at this

theorem not_noFalseReturn : ¬ (model : TokenModel (VState A) A Empty).NoFalseReturn :=
  fun h => h _ _ _ _ call_short

theorem not_revertsOnly : ¬ (model : TokenModel (VState A) A Empty).RevertsOnly := by
  intro h
  have := h empty 0 (.other 0) _ (call_other _ _ _)
  cases this

/-! ## The other laws -/

theorem exactMoves (P : VState A → Prop) : (model : TokenModel (VState A) A Empty).ExactMoves P :=
  plain.exactMoves events P

theorem supplyFixed : (model : TokenModel (VState A) A Empty).SupplyFixed :=
  plain.supplyFixed events

theorem debitAuth : (model : TokenModel (VState A) A Empty).DebitAuth := plain.debitAuth events

theorem allowanceAuth : (model : TokenModel (VState A) A Empty).AllowanceAuth :=
  plain.allowanceAuth events

theorem wfInvariant : (model : TokenModel (VState A) A Empty).WFInvariant := by
  constructor
  · intro s caller c s' r hw h
    have hs : s'.supply = s.supply := by
      have := supplyFixed s caller c s' r
      cases c with
      | other value => simp [call_other] at h
      | permit o sp v live rec =>
        have h' : (variant : Variant A).step s caller (.permit o sp v live rec) = none :=
          plain.step_permit _ _ _ _ _ _ _
        simp [model, Variant.model, Variant.call, h'] at h
        simp [Variant.failKind, Variant.guardOk, variant, Variant.standard,
          Variant.failWith] at h
      | _ => simpa [model, Variant.model, plain.totalSupply] using this rfl h
    refine ⟨?_, hs ▸ hw.2⟩
    rcases step_or_same (V := (variant : Variant A)) h with h | rfl
    · exact plain.subSupply_step hw.1 h
    · exact hw.1
  · intro s e; exact e.elim

/-- **ZRX's laws**: failure by `false` (`ReturnsTrue`, `NoFalseReturn` refuted), `INVALID` on
unknown selectors (`RevertsOnly` refuted); exact moves, fixed supply, debits only by
`transferFrom`, allowances only by their spender, and the invariant hold. -/
theorem zrx_laws :
    ¬ (model : TokenModel (VState A) A Empty).ReturnsTrue ∧
    ¬ (model : TokenModel (VState A) A Empty).NoFalseReturn ∧
    ¬ (model : TokenModel (VState A) A Empty).RevertsOnly ∧
    (model : TokenModel (VState A) A Empty).ExactMoves (fun _ => True) ∧
    (model : TokenModel (VState A) A Empty).SupplyFixed ∧
    (model : TokenModel (VState A) A Empty).DebitAuth ∧
    (model : TokenModel (VState A) A Empty).AllowanceAuth ∧
    (model : TokenModel (VState A) A Empty).WFInvariant :=
  ⟨not_returnsTrue, not_noFalseReturn, not_revertsOnly, exactMoves _, supplyFixed, debitAuth,
    allowanceAuth, wfInvariant⟩

end QEDefi.ERC20.Spec.ZRX
