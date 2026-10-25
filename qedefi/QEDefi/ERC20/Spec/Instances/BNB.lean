module

public import QEDefi.ERC20.Spec.VariantLaws

/-!
# BNB as a token model

`bnbModel` is `Variant.bnb` with BNB's events (`contracts/mainnet/BNB/source/BNB.sol`, solc
0.4.12) and BNB's credit-overflow guard:

* `transfer(dst, v)` logs `Transfer(caller, dst, v)`;
* `transferFrom(src, dst, v)` logs `Transfer(src, dst, v)`;
* `approve` logs nothing: BNB declares no `Approval` event;
* the payable fallback (every unknown selector, `permit` included) logs nothing.

**The overflow guard.** `transfer` and `transferFrom` check
`if (balanceOf[_to] + _value < balanceOf[_to]) throw;` (a `REVERT` in 0.4.12) before changing
anything. Between distinct accounts the model's invariant makes it unreachable (two balances
add up to at most the supply), but for a self-transfer (`transfer(caller, v)`,
`transferFrom(src, src, v)`) of more than `MAX − balance` the code reverts while `Variant.bnb`
alone succeeds with the state unchanged: **`Variant.bnb` is wrong for those calls**, and
`bnbModel` adds the guard (`bnbGuard`: revert when `MAX < bal dst + v`). Every other call and
every operation is `Variant.bnb`'s. Since all of BNB's checks revert, the guard's place among
them does not change the outcome. `bnbModel_laws` re-decides the laws for the guarded model.
-/
@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.BNB

open QEDefi.ERC20 QEDefi.Math QEDefi.ERC20.Spec.VariantLaws

variable {A : Type} [DecidableEq A] [Zero A]

/-- BNB's events of a successful call by `caller`. -/
def bnbEvents (_s : VState A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => [.transfer caller dst v]
  | .transferFrom src dst v => [.transfer src dst v]
  | .approve _ _ => []
  | .other _ => []
  | .permit .. => []

/-- BNB's credit-overflow guard: the recipient's balance plus the value exceeds `MAX`. -/
def bnbGuard (s : VState A) : Call A → Bool
  | .transfer dst v => decide (MAX < s.bal dst + v)
  | .transferFrom _ dst v => decide (MAX < s.bal dst + v)
  | _ => false

/-- **BNB**: `Variant.bnb` with its events, the calls guarded by `bnbGuard`. -/
def bnbModel : TokenModel (VState A) A (Variant.Op A) :=
  { (Variant.bnb : Variant A).model bnbEvents with
    call := fun s caller c =>
      if bnbGuard s c then .halt .revert else (Variant.bnb : Variant A).call s caller c }

theorem bnbModel_call (s : VState A) (caller : A) (c : Call A) :
    bnbModel.call s caller c =
      if bnbGuard s c then .halt .revert else (Variant.bnb : Variant A).call s caller c := rfl

/-- A successful guarded call is a successful `Variant.bnb` call. -/
theorem bnbModel_call_ok {s s' : VState A} {caller : A} {c : Call A} {r : RetData}
    (h : bnbModel.call s caller c = .ok s' r) : (Variant.bnb : Variant A).call s caller c = .ok s' r := by
  rw [bnbModel_call] at h
  split at h
  · cases h
  · exact h

/-- **The laws of BNB** (with the guard): those of `bnb_laws`, the guard only adding reverts. -/
theorem bnbModel_laws [Nontrivial A] :
    ¬ (bnbModel : TokenModel (VState A) A _).ReturnsTrue ∧
      (bnbModel : TokenModel (VState A) A _).NoFalseReturn ∧
      (bnbModel : TokenModel (VState A) A _).RevertsOnly ∧
      (bnbModel : TokenModel (VState A) A _).ExactMoves (fun _ => True) ∧
      (bnbModel : TokenModel (VState A) A _).SupplyFixed ∧
      (bnbModel : TokenModel (VState A) A _).DebitAuth ∧
      (bnbModel : TokenModel (VState A) A _).AllowanceAuth ∧
      (bnbModel : TokenModel (VState A) A _).WFInvariant := by
  obtain ⟨-, hN, hRv, hE, hS, hD, hA, hW⟩ := bnb_laws (A := A) (ev := bnbEvents)
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ⟨?_, hW.2⟩⟩
  · intro hT
    have hg : bnbGuard (wit (0 : A) 1 0 1) (.transfer a 1) = false := by
      simp [bnbGuard, wit, ha, MAX]
    have := hT _ 0 (.transfer a 1) _ _ rfl
      (by rw [bnbModel_call, hg]; exact (bnb_empty_witness ha).2)
    cases this
  · intro s caller c s' h
    exact hN s caller c s' (bnbModel_call_ok h)
  · intro s caller c k h
    rw [bnbModel_call] at h
    split at h
    · cases h; rfl
    · exact hRv s caller c k h
  · intro s caller dst v s' r hP hcd h hr
    exact hE.1 s caller dst v s' r hP hcd (bnbModel_call_ok h) hr
  · intro s caller src dst v s' r hP hcd h hr
    exact hE.2 s caller src dst v s' r hP hcd (bnbModel_call_ok h) hr
  · intro s caller c s' r hc h
    exact hS s caller c s' r hc (bnbModel_call_ok h)
  · intro s caller c s' r o h
    exact hD s caller c s' r o (bnbModel_call_ok h)
  · intro s caller c s' r o sp h
    exact hA s caller c s' r o sp (bnbModel_call_ok h)
  · intro s caller c s' r hw h
    exact hW.1 s caller c s' r hw (bnbModel_call_ok h)

end QEDefi.ERC20.Spec.BNB
