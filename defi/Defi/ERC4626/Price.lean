import Defi.ERC4626.Agree

/-!
# No dilution along sequences of user operations (model level)

The model's per-entry-point price monotonicity (`Solmate.deposit_price_mono`, …,
`[E-PRICE-*]`) extended to **every** operation of `Solmate.Op` that does not move assets out
of the vault's own account, and then to whole sequences:

* `UserOp self op`: the operation is a *user* operation — it does not spend the vault's own
  asset balance directly (`asset.transfer` with the vault as caller, `asset.transferFrom` or
  `asset.burn` from the vault) and is not a deposit/mint paid by the vault itself. The vault's
  code never makes such calls except inside `withdraw`/`redeem`, which are user operations;
  a top-level transaction cannot have the vault as sender (it has code, EIP-3607), so for
  top-level traces the only excluded operation is `MockERC20.burn(vault, ·)`, which the mock
  token lets anyone call (the model's "loss" operation).
* `price_mono_step`: a user operation from a state with shares never lowers assets-per-share:
  `T·S' ≤ T'·S` (reverting steps trivially).
* `price_exec_mono`: along a sequence of user operations during which the vault is never
  empty, the price `T/S` (over `ℚ`) never decreases.
-/

namespace Defi.ERC4626
open Defi.Trace

open Defi.ERC4626 Defi.Math Defi.ERC20 Defi.ERC4626.Solmate Defi.ERC20.Token Finsupp

variable {A : Type} [DecidableEq A]

/-- A user operation of the vault at `self` (see the module docstring). -/
def UserOp (self : A) : Op A → Prop
  | .deposit c _ _ => c ≠ self
  | .mint c _ _ => c ≠ self
  | .withdraw _ _ _ _ => True
  | .redeem _ _ _ _ => True
  | .transfer _ _ _ => True
  | .transferFrom _ _ _ _ => True
  | .approve _ _ _ => True
  | .assetTransfer c _ _ => c ≠ self
  | .assetTransferFrom _ src _ _ => src ≠ self
  | .assetApprove _ _ _ => True
  | .assetMint _ _ => True
  | .assetBurn src _ => src ≠ self

/-- A transfer not debiting `x` does not decrease `x`'s balance. -/
theorem le_move_of_ne (f : A →₀ ℕ) {src dst x : A} (v : ℕ) (h : src ≠ x) :
    f x ≤ (f - single src v + single dst v) x := by
  rw [add_single_apply, sub_single_apply]
  split_ifs <;> simp_all

/-- Operations other than the four entry points keep the supply and do not lower the
vault's asset balance. -/
theorem TS_of_other {s s' : State A} {T' : ℕ} (hS : s'.totalSupply = s.totalSupply)
    (hT : s.totalAssets ≤ T') (hT' : s'.totalAssets = T') :
    s.totalAssets * s'.totalSupply ≤ s'.totalAssets * s.totalSupply := by
  rw [hS, hT']; exact Nat.mul_le_mul_right _ hT

/-- **No dilution, one step.** A successful user operation from a well-formed state with
shares never lowers assets-per-share: `T·S' ≤ T'·S`. -/
theorem price_mono_step {s s' : State A} {op : Op A} (hi : Inv s) (hu : UserOp s.self op)
    (h : step s op = some s') (hS : s.totalSupply ≠ 0) :
    s.totalAssets * s'.totalSupply ≤ s'.totalAssets * s.totalSupply := by
  cases op with
  | deposit c a r =>
    obtain ⟨⟨s₁, n⟩, h₁, rfl⟩ := Option.map_eq_some_iff.1 h
    exact deposit_price_mono h₁ hu hS
  | mint c n r =>
    obtain ⟨⟨s₁, a⟩, h₁, rfl⟩ := Option.map_eq_some_iff.1 h
    exact mint_price_mono h₁ hu hS
  | withdraw c a r o =>
    obtain ⟨⟨s₁, n⟩, h₁, rfl⟩ := Option.map_eq_some_iff.1 h
    exact withdraw_price_mono hi h₁ hS
  | redeem c n r o =>
    obtain ⟨⟨s₁, a⟩, h₁, rfl⟩ := Option.map_eq_some_iff.1 h
    exact redeem_price_mono hi h₁ hS
  | transfer c d v =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := transfer_eq_some.1 ht
    exact TS_of_other rfl le_rfl rfl
  | transferFrom c src d v =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
    exact TS_of_other (transferFrom_eq_some ht).2.2 le_rfl rfl
  | approve c sp v =>
    cases h
    exact TS_of_other rfl le_rfl rfl
  | assetTransfer c d v =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := transfer_eq_some.1 ht
    exact TS_of_other rfl (le_move_of_ne _ v hu) rfl
  | assetTransferFrom c src d v =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
    refine TS_of_other rfl ?_ rfl
    show s.asset.balanceOf s.self ≤ t.balanceOf s.self
    rw [(transferFrom_eq_some ht).2.1]
    exact le_move_of_ne _ v hu
  | assetApprove c sp v =>
    cases h
    exact TS_of_other rfl le_rfl rfl
  | assetMint d v =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := mint_eq_some.1 ht
    refine TS_of_other rfl ?_ rfl
    show s.asset.balanceOf s.self ≤ (s.asset.balanceOf + single d v) s.self
    rw [add_single_apply]; split_ifs <;> omega
  | assetBurn src v =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := burn_eq_some.1 ht
    refine TS_of_other rfl ?_ rfl
    show s.asset.balanceOf s.self ≤ (s.asset.balanceOf - single src v) s.self
    rw [sub_single_apply]
    split_ifs with h
    · exact absurd h hu
    · exact le_rfl

/-- `price_mono_step` for a step in which a revert is a no-op. -/
theorem price_mono_stepD {s : State A} {op : Op A} (hi : Inv s) (hu : UserOp s.self op)
    (hS : s.totalSupply ≠ 0) :
    s.totalAssets * (Lift.stepD step s op).totalSupply ≤
      (Lift.stepD step s op).totalAssets * s.totalSupply := by
  unfold Lift.stepD
  cases e : step s op with
  | none => exact le_of_eq (Nat.mul_comm _ _ ▸ rfl)
  | some s' => exact price_mono_step hi hu e hS

/-- **No dilution along a sequence.** Along any sequence of user operations from a well-formed
state, during which the vault always has shares (before every step and at the end), the share
price `T/S` never decreases. -/
theorem price_exec_mono {s : State A} (hi : Inv s) {ops : List (Op A)}
    (hu : ∀ op ∈ ops, UserOp s.self op)
    (hS : ∀ k ≤ ops.length, (Lift.exec step s (ops.take k)).totalSupply ≠ 0) :
    s.price ≤ (Lift.exec step s ops).price := by
  induction ops generalizing s with
  | nil => exact le_rfl
  | cons op ops ih =>
    have hS₀ : s.totalSupply ≠ 0 := by simpa using hS 0 (Nat.zero_le _)
    have hS₁ : (Lift.stepD step s op).totalSupply ≠ 0 := by
      simpa using hS 1 (by simp)
    have hi₁ : Inv (Lift.stepD step s op) := by
      unfold Lift.stepD
      cases e : step s op with
      | none => exact hi
      | some s' => exact Inv_step hi e
    have h₁ : s.price ≤ (Lift.stepD step s op).price :=
      price_le_of_cross hS₀ hS₁ (price_mono_stepD hi (hu op (by simp)) hS₀)
    refine h₁.trans (ih hi₁ (fun o ho => (self_stepD s op).symm ▸ hu o (by simp [ho]))
      fun k hk => ?_)
    simpa using hS (k + 1) (by simp; omega)

end Defi.ERC4626
