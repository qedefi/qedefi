module

public import Defi.ERC4626.Inflation

/-!
# Concrete witnesses

Concrete well-formed states (addresses `ℕ`) on which the calls in the refutations and
attack theorems do succeed, so those statements are not vacuous.
-/

@[expose] public noncomputable section

namespace Defi.ERC4626.Witnesses
open Defi.Math Defi.ERC20 Finsupp

/-! ## Solmate: deposit→redeem returns more than deposited -/

/-- A vault (address `0`) with no shares and `1` donated asset; user `1` holds `1` asset and
has approved the vault without limit. -/
def solmateDonated : Solmate.State ℕ where
  self := 0
  asset := { balanceOf := single 0 1 + single 1 1, totalSupply := 2,
             allowance := fun o sp => if o = 1 ∧ sp = 0 then MAX else 0 }
  shares := { balanceOf := 0, totalSupply := 0, allowance := fun _ _ => 0 }
  afterDepositCount := 0
  beforeWithdrawCount := 0

theorem solmateDonated_inv : Solmate.Inv solmateDonated := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [solmateDonated, MAX]
  · rw [Token.total_add_single]; simp [total, sum_single_index]
  · norm_num
  · simp [total]
  · norm_num

/-- Deposit→redeem fails: user `1` deposits `1` asset and redeems the share for `2`. -/
theorem solmate_rt_deposit_redeem_witness :
    ((Solmate.deposit solmateDonated 1 1 1).bind fun p =>
      (Solmate.redeem p.1 1 p.2 1 1).map fun q => (p.2, q.2)) = some (1, 2) := by
  simp [Solmate.deposit, solmateDonated, Solmate.State.previewDeposit,
    Solmate.State.convertToShares, Solmate.State.totalSupply, Token.transferFrom, Token.spend,
    Token.transfer, Token.mint, Solmate.bump, checkedAdd, Finsupp.add_apply, MAX,
    Solmate.redeem, Solmate.spendIfNotOwner, Solmate.State.previewRedeem,
    Solmate.State.convertToAssets, mulDivDown, Solmate.State.totalAssets, Token.burn]

/-! ## Solmate: the inflation attack, numerically -/

/-- After the attack with `D = 100`: vault `0` holds `101` assets and `1` share, owned by
the attacker `2`; the victim `1` holds `201` assets and approved the vault. -/
def solmateAttacked : Solmate.State ℕ where
  self := 0
  asset := { balanceOf := single 0 101 + single 1 201, totalSupply := 302,
             allowance := fun o sp => if o = 1 ∧ sp = 0 then MAX else 0 }
  shares := { balanceOf := single 2 1, totalSupply := 1, allowance := fun _ _ => 0 }
  afterDepositCount := 1
  beforeWithdrawCount := 0

/-- The victim's `deposit(201 = 2D + 1)` gets `1` share worth `151` (a loss of `50`);
`deposit(100 = D)` reverts. -/
theorem solmate_attack_witness :
    ((Solmate.deposit solmateAttacked 1 201 1).bind fun p =>
      (p.1.convertToAssets p.2).map fun v => (p.2, v)) = some (1, 151) ∧
    Solmate.deposit solmateAttacked 1 100 1 = none := by
  constructor
  · simp [Solmate.deposit, solmateAttacked, Solmate.State.previewDeposit,
      Solmate.State.convertToShares, Solmate.State.totalSupply, Token.transferFrom, Token.spend,
      Token.transfer, Token.mint, Solmate.bump, checkedAdd, Finsupp.add_apply, MAX,
    Solmate.State.convertToAssets, mulDivDown, Solmate.State.totalAssets]
  · simp [Solmate.deposit, solmateAttacked, Solmate.State.previewDeposit,
      Solmate.State.convertToShares, Solmate.State.totalSupply, mulDivDown,
      Solmate.State.totalAssets, Finsupp.add_apply, MAX]

/-! ## OpenZeppelin (`δ = 0`): a deposit that mints zero shares -/

/-- An OpenZeppelin vault (address `10`, `δ = 0`) after an attacker (`2`, holding the only
share) donated `100`: `101` assets, `1` share. The victim `1` holds `50` assets. -/
def ozAttacked : Oz.State ℕ where
  self := 10
  asset := { balanceOf := single 10 101 + single 1 50, totalSupply := 151,
             allowance := fun o sp => if o = 1 ∧ sp = 10 then MAX else 0 }
  shares := { balanceOf := single 2 1, totalSupply := 1, allowance := fun _ _ => 0 }

/-- The victim's `deposit(50)` succeeds and mints `0` shares (the attacker still lost: the
virtual share absorbed half of the donation). -/
theorem oz_zero_shares_witness :
    (Oz.deposit 0 ozAttacked 1 50 1).map (fun p => (p.2, p.1.totalAssets, p.1.totalSupply)) =
      some (0, 151, 1) := by
  simp [Oz.deposit, ozAttacked, Oz.State.previewDeposit, Oz.State.toShares,
    Oz.State.totalSupply, Oz.State.totalAssets, checkedAdd, ozMulDiv, Token.ozTransferFrom,
    Token.ozSpend, Token.ozTransfer, Token.ozUpdate, Token.ozMint,
    Finsupp.add_apply, MAX]

end Defi.ERC4626.Witnesses
