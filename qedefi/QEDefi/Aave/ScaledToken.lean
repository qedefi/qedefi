module

public import QEDefi.Aave.WadRayMath
public import QEDefi.ERC20.Token

/-!
# Aave v3 scaled-balance tokens (aToken / variable debt token storage)

`ScaledBalanceTokenBase` (+ `MintableIncentivizedERC20`, `IncentivizedERC20`) of the deployed
aToken (`ATOKEN_REVISION = 5`) and variable debt token (`DEBT_TOKEN_REVISION = 5`)
implementations: per-user scaled balances (`uint120`), the scaled total supply (`uint256`) and
the per-user last index (`additionalData`, `uint128`).

* `mintScaled`/`burnScaled` mirror `_mintScaled`/`_burnScaled`, parametrised by the balance
  function `getBal` (`TokenMath.getATokenBalance = rayMulFloor` for aTokens,
  `getVTokenBalance = rayMulCeil` for debt tokens), including every checked subtraction and
  `SafeCast` that can revert.
* `transferScaled` mirrors the aToken's internal
  `_transfer(sender, recipient, amount, scaledAmount, index)`.

The incentives controller hook (`handleAction`) is not modelled (assumed not to revert), nor are
events or allowances. Main fact: `Σ balances = totalSupply` (`WF`) is preserved by every
operation.
-/

section

@[expose] public noncomputable section

namespace QEDefi.Aave
open QEDefi.Math QEDefi.ERC20 Finsupp

/-- `type(uint120).max`. -/
def UINT120_MAX : ℕ := 2 ^ 120 - 1

/-- `type(uint128).max`. -/
def UINT128_MAX : ℕ := 2 ^ 128 - 1

/-- Storage of a scaled-balance token. -/
structure ScaledToken (A : Type) where
  /-- `_userState[u].balance`: the scaled balance (`uint120`). -/
  balance : A →₀ ℕ
  /-- `_totalSupply`: the scaled total supply. -/
  totalSupply : ℕ
  /-- `_userState[u].additionalData`: the index at the user's last interaction (`uint128`). -/
  index : A → ℕ

namespace ScaledToken

variable {A : Type} [DecidableEq A]

/-- Well-formedness: the scaled balances sum to the scaled total supply. -/
def WF (t : ScaledToken A) : Prop := total t.balance = t.totalSupply

/-- The empty token. -/
def empty : ScaledToken A := ⟨0, 0, fun _ => 0⟩

/-- `MintableIncentivizedERC20._mint(account, uint120 amount)`: both additions checked. -/
def mint (t : ScaledToken A) (u : A) (v : ℕ) : Option (ScaledToken A) :=
  if MAX < t.totalSupply + v then none
  else if UINT120_MAX < t.balance u + v then none
  else some { t with totalSupply := t.totalSupply + v, balance := t.balance + single u v }

/-- `MintableIncentivizedERC20._burn(account, uint120 amount)`: both subtractions checked. -/
def burn (t : ScaledToken A) (u : A) (v : ℕ) : Option (ScaledToken A) :=
  if t.totalSupply < v then none
  else if t.balance u < v then none
  else some { t with totalSupply := t.totalSupply - v, balance := t.balance - single u v }

/-- `IncentivizedERC20._transfer(sender, recipient, uint120 amount)`. The recipient's balance is
read after the sender's is written, so `s = r` is a no-op. -/
def move (t : ScaledToken A) (s r : A) (v : ℕ) : Option (ScaledToken A) :=
  if t.balance s < v then none
  else if UINT120_MAX < (t.balance - single s v) r + v then none
  else some { t with balance := t.balance - single s v + single r v }

/-- `_userState[u].additionalData = index`. -/
def setIndex (t : ScaledToken A) (u : A) (i : ℕ) : ScaledToken A :=
  { t with index := Function.update t.index u i }

/-- `ScaledBalanceTokenBase._mintScaled(caller, onBehalfOf = u, amountScaled, index,
getTokenBalance)`. Returns the new storage and `scaledBalance == 0` (first supply). -/
def mintScaled (getBal : ℕ → ℕ → Option ℕ) (t : ScaledToken A) (u : A) (amt idx : ℕ) :
    Option (ScaledToken A × Bool) :=
  if amt = 0 then none else                                   -- InvalidMintAmount
  let sb := t.balance u
  (checkedAdd amt sb).bind fun s1 =>
  (getBal s1 idx).bind fun nextBalance =>
  (getBal sb (t.index u)).bind fun previousBalance =>
  (getBal sb idx).bind fun cur =>
  if cur < previousBalance then none else                     -- balanceIncrease (checked)
  if UINT128_MAX < idx then none else                         -- index.toUint128()
  if UINT120_MAX < amt then none else                         -- amountScaled.toUint120()
  ((t.setIndex u idx).mint u amt).bind fun t' =>
  if nextBalance < previousBalance then none else             -- amountToMint (checked)
  some (t', sb == 0)

/-- `ScaledBalanceTokenBase._burnScaled(user = u, target, amountScaled, index,
getTokenBalance)`. Returns the new storage and `scaledBalance - amountScaled == 0`. -/
def burnScaled (getBal : ℕ → ℕ → Option ℕ) (t : ScaledToken A) (u : A) (amt idx : ℕ) :
    Option (ScaledToken A × Bool) :=
  if amt = 0 then none else                                   -- InvalidBurnAmount
  let sb := t.balance u
  if sb < amt then none else                                  -- scaledBalance - amountScaled
  (getBal (sb - amt) idx).bind fun _nextBalance =>
  (getBal sb (t.index u)).bind fun previousBalance =>
  (getBal sb idx).bind fun cur =>
  if cur < previousBalance then none else                     -- balanceIncrease (checked)
  if UINT128_MAX < idx then none else
  if UINT120_MAX < amt then none else
  ((t.setIndex u idx).burn u amt).map fun t' => (t', sb - amt == 0)

/-- `AToken._transfer(sender, recipient, amount, uint120 scaledAmount, index)` (the scaled
amount's `toUint120()` cast, done by every caller, is included). -/
def transferScaled (getBal : ℕ → ℕ → Option ℕ) (t : ScaledToken A) (s r : A) (sa idx : ℕ) :
    Option (ScaledToken A) :=
  if UINT120_MAX < sa then none else
  (getBal (t.balance s) idx).bind fun curS =>
  (getBal (t.balance s) (t.index s)).bind fun prevS =>
  if curS < prevS then none else                              -- senderBalanceIncrease
  (getBal (t.balance r) idx).bind fun curR =>
  (getBal (t.balance r) (t.index r)).bind fun prevR =>
  if curR < prevR then none else                              -- recipientBalanceIncrease
  if UINT128_MAX < idx then none else
  ((t.setIndex s idx).setIndex r idx).move s r sa

/-! ## Effects -/

theorem mint_eq_some {t t' : ScaledToken A} {u : A} {v : ℕ} (h : t.mint u v = some t') :
    t'.totalSupply = t.totalSupply + v ∧ t'.balance = t.balance + single u v ∧
      t'.index = t.index ∧ t.totalSupply + v ≤ MAX := by
  unfold mint at h; split_ifs at h with h1 h2; cases h; exact ⟨rfl, rfl, rfl, by omega⟩

theorem burn_eq_some {t t' : ScaledToken A} {u : A} {v : ℕ} (h : t.burn u v = some t') :
    t'.totalSupply = t.totalSupply - v ∧ t'.balance = t.balance - single u v ∧
      t'.index = t.index ∧ v ≤ t.totalSupply ∧ v ≤ t.balance u := by
  unfold burn at h; split_ifs at h with h1 h2; cases h; exact ⟨rfl, rfl, rfl, by omega, by omega⟩

theorem move_eq_some {t t' : ScaledToken A} {s r : A} {v : ℕ} (h : t.move s r v = some t') :
    t'.totalSupply = t.totalSupply ∧ t'.balance = t.balance - single s v + single r v ∧
      t'.index = t.index ∧ v ≤ t.balance s := by
  unfold move at h; split_ifs at h with h1 h2; cases h; exact ⟨rfl, rfl, rfl, by omega⟩

/-- A successful `_mintScaled` adds `amt ≠ 0` to the user's balance and to the total. -/
theorem mintScaled_eq_some {getBal} {t : ScaledToken A} {u : A} {amt idx : ℕ} {r}
    (h : t.mintScaled getBal u amt idx = some r) :
    amt ≠ 0 ∧ r.1.totalSupply = t.totalSupply + amt ∧ r.1.balance = t.balance + single u amt ∧
      r.1.index = Function.update t.index u idx ∧ r.2 = (t.balance u == 0) := by
  unfold mintScaled at h
  simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨h0, s1, -, n, -, p, -, c, -, -, -, -, t', ht', -, rfl⟩ := h
  obtain ⟨e1, e2, e3, -⟩ := mint_eq_some ht'
  exact ⟨h0, e1, e2, e3, rfl⟩

/-- A successful `_burnScaled` removes `0 < amt ≤ balance` from the user and the total. -/
theorem burnScaled_eq_some {getBal} {t : ScaledToken A} {u : A} {amt idx : ℕ} {r}
    (h : t.burnScaled getBal u amt idx = some r) :
    amt ≠ 0 ∧ amt ≤ t.balance u ∧ amt ≤ t.totalSupply ∧ r.1.totalSupply = t.totalSupply - amt ∧
      r.1.balance = t.balance - single u amt ∧
      r.1.index = Function.update t.index u idx ∧ r.2 = (t.balance u - amt == 0) := by
  unfold burnScaled at h
  simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some, Option.map_eq_some_iff] at h
  obtain ⟨h0, h1, n, -, p, -, c, -, -, -, -, t', ht', rfl⟩ := h
  obtain ⟨e1, e2, e3, e4, -⟩ := burn_eq_some ht'
  exact ⟨h0, by omega, e4, e1, e2, e3, rfl⟩

/-- A successful transfer moves `sa ≤ balance s` from `s` to `r`; the total is unchanged. -/
theorem transferScaled_eq_some {getBal} {t t' : ScaledToken A} {s r : A} {sa idx : ℕ}
    (h : t.transferScaled getBal s r sa idx = some t') :
    t'.totalSupply = t.totalSupply ∧ t'.balance = t.balance - single s sa + single r sa ∧
      sa ≤ t.balance s := by
  unfold transferScaled at h
  simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some] at h
  obtain ⟨-, cs, -, ps, -, -, cr, -, pr, -, -, -, h⟩ := h
  obtain ⟨e1, e2, -, e4⟩ := move_eq_some h
  exact ⟨e1, e2, e4⟩

/-! ## `Σ scaled balances = scaledTotalSupply` -/

theorem WF_empty : (empty : ScaledToken A).WF := by simp [WF, empty, total]

theorem balance_le_totalSupply {t : ScaledToken A} (hw : t.WF) (a : A) :
    t.balance a ≤ t.totalSupply := hw ▸ Token.le_total _ a

theorem WF_mintScaled {getBal} {t : ScaledToken A} {u : A} {amt idx : ℕ} {r}
    (hw : t.WF) (h : t.mintScaled getBal u amt idx = some r) : r.1.WF := by
  obtain ⟨-, e1, e2, -⟩ := mintScaled_eq_some h
  unfold WF at *; rw [e1, e2, Token.total_add_single, hw]

theorem WF_burnScaled {getBal} {t : ScaledToken A} {u : A} {amt idx : ℕ} {r}
    (hw : t.WF) (h : t.burnScaled getBal u amt idx = some r) : r.1.WF := by
  obtain ⟨-, h1, -, e1, e2, -⟩ := burnScaled_eq_some h
  unfold WF at *; rw [e1, e2, Token.total_sub_single h1, hw]

theorem WF_transferScaled {getBal} {t t' : ScaledToken A} {s r : A} {sa idx : ℕ}
    (hw : t.WF) (h : t.transferScaled getBal s r sa idx = some t') : t'.WF := by
  obtain ⟨e1, e2, h1⟩ := transferScaled_eq_some h
  unfold WF at *
  rw [e1, e2, Token.total_add_single, Token.total_sub_single h1]
  have := Token.le_total t.balance s
  omega

end ScaledToken

end QEDefi.Aave
end

end
