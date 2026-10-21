import QEDefi.ERC20.Rep
import EvmLogic.Tactic.Patched
import Examples.Solmate.Contracts.SolmateVaultData

/-!
# The vault's share token: storage frames and the allowance step

Facts about the share token's storage writes and the model's `spend` used by the refinement
theorems of `Shares.lean` and by the asset's (`ERC20/Spec.lean`); split from `Shares.lean` so
they do not wait for the bytecode theorems.
-/

namespace Examples.Solmate.ERC4626.Shares
open QEDefi.ERC20

open EvmLean Examples.Solmate EvmLogic EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic
open Examples.Solmate.Contracts EvmLogic.Solidity.ERC20 QEDefi.Math

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller : Address} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

/-! ## Storage frames -/

theorem sload_sstore_frame {w : World} {a b : Address} {key k v : Word} (h : b ≠ a ∨ k ≠ key) :
    (w.sstore a key v).sload b k = w.sload b k := by
  rw [World.sload_sstore]
  have : ¬ (b = a ∧ k = key) := by rintro ⟨rfl, rfl⟩; rcases h with h | h <;> exact h rfl
  simp [this]

theorem sload_transferWorld {crypto : Crypto} {w : World} {token src dst b : Address}
    {amount k : Word}
    (h : b ≠ token ∨ (k ≠ balanceSlot crypto Layout.solmate src ∧
      k ≠ balanceSlot crypto Layout.solmate dst)) :
    (transferWorld crypto w token src dst amount).sload b k = w.sload b k := by
  simp only [transferWorld, EvmLogic.Solidity.ERC20.transferWorld]
  rw [sload_sstore_frame (by rcases h with h | h; exact .inl h; exact .inr h.2),
    sload_sstore_frame (by rcases h with h | h; exact .inl h; exact .inr h.1)]

theorem sload_spendWorld {crypto : Crypto} {w : World} {token o sp b : Address} {amount k : Word}
    (h : b ≠ token ∨ k ≠ allowanceSlot crypto Layout.solmate o sp) :
    (spendWorld crypto w token o sp amount).sload b k = w.sload b k := by
  simp only [spendWorld]
  split
  · rfl
  · exact sload_sstore_frame h

/-! ## `transfer` -/

theorem Model_spend_balanceOf {s s₁ : ERC20.State} {o sp : Address} {amount : Word}
    (h : ERC20.Model.spend s o sp amount = some s₁) : s₁.balanceOf = s.balanceOf := by
  unfold ERC20.Model.spend at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

theorem allowance_cond_of_spend {s : ERC20.State} {t t₁ : Token Address} (hr : Rep s t)
    {o sp : Address} {amount : Word} (h : t.spend o sp amount.toNat = some t₁) :
    s.allowance o sp = maxWord ∨ amount.toNat ≤ (s.allowance o sp).toNat := by
  rw [eq_maxWord_iff, hr.allowance o sp trivial]
  unfold Token.spend at h
  split at h
  · exact .inl ‹_›
  · split at h
    · cases h
    · exact .inr (by omega)

theorem balance_spendWorld {crypto : Crypto} {w : World} {token src sp : Address} {amount : Word}
    (ha : AllowanceSlotOk crypto Layout.solmate src sp) {s₁ : ERC20.State}
    (hm : ERC20.Model.spend (view crypto Layout.solmate w token) src sp amount = some s₁) :
    (spendWorld crypto w token src sp amount).sload token (balanceSlot crypto Layout.solmate src) =
      (view crypto Layout.solmate w token).balanceOf src := by
  obtain ⟨-, e2, -, -⟩ := view_spendWorld (w := w) (token := token) ha hm
  have := congrFun e2 src
  rw [Model_spend_balanceOf hm] at this
  exact this

end Examples.Solmate.ERC4626.Shares
