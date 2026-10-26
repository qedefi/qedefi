import Verified.Solady.Spec.Spec
import QEDefi.ERC20.Spec.Invariant

/-!
# Solady's `ERC20`: the supply is the sum of the balances, after any transactions

`solady_supply_eq_sum` (the open challenge *SoladySupplySum*): for the compiled `SoladyToken`
at `a`, the value in Solady's supply slot `0x05345cdf77eb68f44c` equals the sum of the actors'
balance rows `keccak256(o ‖ 0⁸ ‖ 0x87a211a2)` after any sequence of successful transactions,
when it did before, provided every token frame the transactions reach touches only actors and
**makes no `permit` call** (`TxTouch` with `perm = none`: a frame whose calldata is a `permit` is
not well formed there, so such transactions are outside the hypothesis). `permit` is excluded
because Solady's `PermitSpec` is not proved yet; it only writes an allowance row and a nonce row,
so it cannot change the supply or a balance, but that is not a theorem here. It is
`Invariant.variant_conserved` for `Variant.solady PERMIT2` applied to `solady_spec`.
-/

namespace Verified.Solady.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity EvmLogic.Tx
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Solady QEDefi.ERC20.Spec.Invariant
open Verified.Solady.Contracts

theorem delegatedAddress?_soladyCode : delegatedAddress? SoladyToken.runtimeCode = none :=
  delegatedAddress?_of_size (by rw [SoladyToken.size_runtimeCode]; decide)

/-- The model's invariant reads no ether: Solady's `WF` is about balances and supply only. -/
theorem soladyAbs_etherFree : EtherFree soladyAbs M := by
  intro crypto Act w w' t hk hw
  have h := read_congr crypto Act w w' t hk
  simp only [M, Solady.soladyModel, Variant.model_wf, Variant.WF, Variant.solady,
    Variant.standard, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hw ⊢
  show total (read crypto Act w' t).bal + total (read crypto Act w' t).frozen =
    (read crypto Act w' t).supply ∧ (read crypto Act w' t).supply ≤ QEDefi.Math.MAX
  have e1 : (read crypto Act w' t).bal = (read crypto Act w t).bal := by
    simp only [read, balances]
    ext b; simp only [Finsupp.onFinset_apply]
    split
    · rename_i hb; rw [hk _ (bal_mem b hb)]
    · rfl
  have e2 : (read crypto Act w' t).supply = (read crypto Act w t).supply := by
    simp only [read, readSlot]; rw [hk _ supply_mem]
  rw [e1, e2]
  exact hw

theorem total_balances (crypto : Crypto) (Act : Finset Address) (w : World) (a : Address) :
    total (balances crypto Act w a) =
      ∑ b ∈ Act, (w.sload a (balSlot crypto b)).toNat := by
  unfold total balances
  rw [Finsupp.onFinset_sum _ (fun _ => rfl)]
  exact Finset.sum_congr rfl fun b hb => by simp [hb]

/-- **SoladySupplySum: `totalSupply = Σ balanceOf` after any transactions without `permit`.**
For the compiled `SoladyToken` at `a` and a finite set of actors `Act` whose storage rows are
distinct (`SoladySound`): if the actors' balance rows add up to the supply slot in `w` (the
actors hold every token) and all ether is below `2²⁵⁶`, they do after any sequence of
successful transactions using `crypto` whose token frames touch only actors and make no
`permit` call. -/
theorem solady_supply_eq_sum {crypto : Crypto} {Act : Finset Address} {a : Address}
    {w w' : World} (hsound : SoladySound crypto Act)
    (hw : TokInv SoladyToken.runtimeCode soladyAbs M crypto Act a w)
    (hsup : QEDefi.Solvency.supply w < 2 ^ 256)
    (h : TxSteps (TxTouch SoladyToken.runtimeCode soladyAbs M sel ops opAddrs none crypto
      Act a) w w') :
    ∑ b ∈ Act, (w'.sload a (balSlot crypto b)).toNat = (w'.sload a supplySlot).toNat := by
  have := variant_conserved (V := Variant.solady PERMIT2) (ev := soladyEvents)
    (Variant.solady_sane PERMIT2) rfl rfl solady_spec (fun _ _ h => by cases h)
    soladyAbs_etherFree hsound (by rw [SoladyToken.size_runtimeCode]; decide)
    (by rw [SoladyToken.size_runtimeCode]; decide)
    delegatedAddress?_soladyCode ⟨hw, hsup⟩ h
  simp only [soladyAbs, read, total_balances] at this
  simpa [total, readSlot] using this

end Verified.Solady.Spec
