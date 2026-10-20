import EvmLeanSpecs.Refinement.MalformedVaultA
import EvmLeanSpecs.Refinement.MalformedVaultB
import EvmLeanSpecs.Refinement.MalformedAsset

/-!
# Malformed calldata for a known selector reverts

Each function of the vault and the asset that takes arguments starts with solc's ABI decoder
(`abi_decode_tuple_*`): it reverts if the calldata holds fewer argument words than the
function takes (`iszero(slt(sub(calldatasize(), 4), 32·k))`), then decodes the arguments in
order, reverting at the first `address` argument whose high 96 bits are not zero
(`validator_revert_t_address`: `eq(x, and(x, 2¹⁶⁰ − 1))`). Proved for the deployed bytecode
(any immutables), in any fresh frame, with no value, with at least 2000 gas:

* `vault_<f>_short`, `asset_<f>_short` (`MalformedVault*.lean`, `MalformedAsset.lean`): fewer
  than `k` argument words;
* `vault_<f>_dirty<j>`, `asset_<f>_dirty<j>`: the `address` argument `j` is dirty, the
  earlier ones clean (`CleanAddr`);
* `vault_malformed_reverts`, `asset_malformed_reverts`: dispatch over the tables
  `vaultArgShapes` / `assetArgShapes` (selector, number of argument words, positions of the
  `address` arguments) and `Malformed`.

Together with `UnknownSelectors.lean` and the frame summaries of every function, every
calldata is accounted for: an unknown selector or a calldata shorter than a selector, a
malformed one (this file), or a well-formed call (`Executes`, `ViewData`, `PermitData`;
`permit`'s `uint8 v` above 255 fails `Permit.PermitValid`).
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-! ## Dispatch over the function shapes -/

/-- **Malformed calldata for a function of the vault reverts**, in any frame: the selector of a
function with arguments (`vaultArgShapes`), and too few argument words or an `address` argument with
dirty high bytes (the earlier `address` arguments clean). -/
theorem vault_malformed_reverts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hg : 2000 ≤ m.frame.gasLeft)
    {sel k : Nat} {addrs : List Nat} (hmem : (sel, k, addrs) ∈ vaultArgShapes)
    (hsel : Abi.selectorOf m.frame.msg.data = sel) (h4 : 4 ≤ m.frame.msg.data.size)
    (hbad : Malformed m.frame.msg.data k addrs) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  simp only [vaultArgShapes, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_allowance_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact vault_allowance_dirty0 m hf hval hsel hs hsize' hd hg
      · exact vault_allowance_dirty1 m hf hval hsel hs hsize' (hc 0 (by simp) (by decide)) hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_approve_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact vault_approve_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_balanceOf_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact vault_balanceOf_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_convertToAssets_short m hf hval hsel h4 hs hg
    · simp at hj
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_convertToShares_short m hf hval hsel h4 hs hg
    · simp at hj
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_deposit_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact vault_deposit_dirty1 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_maxDeposit_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact vault_maxDeposit_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_maxMint_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact vault_maxMint_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_maxRedeem_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact vault_maxRedeem_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_maxWithdraw_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact vault_maxWithdraw_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_mint_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact vault_mint_dirty1 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_nonces_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact vault_nonces_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_permit_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact vault_permit_dirty0 m hf hval hsel hs hsize' hd hg
      · exact vault_permit_dirty1 m hf hval hsel hs hsize' (hc 0 (by simp) (by decide)) hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_previewDeposit_short m hf hval hsel h4 hs hg
    · simp at hj
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_previewMint_short m hf hval hsel h4 hs hg
    · simp at hj
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_previewRedeem_short m hf hval hsel h4 hs hg
    · simp at hj
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_previewWithdraw_short m hf hval hsel h4 hs hg
    · simp at hj
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_redeem_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact vault_redeem_dirty1 m hf hval hsel hs hsize' hd hg
      · exact vault_redeem_dirty2 m hf hval hsel hs hsize' (hc 1 (by simp) (by decide)) hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_transfer_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact vault_transfer_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_transferFrom_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact vault_transferFrom_dirty0 m hf hval hsel hs hsize' hd hg
      · exact vault_transferFrom_dirty1 m hf hval hsel hs hsize' (hc 0 (by simp) (by decide)) hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact vault_withdraw_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact vault_withdraw_dirty1 m hf hval hsel hs hsize' hd hg
      · exact vault_withdraw_dirty2 m hf hval hsel hs hsize' (hc 1 (by simp) (by decide)) hd hg

/-- **Malformed calldata for a function of the asset reverts**, in any frame: the selector of a
function with arguments (`assetArgShapes`), and too few argument words or an `address` argument with
dirty high bytes (the earlier `address` arguments clean). -/
theorem asset_malformed_reverts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hg : 2000 ≤ m.frame.gasLeft)
    {sel k : Nat} {addrs : List Nat} (hmem : (sel, k, addrs) ∈ assetArgShapes)
    (hsel : Abi.selectorOf m.frame.msg.data = sel) (h4 : 4 ≤ m.frame.msg.data.size)
    (hbad : Malformed m.frame.msg.data k addrs) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  simp only [assetArgShapes, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact asset_allowance_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact asset_allowance_dirty0 m hf hval hsel hs hsize' hd hg
      · exact asset_allowance_dirty1 m hf hval hsel hs hsize' (hc 0 (by simp) (by decide)) hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact asset_approve_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact asset_approve_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact asset_balanceOf_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact asset_balanceOf_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact asset_burn_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact asset_burn_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact asset_mint_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact asset_mint_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact asset_nonces_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact asset_nonces_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact asset_permit_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact asset_permit_dirty0 m hf hval hsel hs hsize' hd hg
      · exact asset_permit_dirty1 m hf hval hsel hs hsize' (hc 0 (by simp) (by decide)) hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact asset_transfer_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact asset_transfer_dirty0 m hf hval hsel hs hsize' hd hg
  · rcases hbad with hs | ⟨hs, j, hj, hc, hd⟩
    · exact asset_transferFrom_short m hf hval hsel h4 hs hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact asset_transferFrom_dirty0 m hf hval hsel hs hsize' hd hg
      · exact asset_transferFrom_dirty1 m hf hval hsel hs hsize' (hc 0 (by simp) (by decide)) hd hg

end EvmLeanSpecs.Refinement
