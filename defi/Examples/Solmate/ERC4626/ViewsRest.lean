import Examples.Solmate.ERC4626.SharesFrameViews
import Examples.Solmate.ERC20.BalanceOf

/-!
# The remaining views of the vault and the asset, in any frame

Frame forms (fresh frame, any parents) of the getters not covered by `SharesFrameViews.lean`,
`VaultViews*.lean`, `AssetBalanceOf.lean`, `Strings*Spec.lean` and `Permit*DS.lean`:

* the vault's hook counters of `MockERC4626`: `beforeWithdrawHookCalledCounter()` (slot 6) and
  `afterDepositHookCalledCounter()` (slot 7): `vaultBeforeWithdrawCounter_halts`,
  `vaultAfterDepositCounter_halts`;
* the asset's `totalSupply()`, `allowance(owner, spender)` and `decimals()`:
  `assetTotalSupply_halts`, `assetAllowance_halts`, `assetDecimals_halts`.

Each returns the ABI word of the value read from storage (`decimals`: the immutable masked to
`uint8`) and leaves the world unchanged (`SharesViewPost`).
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-! ## The vault's hook counters -/

set_option maxHeartbeats 0 in
/-- **`beforeWithdrawHookCalledCounter()` of the vault** (slot 6), in any frame. -/
theorem vaultBeforeWithdrawCounter_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hd : NoArgCall m.frame.msg.data 0xbc368a8a) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget 6#256) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`afterDepositHookCalledCounter()` of the vault** (slot 7), in any frame. -/
theorem vaultAfterDepositCounter_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hd : NoArgCall m.frame.msg.data 0xfc407ae7) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget 7#256) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

/-! ## The asset's views -/

/-- The asset's `decimals` immutable, as its `PUSH32` reads it. -/
theorem readBytes_assetCode_decimals (ia : SolmateAsset.Immutables) :
    readBytes (SolmateAsset.runtimeCodeWith ia) 345 32 = Bytes.ofWord ia.decimals := by
  have hp : ia.patches = [(1063, ia.initialChainId), (1116, ia.initialDomainSeparator)] ++
      (345, ia.decimals) :: [] := rfl
  simp only [SolmateAsset.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateAsset.size_runtimeCode]; decide)
    (by simp)

set_option maxHeartbeats 0 in
/-- **`totalSupply()` of the asset**, in any frame. -/
theorem assetTotalSupply_halts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hd : NoArgCall m.frame.msg.data 0x18160ddd) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget 2#256) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`allowance(owner, spender)` of the asset**, in any frame. -/
theorem assetAllowance_halts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    {owner spender : Address}
    (hd : TwoWordCall m.frame.msg.data 0xdd62ed3e (Word.ofAddress owner) (Word.ofAddress spender))
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget
      (Erc20.allowanceSlot m.ctx.crypto Erc20.Layout.solmate owner spender)) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`decimals()` of the asset**, in any frame: the immutable as a `uint8`. -/
theorem assetDecimals_halts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hd : NoArgCall m.frame.msg.data 0x313ce567) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (ia.decimals &&& 255#256) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64,
    readBytes_assetCode_decimals]
  exact ⟨rfl, rfl⟩

end EvmLeanSpecs.Refinement
