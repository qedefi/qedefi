import Examples.Solmate.ERC4626.UnknownSelectors
import Examples.Solmate.ERC20.Malformed

/-!
# Malformed calldata for the vault (first half)

The vault functions `allowance` to `mint` of `vaultArgShapes`: fewer argument words than the
function takes (`vault_<f>_short`), or a dirty `address` argument after clean ones
(`vault_<f>_dirty<j>`) reverts in the ABI decoder. See `MalformedCalldata.lean`.
-/

section

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

set_option maxHeartbeats 0 in
/-- `allowance` of the vault with fewer than 2 argument words reverts. -/
theorem vault_allowance_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xdd62ed3e) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 68) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `allowance` of the vault with dirty high bytes in its first argument (an `address`) reverts. -/
theorem vault_allowance_dirty0 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xdd62ed3e) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `allowance` of the vault with dirty high bytes in its second argument (an `address`) reverts. -/
theorem vault_allowance_dirty1 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xdd62ed3e) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc0 : CleanAddr m.frame.msg.data 0)
    (hd : ¬ CleanAddr m.frame.msg.data 1) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hc0' := cleanAddr_lit hc0
  simp only [argWord] at hc0'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc0', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `approve` of the vault with fewer than 2 argument words reverts. -/
theorem vault_approve_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 68) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `approve` of the vault with dirty high bytes in its first argument (an `address`) reverts. -/
theorem vault_approve_dirty0 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `balanceOf` of the vault with fewer than 1 argument word reverts. -/
theorem vault_balanceOf_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x70a08231) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `balanceOf` of the vault with dirty high bytes in its first argument (an `address`) reverts. -/
theorem vault_balanceOf_dirty0 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x70a08231) (hsize : 36 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `convertToAssets` of the vault with fewer than 1 argument word reverts. -/
theorem vault_convertToAssets_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x07a2d13a) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `convertToShares` of the vault with fewer than 1 argument word reverts. -/
theorem vault_convertToShares_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xc6e6f592) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `deposit` of the vault with fewer than 2 argument words reverts. -/
theorem vault_deposit_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x6e553f65) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 68) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `deposit` of the vault with dirty high bytes in its second argument (an `address`) reverts. -/
theorem vault_deposit_dirty1 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x6e553f65) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 1) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `maxDeposit` of the vault with fewer than 1 argument word reverts. -/
theorem vault_maxDeposit_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x402d267d) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `maxDeposit` of the vault with dirty high bytes in its first argument (an `address`) reverts. -/
theorem vault_maxDeposit_dirty0 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x402d267d) (hsize : 36 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `maxMint` of the vault with fewer than 1 argument word reverts. -/
theorem vault_maxMint_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xc63d75b6) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `maxMint` of the vault with dirty high bytes in its first argument (an `address`) reverts. -/
theorem vault_maxMint_dirty0 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xc63d75b6) (hsize : 36 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `maxRedeem` of the vault with fewer than 1 argument word reverts. -/
theorem vault_maxRedeem_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd905777e) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `maxRedeem` of the vault with dirty high bytes in its first argument (an `address`) reverts. -/
theorem vault_maxRedeem_dirty0 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd905777e) (hsize : 36 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `maxWithdraw` of the vault with fewer than 1 argument word reverts. -/
theorem vault_maxWithdraw_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xce96cb77) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `maxWithdraw` of the vault with dirty high bytes in its first argument (an `address`) reverts.
-/
theorem vault_maxWithdraw_dirty0 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xce96cb77) (hsize : 36 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `mint` of the vault with fewer than 2 argument words reverts. -/
theorem vault_mint_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x94bf804d) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 68) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `mint` of the vault with dirty high bytes in its second argument (an `address`) reverts. -/
theorem vault_mint_dirty1 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x94bf804d) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 1) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

end EvmLeanSpecs.Refinement

end

section

/-!
## Malformed calldata for the vault (second half)

The remaining vault functions of `vaultArgShapes`: fewer argument words than the function
takes (`vault_<f>_short`), or a dirty `address` argument after clean ones
(`vault_<f>_dirty<j>`) reverts in the ABI decoder. See `MalformedCalldata.lean`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

set_option maxHeartbeats 0 in
/-- `nonces` of the vault with fewer than 1 argument word reverts. -/
theorem vault_nonces_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x7ecebe00) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `nonces` of the vault with dirty high bytes in its first argument (an `address`) reverts. -/
theorem vault_nonces_dirty0 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x7ecebe00) (hsize : 36 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `permit` of the vault with fewer than 7 argument words reverts. -/
theorem vault_permit_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 228) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `permit` of the vault with dirty high bytes in its first argument (an `address`) reverts. -/
theorem vault_permit_dirty0 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (hsize : 228 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `permit` of the vault with dirty high bytes in its second argument (an `address`) reverts. -/
theorem vault_permit_dirty1 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (hsize : 228 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc0 : CleanAddr m.frame.msg.data 0)
    (hd : ¬ CleanAddr m.frame.msg.data 1) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hc0' := cleanAddr_lit hc0
  simp only [argWord] at hc0'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc0', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `previewDeposit` of the vault with fewer than 1 argument word reverts. -/
theorem vault_previewDeposit_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xef8b30f7) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `previewMint` of the vault with fewer than 1 argument word reverts. -/
theorem vault_previewMint_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xb3d7f6b9) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `previewRedeem` of the vault with fewer than 1 argument word reverts. -/
theorem vault_previewRedeem_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x4cdad506) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `previewWithdraw` of the vault with fewer than 1 argument word reverts. -/
theorem vault_previewWithdraw_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x0a28a477) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `redeem` of the vault with fewer than 3 argument words reverts. -/
theorem vault_redeem_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xba087652) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 100) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `redeem` of the vault with dirty high bytes in its second argument (an `address`) reverts. -/
theorem vault_redeem_dirty1 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xba087652) (hsize : 100 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 1) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `redeem` of the vault with dirty high bytes in its third argument (an `address`) reverts. -/
theorem vault_redeem_dirty2 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xba087652) (hsize : 100 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc1 : CleanAddr m.frame.msg.data 1)
    (hd : ¬ CleanAddr m.frame.msg.data 2) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hc1' := cleanAddr_lit hc1
  simp only [argWord] at hc1'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc1', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `transfer` of the vault with fewer than 2 argument words reverts. -/
theorem vault_transfer_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 68) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `transfer` of the vault with dirty high bytes in its first argument (an `address`) reverts. -/
theorem vault_transfer_dirty0 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `transferFrom` of the vault with fewer than 3 argument words reverts. -/
theorem vault_transferFrom_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 100) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `transferFrom` of the vault with dirty high bytes in its first argument (an `address`) reverts.
-/
theorem vault_transferFrom_dirty0 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (hsize : 100 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `transferFrom` of the vault with dirty high bytes in its second argument (an `address`)
reverts. -/
theorem vault_transferFrom_dirty1 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (hsize : 100 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc0 : CleanAddr m.frame.msg.data 0)
    (hd : ¬ CleanAddr m.frame.msg.data 1) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hc0' := cleanAddr_lit hc0
  simp only [argWord] at hc0'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc0', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `withdraw` of the vault with fewer than 3 argument words reverts. -/
theorem vault_withdraw_short {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xb460af94) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 100) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `withdraw` of the vault with dirty high bytes in its second argument (an `address`) reverts. -/
theorem vault_withdraw_dirty1 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xb460af94) (hsize : 100 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 1) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `withdraw` of the vault with dirty high bytes in its third argument (an `address`) reverts. -/
theorem vault_withdraw_dirty2 {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xb460af94) (hsize : 100 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc1 : CleanAddr m.frame.msg.data 1)
    (hd : ¬ CleanAddr m.frame.msg.data 2) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hc1' := cleanAddr_lit hc1
  simp only [argWord] at hc1'
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc1', Solidity.eq_self]
  exact ⟨_, rfl⟩

end EvmLeanSpecs.Refinement

end

section

/-!
## Malformed calldata for a known selector reverts

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

end
