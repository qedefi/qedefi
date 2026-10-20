import Examples.Solmate.ERC4626.MalformedDefs

/-!
# Malformed calldata for the vault (second half)

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
