import Examples.Solmate.ERC4626.UnknownSelectors

/-!
# Malformed calldata for the asset

For each asset function of `assetArgShapes`: too few argument words (`asset_<f>_short`) or a
dirty `address` argument after clean ones (`asset_<f>_dirty<j>`) reverts in the ABI decoder
(`docs/erc4626/details.md` §5).
-/

namespace Examples.Solmate.ERC20
open Examples.Solmate.ERC4626 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

set_option maxHeartbeats 0 in
theorem asset_allowance_short {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xdd62ed3e) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 68) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_allowance_dirty0 {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
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
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_allowance_dirty1 {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
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
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc0', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_approve_short {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 68) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_approve_dirty0 {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
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
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_balanceOf_short {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x70a08231) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_balanceOf_dirty0 {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
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
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_burn_short {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x9dc29fac) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 68) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_burn_dirty0 {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x9dc29fac) (hsize : 68 ≤ m.frame.msg.data.size)
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
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_mint_short {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x40c10f19) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 68) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_mint_dirty0 {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x40c10f19) (hsize : 68 ≤ m.frame.msg.data.size)
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
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_nonces_short {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x7ecebe00) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 36) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_nonces_dirty0 {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
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
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_permit_short {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 228) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_permit_dirty0 {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
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
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_permit_dirty1 {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
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
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc0', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_transfer_short {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 68) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_transfer_dirty0 {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
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
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_transferFrom_short {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (hsize : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 100) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_transferFrom_dirty0 {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
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
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem asset_transferFrom_dirty1 {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
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
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc0', Solidity.eq_self]
  exact ⟨_, rfl⟩

end Examples.Solmate.ERC20
