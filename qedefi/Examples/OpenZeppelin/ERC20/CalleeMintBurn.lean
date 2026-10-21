import Examples.OpenZeppelin.ERC20.Callee
import EvmLogic.Tactic.Patched

/-!
# `OzAsset.mint` and `OzAsset.burn` in any frame

`mint(dst, amount)` and `burn(src, amount)` of the deployed `ERC20Mock` (unrestricted `_mint`/`_burn`):
success with `mintWorld`/`burnWorld` and the `Transfer` log from/to the zero address, or the
reverts of `Model.ozMint`/`Model.ozBurn`.
-/

namespace Examples.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Solidity.ERC20
open EvmLean.Interpreter EvmLogic.Tactic QEDefi.ERC4626 Examples.OpenZeppelin.Contracts
open Examples.Solmate.ERC20 (TwoWordCall Reverts lt_size_four)

set_option maxHeartbeats 0 in
/-- **`mint(dst, amount)`, success**, in any non-static frame: nonzero `dst`, and
`totalSupply + amount` does not overflow. -/
theorem mint_halts_ok (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {dst : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x40c10f19 (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft) (hdst : dst ≠ 0)
    (hov : (assetView m).totalSupply.toNat + amount.toNat < 2 ^ 256) :
    Halts m (MintOk dst amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := ofAddress_ne_zero hdst
  have hov' : (m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat < 2 ^ 256 :=
    hov
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_add_self_eq_zero hov']
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine WP.halt_of_step (step_stop ?_) (by same_frame) ⟨rfl, ?_, rfl, rfl, ?_, ?_⟩
  · pcode_fact
  · rfl
  · event_log [amount]
  · evm_gas

set_option maxHeartbeats 0 in
/-- **`mint(dst, amount)`, revert**, in any frame, when `Model.ozMint` fails
(`ERC20InvalidReceiver`, supply overflow `Panic(0x11)`). -/
theorem mint_halts_revert (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) {dst : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x40c10f19 (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 10000 ≤ m.frame.gasLeft)
    (hm : Model.ozMint (assetView m) dst amount = none) :
    Halts m (Reverts 10000 m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  unfold Model.ozMint at hm
  by_cases hdst : dst = 0
  · subst hdst
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, ofAddress_zero,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    refine ⟨⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]
    evm_gas
  have hd' := ofAddress_ne_zero hdst
  simp only [hdst, ↓reduceIte] at hm
  have hov : 2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat := by
    split at hm
    · cases hm
    · rename_i h; exact Nat.le_of_not_lt h
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_add_self_eq_one hov]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨⟨_, rfl⟩, ?_⟩
  dsimp only [outputMachine]
  evm_gas

set_option maxHeartbeats 0 in
/-- **`burn(src, amount)`, success**, in any non-static frame: nonzero `src`, and
`amount ≤ balanceOf[src]`. -/
theorem burn_halts_ok (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft) (hsrc : src ≠ 0)
    (hbal : amount.toNat ≤ ((assetView m).balanceOf src).toNat) :
    Halts m (BurnOk src amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hs' := ofAddress_ne_zero hsrc
  simp only [view, balanceSlot_oz] at hbal
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [(Word.lt_eq_zero_iff _ _).2 hbal]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine WP.halt_of_step (step_stop ?_) (by same_frame) ⟨rfl, ?_, rfl, rfl, ?_, ?_⟩
  · pcode_fact
  · rfl
  · event_log [amount]
  · evm_gas

set_option maxHeartbeats 0 in
/-- **`burn(src, amount)`, revert**, in any frame, when `Model.ozBurn` fails
(`ERC20InvalidSender`, `ERC20InsufficientBalance`). -/
theorem burn_halts_revert (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) {src : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 10000 ≤ m.frame.gasLeft)
    (hm : Model.ozBurn (assetView m) src amount = none) :
    Halts m (Reverts 10000 m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  unfold Model.ozBurn at hm
  by_cases hsrc : src = 0
  · subst hsrc
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, ofAddress_zero,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    refine ⟨⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]
    evm_gas
  have hs' := ofAddress_ne_zero hsrc
  simp only [hsrc, ↓reduceIte] at hm
  have hbal : (m.world.sload m.frame.msg.currentTarget
      (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 0#256))).toNat <
        amount.toNat := by
    split at hm
    · cases hm
    · rename_i h; exact Nat.lt_of_not_le h
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [(Word.lt_eq_one_iff _ _).2 hbal]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨⟨_, rfl⟩, ?_⟩
  dsimp only [outputMachine]
  evm_gas

end Examples.OpenZeppelin.ERC20
