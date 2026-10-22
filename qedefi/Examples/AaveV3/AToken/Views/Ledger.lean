import Examples.AaveV3.AToken.State

/-!
# `AToken`: the scaled-ledger views

In any fresh frame (so also for the proxy's `DELEGATECALL`), each view returns the ABI word(s)
of the executing account's storage and changes nothing: `scaledBalanceOf(a)` the low 120 bits
of `_userState[a]`, `scaledTotalSupply()` slot 54, `getScaledUserBalanceAndSupply(a)` both,
`getPreviousIndex(a)` the high 128 bits of `_userState[a]`.
-/

namespace Examples.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Examples.AaveV3.Contracts
open Examples.Solmate.ERC20 (lt_size_four)

/-! ## The scaled ledger -/

/-- **`scaledBalanceOf(a)`** returns `scaledBalance` of `a`; nothing changes. -/
theorem scaledBalanceOf_halts (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0x1da24f3e)
    (hsize : 36 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64) {a : Address}
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress a)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (Returns (Bytes.ofWord (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget a))
      3000 m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
      (BitVec.ofNat 256 32)) = 1 := iszero_slt_calldatasize (by omega) (by omega)
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [mask120_and]; rfl
  · dsimp only [outputMachine]
    evm_gas

/-- **`scaledTotalSupply()`** returns slot 54; nothing changes. -/
theorem scaledTotalSupply_halts (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0xb1bf962d)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (Returns (Bytes.ofWord (scaledTotalSupply m.world m.frame.msg.currentTarget)) 3000 m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64]
  refine ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [outputMachine]
  evm_gas

/-- **`getScaledUserBalanceAndSupply(a)`** returns `(scaledBalance a, scaledTotalSupply)`;
nothing changes. -/
theorem getScaledUserBalanceAndSupply_halts (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0x0afbcdc9)
    (hsize : 36 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64) {a : Address}
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress a)
    (hg : 5000 ≤ m.frame.gasLeft) :
    Halts m (Returns
      (Bytes.ofWord (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget a) ++
        Bytes.ofWord (scaledTotalSupply m.world m.frame.msg.currentTarget)) 5000 m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
      (BitVec.ofNat 256 32)) = 1 := iszero_slt_calldatasize (by omega) (by omega)
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [mask120_and]; rfl
  · dsimp only [outputMachine]
    evm_gas

/-- **`getPreviousIndex(a)`** returns `previousIndex` of `a`; nothing changes. -/
theorem getPreviousIndex_halts (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0xe0753986)
    (hsize : 36 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64) {a : Address}
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress a)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (Returns (Bytes.ofWord (previousIndex m.ctx.crypto m.world m.frame.msg.currentTarget a))
      3000 m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
      (BitVec.ofNat 256 32)) = 1 := iszero_slt_calldatasize (by omega) (by omega)
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [mask128_and_div]; rfl
  · dsimp only [outputMachine]
    evm_gas

end Examples.AaveV3.AToken
