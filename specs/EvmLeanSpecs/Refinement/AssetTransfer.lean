import EvmLeanSpecs.Refinement.AssetBalanceOf
import EvmLeanProofs.Solidity.Examples.SolmateAssetTransfer
import EvmLeanProofs.Solidity.ExtraTactic

/-!
# The asset's `transfer` as a callee summary

`transfer_halts_ok` / `transfer_halts_revert`: `transfer(to, amount)` of the deployed asset
(Solmate `MockERC20`, any immutables), run in any fresh frame (non-static for the success
case: the code writes storage and emits a log), either returns ABI `true` with the world
`transferWorld` (the two balance writes, in the code's order; shared with the solidity
package's top-level `transfer_spec`), or, when the caller's balance does not cover `amount`,
reverts with `Panic(0x11)`. Both bound the gas used, so that a caller can continue after the
call (`WP.call`). `AssetSpec` relates them to `Token.transfer`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLean.Solidity.Examples.SolmateAssetTransfer (transferWorld)

/-- Calldata of a function taking two static words `x`, `y`, with selector `sel`. -/
structure TwoWordCall (data : ByteArray) (sel : Nat) (x y : Word) : Prop where
  /-- The selector. -/
  selector : Abi.selectorOf data = sel
  /-- Two argument words. -/
  size : 68 ≤ data.size
  /-- The first argument. -/
  arg0 : Bytes.toWord (readBytes data 4 32) = x
  /-- The second argument. -/
  arg1 : Bytes.toWord (readBytes data 36 32) = y

/-- What a successful `transfer(to, amount)` of the asset ends with: it returns ABI `true`, the
world is `transferWorld` (the two balance writes, in the order the code does them), transient
storage and created accounts are unchanged, and at most 55000 gas is used. -/
def TransferOk (to : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord 1) ∧
  mf.world = transferWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller
    to amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 55000

/-- What a reverting call ends with: a `REVERT` (some data), at most `g` gas used. -/
def Reverts (g : Nat) (m mf : Machine) (o : Outcome) : Prop :=
  (∃ out, o = .revert out) ∧ m.frame.gasLeft ≤ mf.frame.gasLeft + g

set_option maxHeartbeats 0 in
/-- **`transfer(to, amount)` of the asset, success**, in any non-static frame: when the
caller's balance covers `amount`. -/
theorem transfer_halts_ok {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {to : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress to) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller)).toNat) :
    Halts m (TransferOk to amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [balanceSlot_solmate] at hbal
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_sub_self_of_le hbal, iszero_zero]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  pwp_codecopy
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨rfl, by simp only [outputMachine, transferWorld, balanceSlot_solmate], rfl, rfl, ?_⟩
  dsimp only [outputMachine]
  evm_gas

set_option maxHeartbeats 0 in
/-- **`transfer(to, amount)` of the asset, insufficient balance**, in any frame: the checked
subtraction panics (`Panic(0x11)`). -/
theorem transfer_halts_revert {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) {to : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress to) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 10000 ≤ m.frame.gasLeft)
    (hbal : (m.world.sload m.frame.msg.currentTarget
      (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller)).toNat <
        amount.toNat) :
    Halts m (Reverts 10000 m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [balanceSlot_solmate] at hbal
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_sub_self_of_lt hbal, iszero_one]
  pwp_steps
  refine ⟨⟨_, rfl⟩, ?_⟩
  dsimp only [outputMachine]
  evm_gas

end EvmLeanSpecs.Refinement
