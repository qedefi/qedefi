import Examples.Solmate.ERC20.BalanceOf
import EvmLogic.Solidity.Dispatch
import EvmLogic.Solidity.Call
import EvmLogic.Tactic.Patched
import EvmLogic.Solidity.ERC20

/-!
# The asset's `transferFrom` as a callee summary

`transferFrom_halts_ok`/`_revert`: `transferFrom(src, dst, amount)` of the deployed asset in
any non-static frame succeeds with `ERC20.transferFromWorld` when the allowance (unless
infinite) and the balance after the allowance step cover `amount`, and otherwise reverts.
-/

namespace Examples.Solmate.ERC20

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open EvmLogic.Solidity.ERC20 (transferWorld)

/-- Calldata of a function taking three static words `x`, `y`, `z`, with selector `sel`. -/
structure ThreeWordCall (data : ByteArray) (sel : Nat) (x y z : Word) : Prop where
  selector : Abi.selectorOf data = sel
  size : 100 ≤ data.size
  arg0 : Bytes.toWord (readBytes data 4 32) = x
  arg1 : Bytes.toWord (readBytes data 36 32) = y
  arg2 : Bytes.toWord (readBytes data 68 32) = z

/-- Allowance entries represented after `transfer`: those in neither written balance slot. -/
def TransferAllowances (crypto : Crypto) (src dst : Address) (o sp : Address) : Prop :=
  ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp ≠
      ERC20.balanceSlot crypto ERC20.Layout.solmate src ∧
    ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp ≠
      ERC20.balanceSlot crypto ERC20.Layout.solmate dst

theorem maxWord_eq_MAXW : ERC20.maxWord = MAXW := by decide

/-- A successful `transferFrom`: ABI `true`, world `ERC20.transferFromWorld`, ≤ 80000 gas. -/
def TransferFromOk (src dst : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord 1) ∧
  mf.world = ERC20.transferFromWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller
    src dst amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 80000

set_option maxHeartbeats 0 in
/-- **The asset's `transferFrom`, success**: when the allowance is infinite or covers `amount`
and the balance after the allowance step covers `amount`. -/
theorem transferFrom_halts_ok {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src dst : Address}
    {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (hspend : m.world.sload m.frame.msg.currentTarget
        (ERC20.allowanceSlot m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller) =
        ERC20.maxWord ∨
      amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
        (ERC20.allowanceSlot m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller)).toNat)
    (hbal : amount.toNat ≤ ((ERC20.spendWorld m.ctx.crypto m.world m.frame.msg.currentTarget src
      m.frame.msg.caller amount).sload m.frame.msg.currentTarget
        (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat) :
    Halts m (TransferFromOk src dst amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate, allowanceSlot_solmate] at hbal hspend
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  by_cases hmax : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 4#256)))) = MAXW
  · simp only [hmax, Solidity.eq_self, ↓reduceIte] at hbal ⊢
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [gt_sub_self_of_le hbal, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    pwp_codecopy
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine ⟨rfl, ?_, rfl, rfl, ?_⟩
    · simp only [outputMachine, ERC20.transferFromWorld, ERC20.transferWorld, transferWorld,
        ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate,
        allowanceSlot_solmate, hmax, ↓reduceIte]
    · dsimp only [outputMachine]
      evm_gas
  · simp only [eq_of_ne hmax, hmax, ↓reduceIte] at hbal ⊢
    have hle := hspend.resolve_left hmax
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [gt_sub_self_of_le hle, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [gt_sub_self_of_le hbal, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    pwp_codecopy
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine ⟨rfl, ?_, rfl, rfl, ?_⟩
    · simp only [outputMachine, ERC20.transferFromWorld, ERC20.transferWorld, transferWorld,
        ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate,
        allowanceSlot_solmate, hmax, ↓reduceIte]
    · dsimp only [outputMachine]
      evm_gas

set_option maxHeartbeats 0 in
/-- **The asset's `transferFrom`, revert**: otherwise a checked subtraction panics. -/
theorem transferFrom_halts_revert {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src dst : Address}
    {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (hfail : ¬ ((m.world.sload m.frame.msg.currentTarget
        (ERC20.allowanceSlot m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller) =
        ERC20.maxWord ∨
      amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
        (ERC20.allowanceSlot m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller)).toNat) ∧
      amount.toNat ≤ ((ERC20.spendWorld m.ctx.crypto m.world m.frame.msg.currentTarget src
        m.frame.msg.caller amount).sload m.frame.msg.currentTarget
          (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat)) :
    Halts m (Reverts 80000 m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate, allowanceSlot_solmate] at hfail
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  by_cases hmax : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 4#256)))) = MAXW
  · simp only [hmax, Solidity.eq_self, ↓reduceIte, true_or, true_and,
      Nat.not_le] at hfail ⊢
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [gt_sub_self_of_lt hfail, iszero_one]
    pwp_steps
    refine ⟨⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]
    evm_gas
  · simp only [eq_of_ne hmax, hmax, ↓reduceIte, false_or] at hfail ⊢
    by_cases hle : amount.toNat ≤ (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
          (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 4#256))))).toNat
    · simp only [hle, true_and, Nat.not_le] at hfail
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      simp only [gt_sub_self_of_le hle, iszero_zero]
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      simp only [gt_sub_self_of_lt hfail, iszero_one]
      pwp_steps
      refine ⟨⟨_, rfl⟩, ?_⟩
      dsimp only [outputMachine]
      evm_gas
    · rw [Nat.not_le] at hle
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      simp only [gt_sub_self_of_lt hle, iszero_one]
      pwp_steps
      refine ⟨⟨_, rfl⟩, ?_⟩
      dsimp only [outputMachine]
      evm_gas

end Examples.Solmate.ERC20
