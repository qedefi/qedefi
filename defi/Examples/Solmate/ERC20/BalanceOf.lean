import EvmLogic.Tactic.WpStep
import EvmLogic.Program.Summary
import EvmLogic.Solidity.ERC20
import EvmLogic.Tactic.SolStep
import EvmLogic.Solidity.Dispatch
import EvmLogic.Solidity.Word
import Examples.Solmate.Contracts.SolmateAsset
import EvmLogic.Tactic.Patched
import EvmLogic.Tactic.KernelRfl

/-!
# The asset's `balanceOf` as a callee summary

`balanceOf_halts`: `balanceOf(a)` of the deployed asset (any immutables), in any fresh frame
(top level or a callee at any depth), returns the balance word of `a` and changes nothing.
Stated as `Halts` for `WP.call`/`WP.staticcall`; the calldata is described by what the ABI
decoder reads, so it also covers calldata a caller assembled in memory.
-/

namespace Examples.Solmate.ERC20

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

/-- The selector of `balanceOf(address)`. -/
def balanceOfSelector : Nat := 0x70a08231

/-- `balanceOf(a)` returns the word in `a`'s balance slot, changes nothing, uses ≤ 3000 gas. -/
def BalanceOfPost (a : Address) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord (m.world.sload m.frame.msg.currentTarget
    (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate a))) ∧
  mf.world = m.world ∧ mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  mf.frame.sub.logs = m.frame.sub.logs ∧ m.frame.gasLeft ≤ mf.frame.gasLeft + 3000

set_option hygiene false in
/-- Open a fresh frame (`hf : Fresh code m`) for symbolic execution: destructure `m` and
substitute only the frame's start values, so hypotheses about other variables survive (unlike
`wp_intro`). -/
macro "fresh_intro" : tactic => `(tactic| (
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  wp_hide_jump_tables
  subst hs hpc hc hmem))

theorem assetJumpDestsAgree (ia : SolmateAsset.Immutables) :
    JumpDestsAgree (SolmateAsset.runtimeCodeWith ia) SolmateAsset.runtimeCode := by
  unfold JumpDestsAgree; kernel_decide

theorem lt_size_four {n : Nat} (h₁ : 4 ≤ n) (h₂ : n < 2 ^ 256) :
    Word.lt (ofNat n) (BitVec.ofNat 256 4) = 0 := by
  rw [Word.lt_eq_zero_iff]; simp only [ofNat, BitVec.toNat_ofNat]; omega

theorem balanceSlot_solmate (crypto : Crypto) (a : Address) :
    ERC20.balanceSlot crypto ERC20.Layout.solmate a =
      crypto.keccak256 (Bytes.ofWord (Word.ofAddress a) ++ Bytes.ofWord 3#256) := rfl

set_option maxHeartbeats 0 in
/-- **`balanceOf(a)` of the asset, in any frame.** -/
theorem balanceOf_halts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (a : Address)
    (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = balanceOfSelector)
    (hsize : 36 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress a)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (BalanceOfPost a m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64, balanceOfSelector]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only [outputMachine]
  evm_gas

end Examples.Solmate.ERC20

section

/-! ## Callee-summary vocabulary (used by `transfer` and `transferFrom`) -/

namespace Examples.Solmate.ERC20

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open EvmLogic.Solidity.ERC20 (transferWorld)

/-- Calldata of a function taking two static words `x`, `y`, with selector `sel`. -/
structure TwoWordCall (data : ByteArray) (sel : Nat) (x y : Word) : Prop where
  selector : Abi.selectorOf data = sel
  size : 68 ≤ data.size
  arg0 : Bytes.toWord (readBytes data 4 32) = x
  arg1 : Bytes.toWord (readBytes data 36 32) = y

/-- A successful asset `transfer`: ABI `true`, world `transferWorld`, ≤ 55000 gas. -/
def TransferOk (to : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord 1) ∧
  mf.world = transferWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller
    to amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 55000

/-- What a reverting call ends with: a `REVERT` (some data), at most `g` gas used. -/
def Reverts (g : Nat) (m mf : Machine) (o : Outcome) : Prop :=
  (∃ out, o = .revert out) ∧ m.frame.gasLeft ≤ mf.frame.gasLeft + g

end Examples.Solmate.ERC20

end
