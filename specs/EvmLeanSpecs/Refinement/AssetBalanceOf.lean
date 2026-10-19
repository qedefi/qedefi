import EvmLeanProofs.Program.Tactic
import EvmLeanProofs.Program.Summary
import EvmLeanProofs.Solidity.Erc20
import EvmLeanProofs.Solidity.Tactic
import EvmLeanProofs.Solidity.Dispatch
import EvmLeanProofs.Solidity.ExtraWord
import EvmLeanProofs.Contracts.SolmateAsset

/-!
# The asset's `balanceOf` as a callee summary

`balanceOf_halts`: `balanceOf(address)` of the deployed asset (`Contracts.SolmateAsset`,
Solmate `MockERC20`) run in **any** fresh frame — a top-level call or a frame pushed by
`CALL`/`STATICCALL` from another contract, at any depth, with any parents — returns the word
in the balance slot of the argument and changes nothing. It is stated as `Halts`, the form the
callee-summary rules `WP.call` / `WP.staticcall` consume.

The calldata is described by what the ABI decoder reads (selector, length, argument word), so
the summary applies both to `Abi.encodeCall` calldata and to calldata a caller assembled in
memory.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-- The selector of `balanceOf(address)`. -/
def balanceOfSelector : Nat := 0x70a08231

/-- What a frame running `balanceOf(a)` on the asset ends with: it returns the balance word of
`a` (slot `keccak(a ‖ 3)` of the executing account), the world, transient storage, created
accounts and logs are unchanged, and it uses at most 3000 gas. -/
def BalanceOfPost (a : Address) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord (m.world.sload m.frame.msg.currentTarget
    (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate a))) ∧
  mf.world = m.world ∧ mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  mf.frame.sub.logs = m.frame.sub.logs ∧ m.frame.gasLeft ≤ mf.frame.gasLeft + 3000

/-- The dispatcher's `CALLDATASIZE < 4` test fails for calldata holding a selector. -/
theorem lt_size_four {n : Nat} (h₁ : 4 ≤ n) (h₂ : n < 2 ^ 256) :
    Word.lt (ofNat n) (BitVec.ofNat 256 4) = 0 := by
  rw [Word.lt_eq_zero_iff]; simp only [ofNat, BitVec.toNat_ofNat]; omega

set_option maxHeartbeats 0 in
/-- **`balanceOf(a)` of the asset, in any frame.** -/
theorem balanceOf_halts (m : Machine) (hf : Fresh SolmateAsset.runtimeCode m) (a : Address)
    (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = balanceOfSelector)
    (hsize : 36 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress a)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (BalanceOfPost a m) := by
  apply WP.halts_of_false
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  wp_intro m
  wp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64, balanceOfSelector]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only [outputMachine]
  evm_gas

end EvmLeanSpecs.Refinement
