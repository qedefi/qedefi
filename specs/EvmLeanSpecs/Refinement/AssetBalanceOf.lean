import EvmLeanProofs.Program.Tactic
import EvmLeanProofs.Program.Summary
import EvmLeanProofs.Solidity.Erc20
import EvmLeanProofs.Solidity.Tactic
import EvmLeanProofs.Solidity.Dispatch
import EvmLeanProofs.Solidity.ExtraWord
import EvmLeanProofs.Contracts.SolmateAsset
import EvmLeanProofs.Solidity.ExtraPatchedWP
import EvmLeanProofs.KernelRfl

/-!
# The asset's `balanceOf` as a callee summary

`balanceOf_halts`: `balanceOf(address)` of the deployed asset (`Contracts.SolmateAsset`,
Solmate `MockERC20`, deployed with arbitrary immutables `ia`: chain id, domain separator,
decimals; `SolmateAsset.runtimeCodeWith ia`) run in **any** fresh frame — a top-level call or a frame pushed by
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

set_option hygiene false in
/-- Open a fresh frame for symbolic execution: from `hf : Fresh code m`, destructure `m` into
`m_ctx`, `m_world`, `m_msg`, `m_gasLeft`, `m_sub`, … and substitute the frame's start values
(code, pc, empty stack and memory); the jump table is kept as `hj : JumpTable m_jumpDests code`.
Unlike `wp_intro` it substitutes nothing else, so hypotheses about other variables (e.g. an
`amount` that the calldata carries) survive. -/
macro "fresh_intro" : tactic => `(tactic| (
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  wp_hide_jump_tables
  subst hs hpc hc hmem))

/-- The asset's immutables only patch `PUSH32` immediates: its jump table is the canonical one,
for all immutables (kernel evaluation of the `JUMPDEST` scan). -/
theorem assetJumpDestsAgree (ia : SolmateAsset.Immutables) :
    JumpDestsAgree (SolmateAsset.runtimeCodeWith ia) SolmateAsset.runtimeCode := by
  unfold JumpDestsAgree; kernel_decide

/-- The dispatcher's `CALLDATASIZE < 4` test fails for calldata holding a selector. -/
theorem lt_size_four {n : Nat} (h₁ : 4 ≤ n) (h₂ : n < 2 ^ 256) :
    Word.lt (ofNat n) (BitVec.ofNat 256 4) = 0 := by
  rw [Word.lt_eq_zero_iff]; simp only [ofNat, BitVec.toNat_ofNat]; omega

/-- The balance slot of `a` in a Solmate `ERC20`, as symbolic execution computes it
(`keccak256(a ‖ 3)`). -/
theorem balanceSlot_solmate (crypto : Crypto) (a : Address) :
    Erc20.balanceSlot crypto Erc20.Layout.solmate a =
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

end EvmLeanSpecs.Refinement
