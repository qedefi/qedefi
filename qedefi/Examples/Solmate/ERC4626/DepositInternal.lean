import Examples.Solmate.ERC20.Spec
import EvmLogic.Program.Call
import Examples.Solmate.ERC4626.Abstraction
import Examples.Solmate.ERC20.MintBurn
import EvmLogic.Solidity.Word

/-!
# `deposit`/`mint`: the internal `_mint` and `afterDeposit`

`mintShares_wp`, `afterDeposit_wp` (and `bumpWorld`), split from `Deposit.lean` so the event
companions can use them without waiting for the entry points. See `docs/erc4626/details.md` §2.
-/

section

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open QEDefi.Math QEDefi.ERC20 Examples.Solmate.ERC4626.Shares

-- The `asset` immutable as read by the `PUSH32` at `0x07dd` (in `deposit`).
theorem readBytes_code_asset2014 (i : SolmateVault.Immutables) :
    readBytes (SolmateVault.runtimeCodeWith i) 2014 32 = Bytes.ofWord (Word.ofAddress i.asset) := by
  have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
      (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset)] ++
      (2014, Word.ofAddress i.asset) :: [(2169, Word.ofAddress i.asset),
      (2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
  simp only [SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

-- The `asset` immutable as read by the `PUSH32` at `0x0878` (in `mint`).
theorem readBytes_code_asset2169 (i : SolmateVault.Immutables) :
    readBytes (SolmateVault.runtimeCodeWith i) 2169 32 = Bytes.ofWord (Word.ofAddress i.asset) := by
  have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
      (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset),
      (2014, Word.ofAddress i.asset)] ++ (2169, Word.ofAddress i.asset) ::
      [(2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
  simp only [SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

set_option maxHeartbeats 0 in
/-- **`_mint(to, amount)`** (internal, entry `0x0fdc`, stack `amount :: to :: r :: rest`):
without supply overflow returns to `r` with the world `mintWorld` (at most 55000 gas); else
reverts. -/
theorem mintShares_wp {i : SolmateVault.Immutables} (m : Machine) {amount r : Word}
    {dst : Address} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hstatic : m.frame.msg.isStatic = false)
    (hpc : m.frame.pc = 0xfdc)
    (hs : m.frame.stack = amount :: Word.ofAddress dst :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpAfterTransfer m.frame.memory)
    (hg : 60000 ≤ m.frame.gasLeft) :
    WP m (fun m' => (m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat < 2 ^ 256 ∧
        ∃ mem g rd sub,
          m' = { m.resumeWith r.toNat rest mem g rd sub with
            world := mintWorld m.ctx.crypto m.world m.frame.msg.currentTarget dst amount } ∧
          FmpAfterTransfer mem ∧ m.frame.gasLeft ≤ g + 55000)
      (fun _ o => 2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat ∧
        ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩ <;>
  · pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress]
    by_cases hov : (m_world.sload m_msg.currentTarget 2#256).toNat + amount.toNat < 2 ^ 256
    · simp only [gt_add_self_of_lt hov, iszero_zero]
      pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      pwp_codecopy
      pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      refine WP.ret ⟨hov, _, _, _, _, rfl, ?_, ?_⟩
      · unfold FmpAfterTransfer
        simp (disch := decide) only [Memory.loadWord_storeWord_of_disjoint,
          Memory.loadWord_expand, hfmp, Memory.size_storeWord, Memory.size_expand, hsize,
          Memory.wordsAfter, Memory.words, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
          Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def, ↓reduceIte]
        decide
      · evm_gas
    · simp only [gt_add_self_of_le (Nat.le_of_not_lt hov), iszero_one]
      pwp_steps [hfmp, hsize]
      exact ⟨Nat.le_of_not_lt hov, _, rfl⟩

/-- The world after `afterDepositHookCalledCounter++` (slot 7 of the vault). -/
def bumpWorld (w : World) (vault : Address) : World :=
  w.sstore vault 7#256 (1#256 + w.sload vault 7#256)

set_option maxHeartbeats 0 in
/-- **`afterDeposit(assets, shares)`** (internal, entry `0x1033`): without counter overflow
returns to `r` with the world `bumpWorld` (at most 30000 gas); else reverts. -/
theorem afterDeposit_wp {i : SolmateVault.Immutables} (m : Machine) {x y r : Word}
    {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hstatic : m.frame.msg.isStatic = false)
    (hpc : m.frame.pc = 0x1033)
    (hs : m.frame.stack = x :: y :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpAfterTransfer m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) :
    WP m (fun m' => (m.world.sload m.frame.msg.currentTarget 7#256).toNat + 1 < 2 ^ 256 ∧
        ∃ g sub,
          m' = { m.resumeWith r.toNat rest m.frame.memory g m.frame.returnData sub with
            world := bumpWorld m.world m.frame.msg.currentTarget } ∧
          m.frame.gasLeft ≤ g + 30000)
      (fun _ o => (m.world.sload m.frame.msg.currentTarget 7#256).toNat + 1 = 2 ^ 256 ∧
        ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  pwp_steps
  by_cases hov : (m_world.sload m_msg.currentTarget 7#256).toNat + 1 < 2 ^ 256
  · have hne := add_one_ne_zero_of_lt hov
    pwp_steps
    exact WP.ret ⟨hov, _, _, rfl, by evm_gas⟩
  · have he : (m_world.sload m_msg.currentTarget 7#256).toNat + 1 = 2 ^ 256 := by
      have := (m_world.sload m_msg.currentTarget 7#256).isLt; omega
    simp only [add_one_eq_zero_of_eq he]
    rcases hmem with ⟨-, hsize⟩ | ⟨-, hsize⟩ <;>
    · pwp_steps [hsize]
      exact ⟨he, _, rfl⟩

end Examples.Solmate.ERC4626

end
