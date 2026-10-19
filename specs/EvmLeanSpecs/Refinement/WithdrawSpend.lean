import EvmLeanSpecs.Refinement.WithdrawCode
import EvmLeanSpecs.Refinement.AssetTransferFrom

/-!
# The allowance step of `withdraw` and `redeem`

solc inlines `if (msg.sender != owner) { uint256 allowed = allowance[owner][msg.sender];
if (allowed != type(uint256).max) allowance[owner][msg.sender] = allowed - shares; }` into
each function (the checked subtraction jumps to the shared helper at `0x1385`, whose overflow
branch panics). `withdrawSpend_wp` (pc `0x0993` → `0x0a00`) and `redeemSpend_wp`
(pc `0x0a93` → `0x0aff`) summarise the two copies by the world step `Out.spendStep`. Memory: only
scratch space is written (the two Keccak preimages), so the free-memory pointer and the memory
size are kept.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Refinement.Out

/-- `CALLER == owner` as the code tests it, for distinct addresses. -/
theorem eq_ofAddress_of_ne {a b : Address} (h : a ≠ b) :
    Word.eq (Word.ofAddress a) (Word.ofAddress b) = 0#256 :=
  eq_of_ne fun e => h (Word.ofAddress_injective e)

set_option maxHeartbeats 0 in
/-- **The allowance step of `withdraw`** (pc `0x0993`, stack `v :: x :: owner :: rest`, `v` the
shares of `previewWithdraw`): continues at `0x0a00` with stack `v :: owner :: rest` and the world
of `spendStep`, or panics. -/
theorem withdrawSpend_wp {i : SolmateVault.Immutables} (m : Machine) {v x : Word}
    {owner : Address} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x993) (hs : m.frame.stack = v :: x :: Word.ofAddress owner :: rest)
    (hlen : rest.length ≤ 1000) (hstatic : m.frame.msg.isStatic = false)
    (hmem : FmpOk m.frame.memory) (hg : 30000 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ w₁, spendStep m.ctx.crypto m.world m.frame.msg.currentTarget owner
          m.frame.msg.caller v = some w₁ ∧ ∃ mem g sub,
        m' = resumeWorld m 0xa00 (v :: Word.ofAddress owner :: rest) mem g m.frame.returnData sub
          w₁ ∧
        mem.loadWord 64 = m.frame.memory.loadWord 64 ∧ mem.size = m.frame.memory.size ∧
        m.frame.gasLeft ≤ g + 26000)
      (fun _ o => spendStep m.ctx.crypto m.world m.frame.msg.currentTarget owner
          m.frame.msg.caller v = none ∧ ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  by_cases hco : m_msg.caller = owner
  · subst hco
    pwp_run_to 0xa00 [ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    apply WP.ret
    exact ⟨_, by simp [spendStep], _, _, _, rfl, rfl, rfl, by evm_gas⟩
  · have hne1 := eq_ofAddress_of_ne hco
    have hne2 := eq_ofAddress_of_ne (Ne.symm hco)
    have hsp : spendStep m_ctx.crypto m_world m_msg.currentTarget owner m_msg.caller v =
        let a := m_world.sload m_msg.currentTarget
          (Erc20.allowanceSlot m_ctx.crypto Erc20.Layout.solmate owner m_msg.caller)
        if a ≠ Erc20.maxWord ∧ a.toNat < v.toNat then none
        else some (Erc20.spendWorld m_ctx.crypto m_world m_msg.currentTarget owner m_msg.caller v) := by
      simp only [spendStep, hco, ↓reduceIte]
    rw [hsp]
    simp only [Erc20.spendWorld, allowanceSlot_solmate, maxWord_eq_MAXW]
    rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, ofAddress_and_addressMask, addressMask_and_ofAddress, hne1, hne2,
        Memory.read_64]
      by_cases hmax : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
          (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 4#256)))) = MAXW
      · simp only [hmax, Solidity.eq_self]
        pwp_run_to 0xa00 [hsize]
        apply WP.ret
        refine ⟨_, by simp, _, _, _, rfl, ?_, ?_, by evm_gas⟩
        · simp only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide)]
        · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
            hsize]
          decide
      · simp only [eq_of_ne hmax, hmax]
        pwp_steps [hsize]
        by_cases hle : v.toNat ≤ (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
              (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 4#256))))).toNat
        · simp only [gt_sub_self_of_le hle, iszero_zero]
          pwp_run_to 0xa00 [hsize, ofAddress_and_addressMask, addressMask_and_ofAddress,
            Memory.read_64]
          apply WP.ret
          refine ⟨_, by simp [Nat.not_lt.2 hle], _, _, _, rfl, ?_, ?_, by evm_gas⟩
          · simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide)]
          · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter,
              Memory.words, hsize]
            decide
        · rw [Nat.not_le] at hle
          simp only [gt_sub_self_of_lt hle, iszero_one]
          pwp_steps [hsize]
          exact ⟨by simp [hmax, hle], _, rfl⟩

set_option maxHeartbeats 0 in
/-- **The allowance step of `redeem`** (pc `0x0a93`, stack `owner :: y :: v :: rest`, `v` the
`shares` argument): continues at `0x0aff` with stack `0 :: owner :: y :: v :: rest` and the
world of `spendStep`, or panics. -/
theorem redeemSpend_wp {i : SolmateVault.Immutables} (m : Machine) {v y : Word}
    {owner : Address} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0xa93) (hs : m.frame.stack = Word.ofAddress owner :: y :: v :: rest)
    (hlen : rest.length ≤ 1000) (hstatic : m.frame.msg.isStatic = false)
    (hmem : FmpOk m.frame.memory) (hg : 30000 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ w₁, spendStep m.ctx.crypto m.world m.frame.msg.currentTarget owner
          m.frame.msg.caller v = some w₁ ∧ ∃ mem g sub,
        m' = resumeWorld m 0xaff (0#256 :: Word.ofAddress owner :: y :: v :: rest) mem g
          m.frame.returnData sub w₁ ∧
        mem.loadWord 64 = m.frame.memory.loadWord 64 ∧ mem.size = m.frame.memory.size ∧
        m.frame.gasLeft ≤ g + 26000)
      (fun _ o => spendStep m.ctx.crypto m.world m.frame.msg.currentTarget owner
          m.frame.msg.caller v = none ∧ ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  by_cases hco : m_msg.caller = owner
  · subst hco
    pwp_run_to 0xaff [ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    apply WP.ret
    exact ⟨_, by simp [spendStep], _, _, _, rfl, rfl, rfl, by evm_gas⟩
  · have hne1 := eq_ofAddress_of_ne hco
    have hne2 := eq_ofAddress_of_ne (Ne.symm hco)
    have hsp : spendStep m_ctx.crypto m_world m_msg.currentTarget owner m_msg.caller v =
        let a := m_world.sload m_msg.currentTarget
          (Erc20.allowanceSlot m_ctx.crypto Erc20.Layout.solmate owner m_msg.caller)
        if a ≠ Erc20.maxWord ∧ a.toNat < v.toNat then none
        else some (Erc20.spendWorld m_ctx.crypto m_world m_msg.currentTarget owner m_msg.caller v) := by
      simp only [spendStep, hco, ↓reduceIte]
    rw [hsp]
    simp only [Erc20.spendWorld, allowanceSlot_solmate, maxWord_eq_MAXW]
    rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, ofAddress_and_addressMask, addressMask_and_ofAddress, hne1, hne2,
        Memory.read_64]
      by_cases hmax : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
          (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 4#256)))) = MAXW
      · simp only [hmax, Solidity.eq_self]
        pwp_run_to 0xaff [hsize]
        apply WP.ret
        refine ⟨_, by simp, _, _, _, rfl, ?_, ?_, by evm_gas⟩
        · simp only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide)]
        · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
            hsize]
          decide
      · simp only [eq_of_ne hmax, hmax]
        pwp_steps [hsize]
        by_cases hle : v.toNat ≤ (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
              (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 4#256))))).toNat
        · simp only [gt_sub_self_of_le hle, iszero_zero]
          pwp_run_to 0xaff [hsize, ofAddress_and_addressMask, addressMask_and_ofAddress,
            Memory.read_64]
          apply WP.ret
          refine ⟨_, by simp [Nat.not_lt.2 hle], _, _, _, rfl, ?_, ?_, by evm_gas⟩
          · simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide)]
          · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter,
              Memory.words, hsize]
            decide
        · rw [Nat.not_le] at hle
          simp only [gt_sub_self_of_lt hle, iszero_one]
          pwp_steps [hsize]
          exact ⟨by simp [hmax, hle], _, rfl⟩

end EvmLeanSpecs.Refinement
