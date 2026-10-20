import Examples.Solmate.ERC4626.SafeTransfer
import Examples.Solmate.ERC4626.WithdrawInternal

/-!
# The internal functions shared by `withdraw` and `redeem`

solc compiles the hook and the burn of Solmate's `ERC4626` once; `withdraw` and `redeem` jump to
them with a return address:

| internal function | entry | stack | summary | world step |
|---|---|---|---|---|
| `beforeWithdraw(assets, shares)` (`MockERC4626`: counter at slot 6, checked `++`) | `0x104b` | `a :: b :: r :: rest` | `bump_wp` | `Out.bumpStep` |
| `_burn(from, amount)` (checked `balanceOf[from] -= amount`, unchecked `totalSupply -= amount`, `Transfer` log) | `0x105a` | `amount :: from :: r :: rest` | `burn_wp` | `Out.burnStep` |

Both return to `r` with the world of the step, or revert with `Panic(0x11)` (`none`). Memory:
the hook does not touch it; the panic paths and the burn write scratch space and (the burn's
log data) one word at the free-memory pointer, so both take solc's memory shapes at their call
sites (`FmpOk`) and the burn returns `FmpBurnt`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Refinement.Out

set_option maxHeartbeats 0 in
/-- **`beforeWithdraw` (internal, entry `0x104b`, stack `a :: b :: r :: rest`)**:
`beforeWithdrawHookCalledCounter++` (checked) — returns to `r` with `bumpStep` applied, or
panics. -/
theorem bump_wp {i : SolmateVault.Immutables} (m : Machine) {a b r : Word} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x104b) (hs : m.frame.stack = a :: b :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hstatic : m.frame.msg.isStatic = false) (hmem : FmpOk m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ w', bumpStep m.world m.frame.msg.currentTarget = some w' ∧ ∃ g sub,
        m' = resumeWorld m r.toNat rest m.frame.memory g m.frame.returnData sub w' ∧
        m.frame.gasLeft ≤ g + 25000 ∧ g ≤ m.frame.gasLeft)
      (fun _ o => bumpStep m.world m.frame.msg.currentTarget = none ∧ ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  by_cases hmax : m_world.sload m_msg.currentTarget 6#256 = MAXW
  · have hz : m_world.sload m_msg.currentTarget 6#256 + 1#256 = 0#256 := by rw [hmax]; decide
    rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, hz]
      exact ⟨by simp [bumpStep, hmax], _, rfl⟩
  · have hnz : m_world.sload m_msg.currentTarget 6#256 + 1#256 ≠ 0#256 := by
      intro h; apply hmax
      have := congrArg (· - 1#256) h
      simpa [MAXW] using this
    have hnz' : m_world.sload m_msg.currentTarget 6#256 + 1#256 ≠ 0 := hnz
    pwp_steps
    apply WP.ret
    exact ⟨_, by simp [bumpStep, hmax], _, _, rfl, by evm_gas, by evm_gas⟩

/-- Memory after `_burn`: the free pointer at `0x80` with five words, or at `0xa0` with six (the
`Transfer` log data written at the free pointer). -/
def FmpBurnt (mem : Memory) : Prop :=
  (mem.loadWord 64 = 128#256 ∧ mem.size = 160) ∨ (mem.loadWord 64 = 160#256 ∧ mem.size = 192)

set_option maxHeartbeats 0 in
/-- **`_burn(from, amount)` (internal, entry `0x105a`, stack `amount :: from :: r :: rest`)**:
returns to `r` with `burnStep` applied (and a `Transfer` log), or panics when the balance does
not cover `amount`. -/
theorem burn_wp {i : SolmateVault.Immutables} (m : Machine) {amount r : Word} {src : Address}
    {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x105a) (hs : m.frame.stack = amount :: Word.ofAddress src :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hstatic : m.frame.msg.isStatic = false) (hmem : FmpOk m.frame.memory)
    (hg : 60000 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ w', burnStep m.ctx.crypto m.world m.frame.msg.currentTarget src amount =
          some w' ∧ ∃ mem g rd sub,
        m' = resumeWorld m r.toNat rest mem g rd sub w' ∧ FmpBurnt mem ∧
        m.frame.gasLeft ≤ g + 55000 ∧ g ≤ m.frame.gasLeft)
      (fun _ o => burnStep m.ctx.crypto m.world m.frame.msg.currentTarget src amount = none ∧
        ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [burnStep, balanceSlot_solmate]
  by_cases hbal : amount.toNat ≤ (m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 3#256))).toNat
  · rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, hfmp, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Memory.read_64]
      simp only [gt_sub_self_of_le hbal, iszero_zero]
      pwp_steps [hsize, hfmp, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Memory.read_64]
      pwp_codecopy
      pwp_steps [hsize, hfmp, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Memory.read_64]
      apply WP.ret
      refine ⟨_, by simp only [Nat.not_lt.2 hbal, ↓reduceIte], _, _, _, _, rfl, ?_, by evm_gas,
        by evm_gas⟩
      first
        | refine .inl ⟨?_, ?_⟩
          · simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 128 64 _ (by decide), hfmp]
          · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
              hsize]
            decide
        | refine .inr ⟨?_, ?_⟩
          · simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 160 64 _ (by decide), hfmp]
          · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
              hsize]
            decide
  · rw [Nat.not_le] at hbal
    rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, hfmp, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Memory.read_64]
      simp only [gt_sub_self_of_lt hbal, iszero_one]
      pwp_steps [hsize, hfmp]
      exact ⟨by simp only [hbal, ↓reduceIte], _, rfl⟩

end EvmLeanSpecs.Refinement
