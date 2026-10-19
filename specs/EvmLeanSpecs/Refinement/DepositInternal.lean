import EvmLeanSpecs.Refinement.AssetCallIn
import EvmLeanProofs.Solidity.InExtraWord

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault Shares

set_option maxHeartbeats 0 in
theorem mintShares_explore {i : SolmateVault.Immutables} (m : Machine) {amount r : Word}
    {dst : Address} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hstatic : m.frame.msg.isStatic = false)
    (hpc : m.frame.pc = 0xfdc)
    (hs : m.frame.stack = amount :: Word.ofAddress dst :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hfmp : m.frame.memory.loadWord 64 = 128#256) (hsize : m.frame.memory.size = 256)
    (hg : 60000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun _ => False) (fun _ _ => False) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress]
  by_cases hov : (m_world.sload m_msg.currentTarget 2#256).toNat + amount.toNat < 2 ^ 256
  · simp only [iszero_gt_add_of_lt hov]
    pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress]
    pwp_codecopy
    pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress]
    trace_state
    sorry
  · simp only [iszero_gt_add_of_ge (Nat.le_of_not_lt hov)]
    pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress]
    trace_state
    sorry

end EvmLeanSpecs.Refinement
