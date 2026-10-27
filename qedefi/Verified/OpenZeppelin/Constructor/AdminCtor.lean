import Verified.OpenZeppelin.Constructor.AdminDefs
import EvmLogic.Tactic.StepExt

/-!
# The `ProxyAdmin` constructor

`admin_ctor_halts`: the frame running `initCodeFor o` (the `ProxyAdmin` creation code with
`initialOwner = o`) with no value, not static, slot 0 empty and enough gas returns the runtime
code and writes `o` into slot 0 (`Ownable._owner`). The proxy's constructor creates it.
-/

namespace Verified.OpenZeppelin.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Verified.OpenZeppelin.Contracts Verified.Solmate.Constructor

/-- The runtime code, as the constructor copies it out of the init code. -/
theorem readBytes_initCode_runtime : readBytes OzProxyAdmin.initCode 236 964 = OzProxyAdmin.runtimeCode := by
  rw [OzProxyAdmin.initCode_eq, readBytes_append_of_le _ _ _ _
    (by rw [OzProxyAdmin.size_creationCode]; omega)]
  apply eq_of_data_toList_eq
  rw [readBytes_toList _ _ _ (by rw [OzProxyAdmin.size_creationCode]; omega)
    (by rw [OzProxyAdmin.size_creationCode]; omega)]
  decide +kernel

set_option maxHeartbeats 0 in
theorem admin_ctor_halts (o : Address) (m : Machine) (hf : Fresh (OzProxyAdmin.initCodeFor o) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    (ho : Word.ofAddress o ≠ 0#256)
    (hs0 : m.world.sload m.frame.msg.currentTarget 0#256 = 0#256)
    (hg : 300000 ≤ m.frame.gasLeft) :
    Halts m (fun mf out => out = .success OzProxyAdmin.runtimeCode ∧
      mf.world = m.world.sstore m.frame.msg.currentTarget 0#256 (Word.ofAddress o) ∧
      m.frame.gasLeft ≤ mf.frame.gasLeft + 50000) := by
  apply WP.halts_of_false
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  wp_hide_jump_tables
  subst hs hpc hc hmem
  have hJ := OzProxyAdmin.jumpTable_initCodeFor hj
  pwp_xsteps 400 [hval, OzProxyAdmin.size_initCodeFor, OzProxyAdmin.readBytes_initCodeFor_arg,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, ho, Memory.write_ofWord,
    hs0, BitVec.zero_and, BitVec.or_zero]
  wp_abstract_mem M with hM
  simp only [EvmLean.Interpreter.size_readBytes] at M_size
  pwp_xsteps 20 [M_size]
  refine ⟨?_, rfl, ?_⟩
  · rw [← hM, Memory.read_write_of_size _ _ _ _ (size_readBytes _ _ _),
      readBytes_initCode_runtime]
  · dsimp only [outputMachine]; evm_gas

end Verified.OpenZeppelin.Constructor
