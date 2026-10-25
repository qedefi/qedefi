import Verified.OpenZeppelin.Contracts.ActorImpl
import Verified.Solmate.ERC4626.Views
import EvmLogic.Tactic.StepExt

/-!
# `ActorImpl.set(v)` as a frame summary

The proxy's constructor delegatecalls its initialization data into the implementation; with
`ActorImpl` and the data `set(v)`, the frame writes `v` into slot 0 of the executing account
(the proxy) and returns nothing. `actorSet_halts` holds for any frame (in particular the
`delegateChild` of the constructor).
-/

namespace Verified.OpenZeppelin.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Verified.OpenZeppelin.Contracts Verified.Solmate.ERC4626 Verified.Solmate.ERC20

set_option maxHeartbeats 0 in
/-- **`set(v)` of `ActorImpl`**, in any frame running its code with no value and not static:
returns nothing, writes `v` into slot 0 of the executing account, under 25 000 gas. -/
theorem actorSet_halts (m : Machine) (hf : Fresh ActorImpl.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {v : Word}
    (hd : WordCall m.frame.msg.data 0x60fe47b1 v) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 30000 ≤ m.frame.gasLeft) :
    Halts m (fun mf o => o = .success .empty ∧
      mf.world = m.world.sstore m.frame.msg.currentTarget 0#256 v ∧
      m.frame.gasLeft ≤ mf.frame.gasLeft + 25000) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg, Solidity.eq_self]
  refine WP.halt_of_step (step_stop (by pcode_fact)) (by same_frame) ⟨rfl, rfl, ?_⟩
  dsimp only
  evm_gas

end Verified.OpenZeppelin.Constructor
