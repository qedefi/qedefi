import Verified.WeirdERC20.USDT.Spec.ViewOut

/-!
# USDT `approve(sp, v)` on the lift

`approve_high`: the lift of an `approve` frame reverts with value, fails in a static frame (at
the `SSTORE`), reverts when `v ≠ 0` and the current allowance `allowed[caller][sp]` is nonzero
(the race guard), and otherwise writes `v` to that row, logs `Approval(caller, sp, v)` and stops
(`ApproveOut`).
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.USDT.Contracts EvmLogic.Program.Nested EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626

/-- The row `allowed[o][sp]`. -/
def allowRow (crypto : Crypto) (o sp : Address) : Word :=
  mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) allowedSlot

/-- What the lift of an `approve(sp, v)` frame ends with. -/
def ApproveOut (sp : Address) (v : Word) (m mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.value ≠ 0 ∧ Fails o) ∨ (m.frame.msg.isStatic = true ∧ Fails o) ∨
  (m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧
    ((v ≠ 0 ∧ m.world.sload m.frame.msg.currentTarget
        (allowRow m.ctx.crypto m.frame.msg.caller sp) ≠ 0 ∧ ∃ out, o = .revert out) ∨
     (¬ (v ≠ 0 ∧ m.world.sload m.frame.msg.currentTarget
        (allowRow m.ctx.crypto m.frame.msg.caller sp) ≠ 0) ∧
      o = .success .empty ∧
      mf.world = m.world.sstore m.frame.msg.currentTarget
        (allowRow m.ctx.crypto m.frame.msg.caller sp) v ∧
      mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
      mf.frame.sub.logs = m.frame.sub.logs.push
        (approvalLog m.frame.msg.currentTarget m.frame.msg.caller sp v))))

theorem approveOut_halt {sp : Address} {v : Word} {m mf : Machine} {e e' : ExceptionalHalt}
    (h : ApproveOut sp v m mf (.halt e)) : ApproveOut sp v m mf (.halt e') := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, ⟨-, -, hr⟩ | ⟨-, hs, -⟩⟩
  · exact .inl ⟨h1, trivial⟩
  · exact .inr (.inl ⟨h1, trivial⟩)
  · obtain ⟨_, hr⟩ := hr; cases hr
  · cases hs

set_option maxHeartbeats 0 in
/-- **`approve(sp, v)`** on the lift. -/
theorem approve_high (m : Machine) (hf : Fresh USDT.runtimeCode m) (d : Nat) (sp : Address)
    (v : Word) (hg : g₀ ≤ m.frame.gasLeft + d)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3)
    (hsize : 68 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress sp)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = v)
    (hdep : m.frame.msg.value = 0 →
      deprecatedField.get (m.world.sload m.frame.msg.currentTarget 10#256) = 0) :
    WP (lift patchedCode d m) (fun mh' => mh'.frame.pc ∉ patchPcs ∧
      ExitsWith (ApproveOut sp v m) mh') (fun _ _ => False) := by
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have h68 := lt_size_le (k := 68) hsize (by omega)
  simp only [deprecatedField_get] at hdep
  simp only [g₀] at hg
  by_cases hval : m.frame.msg.value = 0
  swap
  · have hz := iszero_value hval
    lift_intro
    usdt_run [hz, hsel', hlt, Memory.read_64, div_selector]
    usdt_revert
    exact .inl ⟨hval, trivial⟩
  have hdep := hdep hval
  have hrow : allowRow m.ctx.crypto m.frame.msg.caller sp =
      m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress sp) ++ Bytes.ofWord
        (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m.frame.msg.caller) ++
          Bytes.ofWord 5#256))) := rfl
  cases hst : m.frame.msg.isStatic
  all_goals
    lift_intro
    usdt_run [hval, hsel', hlt, Memory.read_64, div_selector, expCost_20, expCost_0, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, h68]
    simp only [hdep]
    usdt_run [ofAddress_and_addressMask, addressMask_and_ofAddress, expCost_20, expCost_0, h68,
      Memory.read_64]
  · -- not static
    by_cases hv0 : v = 0#256
    · simp only [hv0, Solidity.eq_self, Solidity.iszero_one, Solidity.iszero_zero]
      usdt_run [ofAddress_and_addressMask, addressMask_and_ofAddress, expCost_20, expCost_0,
        Memory.read_64]
      usdt_stop
      refine .inr (.inr ⟨hval, hst, .inr ⟨fun h => h.1 rfl, rfl, rfl, rfl, rfl, ?_⟩⟩)
      event_log [0#256]
    · simp only [Solidity.eq_of_ne hv0, Solidity.iszero_one, Solidity.iszero_zero]
      usdt_run [ofAddress_and_addressMask, addressMask_and_ofAddress, expCost_20, expCost_0,
        Memory.read_64]
      by_cases hc : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
          (Bytes.ofWord (Word.ofAddress sp) ++ Bytes.ofWord (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 5#256)))) = 0#256
      · simp only [hc, Solidity.eq_self, Solidity.iszero_one, Solidity.iszero_zero]
        usdt_run [ofAddress_and_addressMask, addressMask_and_ofAddress, expCost_20, expCost_0,
          Memory.read_64]
        usdt_stop
        refine .inr (.inr ⟨hval, hst, .inr ⟨fun h => h.2 (by rw [hrow]; exact hc), rfl, rfl, rfl,
          rfl, ?_⟩⟩)
        event_log [v]
      · simp only [Solidity.eq_of_ne hc, Solidity.iszero_one, Solidity.iszero_zero]
        usdt_run []
        usdt_revert
        exact .inr (.inr ⟨hval, hst, .inl ⟨hv0, by rw [hrow]; exact hc, _, rfl⟩⟩)
  · -- static: the `SSTORE` fails, or the guard reverts first
    by_cases hv0 : v = 0#256
    · simp only [hv0, Solidity.eq_self, Solidity.iszero_one, Solidity.iszero_zero]
      usdt_run [ofAddress_and_addressMask, addressMask_and_ofAddress, expCost_20, expCost_0,
        Memory.read_64]
      usdt_static
      exact .inr (.inl ⟨hst, trivial⟩)
    · simp only [Solidity.eq_of_ne hv0, Solidity.iszero_one, Solidity.iszero_zero]
      usdt_run [ofAddress_and_addressMask, addressMask_and_ofAddress, expCost_20, expCost_0,
        Memory.read_64]
      by_cases hc : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
          (Bytes.ofWord (Word.ofAddress sp) ++ Bytes.ofWord (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 5#256)))) = 0#256
      · simp only [hc, Solidity.eq_self, Solidity.iszero_one, Solidity.iszero_zero]
        usdt_run [ofAddress_and_addressMask, addressMask_and_ofAddress, expCost_20, expCost_0,
          Memory.read_64]
        usdt_static
        exact .inr (.inl ⟨hst, trivial⟩)
      · simp only [Solidity.eq_of_ne hc, Solidity.iszero_one, Solidity.iszero_zero]
        usdt_run []
        usdt_revert
        exact .inr (.inl ⟨hst, trivial⟩)

end Verified.WeirdERC20.USDT.Spec
