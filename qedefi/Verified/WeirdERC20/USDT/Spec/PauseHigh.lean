import Verified.WeirdERC20.USDT.Spec.OpHigh

/-!
# USDT's `pause()` and `unpause()` on the lift

`pause()` (`onlyOwner whenNotPaused`) and `unpause()` (`onlyOwner whenPaused`) run through every
branch of the code: they fail unless the owner calls and the `paused` byte of slot 0 is not
already the target flag, and otherwise write that byte (`pauseW`) and stop. The code's condition
is `pauseOk`, which `pause_spec` (`Ops.lean`) matches with the model's guarded `setPaused`.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.USDT.Contracts EvmLogic.Program.Nested EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626

/-- The word the code `OR`s into the cleared `paused` byte: `2¹⁶⁰` for `pause()`, `0` for
`unpause()`. -/
def pauseFlag (b : Bool) : Word :=
  if b then 1461501637330902918203684832716283019655932542976#256 else 0#256

/-- `pause()` (`b = true`) / `unpause()` (`b = false`): the owner calls and the `paused` byte is
`0` exactly when pausing (`whenNotPaused` / `whenPaused`). -/
def pauseOk (w : World) (t c : Address) (b : Bool) : Prop :=
  c = ownerA w t ∧ (pausedW w t = 0#256 ↔ b = true)

/-- `pause()` / `unpause()`: byte 20 of slot 0 set to the flag, the rest of the slot kept. -/
def pauseW (w : World) (t : Address) (b : Bool) : World :=
  w.sstore t 0#256 (pauseFlag b |||
    115792089237316195423570984636004990333889740523700931696805413995650331181055#256 &&&
      w.sload t 0#256)

set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
/-- **`pause()` (selector `0x8456cb59`, `b = true`) and `unpause()` (selector `0x3f4ba83a`,
`b = false`)** on the lift. -/
theorem pause_high (m : Machine) (hf : Fresh USDT.runtimeCode m) (d : Nat) (b : Bool)
    (hg : g₀ ≤ m.frame.gasLeft + d)
    (hsel : Abi.selectorOf m.frame.msg.data = if b then 0x8456cb59 else 0x3f4ba83a)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) :
    WP (lift patchedCode d m) (fun mh' => mh'.frame.pc ∉ patchPcs ∧
      ExitsWith (OpOut (pauseOk m.world m.frame.msg.currentTarget m.frame.msg.caller b)
        (pauseW m.world m.frame.msg.currentTarget b) m) mh') (fun _ _ => False) := by
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  simp only [g₀] at hg
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hsel
    have hsel' := Dispatch.selector_eq hsel
    lift_intro
    usdt_run [hval, hsel', hlt, Memory.read_64, div_selector, expCost_20, expCost_0,
      ofAddress_and_addressMask, addressMask_and_ofAddress, owner_mask2, owner_mask]
    by_cases hown : m_msg.caller = ownerA m_world m_msg.currentTarget
    swap
    · simp only [eq_of_ne (fun e => hown (Word.ofAddress_injective e)), Solidity.iszero_zero,
        Solidity.iszero_one]
      xrun [owner_mask]
      usdt_revert
      exact .inr (.inl ⟨fun h => hown h.1, trivial⟩)
    have heq : Word.eq (Word.ofAddress m_msg.caller)
        (Word.ofAddress (ownerA m_world m_msg.currentTarget)) = 1#256 := by
      rw [hown]; exact Solidity.eq_self _
    simp only [heq, Solidity.iszero_zero, Solidity.iszero_one]
    xrun [owner_mask]
    by_cases hp : (255#256 &&& (m_world.sload m_msg.currentTarget 0#256).div
        1461501637330902918203684832716283019655932542976#256) = 0#256
    · simp only [hp, Solidity.iszero_zero, Solidity.iszero_one]
      xrun [owner_mask]
      usdt_revert
      exact .inr (.inl ⟨fun h => by simp [pauseOk, hp] at h, trivial⟩)
    simp only [iszero_of_ne hp, Solidity.iszero_zero, Solidity.iszero_one]
    xrun [owner_mask]
    by_cases hst : m_msg.isStatic = true
    · usdt_static
      exact .inl ⟨hst, trivial⟩
    have hst' : m_msg.isStatic = false := by simpa using hst
    xrun [owner_mask]
    usdt_stop
    exact .inr (.inr ⟨⟨hown, by simp [hp]⟩, ⟨_, rfl⟩, rfl, rfl, rfl⟩)
  · simp only [↓reduceIte] at hsel
    have hsel' := Dispatch.selector_eq hsel
    lift_intro
    usdt_run [hval, hsel', hlt, Memory.read_64, div_selector, expCost_20, expCost_0,
      ofAddress_and_addressMask, addressMask_and_ofAddress, owner_mask2, owner_mask]
    by_cases hown : m_msg.caller = ownerA m_world m_msg.currentTarget
    swap
    · simp only [eq_of_ne (fun e => hown (Word.ofAddress_injective e)), Solidity.iszero_zero,
        Solidity.iszero_one]
      xrun [owner_mask]
      usdt_revert
      exact .inr (.inl ⟨fun h => hown h.1, trivial⟩)
    have heq : Word.eq (Word.ofAddress m_msg.caller)
        (Word.ofAddress (ownerA m_world m_msg.currentTarget)) = 1#256 := by
      rw [hown]; exact Solidity.eq_self _
    simp only [heq, Solidity.iszero_zero, Solidity.iszero_one]
    xrun [owner_mask]
    by_cases hp : (255#256 &&& (m_world.sload m_msg.currentTarget 0#256).div
        1461501637330902918203684832716283019655932542976#256) = 0#256
    swap
    · simp only [iszero_of_ne hp, Solidity.iszero_zero, Solidity.iszero_one]
      xrun [owner_mask]
      usdt_revert
      exact .inr (.inl ⟨fun h => hp (h.2.2 rfl), trivial⟩)
    simp only [hp, Solidity.iszero_zero, Solidity.iszero_one]
    xrun [owner_mask]
    by_cases hst : m_msg.isStatic = true
    · usdt_static
      exact .inl ⟨hst, trivial⟩
    have hst' : m_msg.isStatic = false := by simpa using hst
    xrun [owner_mask]
    usdt_stop
    exact .inr (.inr ⟨⟨hown, by simp [hp]⟩, ⟨_, rfl⟩, rfl, rfl, rfl⟩)

end Verified.WeirdERC20.USDT.Spec
