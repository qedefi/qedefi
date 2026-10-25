import Verified.WeirdERC20.USDT.Spec.Basic

/-!
# USDT views: the lift's end and `ViewSpec`

`ViewOut`: what the lift of a view's frame ends with; `viewSpec_of_out` turns it into
`ViewSpec`'s postcondition at any gas.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.USDT.Contracts EvmLogic.Program.Nested EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math

/-- What the lift of a view's frame ends with: with no value the word `x`, nothing changed;
with value a failure. -/
def ViewOut (x : Word) (m mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.value = 0 ∧ o = .success (Bytes.ofWord x) ∧ mf.world = m.world ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs) ∨
  (m.frame.msg.value ≠ 0 ∧ Fails o)

theorem iszero_value {v : Word} (h : v ≠ 0) : Word.iszero v = 0 := iszero_of_ne h

/-! ## `ViewSpec` -/

theorem viewOut_halt {x : Word} {m mf : Machine} {e e' : ExceptionalHalt}
    (h : ViewOut x m mf (.halt e)) : ViewOut x m mf (.halt e') := by
  rcases h with ⟨-, h, -⟩ | ⟨hv, -⟩
  · cases h
  · exact .inr ⟨hv, trivial⟩

/-- From the lift's end to `ViewSpec`'s postcondition, given the value the model reads. -/
theorem viewSpec_of_out {v : View} {Act : Finset Address} {m : Machine} {x : Word}
    (hs : Start USDT.runtimeCode usdtAbs M Act m)
    (hx : m.frame.msg.value = 0 → x.toNat = v.value M (pre usdtAbs Act m))
    (hw : WP (lift patchedCode (g₀ - m.frame.gasLeft) m) (fun mh' => mh'.frame.pc ∉ patchPcs ∧
      ExitsWith (ViewOut x m) mh') (fun _ _ => False)) :
    Halts m fun mf o =>
      (∃ x : Word, o = .success (Bytes.ofWord x) ∧ x.toNat = v.value M (pre usdtAbs Act m) ∧
        mf.world = m.world ∧ mf.transient = m.transient ∧
        mf.createdAccounts = m.createdAccounts ∧ mf.frame.sub.logs = m.frame.sub.logs) ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0)) := by
  refine (halts_of_high hs.fresh (Post := ViewOut x m) (fun _ _ _ h => viewOut_halt h)
    (fun _ _ h => h) hw).mono
    fun mf o _ h => ?_
  rcases h with ⟨hf, hlt⟩ | ⟨hv, ho, h1, h2, h3, h4⟩ | ⟨hv, hf⟩
  · exact .inr ⟨hf, fun h => by omega⟩
  · exact .inl ⟨x, ho, hx hv, h1, h2, h3, h4⟩
  · exact .inr ⟨hf, fun h => hv h.2⟩

/-- The deprecated flag of a live token, as the frame reads it (no value). -/
theorem dep_of_start {Act : Finset Address} {m : Machine}
    (hs : Start USDT.runtimeCode usdtAbs M Act m) (hval : m.frame.msg.value = 0) :
    deprecatedField.get (m.world.sload m.frame.msg.currentTarget 10#256) = 0 := by
  rw [world_of_start hs hval]; exact (live_of_start hs).1.1

end Verified.WeirdERC20.USDT.Spec
