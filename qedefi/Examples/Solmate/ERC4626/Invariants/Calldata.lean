import Examples.Solmate.ERC20.TransferFrom
import EvmLogic.Program.Call
import Examples.MathlibDeps
import QEDefi.Trace.Lift
import QEDefi.ERC4626.Solmate

/-!
# Calldata of two- and three-word calls

`twoWordCall_encodeCall`, `threeWordCall_encodeCall`: `Abi.encodeCall` builds the calldata the
refinement theorems expect. Split from `System.lean` so the event theorems need not wait for it.
-/

section

namespace Examples.Solmate.ERC4626.Invariants
open Examples.Solmate.ERC20 QEDefi.ERC4626 QEDefi.Trace
open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC4626.Solmate QEDefi.Trace.Lift

theorem twoWordCall_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (x y : Word) :
    TwoWordCall (Abi.encodeCall sel [x, y]) sel x y :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _,
   Abi.calldataload_encodeCall_1 _ _ _ _⟩

theorem threeWordCall_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (x y z : Word) :
    ThreeWordCall (Abi.encodeCall sel [x, y, z]) sel x y z :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _,
   Abi.calldataload_encodeCall_1 _ _ _ _, Abi.calldataload_encodeCall_2 _ _ _ _ _⟩

end Examples.Solmate.ERC4626.Invariants

end
