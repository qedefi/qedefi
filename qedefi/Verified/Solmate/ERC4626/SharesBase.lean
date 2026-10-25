import EvmLogic.Tactic.Patched
import EvmLogic.Solidity.Dispatch
import EvmLogic.Solidity.ERC20
import Verified.Solmate.Contracts.SolmateVault
import Verified.Solmate.Contracts.Deploy
import EvmLogic.Tactic.KernelRfl

/-!
# The vault's code for arbitrary immutables

`Shares.code i` (the runtime code with immutables `i`), its jump table for all immutables
(`jumpDestsAgree`), size, delegation and `decimals` facts. Shared by the bytecode proofs; split
from `SharesCode.lean` so they can start before the share-token theorems finish.
-/

section

namespace Verified.Solmate.ERC4626.Shares

open EvmLean Verified.Solmate EvmLogic EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic
open Verified.Solmate.Contracts EvmLogic.Solidity.Dispatch

/-! ## Code -/

/-- The runtime code of the vault deployed with immutables `i`. -/
abbrev code (i : SolmateVault.Immutables) : ByteArray := SolmateVault.runtimeCodeWith i

theorem code_deployment : code SolmateVault.deployment = SolmateVault.runtimeCode :=
  SolmateVault.runtimeCodeWith_deployment

theorem code_immutablesFor (keccak256 : ByteArray → Word) (chainId : Nat) (asset self : Address) :
    code (SolmateVault.immutablesFor keccak256 chainId asset self) =
      SolmateVault.runtimeCodeFor keccak256 chainId asset self := rfl

theorem decimals_immutablesFor (keccak256 : ByteArray → Word) (chainId : Nat)
    (asset self : Address) : (SolmateVault.immutablesFor keccak256 chainId asset self).decimals = 18#256 :=
  rfl

/-- The patches only touch `PUSH32` immediates, so the jump table is the canonical one for all
immutables (kernel evaluation of the `JUMPDEST` scan, which skips the patched bytes). -/
theorem jumpDestsAgree (i : SolmateVault.Immutables) :
    JumpDestsAgree (code i) SolmateVault.runtimeCode := by
  unfold JumpDestsAgree; kernel_decide

theorem size_code (i : SolmateVault.Immutables) : (code i).size = 5248 := by
  exact (size_patchWords _ _).trans SolmateVault.size_runtimeCode

theorem delegatedAddress?_code (i : SolmateVault.Immutables) : delegatedAddress? (code i) = none :=
  delegatedAddress?_of_size (by rw [size_code]; decide)

-- The `decimals` immutable, as the `PUSH32` at 622 reads it.
theorem readBytes_code_decimals (i : SolmateVault.Immutables) :
    readBytes (code i) 623 32 = Bytes.ofWord i.decimals := by
  have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
      (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset),
      (2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset),
      (2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset)] ++ (623, i.decimals) :: [] :=
    rfl
  simp only [code, SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

end Verified.Solmate.ERC4626.Shares

namespace Verified.Solmate.ERC4626
open EvmLean EvmLean.Interpreter

/-- A view returning the word `v` and changing nothing. -/
def SharesViewPost (v : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord v) ∧ mf.world = m.world

end Verified.Solmate.ERC4626

end
