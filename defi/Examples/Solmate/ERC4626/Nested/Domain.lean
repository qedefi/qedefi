import Examples.Solmate.ERC20.Permit
import Examples.Solmate.Contracts.SolmateVault
import Examples.Solmate.Contracts.SolmateAsset

/-!
# The `DOMAIN_SEPARATOR()`/`permit` frame condition

`DomainOk`, shared by the view and `permit` frame summaries (`Nested/Views.lean`,
`Nested/Permit.lean`); a module of its own so that the two can be checked in parallel.
-/

namespace Examples.Solmate.ERC4626.Nested
open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open Examples.Solmate.ERC20

/-- The cases `DOMAIN_SEPARATOR()` and `permit` are proved for (`Permit.DomainCase`): the
deployment chain, or a name in slot 0 shorter than 32 bytes. A long name on another chain is not
covered (the out-of-place string encoder is not verified). -/
def DomainOk (m : Machine) : Prop :=
  (∀ i : SolmateVault.Immutables,
    m.world.code m.frame.msg.currentTarget = SolmateVault.runtimeCodeWith i →
    Permit.DomainCase i.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256)) ∧
  (∀ ia : SolmateAsset.Immutables,
    m.world.code m.frame.msg.currentTarget = SolmateAsset.runtimeCodeWith ia →
    Permit.DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))

end Examples.Solmate.ERC4626.Nested
