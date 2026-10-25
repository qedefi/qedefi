import Verified.OpenZeppelin.ERC20.Spec.LowGas
import Verified.OpenZeppelin.Contracts.OzAsset
import EvmLogic.Tactic.KernelRfl

/-!
# `OzAsset` has no `GAS`, calls or creations

Decided by the kernel on the instruction scan, so the low-gas lift (`LowGas.lean`) applies to
every frame of `ERC20Mock`.
-/

namespace Verified.OpenZeppelin.ERC20.Spec
open EvmLean EvmLogic.GasMono Verified.OpenZeppelin.Contracts

/-- **No instruction of `ERC20Mock` reads the gas or starts a child.** -/
theorem noGasCode_oz : NoGasCode OzAsset.runtimeCode := noGasCode_of_scan (by kernel_decide)

end Verified.OpenZeppelin.ERC20.Spec
