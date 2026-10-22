import Examples.AaveV3.Contracts.ATokenProxy
import EvmLogic.Program.Code

/-!
# `ATokenProxy`: code facts

The kernel lookup table of the deployed `InitializableImmutableAdminUpgradeabilityProxy` runtime
code of the aTokens (`runtimeCode.codeTable`, checked once as `runtimeCode.codeTable_ok`). The
variable-debt-token proxies run the same bytes (same admin, the PoolConfigurator).
-/

namespace Examples.AaveV3.Contracts.ATokenProxy

/-! Kernel lookup table of `runtimeCode` (bytes and jump destinations). -/
code_table runtimeCode

end Examples.AaveV3.Contracts.ATokenProxy
