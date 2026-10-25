import Verified.AaveV3.Contracts.ATokenProxy
import EvmLogic.Program.Code
import EvmLogic.GasMono.CodeScan
import EvmLogic.Tactic.KernelRfl

/-!
# `ATokenProxy`: code facts

The kernel lookup table of the deployed `InitializableImmutableAdminUpgradeabilityProxy` runtime
code of the aTokens (`runtimeCode.codeTable`, checked once as `runtimeCode.codeTable_ok`). The
variable-debt-token proxies run the same bytes (same admin, the PoolConfigurator).

For gas monotonicity (`EvmLogic.GasMono`), on the region `[0, 2347)` before the final
`INVALID` and the metadata (`regionOk_runtimeCode`): every `GAS` feeds a `CALL`, `STATICCALL` or
`DELEGATECALL` (`gasFeedsCall_runtimeCode`; the code's only calls are `GAS; DELEGATECALL` at
pcs 516, 944 and 1137, the last the fallback's `_delegate`), and every call follows a `GAS`
(`callsFed_runtimeCode`).
-/

namespace Verified.AaveV3.Contracts.ATokenProxy

/-! Kernel lookup table of `runtimeCode` (bytes and jump destinations). -/
code_table runtimeCode

open EvmLogic.GasMono in
theorem regionOk_runtimeCode : RegionOk runtimeCode 2347 := by
  rw [regionOk_iff]; kernel_decide

open EvmLogic.GasMono in
theorem gasFeedsCall_runtimeCode : GasFeedsCall runtimeCode 2347 := by
  rw [gasFeedsCall_iff]; kernel_decide

open EvmLogic.GasMono in
theorem callsFed_runtimeCode : CallsFed runtimeCode 2347 :=
  callsFed_of_scan (by kernel_decide)

end Verified.AaveV3.Contracts.ATokenProxy
