import Verified.AaveV3.Contracts.AToken
import EvmLogic.Program.Code

/-!
# `AToken`: code facts

The kernel lookup table of the deployed AToken implementation's runtime code
(`runtimeCode.codeTable`, checked once as `runtimeCode.codeTable_ok`), so that the symbolic
executors read code bytes and `PUSH` immediates in logarithmically many kernel steps instead of
scanning the 10,477-byte literal. The generated mainnet modules have no table of their own.
-/

namespace Verified.AaveV3.Contracts.AToken

/-! Kernel lookup table of `runtimeCode` (bytes and jump destinations). -/
code_table runtimeCode

end Verified.AaveV3.Contracts.AToken
