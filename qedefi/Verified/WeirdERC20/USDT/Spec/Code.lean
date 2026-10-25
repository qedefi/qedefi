import Verified.WeirdERC20.USDT.Contracts.USDT
import EvmLogic.Program.Code

/-!
# USDT: code facts

The kernel lookup table of mainnet `TetherToken`'s runtime code (`runtimeCode.codeTable`,
checked once as `runtimeCode.codeTable_ok`), so that the symbolic executors read code bytes,
`PUSH` immediates and jump destinations of the 11,075-byte literal in logarithmically many
kernel steps. The generated mainnet modules have no table of their own.
-/

namespace Verified.WeirdERC20.USDT.Contracts.USDT

/-! Kernel lookup table of `runtimeCode` (bytes and jump destinations). -/
code_table runtimeCode

end Verified.WeirdERC20.USDT.Contracts.USDT
