import Verified.WeirdERC20.USDT.Contracts.USDT
import EvmLogic.Program.Code
import EvmLogic.Tactic.Patched

/-!
# The code table of USDT's deployed code

`code_table` for `USDT.runtimeCode` (the existing USDT proofs run the patched code, whose
forwarding bytes are replaced by `INVALID`); the malformed-calldata runs read the deployed
code itself.
-/

namespace Verified.WeirdERC20.USDT.Spec.Malformed
open Verified.WeirdERC20.USDT.Contracts

code_table USDT.runtimeCode

end Verified.WeirdERC20.USDT.Spec.Malformed
