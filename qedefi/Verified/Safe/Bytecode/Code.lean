import Verified.Safe.Contracts.SafeSingleton
import Verified.Safe.Contracts.SafeProxy
import EvmLogic.Program.Code

/-!
# Code tables of Safe v1.5.0

Kernel lookup tables (bytes and jump destinations) of the singleton's and the proxy's runtime
code, checked once, for symbolic execution (`own_explore` reads code bytes through them).
-/

namespace Verified.Safe.Contracts.SafeSingleton
code_table runtimeCode
end Verified.Safe.Contracts.SafeSingleton

namespace Verified.Safe.Contracts.SafeProxy
code_table runtimeCode
end Verified.Safe.Contracts.SafeProxy
