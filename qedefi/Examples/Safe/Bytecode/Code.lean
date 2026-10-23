import Examples.Safe.Contracts.SafeSingleton
import Examples.Safe.Contracts.SafeProxy
import EvmLogic.Program.Code

/-!
# Code tables of Safe v1.5.0

Kernel lookup tables (bytes and jump destinations) of the singleton's and the proxy's runtime
code, checked once, for symbolic execution (`own_explore` reads code bytes through them).
-/

namespace Examples.Safe.Contracts.SafeSingleton
code_table runtimeCode
end Examples.Safe.Contracts.SafeSingleton

namespace Examples.Safe.Contracts.SafeProxy
code_table runtimeCode
end Examples.Safe.Contracts.SafeProxy
