import EvmLean.Opcode
import EvmLean.Machine.Memory
import EvmLean.Machine.Types
import EvmLean.Precompile
import EvmLean.Prelude.Rlp

/-!
# Interpreter

Executes a `Message` to completion. Internally a small-step machine with an explicit
call stack: `step` is a total, non-recursive function, `run` iterates it with fuel.
-/

namespace EvmLean.Interpreter

/-- Fuel ran out before execution finished. This is not an EVM outcome: with enough fuel
every message terminates (gas strictly bounds execution). -/
structure OutOfFuel where
  deriving Inhabited, Repr

/-- Execute a top-level message (call or creation) to completion. Mirrors
`process_message_call` in `ethereum/execution-specs`. -/
def processMessageCall (fuel : Nat) (ctx : Context) (world : World)
    (transient : TransientStorage) (msg : Message) : Except OutOfFuel MessageResult := sorry

/-- The address of a contract created by `sender` with nonce `nonce` (`CREATE`). -/
def createAddress (keccak256 : ByteArray → Word) (sender : Address) (nonce : Nat) : Address := sorry

/-- The address of a contract created by `CREATE2`. -/
def create2Address (keccak256 : ByteArray → Word) (sender : Address) (salt : Word) (initCode : ByteArray) : Address := sorry

end EvmLean.Interpreter
