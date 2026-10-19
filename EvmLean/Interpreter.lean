import EvmLean.Opcode
import EvmLean.Machine.Memory
import EvmLean.Machine.Types
import EvmLean.Precompile
import EvmLean.Prelude.Rlp
import EvmLean.Gas
import EvmLean.Interpreter.JumpDest
import EvmLean.Interpreter.State
import EvmLean.Interpreter.Frame
import EvmLean.Interpreter.Monad
import EvmLean.Interpreter.Instructions
import EvmLean.Interpreter.Step

/-!
# Interpreter

Executes a `Message` to completion. Internally a small-step machine with an explicit
call stack: `step` is a total, non-recursive function, `run` iterates it with fuel.

| Module | Contents | Reference |
|---|---|---|
| `Interpreter.JumpDest` | jump destination bitmap | `vm/runtime.py` |
| `Interpreter.State` | world/transient operations, addresses | `state_tracker.py`, `utils/address.py` |
| `Interpreter.Frame` | `Frame`, `Machine`, results | `vm/__init__.py` (`Evm`) |
| `Interpreter.Monad` | stack, gas, memory primitives | `vm/stack.py`, `vm/gas.py`, `vm/memory.py` |
| `Interpreter.Instructions` | `exec : Opcode → M Action` | `vm/instructions/*.py` |
| `Interpreter.Step` | `step`, `run`, `OutOfFuel` | `vm/interpreter.py`, `generic_call`, `generic_create` |
| this file | `processMessageCall` | `process_message_call` |

The frozen entry points are `OutOfFuel` (in `Interpreter.Step`), `processMessageCall`
(here), and `createAddress` / `create2Address` (in `Interpreter.State`).
-/

namespace EvmLean.Interpreter

/-- A failed top-level message that never ran: all gas consumed, state unchanged. -/
def failureResult (e : ExceptionalHalt) (world : World) (transient : TransientStorage) :
    MessageResult :=
  { gasLeft := 0, refundCounter := 0, logs := #[], accountsToDelete := ∅,
    touchedAccounts := ∅, error := some e, reverted := false, output := .empty,
    world, transientStorage := transient }

/-- Set up the machine for a top-level message, or return its result directly if it
completes without executing code (address collision, precompile call, impossible depth or
value). Mirrors `process_message_call` up to the execution loop.

The reference asserts that the caller can afford the value (the transaction layer has
checked it); here an unaffordable value is reported as `insufficientFunds` without any
state change. -/
def initMachine (pre : PrecompileImpl) (ctx : Context) (world : World)
    (transient : TransientStorage) (msg : Message) : MessageResult ⊕ Machine :=
  let snapshot := (world, transient)
  let mk (world : World) (created : AddressSet) (kind : FrameKind) : Machine :=
    { ctx, precompiles := pre, world, transient, originalWorld := snapshot.1,
      createdAccounts := created, frame := Frame.init msg kind snapshot, parents := [] }
  if msg.depth > Gas.stackDepthLimit then .inl (failureResult .callDepthExceeded world transient)
  else if msg.shouldTransferValue && (world.balance msg.caller).toNat < msg.value.toNat then
    .inl (failureResult .insufficientFunds world transient)
  else
    match msg.target with
    | none =>
      if !accountDeployable world msg.currentTarget then
        .inl (failureResult .addressCollision world transient)
      else
        let (world', created) := beginCreate world ∅ msg
        .inr (mk world' created .create)
    | some _ =>
      let world' := transferValue world msg
      match precompileOf pre msg with
      | some a =>
        let (r, w, t) := runPrecompile pre a msg (.call 0 0) world' transient snapshot
        .inl (topLevelResult msg.target w t r)
      | none => .inr (mk world' ∅ (.call 0 0))

/-- `processMessageCall` with an explicit precompile implementation. -/
def processMessageCallWith (pre : PrecompileImpl) (fuel : Nat) (ctx : Context) (world : World)
    (transient : TransientStorage) (msg : Message) : Except OutOfFuel MessageResult :=
  match initMachine pre ctx world transient msg with
  | .inl r => .ok r
  | .inr m => run fuel m

/-- Execute a top-level message (call or creation) to completion. Mirrors
`process_message_call` in `ethereum/execution-specs`. Each unit of `fuel` is one `step`. -/
def processMessageCall (fuel : Nat) (ctx : Context) (world : World)
    (transient : TransientStorage) (msg : Message) : Except OutOfFuel MessageResult :=
  processMessageCallWith (PrecompileImpl.standard ctx) fuel ctx world transient msg

end EvmLean.Interpreter
