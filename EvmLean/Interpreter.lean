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
import EvmLean.Interpreter.Delegation
import EvmLean.Interpreter.Instructions
import EvmLean.Interpreter.Step

/-!
# Interpreter

Executes a `Message` to completion. Internally a small-step machine with an explicit
call stack: `step` is a total, non-recursive function, `run` iterates it with fuel.
-/

namespace EvmLean.Interpreter

/-- A failed top-level message that never ran: all gas consumed, state unchanged. -/
def failureResult (e : ExceptionalHalt) (world : World) (transient : TransientStorage) :
    MessageResult :=
  { gasLeft := 0, refundCounter := 0, logs := #[], accountsToDelete := ∅,
    touchedAccounts := ∅, error := some e, reverted := false, output := .empty,
    world, transientStorage := transient }

/-- Set up the machine for a top-level message, or return its result if no code runs.
An unaffordable value (asserted away by the spec) yields `insufficientFunds`, state unchanged. -/
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

/-- `processMessageCall` with explicit precompiles. EIP-7702 authorizations and their refund
persist even if the message fails. -/
def processMessageCallWith (pre : PrecompileImpl) (fuel : Nat) (ctx : Context) (world : World)
    (transient : TransientStorage) (msg : Message) : Except OutOfFuel MessageResult :=
  let (world, msg, authRefund) := applyTopLevelDelegation ctx pre.isPrecompile world msg
  let withRefund (r : MessageResult) : MessageResult :=
    { r with refundCounter := r.refundCounter + authRefund }
  match initMachine pre ctx world transient msg with
  | .inl r => .ok (withRefund r)
  | .inr m => (run fuel m).map withRefund

/-- Execute a top-level message to completion; one unit of `fuel` per `step`. Mirrors
`process_message_call`. -/
def processMessageCall (fuel : Nat) (ctx : Context) (world : World)
    (transient : TransientStorage) (msg : Message) : Except OutOfFuel MessageResult :=
  processMessageCallWith (PrecompileImpl.standard ctx) fuel ctx world transient msg

end EvmLean.Interpreter
