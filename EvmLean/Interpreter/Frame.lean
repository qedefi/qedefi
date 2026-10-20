import EvmLean.Machine.Memory
import EvmLean.Machine.Types
import EvmLean.Precompile
import EvmLean.Interpreter.JumpDest

/-!
# Frames and the machine

A `Frame` is one executing message (the spec's `Evm` plus a rollback snapshot and a
`FrameKind` saying how the parent consumes the result). A `Machine` is the transaction-wide
state with the non-empty frame stack `frame :: parents`; pushing and popping frames replaces
the spec's recursion, so `step` is total and non-recursive.
-/

namespace EvmLean.Interpreter

/-- The precompiled contracts, a parameter so the interpreter works with any implementation. -/
structure PrecompileImpl where
  /-- Is this address a precompile? -/
  isPrecompile : Address → Bool
  /-- Run the precompile at the address on the input with the given gas. -/
  run : Address → ByteArray → Nat → Precompile.Result

/-- The precompiles of `EvmLean.Precompile` for the context's fork and crypto. -/
def PrecompileImpl.standard (ctx : Context) : PrecompileImpl where
  isPrecompile := Precompile.isPrecompile ctx.fork
  run := Precompile.run ctx.crypto ctx.fork

/-- Substate accrued by a frame: merged into the parent on success, discarded on failure. -/
structure Substate where
  /-- Logs emitted (`Evm.logs`). -/
  logs : Array Log := #[]
  /-- Refund counter (`Evm.refund_counter`); may go negative. -/
  refundCounter : Int := 0
  /-- `SELFDESTRUCT`ed accounts (`Evm.accounts_to_delete`). -/
  accountsToDelete : AddressSet := ∅
  /-- EIP-161 touched accounts (pre-`state_tracker` `Evm.touched_accounts`). -/
  touchedAccounts : AddressSet := ∅
  /-- Warm addresses (`Evm.accessed_addresses`), initialised from the message. -/
  accessedAddresses : AddressSet := ∅
  /-- Warm storage keys (`Evm.accessed_storage_keys`), initialised from the message. -/
  accessedStorageKeys : StorageKeySet := ∅
  deriving Inhabited

/-- How the parent consumes a frame's result. -/
inductive FrameKind where
  /-- A message call: output goes to the parent's memory window, then `1`/`0` is pushed. -/
  | call (retOffset retSize : Nat)
  /-- A contract creation: on success the code is deposited and the new address pushed, else `0`. -/
  | create
  deriving Inhabited, Repr, DecidableEq

/-- One executing message: the spec's `Evm` plus rollback snapshot and return continuation. -/
structure Frame where
  /-- The message being executed (`Evm.message`). -/
  msg : Message
  /-- Code being executed (`Evm.code`, equal to `msg.code`). -/
  code : ByteArray
  /-- Valid jump destinations of `code` (`Evm.valid_jump_destinations`), as a bitmap. -/
  jumpDests : Array Bool
  /-- Program counter. -/
  pc : Nat := 0
  /-- Operand stack, head = top. At most 1024 items. -/
  stack : List Word := []
  /-- Memory. -/
  memory : Memory := {}
  /-- Gas left. -/
  gasLeft : Nat
  /-- Output of the most recent child call (`Evm.return_data`). -/
  returnData : ByteArray := .empty
  /-- Accrued substate. -/
  sub : Substate
  /-- World and transient storage to restore if this frame fails. -/
  snapshot : World × TransientStorage
  /-- How the parent consumes this frame's result. -/
  kind : FrameKind

/-- A fresh frame for `msg`: empty stack and memory, all of `msg.gas`, warm sets from `msg`. -/
def Frame.init (msg : Message) (kind : FrameKind) (snapshot : World × TransientStorage) :
    Frame where
  msg := msg
  code := msg.code
  jumpDests := validJumpDests msg.code
  gasLeft := msg.gas
  sub := { accessedAddresses := msg.accessedAddresses,
           accessedStorageKeys := msg.accessedStorageKeys }
  snapshot := snapshot
  kind := kind

/-- The transaction-wide machine state; the frame stack is `frame :: parents`. -/
structure Machine where
  /-- Block and transaction environment, fork, crypto. -/
  ctx : Context
  /-- Precompiled contracts. -/
  precompiles : PrecompileImpl
  /-- Current world state. -/
  world : World
  /-- Current transient storage. -/
  transient : TransientStorage
  /-- The world at the start of the message call (`SSTORE` original values). -/
  originalWorld : World
  /-- Accounts created during the transaction; never rolled back. -/
  createdAccounts : AddressSet
  /-- The executing frame. -/
  frame : Frame
  /-- Suspended ancestor frames, innermost first. -/
  parents : List Frame

/-- How a frame ended. -/
inductive Outcome where
  /-- `STOP`, `RETURN`, `SELFDESTRUCT`, or running off the end of the code. -/
  | success (output : ByteArray)
  /-- `REVERT`: state rolled back, remaining gas returned. -/
  | revert (output : ByteArray)
  /-- Exceptional halt: state rolled back, all gas consumed. -/
  | halt (e : ExceptionalHalt)

/-- The result of a finished child frame (or precompile call) as seen by its parent. -/
structure ChildResult where
  /-- Gas returned to the parent. -/
  gasLeft : Nat
  /-- The exceptional halt, if any (`none` on success and on `REVERT`). -/
  error : Option ExceptionalHalt
  /-- Did the child `REVERT`? -/
  reverted : Bool
  /-- Output (revert data on revert, empty on exceptional halt). -/
  output : ByteArray
  /-- The child's substate (merged on success; touched set used by the RIPEMD-160 quirk). -/
  sub : Substate
  /-- The child's `msg.currentTarget`. -/
  target : Address
  /-- How the parent consumes it. -/
  kind : FrameKind

/-- Did the child succeed? -/
def ChildResult.success (r : ChildResult) : Bool := r.error.isNone && !r.reverted

/-- Result of one `step`. -/
inductive StepResult where
  /-- Execution continues. -/
  | running (m : Machine)
  /-- The top-level frame finished. -/
  | done (r : MessageResult)

/-- A pending child call from a `CALL*` instruction, after all its checks and gas charges. -/
structure CallRequest where
  /-- The child message. -/
  msg : Message
  /-- Output window in the parent's memory. -/
  retOffset : Nat
  /-- Output window size. -/
  retSize : Nat

/-- What an instruction asks `step` to do next. Exceptional halts are `Except.error`. -/
inductive Action where
  /-- Continue with the next instruction (the pc has been updated). -/
  | next
  /-- Halt the frame successfully with this output. -/
  | stop (output : ByteArray)
  /-- `REVERT` with this output. -/
  | revert (output : ByteArray)
  /-- Start a child message call. -/
  | call (req : CallRequest)
  /-- Start a child creation with this message (`target = none`). -/
  | create (msg : Message)

end EvmLean.Interpreter
