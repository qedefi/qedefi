import EvmLean.Gas
import EvmLean.Interpreter.Frame
import EvmLean.Interpreter.State

/-!
# The instruction monad

A single instruction is a computation `M α := StateT Machine (Except ExceptionalHalt)`: it
reads and updates the machine (normally only the executing frame, the world and transient
storage) and may halt exceptionally. On an exceptional halt the updated machine is
discarded; `step` finishes the frame from the pre-instruction machine, which is sound
because a failing frame keeps nothing but its snapshot (`process_message`'s
`except ExceptionalHalt` branch).

The primitives mirror `cancun/vm/stack.py` (`pop`, `push`), `cancun/vm/gas.py`
(`charge_gas`) and the access-list bookkeeping repeated in the instruction files.
-/

namespace EvmLean.Interpreter

/-- The instruction monad. -/
abbrev M := StateT Machine (Except ExceptionalHalt)

/-- The executing frame. -/
@[inline] def getFrame : M Frame := do return (← get).frame

/-- Update the executing frame. -/
@[inline] def modifyFrame (f : Frame → Frame) : M Unit :=
  modify fun m => { m with frame := f m.frame }

/-- Update the world state. -/
@[inline] def modifyWorld (f : World → World) : M Unit :=
  modify fun m => { m with world := f m.world }

/-- Update the executing frame's substate. -/
@[inline] def modifySub (f : Substate → Substate) : M Unit :=
  modifyFrame fun fr => { fr with sub := f fr.sub }

/-- Subtract `amount` from the frame's gas, halting with `outOfGas` if there is not enough.
Mirrors `charge_gas`. -/
def charge (amount : Nat) : M Unit := do
  let g := (← getFrame).gasLeft
  if g < amount then throw .outOfGas
  modifyFrame fun fr => { fr with gasLeft := fr.gasLeft - amount }

/-- Give gas back to the frame (unused call gas). -/
def refundGas (amount : Nat) : M Unit :=
  modifyFrame fun fr => { fr with gasLeft := fr.gasLeft + amount }

/-- Pop the top of the stack, halting with `stackUnderflow` if it is empty. Mirrors `pop`. -/
def pop : M Word := do
  match (← getFrame).stack with
  | [] => throw .stackUnderflow
  | x :: xs =>
    modifyFrame fun fr => { fr with stack := xs }
    return x

/-- Pop a word as a natural number. -/
def popNat : M Nat := return (← pop).toNat

/-- Pop a word as an address (its low 160 bits, `to_address_masked`). -/
def popAddress : M Address := return Word.toAddress (← pop)

/-- Push a word, halting with `stackOverflow` if the stack already holds 1024 items.
Mirrors `push`. -/
def push (w : Word) : M Unit := do
  if (← getFrame).stack.length ≥ Gas.stackLimit then throw .stackOverflow
  modifyFrame fun fr => { fr with stack := w :: fr.stack }

/-- Advance the program counter by `n` (default one). -/
def advance (n : Nat := 1) : M Unit := modifyFrame fun fr => { fr with pc := fr.pc + n }

/-- Halt with `writeInStaticContext` in a static frame. -/
def requireNonStatic : M Unit := do
  if (← getFrame).msg.isStatic then throw .writeInStaticContext

/-- Memory expansion needed for the given `(offset, length)` accesses, computed from the
current memory size. Nothing is allocated. Mirrors `calculate_gas_extend_memory`. -/
def memoryExpansion (exts : List (Nat × Nat)) : M Gas.ExtendMemory := do
  return Gas.extendMemory (← getFrame).memory.size exts

/-- Expand memory to cover the given accesses. Only call after charging the expansion
cost (the size is then bounded by the available gas). -/
def expandMemory (exts : List (Nat × Nat)) : M Unit :=
  modifyFrame fun fr =>
    { fr with memory := exts.foldl (fun mem (off, len) => mem.expand off len) fr.memory }

/-- Write `data` to memory at `off` (memory must already cover the range). Empty writes are
no-ops whatever the offset. Mirrors `memory_write`. -/
def writeMemory (off : Nat) (data : ByteArray) : M Unit :=
  if data.size = 0 then pure ()
  else modifyFrame fun fr => { fr with memory := fr.memory.write off data }

/-- `len` bytes of `b` from `off`, zero-padded (`buffer_read`). Equal to
`Bytes.readPadded b off len`, but offsets at or past the end short-circuit to zeros: offsets
come from 256-bit words, and the runtime's `ByteArray.extract` aborts (out of memory) on
offsets that do not fit a machine word, even for empty ranges. -/
def readBytes (b : ByteArray) (off len : Nat) : ByteArray :=
  if b.size ≤ off then Bytes.zeros len else Bytes.readPadded b off len

/-- Read `len` bytes of memory at `off` (zero-padded). Mirrors `memory_read_bytes`. -/
def readMemory (off len : Nat) : M ByteArray := return readBytes (← getFrame).memory.bytes off len

/-- Mark `a` warm, returning whether it already was (EIP-2929). -/
def accessAddress (a : Address) : M Bool := do
  let warm := (← getFrame).sub.accessedAddresses.contains a
  unless warm do
    modifySub fun s => { s with accessedAddresses := s.accessedAddresses.insert a }
  return warm

/-- Mark storage key `k` of the current account warm, returning whether it already was. -/
def accessStorageKey (k : Word) : M Bool := do
  let fr ← getFrame
  let a := fr.msg.currentTarget
  let warm := storageKeyWarm fr.sub.accessedStorageKeys a k
  unless warm do
    modifySub fun s => { s with accessedStorageKeys := addStorageKey s.accessedStorageKeys a k }
  return warm

/-- Set the return-data buffer. -/
def setReturnData (data : ByteArray) : M Unit :=
  modifyFrame fun fr => { fr with returnData := data }

end EvmLean.Interpreter
