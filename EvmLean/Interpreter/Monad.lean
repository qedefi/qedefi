import EvmLean.Gas
import EvmLean.Interpreter.Frame
import EvmLean.Interpreter.State

/-!
# The instruction monad

`M α := StateT Machine (Except ExceptionalHalt)`, plus stack, gas, memory and access-set
primitives. On an exceptional halt the updated machine is discarded and `step` finishes the
frame from the pre-instruction machine: a failing frame keeps only its snapshot anyway.
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

/-- Subtract `amount` from the frame's gas, halting with `outOfGas` if short. -/
def charge (amount : Nat) : M Unit := do
  let g := (← getFrame).gasLeft
  if g < amount then throw .outOfGas
  modifyFrame fun fr => { fr with gasLeft := fr.gasLeft - amount }

/-- Give gas back to the frame (unused call gas). -/
def refundGas (amount : Nat) : M Unit :=
  modifyFrame fun fr => { fr with gasLeft := fr.gasLeft + amount }

/-- Pop the top of the stack, halting with `stackUnderflow` if empty. -/
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

/-- Push a word, halting with `stackOverflow` if the stack already holds 1024 items. -/
def push (w : Word) : M Unit := do
  if (← getFrame).stack.length ≥ Gas.stackLimit then throw .stackOverflow
  modifyFrame fun fr => { fr with stack := w :: fr.stack }

/-- Advance the program counter by `n` (default one). -/
def advance (n : Nat := 1) : M Unit := modifyFrame fun fr => { fr with pc := fr.pc + n }

/-- Halt with `writeInStaticContext` in a static frame. -/
def requireNonStatic : M Unit := do
  if (← getFrame).msg.isStatic then throw .writeInStaticContext

/-- Expansion cost of the `(offset, length)` accesses; allocates nothing. -/
def memoryExpansion (exts : List (Nat × Nat)) : M Gas.ExtendMemory := do
  return Gas.extendMemory (← getFrame).memory.size exts

/-- Expand memory to cover the accesses. Call only after charging (bounds the size by gas). -/
def expandMemory (exts : List (Nat × Nat)) : M Unit :=
  modifyFrame fun fr =>
    { fr with memory := exts.foldl (fun mem (off, len) => mem.expand off len) fr.memory }

/-- Write `data` at `off` (already expanded); empty writes are no-ops at any offset. -/
def writeMemory (off : Nat) (data : ByteArray) : M Unit :=
  if data.size = 0 then pure ()
  else modifyFrame fun fr => { fr with memory := fr.memory.write off data }

/-- `Bytes.readPadded b off len`, short-circuiting offsets past the end: `ByteArray.extract`
aborts on offsets ≥ 2⁶⁴ even for empty ranges. -/
def readBytes (b : ByteArray) (off len : Nat) : ByteArray :=
  if b.size ≤ off then Bytes.zeros len else Bytes.readPadded b off len

/-- Read `len` bytes of memory at `off` (zero-padded). -/
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
