import EvmLean.Prelude.Bytes

/-!
# Memory

EVM memory is a byte array that grows in 32-byte words. We keep the backing array
exactly as large as the active memory (`size = 32 * words`); expansion appends zeros.
Callers must charge the expansion gas (see `EvmLean.Gas.memoryExpansion`) *before*
expanding, so huge offsets are rejected before anything is allocated.
-/

namespace EvmLean

/-- EVM memory. Invariant (preserved by every operation): `bytes.size % 32 = 0`. -/
structure Memory where
  /-- The active memory, zero-initialised. -/
  bytes : ByteArray := .empty
  deriving Inhabited, DecidableEq

namespace Memory

/-- Active size in bytes (`MSIZE`). -/
def size (m : Memory) : Nat := m.bytes.size

/-- Active size in 32-byte words. -/
def words (m : Memory) : Nat := m.size / 32

/-- Active words after an access to `[off, off + len)`; zero-length accesses never expand. -/
def wordsAfter (words off len : Nat) : Nat :=
  if len = 0 then words else max words ((off + len + 31) / 32)

/-- Expand memory to cover `[off, off + len)`. -/
def expand (m : Memory) (off len : Nat) : Memory :=
  let target := 32 * wordsAfter m.words off len
  if target ≤ m.size then m else ⟨m.bytes ++ Bytes.zeros (target - m.size)⟩

/-- Read `len` bytes at `off` (zero-padded; normally called after `expand`). -/
def read (m : Memory) (off len : Nat) : ByteArray := Bytes.readPadded m.bytes off len

/-- Expand, then overwrite memory at `off` with `data`. -/
def write (m : Memory) (off : Nat) (data : ByteArray) : Memory :=
  let m := m.expand off data.size
  ⟨Bytes.write m.bytes off data⟩

/-- `MLOAD` value (after expansion). -/
def loadWord (m : Memory) (off : Nat) : Word := Bytes.toWord (m.read off 32)

/-- `MSTORE`. -/
def storeWord (m : Memory) (off : Nat) (w : Word) : Memory := m.write off (Bytes.ofWord w)

/-- `MSTORE8`: store the low byte of `w`. -/
def storeByte (m : Memory) (off : Nat) (w : Word) : Memory :=
  m.write off ⟨#[(w.toNat % 256).toUInt8]⟩

end Memory

end EvmLean
