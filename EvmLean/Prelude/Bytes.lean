import EvmLean.Prelude.Word

/-!
# Byte strings

Total, kernel-reducible helpers on `ByteArray`. Everything here is defined in plain
Lean (no `@[extern]`, no `opaque`), so the kernel can evaluate and reason about it.
Big-endian is the EVM's byte order throughout.
-/

namespace EvmLean.Bytes

/-- `n` zero bytes. -/
def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- Read `len` bytes of `b` starting at `off`, reading zeros past the end of `b`.
This is how the EVM reads calldata, code and return data. -/
def readPadded (b : ByteArray) (off len : Nat) : ByteArray :=
  let chunk := b.extract off (off + len)
  chunk ++ zeros (len - chunk.size)

/-- Interpret bytes as a big-endian natural number. -/
def toNat (b : ByteArray) : Nat := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- Interpret bytes as a big-endian word (taken modulo `2²⁵⁶`). -/
def toWord (b : ByteArray) : Word := BitVec.ofNat 256 (toNat b)

/-- `n` as exactly `len` big-endian bytes (high bytes beyond `len` are dropped). -/
def ofNatBE (len n : Nat) : ByteArray :=
  ⟨Array.ofFn (n := len) fun i => (n / 256 ^ (len - 1 - i.val)).toUInt8⟩

/-- A word as 32 big-endian bytes. -/
def ofWord (w : Word) : ByteArray := ofNatBE 32 w.toNat

/-- An address as 20 big-endian bytes. -/
def ofAddress (a : Address) : ByteArray := ofNatBE 20 a.toNat

/-- The minimal big-endian encoding of `n` (empty for zero), as used by RLP. -/
def ofNatMinimal (n : Nat) : ByteArray :=
  if n = 0 then .empty else ofNatBE ((n.log2 / 8) + 1) n

/-- Overwrite `dst` at `off` with `src`. The caller guarantees `off + src.size ≤ dst.size`
(memory is expanded before it is written). -/
def write (dst : ByteArray) (off : Nat) (src : ByteArray) : ByteArray :=
  src.copySlice 0 dst off src.size

end EvmLean.Bytes
