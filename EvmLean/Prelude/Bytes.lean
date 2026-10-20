import EvmLean.Prelude.Word

/-!
# Byte strings

Total, kernel-reducible helpers on `ByteArray`. Big-endian throughout.
-/

namespace EvmLean.Bytes

/-- `n` zero bytes. -/
def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- `len` bytes of `b` from `off`, zero-padded past the end (calldata/code/returndata reads). -/
def readPadded (b : ByteArray) (off len : Nat) : ByteArray :=
  -- `ByteArray.extract` panics at runtime for offsets ≥ 2⁶⁴ even on empty ranges, so
  -- offsets past the end (which may be arbitrary stack words) never reach it.
  if off < b.size then
    let chunk := b.extract off (min (off + len) b.size)
    chunk ++ zeros (len - chunk.size)
  else zeros len

/-- Byte `i` of `b`, or zero past the end. -/
def getD (b : ByteArray) (i : Nat) : UInt8 := if h : i < b.size then b[i] else 0

/-- The 8 bytes at `i` as a big-endian `UInt64` (zero past the end). -/
def chunk64 (b : ByteArray) (i : Nat) : UInt64 :=
  (getD b i).toUInt64 <<< 56 ||| (getD b (i + 1)).toUInt64 <<< 48 |||
  (getD b (i + 2)).toUInt64 <<< 40 ||| (getD b (i + 3)).toUInt64 <<< 32 |||
  (getD b (i + 4)).toUInt64 <<< 24 ||| (getD b (i + 5)).toUInt64 <<< 16 |||
  (getD b (i + 6)).toUInt64 <<< 8 ||| (getD b (i + 7)).toUInt64

/-- Accumulate `k` big-endian 8-byte chunks of `b` starting at `i` into `acc`. -/
def toNatChunks (b : ByteArray) (acc i : Nat) : (k : Nat) → Nat
  | 0 => acc
  | k + 1 => toNatChunks b ((acc <<< 64) ||| (chunk64 b i).toNat) (i + 8) k

/-- Big-endian bytes as a `Nat`, folded in 64-bit chunks (one bignum op per 8 bytes). -/
def toNat (b : ByteArray) : Nat :=
  let head := b.size % 8
  let acc := (b.extract 0 head).foldl (fun acc x => acc * 256 + x.toNat) 0
  toNatChunks b acc head (b.size / 8)

/-- Interpret bytes as a big-endian word (taken modulo `2²⁵⁶`). -/
def toWord (b : ByteArray) : Word := BitVec.ofNat 256 (toNat b)

/-- `n` as exactly `len` big-endian bytes (high bytes beyond `len` are dropped). -/
def ofNatBE (len n : Nat) : ByteArray :=
  ⟨Array.ofFn (n := len) fun i => (n >>> (8 * (len - 1 - i.val))).toUInt8⟩

/-- A word as 32 big-endian bytes. -/
def ofWord (w : Word) : ByteArray := ofNatBE 32 w.toNat

/-- An address as 20 big-endian bytes. -/
def ofAddress (a : Address) : ByteArray := ofNatBE 20 a.toNat

/-- The minimal big-endian encoding of `n` (empty for zero), as used by RLP. -/
def ofNatMinimal (n : Nat) : ByteArray :=
  if n = 0 then .empty else ofNatBE ((n.log2 / 8) + 1) n

/-- Overwrite `dst` at `off` with `src`; caller ensures `off + src.size ≤ dst.size`. -/
def write (dst : ByteArray) (off : Nat) (src : ByteArray) : ByteArray :=
  src.copySlice 0 dst off src.size

end EvmLean.Bytes
