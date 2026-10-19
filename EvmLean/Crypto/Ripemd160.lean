import EvmLean.Prelude.Bytes

/-!
# RIPEMD-160, for precompile `0x03`

Source: H. Dobbertin, A. Bosselaers, B. Preneel, *RIPEMD-160: A Strengthened Version of
RIPEMD* (FSE 1996), and its pseudocode appendix "The hash function RIPEMD-160".

## Algorithm

* Padding is MD4-style: `0x80`, zeros, then the 64-bit **little-endian** bit length, to a
  multiple of 64 bytes.
* Each 64-byte block is read as 16 little-endian words `X` and processed by two parallel
  lines of 80 steps (five rounds of 16). Step `j` of the left line computes
  `T = rotl (A + f j B C D + X[r j] + K j) (s j) + E`, then shifts the registers:
  `(A, B, C, D, E) := (E, T, B, rotl C 10, D)`. The right line is identical but uses
  `r'`, `s'`, `K'` and the boolean functions in reverse order (`f (79 - j)`).
* The two lines are combined into the chaining value with a rotation (see `compress`).
* The digest is the 5 state words, little-endian.

Table reads go through `getD`, whose fallback is never taken (all indices are below 80).
-/

namespace EvmLean.Ripemd160

/-- Message-word selection for the left line, `r` (80 entries). -/
def rL : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]

/-- Message-word selection for the right line, `r'` (80 entries). -/
def rR : Array Nat := #[
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]

/-- Rotation amounts for the left line, `s` (80 entries). -/
def sL : Array UInt32 := #[
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]

/-- Rotation amounts for the right line, `s'` (80 entries). -/
def sR : Array UInt32 := #[
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]

/-- Round constants of the left line, `K`, one per round of 16 steps. -/
def kL : Array UInt32 := #[0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]

/-- Round constants of the right line, `K'`, one per round of 16 steps. -/
def kR : Array UInt32 := #[0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

/-- Rotate left by `n` bits, `0 < n < 32`. -/
@[inline] def rotl (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- The boolean function of round `rnd ∈ {0, …, 4}` (`f` of steps `16·rnd … 16·rnd+15`). -/
@[inline] def f (rnd : Nat) (x y z : UInt32) : UInt32 :=
  match rnd with
  | 0 => x ^^^ y ^^^ z
  | 1 => (x &&& y) ||| (~~~x &&& z)
  | 2 => (x ||| ~~~y) ^^^ z
  | 3 => (x &&& z) ||| (y &&& ~~~z)
  | _ => x ^^^ (y ||| ~~~z)

/-- Byte `i` of `b` widened to a word, zero past the end. -/
@[inline] def byteAt (b : ByteArray) (i : Nat) : UInt32 :=
  if h : i < b.size then b[i].toUInt32 else 0

/-- The little-endian 32-bit word at byte offset `o` of `b`. -/
@[inline] def wordAt (b : ByteArray) (o : Nat) : UInt32 :=
  byteAt b o ||| (byteAt b (o + 1) <<< 8) ||| (byteAt b (o + 2) <<< 16) |||
  (byteAt b (o + 3) <<< 24)

/-- Process the 64-byte block at offset `o` of `b`: both lines of 80 steps, then the
combination `h' = (h₁+C+D', h₂+D+E', h₃+E+A', h₄+A+B', h₀+B+C')`. -/
def compress (h : Vector UInt32 5) (b : ByteArray) (o : Nat) : Vector UInt32 5 := Id.run do
  let x : Array UInt32 := Array.ofFn (n := 16) fun i => wordAt b (o + 4 * i.val)
  let mut al := h[0]
  let mut bl := h[1]
  let mut cl := h[2]
  let mut dl := h[3]
  let mut el := h[4]
  let mut ar := h[0]
  let mut br := h[1]
  let mut cr := h[2]
  let mut dr := h[3]
  let mut er := h[4]
  for j in [0:80] do
    let rnd := j / 16
    let t := rotl (al + f rnd bl cl dl + x.getD (rL.getD j 0) 0 + kL.getD rnd 0)
      (sL.getD j 0) + el
    al := el
    el := dl
    dl := rotl cl 10
    cl := bl
    bl := t
    let t := rotl (ar + f (4 - rnd) br cr dr + x.getD (rR.getD j 0) 0 + kR.getD rnd 0)
      (sR.getD j 0) + er
    ar := er
    er := dr
    dr := rotl cr 10
    cr := br
    br := t
  return #v[h[1] + cl + dr, h[2] + dl + er, h[3] + el + ar, h[4] + al + br, h[0] + bl + cr]

/-- Process `n` consecutive 64-byte blocks of `b` starting at offset `o`. -/
def compressBlocks (b : ByteArray) : (n : Nat) → (o : Nat) → Vector UInt32 5 → Vector UInt32 5
  | 0, _, h => h
  | n + 1, o, h => compressBlocks b n (o + 64) (compress h b o)

/-- The initial chaining value. -/
def iv : Vector UInt32 5 := #v[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]

/-- `n` as 8 little-endian bytes. -/
def le64 (n : Nat) : ByteArray := ⟨Array.ofFn (n := 8) fun i => (n >>> (8 * i.val)).toUInt8⟩

/-- The padded message: `data ‖ 0x80 ‖ 0…0 ‖ bitlen` (64-bit little-endian), a multiple
of 64 bytes long. -/
def pad (data : ByteArray) : ByteArray :=
  let zeros := (119 - data.size % 64) % 64
  data ++ ⟨#[0x80]⟩ ++ Bytes.zeros zeros ++ le64 (8 * data.size)

/-- RIPEMD-160 digest (20 bytes). -/
def hash (data : ByteArray) : ByteArray :=
  let m := pad data
  let h := compressBlocks m (m.size / 64) 0 iv
  ⟨Array.ofFn (n := 20) fun i =>
    let word := if hi : i.val / 4 < 5 then h[i.val / 4] else 0
    (word >>> (8 * (i.val % 4)).toUInt32).toUInt8⟩

end EvmLean.Ripemd160
