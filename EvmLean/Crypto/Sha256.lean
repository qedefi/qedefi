import EvmLean.Prelude.Bytes

/-!
# SHA-256 (FIPS 180-4), for precompile `0x02`

Source: NIST FIPS 180-4, *Secure Hash Standard*, §4.1.2 (functions), §4.2.2 (constants),
§5.1.1 (padding), §5.3.3 (initial hash value) and §6.2 (computation).

## Algorithm

* Pad the message with `0x80`, zeros, and the 64-bit big-endian bit length, to a multiple
  of 64 bytes.
* For each 64-byte block, expand the 16 big-endian message words into the 64-word
  schedule `W`, run the 64 compression rounds on the working variables `a … h`, and add
  them into the hash state.
* The digest is the 8 state words, big-endian.

All arithmetic is on `UInt32` (wrapping mod `2³²`, as the standard requires). Table and
schedule reads go through `getD`, whose fallback is never taken because every index is
below 64.
-/

namespace EvmLean.Sha256

/-- The 64 round constants `K` (FIPS 180-4, §4.2.2). -/
def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value `H⁽⁰⁾` (FIPS 180-4, §5.3.3). -/
def iv : Vector UInt32 8 :=
  #v[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
    0x5be0cd19]

/-- Rotate right by `n` bits, `0 < n < 32`. -/
@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- `Σ₀` (FIPS 180-4, (4.4)). -/
@[inline] def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- `Σ₁` (FIPS 180-4, (4.5)). -/
@[inline] def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- `σ₀` (FIPS 180-4, (4.6)). -/
@[inline] def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

/-- `σ₁` (FIPS 180-4, (4.7)). -/
@[inline] def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- Byte `i` of `b` widened to a word, zero past the end. -/
@[inline] def byteAt (b : ByteArray) (i : Nat) : UInt32 :=
  if h : i < b.size then b[i].toUInt32 else 0

/-- The big-endian 32-bit word at byte offset `o` of `b`. -/
@[inline] def wordAt (b : ByteArray) (o : Nat) : UInt32 :=
  (byteAt b o <<< 24) ||| (byteAt b (o + 1) <<< 16) ||| (byteAt b (o + 2) <<< 8) |||
  byteAt b (o + 3)

/-- The message schedule `W₀ … W₆₃` of the 64-byte block at offset `o`
(FIPS 180-4, §6.2.2 step 1). -/
def schedule (b : ByteArray) (o : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.emptyWithCapacity 64
  for i in [0:16] do
    w := w.push (wordAt b (o + 4 * i))
  for i in [16:64] do
    w := w.push (smallSigma1 (w.getD (i - 2) 0) + w.getD (i - 7) 0 +
      smallSigma0 (w.getD (i - 15) 0) + w.getD (i - 16) 0)
  return w

/-- Process the 64-byte block at offset `o` of `b` (FIPS 180-4, §6.2.2 steps 2–4). -/
def compress (h : Vector UInt32 8) (b : ByteArray) (o : Nat) : Vector UInt32 8 := Id.run do
  let w := schedule b o
  let mut a := h[0]
  let mut b' := h[1]
  let mut c := h[2]
  let mut d := h[3]
  let mut e := h[4]
  let mut f := h[5]
  let mut g := h[6]
  let mut hh := h[7]
  for i in [0:64] do
    let t1 := hh + bigSigma1 e + ((e &&& f) ^^^ (~~~e &&& g)) + k.getD i 0 + w.getD i 0
    let t2 := bigSigma0 a + ((a &&& b') ^^^ (a &&& c) ^^^ (b' &&& c))
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b'
    b' := a
    a := t1 + t2
  return #v[h[0] + a, h[1] + b', h[2] + c, h[3] + d, h[4] + e, h[5] + f, h[6] + g, h[7] + hh]

/-- Process `n` consecutive 64-byte blocks of `b` starting at offset `o`. -/
def compressBlocks (b : ByteArray) : (n : Nat) → (o : Nat) → Vector UInt32 8 → Vector UInt32 8
  | 0, _, h => h
  | n + 1, o, h => compressBlocks b n (o + 64) (compress h b o)

/-- The padded message (FIPS 180-4, §5.1.1): `data ‖ 0x80 ‖ 0…0 ‖ bitlen` (64-bit
big-endian), a multiple of 64 bytes long. -/
def pad (data : ByteArray) : ByteArray :=
  let zeros := (119 - data.size % 64) % 64
  data ++ ⟨#[0x80]⟩ ++ Bytes.zeros zeros ++ Bytes.ofNatBE 8 (8 * data.size)

/-- SHA-256 digest (32 bytes). -/
def hash (data : ByteArray) : ByteArray :=
  let m := pad data
  let h := compressBlocks m (m.size / 64) 0 iv
  ⟨Array.ofFn (n := 32) fun i =>
    let word := if hi : i.val / 4 < 8 then h[i.val / 4] else 0
    (word >>> (8 * (3 - i.val % 4)).toUInt32).toUInt8⟩

end EvmLean.Sha256
