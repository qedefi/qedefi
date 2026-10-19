import EvmLean.Prelude.Bytes

/-!
# Keccak-256

The pre-standard Keccak-256 used by Ethereum (domain padding byte `0x01`, not FIPS 202
SHA3's `0x06`), implemented in plain Lean.

Source: the Keccak team's reference specification ("The Keccak reference", version 3.0,
Bertoni, Daemen, Peeters, Van Assche), with the permutation Keccak-f[1600] as specified
in FIPS 202 §3.

## Algorithm

* The state is 25 little-endian 64-bit lanes, lane `(x, y)` at index `x + 5 * y`.
* The sponge has rate `r = 136` bytes (17 lanes) and capacity 512 bits.
* Absorbing XORs each 136-byte block into the first 17 lanes and applies Keccak-f[1600]
  (24 rounds of θ, ρ, π, χ, ι).
* Padding is `pad10*1` with the Keccak domain bits: after the message, the byte `0x01` is
  XORed in, and `0x80` into the last byte of the block (both land in the same byte, `0x81`,
  when the remainder is 135 bytes).
* The digest is the first 32 bytes of the state (lanes 0–3, little-endian), which
  `hash256` reads as a big-endian 256-bit word, the EVM's convention for `KECCAK256`.

## Implementation notes

The round function is fully unrolled over `Vector UInt64 25` with literal indices, so it
needs no bounds checks or runtime proofs. Message bytes are read straight from the input
(`byteAt` reads zero past the end), so the final, padded block is never materialised: its
padding bits are XORed directly into the state. Every recursion is structural, so the
kernel can evaluate the hash (see `EvmLeanTest/Keccak.lean`).
-/

namespace EvmLean.Keccak

/-- The Keccak-f[1600] state: 25 lanes, lane `(x, y)` at index `x + 5 * y`. -/
abbrev State := Vector UInt64 25

/-- Rotate a lane left by `n` bits, `0 < n < 64`. -/
@[inline] def rotl (x : UInt64) (n : UInt64) : UInt64 := (x <<< n) ||| (x >>> (64 - n))

/-- The 24 round constants of the ι step (Keccak reference, §1.2). -/
def roundConstants : List UInt64 :=
  [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
   0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
   0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
   0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
   0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
   0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- One round of Keccak-f[1600] with round constant `rc`: θ (column parities `c`, mixing
terms `d`), then ρ and π combined (`b[y, 2x+3y] = rotl (a[x, y] ^ d[x]) r[x, y]`), then
χ and ι. Unrolled; the rotation offsets are those of the Keccak reference, §1.2. -/
def round (rc : UInt64) (a : State) : State :=
  let c0 := a[0] ^^^ a[5] ^^^ a[10] ^^^ a[15] ^^^ a[20]
  let c1 := a[1] ^^^ a[6] ^^^ a[11] ^^^ a[16] ^^^ a[21]
  let c2 := a[2] ^^^ a[7] ^^^ a[12] ^^^ a[17] ^^^ a[22]
  let c3 := a[3] ^^^ a[8] ^^^ a[13] ^^^ a[18] ^^^ a[23]
  let c4 := a[4] ^^^ a[9] ^^^ a[14] ^^^ a[19] ^^^ a[24]
  let d0 := c4 ^^^ rotl c1 1
  let d1 := c0 ^^^ rotl c2 1
  let d2 := c1 ^^^ rotl c3 1
  let d3 := c2 ^^^ rotl c4 1
  let d4 := c3 ^^^ rotl c0 1
  let b0 := (a[0] ^^^ d0)
  let b1 := rotl (a[6] ^^^ d1) 44
  let b2 := rotl (a[12] ^^^ d2) 43
  let b3 := rotl (a[18] ^^^ d3) 21
  let b4 := rotl (a[24] ^^^ d4) 14
  let b5 := rotl (a[3] ^^^ d3) 28
  let b6 := rotl (a[9] ^^^ d4) 20
  let b7 := rotl (a[10] ^^^ d0) 3
  let b8 := rotl (a[16] ^^^ d1) 45
  let b9 := rotl (a[22] ^^^ d2) 61
  let b10 := rotl (a[1] ^^^ d1) 1
  let b11 := rotl (a[7] ^^^ d2) 6
  let b12 := rotl (a[13] ^^^ d3) 25
  let b13 := rotl (a[19] ^^^ d4) 8
  let b14 := rotl (a[20] ^^^ d0) 18
  let b15 := rotl (a[4] ^^^ d4) 27
  let b16 := rotl (a[5] ^^^ d0) 36
  let b17 := rotl (a[11] ^^^ d1) 10
  let b18 := rotl (a[17] ^^^ d2) 15
  let b19 := rotl (a[23] ^^^ d3) 56
  let b20 := rotl (a[2] ^^^ d2) 62
  let b21 := rotl (a[8] ^^^ d3) 55
  let b22 := rotl (a[14] ^^^ d4) 39
  let b23 := rotl (a[15] ^^^ d0) 41
  let b24 := rotl (a[21] ^^^ d1) 2
  #v[b0 ^^^ (~~~b1 &&& b2) ^^^ rc,
    b1 ^^^ (~~~b2 &&& b3),
    b2 ^^^ (~~~b3 &&& b4),
    b3 ^^^ (~~~b4 &&& b0),
    b4 ^^^ (~~~b0 &&& b1),
    b5 ^^^ (~~~b6 &&& b7),
    b6 ^^^ (~~~b7 &&& b8),
    b7 ^^^ (~~~b8 &&& b9),
    b8 ^^^ (~~~b9 &&& b5),
    b9 ^^^ (~~~b5 &&& b6),
    b10 ^^^ (~~~b11 &&& b12),
    b11 ^^^ (~~~b12 &&& b13),
    b12 ^^^ (~~~b13 &&& b14),
    b13 ^^^ (~~~b14 &&& b10),
    b14 ^^^ (~~~b10 &&& b11),
    b15 ^^^ (~~~b16 &&& b17),
    b16 ^^^ (~~~b17 &&& b18),
    b17 ^^^ (~~~b18 &&& b19),
    b18 ^^^ (~~~b19 &&& b15),
    b19 ^^^ (~~~b15 &&& b16),
    b20 ^^^ (~~~b21 &&& b22),
    b21 ^^^ (~~~b22 &&& b23),
    b22 ^^^ (~~~b23 &&& b24),
    b23 ^^^ (~~~b24 &&& b20),
    b24 ^^^ (~~~b20 &&& b21)]


/-- Keccak-f[1600]: the 24 rounds. -/
def permute (s : State) : State :=
  roundConstants.foldl (fun s rc => round rc s) s

/-- Byte `i` of `b` as a lane fragment, zero past the end of `b`. -/
@[inline] def byteAt (b : ByteArray) (i : Nat) : UInt64 :=
  if h : i < b.size then b[i].toUInt64 else 0

/-- The little-endian 64-bit lane at byte offset `o` of `b` (zero-padded past the end). -/
@[inline] def laneAt (b : ByteArray) (o : Nat) : UInt64 :=
  byteAt b o ||| (byteAt b (o + 1) <<< 8) ||| (byteAt b (o + 2) <<< 16) |||
  (byteAt b (o + 3) <<< 24) ||| (byteAt b (o + 4) <<< 32) ||| (byteAt b (o + 5) <<< 40) |||
  (byteAt b (o + 6) <<< 48) ||| (byteAt b (o + 7) <<< 56)

/-- The sponge rate of Keccak-256, in bytes. -/
def rate : Nat := 136

/-- XOR the 136-byte block of `b` at offset `o` (zero-padded past the end of `b`) into
the 17 rate lanes of `s`. -/
def xorBlock (s : State) (b : ByteArray) (o : Nat) : State :=
  #v[s[0] ^^^ laneAt b o, s[1] ^^^ laneAt b (o + 8), s[2] ^^^ laneAt b (o + 16),
    s[3] ^^^ laneAt b (o + 24), s[4] ^^^ laneAt b (o + 32), s[5] ^^^ laneAt b (o + 40),
    s[6] ^^^ laneAt b (o + 48), s[7] ^^^ laneAt b (o + 56), s[8] ^^^ laneAt b (o + 64),
    s[9] ^^^ laneAt b (o + 72), s[10] ^^^ laneAt b (o + 80), s[11] ^^^ laneAt b (o + 88),
    s[12] ^^^ laneAt b (o + 96), s[13] ^^^ laneAt b (o + 104),
    s[14] ^^^ laneAt b (o + 112), s[15] ^^^ laneAt b (o + 120),
    s[16] ^^^ laneAt b (o + 128),
    s[17], s[18], s[19], s[20], s[21], s[22], s[23], s[24]]

/-- XOR `v` into lane `i` of `s` (no-op if `i ≥ 25`, which the callers never pass). -/
@[inline] def xorLane (s : State) (i : Nat) (v : UInt64) : State :=
  if h : i < 25 then s.set i (s[i] ^^^ v) else s

/-- Absorb `n` full blocks of `b`, starting at byte offset `o`. -/
def absorb (b : ByteArray) : (n : Nat) → (o : Nat) → State → State
  | 0, _, s => s
  | n + 1, o, s => absorb b n (o + rate) (permute (xorBlock s b o))

/-- The Keccak sponge with rate 136 bytes and domain-padding byte `delim` (`0x01` for
Keccak, `0x06` for FIPS 202 SHA3-256), returning the full state after absorbing; the
digest is its first 32 bytes. -/
def sponge (delim : UInt64) (b : ByteArray) : State :=
  let full := b.size / rate
  let s := absorb b full 0 (Vector.replicate 25 0)
  let o := full * rate
  let rem := b.size - o
  -- The final block holds the `rem < 136` remaining bytes, then the padding.
  let s := xorBlock s b o
  let s := xorLane s (rem / 8) (delim <<< (8 * (rem % 8)).toUInt64)
  let s := xorLane s 16 0x8000000000000000
  permute s

/-- The first 32 bytes of the state (lanes 0–3, little-endian), i.e. the digest. -/
def digestBytes (s : State) : ByteArray :=
  ⟨Array.ofFn (n := 32) fun i =>
    let lane := if h : i.val / 8 < 25 then s[i.val / 8] else 0
    (lane >>> (8 * (i.val % 8)).toUInt64).toUInt8⟩

/-- Keccak-256 of `data`, as a big-endian word. -/
def hash256 (data : ByteArray) : Word := Bytes.toWord (digestBytes (sponge 0x01 data))

end EvmLean.Keccak
