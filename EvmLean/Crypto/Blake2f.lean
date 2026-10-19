import EvmLean.Prelude.Bytes

/-!
# BLAKE2b compression function `F` (EIP-152), for precompile `0x09`

Source: RFC 7693 (*The BLAKE2 Cryptographic Hash and Message Authentication Code*),
§3.1 (mixing function `G`) and §3.2 (compression function `F`), with EIP-152's
generalisation to a caller-chosen number of rounds. Mirrors `Blake2.compress` in the
execution specs (`src/ethereum/crypto/blake2.py`).

## Algorithm

* Initialise the 16-word work vector `v` with the state `h` and the BLAKE2b IV, XOR the
  offset counters `t₀ t₁` into `v₁₂ v₁₃`, and invert `v₁₄` for the final block.
* Each round applies `G` to the four columns and then the four diagonals of `v` (viewed
  as a 4×4 matrix), feeding message words in the order given by the permutation
  `σ[r mod 10]`. BLAKE2b proper uses 12 rounds; EIP-152 lets the caller pick any number
  (including 0), the schedule wrapping around every 10 rounds.
* The new state is `h[i] ⊕ v[i] ⊕ v[i+8]`.

`G`'s rotation constants for BLAKE2b are `(32, 24, 16, 63)`. All indices are `Fin 16` /
`Fin 8` literals or `σ` entries typed `Fin 16`, so there are no bounds checks.
-/

namespace EvmLean.Blake2

/-- The BLAKE2b initialisation vector (RFC 7693, §2.6): the SHA-512 IV. -/
def iv : Vector UInt64 8 :=
  #v[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- The message schedule `σ` (RFC 7693, §2.7): round `r` uses `sigma[r mod 10]`. -/
def sigma : Vector (Vector (Fin 16) 16) 10 :=
  #v[#v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    #v[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    #v[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    #v[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    #v[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    #v[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    #v[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    #v[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    #v[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    #v[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- Rotate right by `n` bits, `0 < n < 64`. -/
@[inline] def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- The mixing function `G` (RFC 7693, §3.1) on words `a b c d` of `v`, with message
words `x y`. -/
@[inline] def g (v : Vector UInt64 16) (a b c d : Fin 16) (x y : UInt64) :
    Vector UInt64 16 :=
  let va := v[a] + v[b] + x
  let vd := rotr (v[d] ^^^ va) 32
  let vc := v[c] + vd
  let vb := rotr (v[b] ^^^ vc) 24
  let va := va + vb + y
  let vd := rotr (vd ^^^ va) 16
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 63
  (((v.set a va).set b vb).set c vc).set d vd

/-- One round: `G` on the four columns, then on the four diagonals, with the message
words permuted by `s = σ[r mod 10]`. -/
def round (m : Vector UInt64 16) (s : Vector (Fin 16) 16) (v : Vector UInt64 16) :
    Vector UInt64 16 :=
  let v := g v 0 4 8 12 m[s[0]] m[s[1]]
  let v := g v 1 5 9 13 m[s[2]] m[s[3]]
  let v := g v 2 6 10 14 m[s[4]] m[s[5]]
  let v := g v 3 7 11 15 m[s[6]] m[s[7]]
  let v := g v 0 5 10 15 m[s[8]] m[s[9]]
  let v := g v 1 6 11 12 m[s[10]] m[s[11]]
  let v := g v 2 7 8 13 m[s[12]] m[s[13]]
  g v 3 4 9 14 m[s[14]] m[s[15]]

/-- Run `n` rounds starting at round index `r` (the schedule index is `r mod 10`). -/
def rounds (m : Vector UInt64 16) : (n : Nat) → (r : Nat) → Vector UInt64 16 →
    Vector UInt64 16
  | 0, _, v => v
  | n + 1, r, v =>
    rounds m n (r + 1) (round m (sigma[r % 10]'(Nat.mod_lt _ (by decide))) v)

/-- BLAKE2b `F` with a caller-chosen number of rounds: state `h`, message block `m`,
offset counters `t₀ t₁`, final-block flag. -/
def compress (rounds : Nat) (h : Vector UInt64 8) (m : Vector UInt64 16)
    (t₀ t₁ : UInt64) (final : Bool) : Vector UInt64 8 :=
  let v : Vector UInt64 16 :=
    #v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7],
      iv[0], iv[1], iv[2], iv[3], iv[4] ^^^ t₀, iv[5] ^^^ t₁,
      if final then ~~~iv[6] else iv[6], iv[7]]
  let v := Blake2.rounds m rounds 0 v
  Vector.ofFn fun i => h[i] ^^^ v[i.castAdd 8] ^^^ v[i.natAdd 8]

end EvmLean.Blake2
