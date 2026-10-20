import EvmLean.Prelude.Bytes

/-!
# BLAKE2b compression function `F` (EIP-152), for precompile `0x09`

RFC 7693 §3.2 with EIP-152's caller-chosen round count (any number, including 0; the
schedule `σ` wraps every 10 rounds). Mirrors `Blake2.compress` in `ethereum/crypto/blake2.py`.
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

/-- Run `n` rounds from round `r`; `G` is unrolled and `v` lives in arguments (stays unboxed). -/
def rounds (m : Vector UInt64 16) (n r : Nat)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) : Vector UInt64 16 :=
  match n with
  | 0 => #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
  | n + 1 =>
    let s := sigma[r % 10]'(Nat.mod_lt _ (by decide))
    -- G(0, 4, 8, 12)
    let v0_1 := v0 + v4 + (m.get (s.get 0))
    let v12_1 := rotr (v12 ^^^ v0_1) 32
    let v8_1 := v8 + v12_1
    let v4_1 := rotr (v4 ^^^ v8_1) 24
    let v0_2 := v0_1 + v4_1 + (m.get (s.get 1))
    let v12_2 := rotr (v12_1 ^^^ v0_2) 16
    let v8_2 := v8_1 + v12_2
    let v4_2 := rotr (v4_1 ^^^ v8_2) 63
    -- G(1, 5, 9, 13)
    let v1_1 := v1 + v5 + (m.get (s.get 2))
    let v13_1 := rotr (v13 ^^^ v1_1) 32
    let v9_1 := v9 + v13_1
    let v5_1 := rotr (v5 ^^^ v9_1) 24
    let v1_2 := v1_1 + v5_1 + (m.get (s.get 3))
    let v13_2 := rotr (v13_1 ^^^ v1_2) 16
    let v9_2 := v9_1 + v13_2
    let v5_2 := rotr (v5_1 ^^^ v9_2) 63
    -- G(2, 6, 10, 14)
    let v2_1 := v2 + v6 + (m.get (s.get 4))
    let v14_1 := rotr (v14 ^^^ v2_1) 32
    let v10_1 := v10 + v14_1
    let v6_1 := rotr (v6 ^^^ v10_1) 24
    let v2_2 := v2_1 + v6_1 + (m.get (s.get 5))
    let v14_2 := rotr (v14_1 ^^^ v2_2) 16
    let v10_2 := v10_1 + v14_2
    let v6_2 := rotr (v6_1 ^^^ v10_2) 63
    -- G(3, 7, 11, 15)
    let v3_1 := v3 + v7 + (m.get (s.get 6))
    let v15_1 := rotr (v15 ^^^ v3_1) 32
    let v11_1 := v11 + v15_1
    let v7_1 := rotr (v7 ^^^ v11_1) 24
    let v3_2 := v3_1 + v7_1 + (m.get (s.get 7))
    let v15_2 := rotr (v15_1 ^^^ v3_2) 16
    let v11_2 := v11_1 + v15_2
    let v7_2 := rotr (v7_1 ^^^ v11_2) 63
    -- G(0, 5, 10, 15)
    let v0_3 := v0_2 + v5_2 + (m.get (s.get 8))
    let v15_3 := rotr (v15_2 ^^^ v0_3) 32
    let v10_3 := v10_2 + v15_3
    let v5_3 := rotr (v5_2 ^^^ v10_3) 24
    let v0_4 := v0_3 + v5_3 + (m.get (s.get 9))
    let v15_4 := rotr (v15_3 ^^^ v0_4) 16
    let v10_4 := v10_3 + v15_4
    let v5_4 := rotr (v5_3 ^^^ v10_4) 63
    -- G(1, 6, 11, 12)
    let v1_3 := v1_2 + v6_2 + (m.get (s.get 10))
    let v12_3 := rotr (v12_2 ^^^ v1_3) 32
    let v11_3 := v11_2 + v12_3
    let v6_3 := rotr (v6_2 ^^^ v11_3) 24
    let v1_4 := v1_3 + v6_3 + (m.get (s.get 11))
    let v12_4 := rotr (v12_3 ^^^ v1_4) 16
    let v11_4 := v11_3 + v12_4
    let v6_4 := rotr (v6_3 ^^^ v11_4) 63
    -- G(2, 7, 8, 13)
    let v2_3 := v2_2 + v7_2 + (m.get (s.get 12))
    let v13_3 := rotr (v13_2 ^^^ v2_3) 32
    let v8_3 := v8_2 + v13_3
    let v7_3 := rotr (v7_2 ^^^ v8_3) 24
    let v2_4 := v2_3 + v7_3 + (m.get (s.get 13))
    let v13_4 := rotr (v13_3 ^^^ v2_4) 16
    let v8_4 := v8_3 + v13_4
    let v7_4 := rotr (v7_3 ^^^ v8_4) 63
    -- G(3, 4, 9, 14)
    let v3_3 := v3_2 + v4_2 + (m.get (s.get 14))
    let v14_3 := rotr (v14_2 ^^^ v3_3) 32
    let v9_3 := v9_2 + v14_3
    let v4_3 := rotr (v4_2 ^^^ v9_3) 24
    let v3_4 := v3_3 + v4_3 + (m.get (s.get 15))
    let v14_4 := rotr (v14_3 ^^^ v3_4) 16
    let v9_4 := v9_3 + v14_4
    let v4_4 := rotr (v4_3 ^^^ v9_4) 63
    rounds m n (r + 1) v0_4 v1_4 v2_4 v3_4 v4_4 v5_4
      v6_4 v7_4 v8_4 v9_4 v10_4 v11_4
      v12_4 v13_4 v14_4 v15_4


/-- BLAKE2b `F` with a caller-chosen number of rounds. -/
def compress (rounds : Nat) (h : Vector UInt64 8) (m : Vector UInt64 16)
    (t₀ t₁ : UInt64) (final : Bool) : Vector UInt64 8 :=
  let v := Blake2.rounds m rounds 0 h[0] h[1] h[2] h[3] h[4] h[5] h[6] h[7]
    iv[0] iv[1] iv[2] iv[3] (iv[4] ^^^ t₀) (iv[5] ^^^ t₁)
    (if final then ~~~iv[6] else iv[6]) iv[7]
  Vector.ofFn fun i => h[i] ^^^ v[i.castAdd 8] ^^^ v[i.natAdd 8]

end EvmLean.Blake2
