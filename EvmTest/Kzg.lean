import EvmLean.Crypto.Kzg

/-!
# Tests for `EvmLean.Crypto.Kzg` and the BLS12-381 code under `EvmLean/Crypto/Bls12381/`

* Curve constants: generators and `[τ]G2` are on their curves and in the order-`r` subgroups,
  and `[τ]G2` compresses to the ceremony's `KZG_SETUP_G2_MONOMIAL_1` bytes.
* Frobenius maps and the optimized final exponentiation against plain exponentiation.
* Pairing: non-degenerate, of order `r`, bilinear on small multiples.
* `G1` decoding edge cases (flags, `x ≥ p`, off-subgroup points).
* `verifyProof`: vectors from c-kzg-4844 `tests/verify_kzg_proof/kzg-mainnet`
  (the consensus-spec-tests `verify_kzg_proof` suite), covering valid-true, valid-false and
  invalid-input cases.
-/

open EvmLean EvmLean.Bls12381

namespace EvmTest.Kzg

/-- `n` as `len` big-endian bytes; test vectors are written as hex `Nat` literals. -/
def hex (len n : Nat) : ByteArray := Bytes.ofNatBE len n

/-- The point at infinity, compressed. -/
def inf48 : ByteArray := hex 48 (0xc0 <<< 376)

/-! ## Constants -/

#guard g1Gen.isOnCurve b1
#guard g2Gen.isOnCurve b2
#guard tauG2.isOnCurve b2
#guard g1Gen.inSubgroup
#guard g2Gen.inSubgroup
#guard tauG2.inSubgroup
#guard (P * P * P * P - P * P + 1) % R = 0

/-- ZCash compression of a `G2` point (py_ecc `compress_G2`): `(x.c1 | flags, x.c0)` as two
48-byte big-endian halves. Used only to tie `tauG2` to the published bytes. -/
def compressG2 : Affine Fp2 → ByteArray
  | .infinity => hex 96 (0xc0 <<< 760)
  | .point x y =>
    let flags := (1 <<< 383) + (if y.isLargest then 1 <<< 381 else 0)
    hex 48 (flags + x.c1.val) ++ hex 48 x.c0.val

-- `KZG_SETUP_G2_MONOMIAL_1` of execution-specs `crypto/kzg.py`.
#guard compressG2 tauG2 = hex 96
  0xb5bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2
-- `KZG_SETUP_G2_MONOMIAL[0]` is the generator.
#guard compressG2 g2Gen = hex 96
  0x93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8

/-! ## Field and group sanity -/

#guard Fp2.mul (Fp2.inv ⟨⟨5⟩, ⟨7⟩⟩) ⟨⟨5⟩, ⟨7⟩⟩ = Fp2.one
#guard Affine.add g1Gen (Affine.neg g1Gen) = .infinity
#guard Affine.add g1Gen g1Gen = Affine.mul g1Gen 2
#guard Affine.add (Affine.mul g2Gen 3) (Affine.mul g2Gen 4) = Affine.mul g2Gen 7
#guard Affine.mul g1Gen (R - 1) = Affine.neg g1Gen

/-! ## Frobenius and final exponentiation -/

/-- A generic-looking `𝔽ₚ¹²` element: a Miller-loop value (before final exponentiation). -/
def mGen : Fp12 := millerLoop g2Gen g1Gen

#guard Fp12.frobGamma2.c1 = Fp.zero
#guard Fp12.frobenius mGen = Fp12.pow mGen P
#guard Fp12.frobenius2 mGen = Fp12.pow mGen (P * P)
#guard Fp12.mul (Fp12.inv mGen) mGen = Fp12.one
#guard (xAbs + 1) * (xAbs + 1) % 3 = 0
-- The hard-part decomposition, and `finalExp` against plain square-and-multiply.
#guard hardExp0 * (P - xAbs) * (xAbs * xAbs + P * P - 1) + 1 = hardExp
#guard finalExp mGen = Fp12.pow (Fp12.conj mGen * Fp12.inv mGen) ((P * P + 1) * hardExp)

/-! ## Pairing -/

/-- `e(G1, G2)`, a generator of `GT`. -/
def eGen : Fp12 := pairing g1Gen g2Gen

#guard eGen ≠ Fp12.one
#guard Fp12.pow eGen R = Fp12.one
#guard pairing (Affine.mul g1Gen 6) g2Gen = pairing g1Gen (Affine.mul g2Gen 6)
#guard pairingCheck [(Affine.mul g1Gen 2, Affine.mul g2Gen 3), (Affine.neg (Affine.mul g1Gen 6), g2Gen)]
#guard !pairingCheck [(Affine.mul g1Gen 2, Affine.mul g2Gen 3), (Affine.neg (Affine.mul g1Gen 5), g2Gen)]

/-! ## `G1` decoding -/

#guard decompressG1 inf48 = some .infinity
#guard decompressG1 (hex 48
  0x97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
  = some g1Gen
#guard decompressG1 (hex 48
  0xb7f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
  = some (Affine.neg g1Gen)
-- Compression flag clear.
#guard decompressG1 (hex 48
  0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
  = none
-- Infinity with the sign flag, or with non-zero low bits.
#guard decompressG1 (hex 48 (0xe0 <<< 376)) = none
#guard decompressG1 (hex 48 ((0xc0 <<< 376) + 1)) = none
-- Zero low bits without the infinity flag.
#guard decompressG1 (hex 48 (0x80 <<< 376)) = none
-- `x = p` (not canonical).
#guard decompressG1 (hex 48 ((1 <<< 383) + P)) = none
-- `x = 4`: on the curve, but not in the order-`r` subgroup.
#guard (Affine.point (⟨4⟩ : Fp) (Fp.sqrtCandidate ⟨68⟩)).isOnCurve b1
#guard decompressG1 (hex 48 ((1 <<< 383) + 4)) = none
-- Wrong lengths.
#guard decompressG1 (hex 47 0) = none
#guard decompressG1 (inf48 ++ hex 1 0) = none

/-! ## `verify_kzg_proof` vectors (c-kzg-4844, kzg-mainnet) -/

-- correct_proof_0_0: zero polynomial, all infinity.
#guard Kzg.verifyProof inf48 (hex 32 0) (hex 32 0) inf48 = some true

-- correct_proof_2_1
#guard Kzg.verifyProof
  (hex 48 0xa421e229565952cfff4ef3517100a97da1d4fe57956fa50a442f92af03b1bf37adacc8ad4ed209b31287ea5bb94d9d06)
  (hex 32 0x0000000000000000000000000000000000000000000000000000000000000001)
  (hex 32 0x1824b159acc5056f998c4fefecbc4ff55884b7fa0003480200000001fffffffe)
  (hex 48 0xb0c829a8d2d3405304fecbea193e6c67f7c3912a6adc7c3737ad3f8a3b750425c1531a7426f03033a3994bc82a10609f)
  = some true

-- correct_proof_3_2
#guard Kzg.verifyProof
  (hex 48 0xb49d88afcd7f6c61a8ea69eff5f609d2432b47e7e4cd50b02cdddb4e0c1460517e8df02e4e64dc55e3d8ca192d57193a)
  (hex 32 0x0000000000000000000000000000000000000000000000000000000000000002)
  (hex 32 0x6a75e4fe63e5e148c853462a680c3e3ccedea34719d28f19bf1b35ae4eea37d6)
  (hex 48 0xa38758fca85407078c0a7e5fd6d38b34340c809baa0e1fed9deaabb11aa503062acbbe23fcbe620a21b40a83bfa71b89)
  = some true

-- correct_proof_4_3
#guard Kzg.verifyProof
  (hex 48 0x8f59a8d2a1a625a17f3fea0fe5eb8c896db3764f3185481bc22f91b4aaffcca25f26936857bc3a7c2539ea8ec3a952b7)
  (hex 32 0x5eb7004fe57383e6c88b99d839937fddf3f99279353aaf8d5c9a75f91ce33c62)
  (hex 32 0x4882cf0609af8c7cd4c256e63a35838c95a9ebbf6122540ab344b42fd66d32e1)
  (hex 48 0x987ea6df69bbe97c23e0dd948cf2d4490824ba7fea5af812721b2393354b0810a9dba2c231ea7ae30f26c412c7ea6e3a)
  = some true

-- correct_proof_6_5
#guard Kzg.verifyProof
  (hex 48 0x93efc82d2017e9c57834a1246463e64774e56183bb247c8fc9dd98c56817e878d97b05f5c8d900acf1fbbbca6f146556)
  (hex 32 0x564c0a11a0f704f4fc3e8acfe0f8245f0ad1347b378fbf96e206da11a5d36306)
  (hex 32 0x0000000000000000000000000000000000000000000000000000000000000000)
  (hex 48 0xa256a681861974cdf6b116467044aa75c85b01076423a92c3335b93d10bf2fcb99b943a53adc1ab8feb6b475c4688948)
  = some true

-- correct_proof_point_at_infinity_for_twos_poly_0
#guard Kzg.verifyProof
  (hex 48 0xa572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e)
  (hex 32 0x0000000000000000000000000000000000000000000000000000000000000000)
  (hex 32 0x0000000000000000000000000000000000000000000000000000000000000002)
  inf48
  = some true

-- incorrect_proof_0_0
#guard Kzg.verifyProof inf48 (hex 32 0) (hex 32 0)
  (hex 48 0x97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
  = some false

-- incorrect_proof_1_1
#guard Kzg.verifyProof
  (hex 48 0xa572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e)
  (hex 32 0x0000000000000000000000000000000000000000000000000000000000000001)
  (hex 32 0x0000000000000000000000000000000000000000000000000000000000000002)
  (hex 48 0x97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
  = some false

-- incorrect_proof_5_4
#guard Kzg.verifyProof
  (hex 48 0xb7f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
  (hex 32 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000)
  (hex 32 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000)
  (hex 48 0x97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
  = some false

-- incorrect_proof_point_at_infinity_0
#guard Kzg.verifyProof
  (hex 48 0xa421e229565952cfff4ef3517100a97da1d4fe57956fa50a442f92af03b1bf37adacc8ad4ed209b31287ea5bb94d9d06)
  (hex 32 0x0000000000000000000000000000000000000000000000000000000000000000)
  (hex 32 0x50625ad853cc21ba40594f79591e5d35c445ecf9453014da6524c0cf6367c359)
  inf48
  = some false

/-- `z`, `y` and `proof` of the `invalid_commitment_*` cases (from correct_proof_2_1). -/
def zOne : ByteArray := hex 32 1
/-- See `zOne`. -/
def y21 : ByteArray := hex 32 0x1824b159acc5056f998c4fefecbc4ff55884b7fa0003480200000001fffffffe
/-- See `zOne`. -/
def proof21 : ByteArray :=
  hex 48 0xb0c829a8d2d3405304fecbea193e6c67f7c3912a6adc7c3737ad3f8a3b750425c1531a7426f03033a3994bc82a10609f
/-- The commitment of correct_proof_2_1, used by the `invalid_proof_*` cases. -/
def commit21 : ByteArray :=
  hex 48 0xa421e229565952cfff4ef3517100a97da1d4fe57956fa50a442f92af03b1bf37adacc8ad4ed209b31287ea5bb94d9d06

-- invalid_commitment_0: 47 bytes.
#guard Kzg.verifyProof (hex 47
  0x97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6)
  zOne y21 proof21 = none
-- invalid_commitment_1: 49 bytes.
#guard Kzg.verifyProof (hex 49
  0x97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb00)
  zOne y21 proof21 = none
-- invalid_commitment_2: not on the curve.
#guard Kzg.verifyProof (hex 48
  0x8123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef)
  zOne y21 proof21 = none
-- invalid_commitment_3
#guard Kzg.verifyProof (hex 48
  0x8123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcde0)
  zOne y21 proof21 = none
-- invalid_proof_0..3
#guard Kzg.verifyProof commit21 zOne y21 (hex 47
  0x97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6) = none
#guard Kzg.verifyProof commit21 zOne y21 (hex 49
  0x97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb00) = none
#guard Kzg.verifyProof commit21 zOne y21 (hex 48
  0x8123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef) = none
#guard Kzg.verifyProof commit21 zOne y21 (hex 48
  0x8123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcde0) = none

/-- The commitment of the `invalid_z_*` / `invalid_y_*` cases. -/
def commit43 : ByteArray :=
  hex 48 0x8f59a8d2a1a625a17f3fea0fe5eb8c896db3764f3185481bc22f91b4aaffcca25f26936857bc3a7c2539ea8ec3a952b7
/-- The proof of the `invalid_z_*` / `invalid_y_*` cases. -/
def proof43 : ByteArray :=
  hex 48 0xb30b3d1e4faccc380557792c9a0374d58fa286f5f75fea48870585393f890909cd3c53cfe4897e799fb211b4be531e43
/-- The valid `y` of the `invalid_z_*` cases. -/
def y43 : ByteArray := hex 32 0x60f840641ec0d0c0d2b77b2d5a393b329442721fad05ab78c7b98f2aa3c20ec9

-- invalid_z_0..5: z = r, r + 1, 2²⁵⁶ − 1, a large value, 33 bytes, 31 bytes.
#guard Kzg.verifyProof commit43 (hex 32 R) y43 proof43 = none
#guard Kzg.verifyProof commit43 (hex 32 (R + 1)) y43 proof43 = none
#guard Kzg.verifyProof commit43 (hex 32 (2 ^ 256 - 1)) y43 proof43 = none
#guard Kzg.verifyProof commit43
  (hex 32 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) y43 proof43 = none
#guard Kzg.verifyProof commit43 (hex 33 0) y43 proof43 = none
#guard Kzg.verifyProof commit43 (hex 31 0) y43 proof43 = none
-- invalid_y_0..5
#guard Kzg.verifyProof commit43 zOne (hex 32 R) proof43 = none
#guard Kzg.verifyProof commit43 zOne (hex 32 (R + 1)) proof43 = none
#guard Kzg.verifyProof commit43 zOne (hex 32 (2 ^ 256 - 1)) proof43 = none
#guard Kzg.verifyProof commit43 zOne
  (hex 32 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) proof43 = none
#guard Kzg.verifyProof commit43 zOne (hex 33 0) proof43 = none
#guard Kzg.verifyProof commit43 zOne (hex 31 0) proof43 = none
-- An off-subgroup commitment (`x = 4`, see above).
#guard Kzg.verifyProof (hex 48 ((1 <<< 383) + 4)) zOne y43 proof43 = none

-- correct_proof_4_1 (the base case of `invalid_z_*` / `invalid_y_*`).
#guard Kzg.verifyProof commit43 zOne y43 proof43 = some true
-- The same with `y + 1`: a well-formed but wrong claim.
#guard Kzg.verifyProof commit43 zOne
  (hex 32 0x60f840641ec0d0c0d2b77b2d5a393b329442721fad05ab78c7b98f2aa3c20eca) proof43 = some false

end EvmTest.Kzg
