import EvmLean.Crypto.Bls12381.Curve

/-!
# BLS12-381 map-to-curve (RFC 9380) for EIP-2537

The EIP-2537 precompiles `MAP_FP_TO_G1` (`0x10`) and `MAP_FP2_TO_G2` (`0x11`) compute
`clear_cofactor(map_to_curve(u))` from RFC 9380 (the `BLS12381G1_XMD:SHA-256_SSWU_RO_` and
`BLS12381G2_XMD:SHA-256_SSWU_RO_` suites), without the hash-to-field step. execution-specs
calls py_ecc's `map_to_curve_G1/G2` and `clear_cofactor_G1/G2`
(`py_ecc/bls/hash_to_curve.py`, `py_ecc/optimized_bls12_381/optimized_swu.py`); this file
mirrors them step by step, and all constants are copied from py_ecc's
`optimized_bls12_381/constants.py`:

1. **Simplified SWU** onto an isogenous curve `E' : y² = x³ + A'x + B'` (11-isogenous to `E`
   for `G1`, 3-isogenous to the twist for `G2`), as in Wahby–Boneh (ePrint 2019/403, §4):
   `x₁ = B'(Z²u⁴ + Zu² + 1) / (−A'(Z²u⁴ + Zu²))` (or `B'/(ZA')` when the denominator
   vanishes); if `g(x₁)` is not a square, `x₂ = Zu²·x₁` is used instead. The sign of `y` is
   fixed by `sgn0(y) = sgn0(u)`.
2. **Isogeny map** `(x, y) ↦ (xNum(x)/xDen(x), y·yNum(x)/yDen(x))` back to `E` (resp. the
   twist). A vanishing denominator gives the point at infinity.
3. **Cofactor clearing** by scalar multiplication with `h_eff` (py_ecc
   `multiply_clear_cofactor_G1/G2`; it does not use the endomorphism shortcut).

py_ecc carries homogeneous projective coordinates through steps 1–2. Every point has a
unique affine form and the final result is normalized, so computing in affine coordinates
here (with one inversion per step) gives bit-identical outputs. Square roots follow py_ecc's
`sqrt_division_FQ` (exponent `(p − 3)/4`, since `p ≡ 3 mod 4`) and `sqrt_division_FQ2`
(exponent `(p² − 9)/16` and the four "positive" eighth roots of unity).
-/

namespace EvmLean.Bls12381

open FieldOps

/-! ## Signs and polynomial evaluation -/

/-- RFC 9380 `sgn0` on `𝔽ₚ`: the parity of the canonical residue (py_ecc `FQ.sgn0`). -/
def Fp.sgn0 (a : Fp) : Bool := a.val % 2 == 1

/-- RFC 9380 `sgn0` on `𝔽ₚ²`: the parity of `c0`, or of `c1` when `c0 = 0`
(py_ecc `FQ2.sgn0`). -/
def Fp2.sgn0 (a : Fp2) : Bool := a.c0.val % 2 == 1 || (a.c0.val == 0 && a.c1.val % 2 == 1)

/-- Evaluate the polynomial with coefficients `cs` (constant term first) at `x`, by Horner's
rule. -/
def polyEval {α : Type} [FieldOps α] (cs : List α) (x : α) : α :=
  cs.foldr (fun c acc => acc * x + c) zero

/-- Apply a rational isogeny map given by its four coefficient tables (constant terms first):
`(x, y) ↦ (xNum(x)/xDen(x), y·yNum(x)/yDen(x))`, with one inversion. A zero denominator gives
the point at infinity, as py_ecc's projective `iso_map_G1/G2` then produces `z = 0`. -/
def isoMap {α : Type} [FieldOps α] (xNum xDen yNum yDen : List α) (x y : α) : Affine α :=
  let xd := polyEval xDen x
  let yd := polyEval yDen x
  let d := xd * yd
  if isZero d then .infinity
  else
    let di := inv d
    .point (polyEval xNum x * yd * di) (y * polyEval yNum x * xd * di)

/-! ## `G1`: SSWU onto the 11-isogenous curve -/

/-- `Z = 11` for the `G1` SSWU map (py_ecc `ISO_11_Z`). -/
def isoZ1 : Fp := ⟨11⟩

/-- `A'` of the 11-isogenous curve `E₁'` (py_ecc `ISO_11_A`). -/
def isoA1 : Fp :=
  ⟨0x144698a3b8e9433d693a02c96d4982b0ea985383ee66a8d8e8981aefd881ac98936f8da0e0f97f5cf428082d584c1d⟩

/-- `B'` of the 11-isogenous curve `E₁'` (py_ecc `ISO_11_B`). -/
def isoB1 : Fp :=
  ⟨0x12e2908d11688030018b12e8753eee3b2016c1f0f24f4070a0b9c14fcef35ef55a23215a316ceaa5d1cc48e98e172be0⟩

/-- `√(−11³)` (py_ecc `SQRT_MINUS_11_CUBED`), which turns a square root of `−g(x₁)` into one
of `g(x₂) = Z³u⁶·g(x₁)`. -/
def sqrtMinus11Cubed : Fp :=
  ⟨0x3d689d1e0e762cef9f2bec6130316806b4c80eda6fc10ce77ae83eab1ea8b8b8a407c9c6db195e06f2dbeabc2baeff5⟩

/-- `h_eff` for `G1` (py_ecc `H_EFF_G1`, RFC 9380 §8.8.1): `1 − x` for the BLS parameter `x`. -/
def hEffG1 : Nat := 0xd201000000010001

/-- 11-isogeny `x` numerator coefficients, constant term first (py_ecc `ISO_11_X_NUMERATOR`). -/
def iso11XNum : List Fp :=
  [⟨0x11a05f2b1e833340b809101dd99815856b303e88a2d7005ff2627b56cdb4e2c85610c2d5f2e62d6eaeac1662734649b7⟩,
   ⟨0x17294ed3e943ab2f0588bab22147a81c7c17e75b2f6a8417f565e33c70d1e86b4838f2a6f318c356e834eef1b3cb83bb⟩,
   ⟨0xd54005db97678ec1d1048c5d10a9a1bce032473295983e56878e501ec68e25c958c3e3d2a09729fe0179f9dac9edcb0⟩,
   ⟨0x1778e7166fcc6db74e0609d307e55412d7f5e4656a8dbf25f1b33289f1b330835336e25ce3107193c5b388641d9b6861⟩,
   ⟨0xe99726a3199f4436642b4b3e4118e5499db995a1257fb3f086eeb65982fac18985a286f301e77c451154ce9ac8895d9⟩,
   ⟨0x1630c3250d7313ff01d1201bf7a74ab5db3cb17dd952799b9ed3ab9097e68f90a0870d2dcae73d19cd13c1c66f652983⟩,
   ⟨0xd6ed6553fe44d296a3726c38ae652bfb11586264f0f8ce19008e218f9c86b2a8da25128c1052ecaddd7f225a139ed84⟩,
   ⟨0x17b81e7701abdbe2e8743884d1117e53356de5ab275b4db1a682c62ef0f2753339b7c8f8c8f475af9ccb5618e3f0c88e⟩,
   ⟨0x80d3cf1f9a78fc47b90b33563be990dc43b756ce79f5574a2c596c928c5d1de4fa295f296b74e956d71986a8497e317⟩,
   ⟨0x169b1f8e1bcfa7c42e0c37515d138f22dd2ecb803a0c5c99676314baf4bb1b7fa3190b2edc0327797f241067be390c9e⟩,
   ⟨0x10321da079ce07e272d8ec09d2565b0dfa7dccdde6787f96d50af36003b14866f69b771f8c285decca67df3f1605fb7b⟩,
   ⟨0x6e08c248e260e70bd1e962381edee3d31d79d7e22c837bc23c0bf1bc24c6b68c24b1b80b64d391fa9c8ba2e8ba2d229⟩]

/-- 11-isogeny `x` denominator coefficients (py_ecc `ISO_11_X_DENOMINATOR`). -/
def iso11XDen : List Fp :=
  [⟨0x8ca8d548cff19ae18b2e62f4bd3fa6f01d5ef4ba35b48ba9c9588617fc8ac62b558d681be343df8993cf9fa40d21b1c⟩,
   ⟨0x12561a5deb559c4348b4711298e536367041e8ca0cf0800c0126c2588c48bf5713daa8846cb026e9e5c8276ec82b3bff⟩,
   ⟨0xb2962fe57a3225e8137e629bff2991f6f89416f5a718cd1fca64e00b11aceacd6a3d0967c94fedcfcc239ba5cb83e19⟩,
   ⟨0x3425581a58ae2fec83aafef7c40eb545b08243f16b1655154cca8abc28d6fd04976d5243eecf5c4130de8938dc62cd8⟩,
   ⟨0x13a8e162022914a80a6f1d5f43e7a07dffdfc759a12062bb8d6b44e833b306da9bd29ba81f35781d539d395b3532a21e⟩,
   ⟨0xe7355f8e4e667b955390f7f0506c6e9395735e9ce9cad4d0a43bcef24b8982f7400d24bc4228f11c02df9a29f6304a5⟩,
   ⟨0x772caacf16936190f3e0c63e0596721570f5799af53a1894e2e073062aede9cea73b3538f0de06cec2574496ee84a3a⟩,
   ⟨0x14a7ac2a9d64a8b230b3f5b074cf01996e7f63c21bca68a81996e1cdf9822c580fa5b9489d11e2d311f7d99bbdcc5a5e⟩,
   ⟨0xa10ecf6ada54f825e920b3dafc7a3cce07f8d1d7161366b74100da67f39883503826692abba43704776ec3a79a1d641⟩,
   ⟨0x95fc13ab9e92ad4476d6e3eb3a56680f682b4ee96f7d03776df533978f31c1593174e4b4b7865002d6384d168ecdd0a⟩,
   ⟨1⟩]

/-- 11-isogeny `y` numerator coefficients (py_ecc `ISO_11_Y_NUMERATOR`). -/
def iso11YNum : List Fp :=
  [⟨0x90d97c81ba24ee0259d1f094980dcfa11ad138e48a869522b52af6c956543d3cd0c7aee9b3ba3c2be9845719707bb33⟩,
   ⟨0x134996a104ee5811d51036d776fb46831223e96c254f383d0f906343eb67ad34d6c56711962fa8bfe097e75a2e41c696⟩,
   ⟨0xcc786baa966e66f4a384c86a3b49942552e2d658a31ce2c344be4b91400da7d26d521628b00523b8dfe240c72de1f6⟩,
   ⟨0x1f86376e8981c217898751ad8746757d42aa7b90eeb791c09e4a3ec03251cf9de405aba9ec61deca6355c77b0e5f4cb⟩,
   ⟨0x8cc03fdefe0ff135caf4fe2a21529c4195536fbe3ce50b879833fd221351adc2ee7f8dc099040a841b6daecf2e8fedb⟩,
   ⟨0x16603fca40634b6a2211e11db8f0a6a074a7d0d4afadb7bd76505c3d3ad5544e203f6326c95a807299b23ab13633a5f0⟩,
   ⟨0x4ab0b9bcfac1bbcb2c977d027796b3ce75bb8ca2be184cb5231413c4d634f3747a87ac2460f415ec961f8855fe9d6f2⟩,
   ⟨0x987c8d5333ab86fde9926bd2ca6c674170a05bfe3bdd81ffd038da6c26c842642f64550fedfe935a15e4ca31870fb29⟩,
   ⟨0x9fc4018bd96684be88c9e221e4da1bb8f3abd16679dc26c1e8b6e6a1f20cabe69d65201c78607a360370e577bdba587⟩,
   ⟨0xe1bba7a1186bdb5223abde7ada14a23c42a0ca7915af6fe06985e7ed1e4d43b9b3f7055dd4eba6f2bafaaebca731c30⟩,
   ⟨0x19713e47937cd1be0dfd0b8f1d43fb93cd2fcbcb6caf493fd1183e416389e61031bf3a5cce3fbafce813711ad011c132⟩,
   ⟨0x18b46a908f36f6deb918c143fed2edcc523559b8aaf0c2462e6bfe7f911f643249d9cdf41b44d606ce07c8a4d0074d8e⟩,
   ⟨0xb182cac101b9399d155096004f53f447aa7b12a3426b08ec02710e807b4633f06c851c1919211f20d4c04f00b971ef8⟩,
   ⟨0x245a394ad1eca9b72fc00ae7be315dc757b3b080d4c158013e6632d3c40659cc6cf90ad1c232a6442d9d3f5db980133⟩,
   ⟨0x5c129645e44cf1102a159f748c4a3fc5e673d81d7e86568d9ab0f5d396a7ce46ba1049b6579afb7866b1e715475224b⟩,
   ⟨0x15e6be4e990f03ce4ea50b3b42df2eb5cb181d8f84965a3957add4fa95af01b2b665027efec01c7704b456be69c8b604⟩]

/-- 11-isogeny `y` denominator coefficients (py_ecc `ISO_11_Y_DENOMINATOR`). -/
def iso11YDen : List Fp :=
  [⟨0x16112c4c3a9c98b252181140fad0eae9601a6de578980be6eec3232b5be72e7a07f3688ef60c206d01479253b03663c1⟩,
   ⟨0x1962d75c2381201e1a0cbd6c43c348b885c84ff731c4d59ca4a10356f453e01f78a4260763529e3532f6102c2e49a03d⟩,
   ⟨0x58df3306640da276faaae7d6e8eb15778c4855551ae7f310c35a5dd279cd2eca6757cd636f96f891e2538b53dbf67f2⟩,
   ⟨0x16b7d288798e5395f20d23bf89edb4d1d115c5dbddbcd30e123da489e726af41727364f2c28297ada8d26d98445f5416⟩,
   ⟨0xbe0e079545f43e4b00cc912f8228ddcc6d19c9f0f69bbb0542eda0fc9dec916a20b15dc0fd2ededda39142311a5001d⟩,
   ⟨0x8d9e5297186db2d9fb266eaac783182b70152c65550d881c5ecd87b6f0f5a6449f38db9dfa9cce202c6477faaf9b7ac⟩,
   ⟨0x166007c08a99db2fc3ba8734ace9824b5eecfdfa8d0cf8ef5dd365bc400a0051d5fa9c01a58b1fb93d1a1399126a775c⟩,
   ⟨0x16a3ef08be3ea7ea03bcddfabba6ff6ee5a4375efa1f4fd7feb34fd206357132b920f5b00801dee460ee415a15812ed9⟩,
   ⟨0x1866c8ed336c61231a1be54fd1d74cc4f9fb0ce4c6af5920abc5750c4bf39b4852cfe2f7bb9248836b233d9d55535d4a⟩,
   ⟨0x167a55cda70a6e1cea820597d94a84903216f763e13d87bb5308592e7ea7d4fbc7385ea3d529b35e346ef48bb8913f55⟩,
   ⟨0x4d2f259eea405bd48f010a01ad2911d9c6dd039bb61a6290e591b36e636a5c871a5c29f4f83060400f8b49cba8f6aa8⟩,
   ⟨0xaccbb67481d033ff5852c1e48c50c477f94ff8aefce42d28c0f9a88cea7913516f968986f7ebbea9684b529e2561092⟩,
   ⟨0xad6b9514c767fe3c3613144b45f1496543346d98adf02267d5ceef9a00d9b8693000763e3b90ac11e99b138573345cc⟩,
   ⟨0x2660400eb2e4f3b628bdd0d53cd76f2bf565b94e72927c1cb748df27942480e420517bd8714cc80d1fadc1326ed06f7⟩,
   ⟨0xe0fa1d816ddc03e6b24255e0d7819c171c40f65e273b853324efcd6356caa205ca2f570f13497804415473a1d634b8f⟩,
   ⟨1⟩]

/-- py_ecc `sqrt_division_FQ`: `y = uv·(uv³)^((p − 3)/4)`, together with whether `y² v = u`.
When `u/v` is not a square, `y² = −u/v` instead. -/
def sqrtDivFp (u v : Fp) : Bool × Fp :=
  let t := u * v
  let y := t * (t * (v * v)).pow ((P - 3) / 4)
  (decide (y * y * v = u), y)

/-- Simplified SWU onto `E₁'`, as affine `(x, y)`. Mirrors py_ecc `optimized_swu_G1`. -/
def swuG1 (t : Fp) : Fp × Fp :=
  let t2 := t * t
  let zt2 := isoZ1 * t2
  let tmp := zt2 + zt2 * zt2
  let den0 := -(isoA1 * tmp)
  let num0 := isoB1 * (tmp + Fp.one)
  -- Exceptional case `Z²t⁴ + Zt² = 0`: `x₁ = B'/(Z·A')`.
  let den := if den0.isZero then isoZ1 * isoA1 else den0
  let v := den * den * den
  let u := num0 * num0 * num0 + isoA1 * num0 * (den * den) + isoB1 * v
  let (isRoot, y0) := sqrtDivFp u v
  let y1 := if isRoot then y0 else y0 * (t2 * t) * sqrtMinus11Cubed
  let num := if isRoot then num0 else num0 * zt2
  let y := if t.sgn0 != y1.sgn0 then -y1 else y1
  (num * Fp.inv den, y)

/-- py_ecc `map_to_curve_G1`: SSWU onto `E₁'`, then the 11-isogeny to `E`. -/
def mapToCurveG1 (t : Fp) : Affine Fp :=
  let (x, y) := swuG1 t
  isoMap iso11XNum iso11XDen iso11YNum iso11YDen x y

/-- `MAP_FP_TO_G1`: `clear_cofactor_G1(map_to_curve_G1(t))`, i.e. `[h_eff]` of the mapped
point. -/
def mapFpToG1 (t : Fp) : Affine Fp :=
  (Jac.mul (Jac.ofAffine (mapToCurveG1 t)) hEffG1).toAffine

/-! ## `G2`: SSWU onto the 3-isogenous curve -/

/-- `Z = −(2 + u)` for the `G2` SSWU map (py_ecc `ISO_3_Z = FQ2([-2, -1])`). -/
def isoZ2 : Fp2 := ⟨⟨P - 2⟩, ⟨P - 1⟩⟩

/-- `A' = 240u` of the 3-isogenous curve `E₂'` (py_ecc `ISO_3_A`). -/
def isoA2 : Fp2 := ⟨⟨0⟩, ⟨240⟩⟩

/-- `B' = 1012(1 + u)` of `E₂'` (py_ecc `ISO_3_B`). -/
def isoB2 : Fp2 := ⟨⟨1012⟩, ⟨1012⟩⟩

/-- `(p² − 9)/16`, the exponent of `sqrt_division_FQ2` (py_ecc `P_MINUS_9_DIV_16`). -/
def pMinus9Div16 : Nat := (P * P - 9) / 16

/-- py_ecc `RV1`: `1/√2`, so that `RV1·(1 ± u)` are primitive eighth roots of unity. -/
def rv1 : Nat :=
  1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257

/-- py_ecc `POSITIVE_EIGHTH_ROOTS_OF_UNITY`: `1, u, RV1(1 + u), RV1(1 − u)`. The order of the
list matters: the first root that works is used. -/
def eighthRoots : List Fp2 :=
  [⟨⟨1⟩, ⟨0⟩⟩, ⟨⟨0⟩, ⟨1⟩⟩, ⟨⟨rv1⟩, ⟨rv1⟩⟩, ⟨⟨rv1⟩, ⟨P - rv1⟩⟩]

/-- py_ecc `EV1`. -/
def ev1 : Nat :=
  1015919005498129635886032702454337503112659152043614931979881174103627376789972962005013361970813319613593700736144
/-- py_ecc `EV2`. -/
def ev2 : Nat :=
  1244231661155348484223428017511856347821538750986231559855759541903146219579071812422210818684355842447591283616181
/-- py_ecc `EV3`. -/
def ev3 : Nat :=
  1646015993121829755895883253076789309308090876275172350194834453434199515639474951814226234213676147507404483718679
/-- py_ecc `EV4`. -/
def ev4 : Nat :=
  1637752706019426886789797193293828301565549384974986623510918743054325021588194075665960171838131772227885159387073

/-- py_ecc `ETAS`: the constants `η` with `η²·Z³` an eighth root of unity, used to turn the
square-root candidate for `x₁` into one for `x₂ = Z t² x₁`. Order matters (first match). -/
def etas : List Fp2 :=
  [⟨⟨ev1⟩, ⟨ev2⟩⟩, ⟨⟨P - ev2⟩, ⟨ev1⟩⟩, ⟨⟨ev3⟩, ⟨ev4⟩⟩, ⟨⟨P - ev4⟩, ⟨ev3⟩⟩]

/-- `h_eff` for `G2` (py_ecc `H_EFF_G2`, RFC 9380 §8.8.2), a 636-bit scalar. -/
def hEffG2 : Nat :=
  209869847837335686905080341498658477663839067235703451875306851526599783796572738804459333109033834234622528588876978987822447936461846631641690358257586228683615991308971558879306463436166481

/-- `ISO_3_K_1_0_VAL`. -/
private def k10 : Nat :=
  889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542
/-- `ISO_3_K_3_0_VAL`. -/
private def k30 : Nat :=
  3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558
/-- `ISO_3_K_4_0_VAL`. -/
private def k40 : Nat :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355

/-- 3-isogeny `x` numerator coefficients, constant term first (py_ecc `ISO_3_X_NUMERATOR`). -/
def iso3XNum : List Fp2 :=
  [⟨⟨k10⟩, ⟨k10⟩⟩,
   ⟨⟨0⟩, ⟨2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706522⟩⟩,
   ⟨⟨2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706526⟩,
    ⟨1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853261⟩⟩,
   ⟨⟨3557697382419259905260257622876359250272784728834673675850718343221361467102966990615722337003569479144794908942033⟩, ⟨0⟩⟩]

/-- 3-isogeny `x` denominator coefficients (py_ecc `ISO_3_X_DENOMINATOR`, whose trailing zero
coefficient is dropped: it does not change the polynomial). -/
def iso3XDen : List Fp2 :=
  [⟨⟨0⟩, ⟨4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559715⟩⟩,
   ⟨⟨12⟩, ⟨4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559775⟩⟩,
   ⟨⟨1⟩, ⟨0⟩⟩]

/-- 3-isogeny `y` numerator coefficients (py_ecc `ISO_3_Y_NUMERATOR`). -/
def iso3YNum : List Fp2 :=
  [⟨⟨k30⟩, ⟨k30⟩⟩,
   ⟨⟨0⟩, ⟨889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235518⟩⟩,
   ⟨⟨2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706524⟩,
    ⟨1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853263⟩⟩,
   ⟨⟨2816510427748580758331037284777117739799287910327449993381818688383577828123182200904113516794492504322962636245776⟩, ⟨0⟩⟩]

/-- 3-isogeny `y` denominator coefficients (py_ecc `ISO_3_Y_DENOMINATOR`). -/
def iso3YDen : List Fp2 :=
  [⟨⟨k40⟩, ⟨k40⟩⟩,
   ⟨⟨0⟩, ⟨4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559571⟩⟩,
   ⟨⟨18⟩, ⟨4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559769⟩⟩,
   ⟨⟨1⟩, ⟨0⟩⟩]

/-- py_ecc `sqrt_division_FQ2`: `γ = uv⁷·(uv¹⁵)^((p² − 9)/16)`, then the first eighth root of
unity `ζ` (in `eighthRoots` order) with `(ζγ)²v = u`. Returns whether one was found, and
`ζγ` (or `γ` when none was). -/
def sqrtDivFp2 (u v : Fp2) : Bool × Fp2 :=
  let v2 := Fp2.sq v
  let v4 := Fp2.sq v2
  let v7 := v4 * v2 * v
  let t1 := u * v7
  let t2 := t1 * Fp2.sq v4
  let gamma := Fp2.pow t2 pMinus9Div16 * t1
  match eighthRoots.find? (fun z => decide (Fp2.sq (z * gamma) * v = u)) with
  | some z => (true, z * gamma)
  | none => (false, gamma)

/-- Simplified SWU onto `E₂'`, as affine `(x, y)`. Mirrors py_ecc `optimized_swu_G2`.
`none` only in the case py_ecc reports as unreachable (no square root for either `x₁` or
`x₂`), which cannot happen because `Z` is not a square in `𝔽ₚ²`. -/
def swuG2 (t : Fp2) : Option (Fp2 × Fp2) :=
  let t2 := Fp2.sq t
  let zt2 := isoZ2 * t2
  let tmp := zt2 + Fp2.sq zt2
  let den0 := -(isoA2 * tmp)
  let num0 := isoB2 * (tmp + Fp2.one)
  -- Exceptional case `Z²t⁴ + Zt² = 0`: `x₁ = B'/(Z·A')`.
  let den := if den0.isZero then isoZ2 * isoA2 else den0
  let v := den * den * den
  let u := num0 * num0 * num0 + isoA2 * num0 * (den * den) + isoB2 * v
  let (success, y0) := sqrtDivFp2 u v
  let y1 : Option Fp2 :=
    if success then some y0
    else
      -- Candidate for `x₂`: `√g(x₂) = η·t³·γ` with `g(x₂) = (Zt²)³·g(x₁)`.
      let cand := y0 * (t2 * t)
      let u2 := zt2 * zt2 * zt2 * u
      (etas.find? (fun e => decide (Fp2.sq (e * cand) * v = u2))).map (· * cand)
  y1.map fun y1 =>
    let num := if success then num0 else num0 * zt2
    let y := if t.sgn0 != y1.sgn0 then -y1 else y1
    (num * Fp2.inv den, y)

/-- py_ecc `map_to_curve_G2`: SSWU onto `E₂'`, then the 3-isogeny to the twist. -/
def mapToCurveG2 (t : Fp2) : Option (Affine Fp2) :=
  (swuG2 t).map fun (x, y) => isoMap iso3XNum iso3XDen iso3YNum iso3YDen x y

/-- `MAP_FP2_TO_G2`: `clear_cofactor_G2(map_to_curve_G2(t))`, i.e. `[h_eff]` of the mapped
point (py_ecc `multiply_clear_cofactor_G2`). -/
def mapFp2ToG2 (t : Fp2) : Option (Affine Fp2) :=
  (mapToCurveG2 t).map fun q => (Jac.mul (Jac.ofAffine q) hEffG2).toAffine

end EvmLean.Bls12381
