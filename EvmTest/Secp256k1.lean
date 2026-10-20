import EvmLean.Crypto.Secp256k1
import EvmTest.PrecompileHex

/-!
Unit tests for `EvmLean.Crypto.Secp256k1`.

Vectors: go-ethereum `core/vm/testdata/precompiles/ecRecover.json` (the `ValidKey` vector
recovers the key of the well-known test account `0xa94f5374…ebf0b`, private key
`0x45a915e4…5ff2d8`; its keccak-256 address was checked against the vector's output), plus
signatures over keccak-256 digests made with that key and an independent reference
implementation.
-/

open EvmLean EvmLean.PrecompileTest

namespace EvmLean.Secp256k1Test

/-- The uncompressed public key of the test account `0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b`. -/
def testPub : ByteArray :=
  hex "3a514176466fa815ed481ffad09110a2d344f6c9b78c1d14afc351c3a51be33d8072e77939dc03ba44790779b7a1025baf3003f6732430e20cd9b76d953391b3"

-- Group law sanity: 2G, G + G, and n·G = O.
#guard (Secp256k1.Point.mul 2 Secp256k1.g).toAffine ==
  some (0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5,
        0x1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a)
#guard (Secp256k1.g.add Secp256k1.g).toAffine == (Secp256k1.Point.mul 2 Secp256k1.g).toAffine
#guard (Secp256k1.Point.mul Secp256k1.n Secp256k1.g).toAffine == none
-- Private key → public key.
#guard (Secp256k1.Point.mul 0x45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8
  Secp256k1.g).toAffine.map (fun (x, y) => Bytes.ofNatBE 32 x ++ Bytes.ofNatBE 32 y) == some testPub

-- geth `ValidKey` (v = 28).
#guard Secp256k1.recover
  (hex "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c") 1
  0x73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f
  0xeeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549 == some testPub

-- keccak256("hello"), v = 28.
#guard Secp256k1.recover
  (hex "1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8") 1
  0xf01d6b9018ab421dd410404cb869072065522bf85734008f105cf385a023a80f
  0x1d20f3247b535267f9e948b3bb0fe900802708a19b17b055625c27bac65d0f0e == some testPub

-- keccak256("evm-lean"), v = 28.
#guard Secp256k1.recover
  (hex "3d6fc083053d854e527910b991afea21add2be43465660451bab3f56541ace6b") 1
  0x259bd7bfc4cd47f14f8fd9593e4d72be33cd8b96e1dee6ec1a6a5ef30ead2bd7
  0x5343f2391ef11503b2ac7f7487b013edc11a4c38d94bf8c18484e7028f981710 == some testPub

-- keccak256(""), v = 27.
#guard Secp256k1.recover
  (hex "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470") 0
  0x2f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4
  0x6c24e9a9eb200d7740b9c244dfb7a4dc73bb2bae86709d0acddbe14e071321cc == some testPub

-- The wrong recovery id gives a different (valid) key.
#guard (Secp256k1.recover
  (hex "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470") 1
  0x2f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4
  0x6c24e9a9eb200d7740b9c244dfb7a4dc73bb2bae86709d0acddbe14e071321cc).map (·.size) == some 64
#guard Secp256k1.recover
  (hex "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470") 1
  0x2f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4
  0x6c24e9a9eb200d7740b9c244dfb7a4dc73bb2bae86709d0acddbe14e071321cc != some testPub

-- geth `CallEcrecoverUnrecoverableKey` (v = 27): no key.
#guard Secp256k1.recover
  (hex "a8b53bdf3306a35a7103ab5504a0c9b492295564b6202b1942a84ef300107281") 0
  0x3078356531653033663533636531386237373263636230303933666637316633
  0x6635336635633735623734646362333161383561613862383839326234653862 == none

-- Range checks: recId ∉ {0,1}, r or s zero or ≥ n.
#guard Secp256k1.recover
  (hex "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c") 2
  0x73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f
  0xeeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549 == none
#guard Secp256k1.recover
  (hex "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c") 1 0
  0xeeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549 == none
#guard Secp256k1.recover
  (hex "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c") 1
  0x73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f 0 == none
#guard Secp256k1.recover
  (hex "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c") 1 Secp256k1.n
  0xeeb940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549 == none
#guard Secp256k1.recover
  (hex "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c") 1
  0x73b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f Secp256k1.n == none
-- r = 5: 5³ + 7 = 132 is not a square modulo p, so no point has x = 5.
#guard Nat.powMod 132 ((Secp256k1.p - 1) / 2) Secp256k1.p ≠ 1
#guard Secp256k1.recover
  (hex "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c") 0 5 1 == none

end EvmLean.Secp256k1Test
