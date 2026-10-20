import EvmLean.Crypto.Keccak
import EvmTest.HashUtil

/-!
# Tests for `EvmLean.Crypto.Keccak`

Expected digests are from OpenSSL 3 (`openssl dgst -keccak-256`) and Python's
`hashlib.sha3_256`. Inputs `seq n` are the bytes `0, 1, …, n-1` (mod 256); the lengths
cover the 136-byte rate boundaries (135 puts both padding bits in one byte, 136 needs a
whole padding block). The SHA3-256 checks run the same sponge with FIPS 202's domain byte
`0x06`, which pins down the permutation independently of the Keccak padding.
-/

open EvmLean EvmTest.HashUtil

#guard Keccak.hash256 .empty =
  0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470#256
#guard Keccak.hash256 (ascii "abc") =
  0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45#256
#guard Keccak.hash256 (ascii "The quick brown fox jumps over the lazy dog") =
  0x4d741b6f1eb29cb2a9b9911c82f56fa8d73b04959d3d9d222895df6c0b28aa15#256
#guard Keccak.hash256 (seq 1) =
  0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a#256
#guard Keccak.hash256 (seq 7) =
  0x801560412425120fa609be232d6fa71c7f64f42aee7977267687dcc0a2f5aa63#256
#guard Keccak.hash256 (seq 8) =
  0x59e7c99f6be4fd053d7c99f54e371304a33213473dc41f1825b7f3ceb33841a6#256
#guard Keccak.hash256 (seq 135) =
  0xcbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62#256
#guard Keccak.hash256 (seq 136) =
  0x7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e#256
#guard Keccak.hash256 (seq 137) =
  0xac73d4fae68b8453f764007c1a20ce95994187861f0c3227a3a8e99a73a3b1db#256
#guard Keccak.hash256 (seq 271) =
  0x7c974895b2a88303ff2dc6b58f438ceb0b298cac91099ac0539cc0f477506191#256
#guard Keccak.hash256 (seq 272) =
  0xfdf2ec49e749960d3c8521a0219af8d03e30e2b3bf19bd16150ee0eaf133d66e#256
#guard Keccak.hash256 (seq 273) =
  0x4f707289a9c3ccd0c4a51f2f17339f5dd171d371c04ff7783b735b5b22682eaf#256
#guard Keccak.hash256 (seq 1000) =
  0xaca79e4146e30eb1c733f6d6060d72471c36ea4e01ebf45d7f4916249c2bbd82#256

/-- FIPS 202 SHA3-256, via the same sponge with domain byte `0x06`. -/
def sha3_256 (b : ByteArray) : ByteArray := Keccak.digestBytes (Keccak.sponge 0x06 b)

#guard sha3_256 .empty =
  hex "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
#guard sha3_256 (ascii "abc") =
  hex "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
#guard sha3_256 (seq 135) =
  hex "fded8fd9d6551c601eeb3b7c6bc5e5cfd8aad1d015b7e9aaa9c9b9475231d5e2"
#guard sha3_256 (seq 136) =
  hex "cf3ccff92480a29160c2d38317c430e14749bfee1788106957dfe73f8c4930e5"
#guard sha3_256 (seq 137) =
  hex "ce9d7dc90913ee5d92745019479a5352c6d6279bef18ed07dc0a83ee8084daca"
#guard sha3_256 (seq 272) =
  hex "0b21ec4a8eff6d179e09ba9fe0ab08515b24e0923fbf419f5c30a38e64577db5"
#guard sha3_256 (seq 1000) =
  hex "14e5de35911194ddad95ac1572e2b6ce054ed2146cd0562280fcab04ccfecbd8"

/-! Kernel checks: the definition reduces in the kernel (no compiler involved). -/

example : Keccak.hash256 ByteArray.empty =
    0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470#256 := by
  decide +kernel

example : Keccak.hash256 "abc".toUTF8 =
    0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45#256 := by
  decide +kernel
