import EvmLean.Crypto.Sha256
import EvmLeanTest.HashUtil

/-!
# Tests for `EvmLean.Crypto.Sha256`

NIST FIPS 180-4 example vectors (`""`, `"abc"`, the 448-bit and 896-bit messages), plus
`seq n` inputs (bytes `0, 1, …, n-1`) at the padding boundaries: 55 bytes is the longest
message whose length fits in the same block, 56 forces an extra block, 64 is exactly one
block. Expected values for the `seq` inputs are from Python's `hashlib.sha256`.
-/

open EvmLean EvmLeanTest.HashUtil

#guard Sha256.hash .empty =
  hex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard Sha256.hash (ascii "abc") =
  hex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard Sha256.hash (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
  hex "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard Sha256.hash (ascii ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn" ++
    "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")) =
  hex "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
#guard Sha256.hash (seq 55) =
  hex "463eb28e72f82e0a96c0a4cc53690c571281131f672aa229e0d45ae59b598b59"
#guard Sha256.hash (seq 56) =
  hex "da2ae4d6b36748f2a318f23e7ab1dfdf45acdc9d049bd80e59de82a60895f562"
#guard Sha256.hash (seq 63) =
  hex "29af2686fd53374a36b0846694cc342177e428d1647515f078784d69cdb9e488"
#guard Sha256.hash (seq 64) =
  hex "fdeab9acf3710362bd2658cdc9a29e8f9c757fcf9811603a8c447cd1d9151108"
#guard Sha256.hash (seq 65) =
  hex "4bfd2c8b6f1eec7a2afeb48b934ee4b2694182027e6d0fc075074f2fabb31781"
#guard Sha256.hash (seq 119) =
  hex "da18797ed7c3a777f0847f429724a2d8cd5138e6ed2895c3fa1a6d39d18f7ec6"
#guard Sha256.hash (seq 120) =
  hex "f52b23db1fbb6ded89ef42a23ce0c8922c45f25c50b568a93bf1c075420bbb7c"
#guard Sha256.hash (seq 1000) =
  hex "a8af099bf2e878609558dbf69d8f88f4a31040a8cf84b549a0cfa912f12ffc3f"
#guard (Sha256.hash (seq 3)).size = 32
