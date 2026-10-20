import EvmLean.Crypto.Ripemd160
import EvmTest.HashUtil

/-!
# Tests for `EvmLean.Crypto.Ripemd160`

Vectors from the RIPEMD-160 paper, plus `seq n` inputs at the 55/56/64-byte padding
boundaries checked against Python's `hashlib`.
-/

open EvmLean EvmTest.HashUtil

#guard Ripemd160.hash .empty = hex "9c1185a5c5e9fc54612808977ee8f548b2258d31"
#guard Ripemd160.hash (ascii "a") = hex "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"
#guard Ripemd160.hash (ascii "abc") = hex "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"
#guard Ripemd160.hash (ascii "message digest") = hex "5d0689ef49d2fae572b881b123a85ffa21595f36"
#guard Ripemd160.hash (ascii "abcdefghijklmnopqrstuvwxyz") =
  hex "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"
#guard Ripemd160.hash (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
  hex "12a053384a9c0c88e405a06c27dcf49ada62eb2b"
#guard Ripemd160.hash
    (ascii "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789") =
  hex "b0e20b6e3116640286ed3a87a5713079b21f5189"
#guard Ripemd160.hash (ascii ("1234567890123456789012345678901234567890" ++
    "1234567890123456789012345678901234567890")) =
  hex "9b752e45573d4b39f4dbd3323cab82bf63326bfb"
#guard Ripemd160.hash (seq 55) = hex "3c86963b3ff646a65ae42996e9664c747cc7e5e6"
#guard Ripemd160.hash (seq 56) = hex "ebdd79cfd4fd9949ef8089673d2620427f487cfb"
#guard Ripemd160.hash (seq 64) = hex "2581f5e9f957b44b0fa24d31996de47409dd1e0f"
#guard Ripemd160.hash (seq 1000) = hex "603d0d8e28f2d5f4f1dd75118d90f209d44f23d2"
