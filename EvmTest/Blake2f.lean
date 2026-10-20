import EvmLean.Crypto.Blake2f
import EvmTest.HashUtil

/-!
# Tests for `EvmLean.Crypto.Blake2f`

The valid EIP-152 test vectors 4–7 (inputs in the precompile's 213-byte encoding:
`rounds` big-endian, `h`, `m`, `t₀ t₁` little-endian, final flag). Vector 8
(`rounds = 2³² − 1`) is omitted: it needs ~4·10⁹ rounds and is far too slow for a unit
test. Vectors 0–3 test the precompile's length/flag validation, which is not part of `F`.

The extra round counts 10, 11, 20 and 23 exercise the wrap-around of the `σ` schedule;
their expected values come from an independent Python transcription of RFC 7693 (the same
script reproduces EIP-152 vectors 4–7).
-/

open EvmLean EvmTest.HashUtil

/-- Little-endian 64-bit word at byte offset `o`. -/
def le64At (b : ByteArray) (o : Nat) : UInt64 :=
  (List.range 8).foldl (fun acc i => acc ||| ((b[o + i]?.getD 0).toUInt64 <<< (8 * i).toUInt64)) 0

/-- Run `F` on a 213-byte EIP-152 precompile input, returning the 64-byte output. -/
def blake2fBytes (input : ByteArray) : ByteArray :=
  let rounds := Bytes.toNat (input.extract 0 4)
  let h : Vector UInt64 8 := Vector.ofFn fun i => le64At input (4 + 8 * i.val)
  let m : Vector UInt64 16 := Vector.ofFn fun i => le64At input (68 + 8 * i.val)
  let out := Blake2.compress rounds h m (le64At input 196) (le64At input 204)
    (input[212]?.getD 0 == 1)
  ⟨(out.toArray.map fun w => (List.range 8).map fun i => (w >>> (8 * i).toUInt64).toUInt8)
    |>.toList.flatten.toArray⟩

/-- EIP-152 test-vector input with the given 4-byte `rounds` and 1-byte `final` (hex). -/
def eip152Input (rounds final : String) : ByteArray :=
  hex (rounds ++
    "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
    "d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b" ++
    "6162630000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0300000000000000" ++ "0000000000000000" ++ final)

#guard (eip152Input "0000000c" "01").size = 213

-- EIP-152 test vector 4: zero rounds.
#guard blake2fBytes (eip152Input "00000000" "01") = hex
  ("08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
   "d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b")

-- EIP-152 test vector 5: 12 rounds (BLAKE2b-512 of "abc").
#guard blake2fBytes (eip152Input "0000000c" "01") = hex
  ("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
   "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923")

-- EIP-152 test vector 6: 12 rounds, final flag false.
#guard blake2fBytes (eip152Input "0000000c" "00") = hex
  ("75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d28752" ++
   "98743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735")

-- EIP-152 test vector 7: one round.
#guard blake2fBytes (eip152Input "00000001" "01") = hex
  ("b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fb" ++
   "a551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421")

-- Schedule wrap-around (σ index = round mod 10).
#guard blake2fBytes (eip152Input "0000000a" "01") = hex
  ("5a4308e0e1daede181b47775d926a6b4b6a0adf86d05bfea696fac45f0841962" ++
   "3976bd3c786f61500b9f94a043b9dcf397e38ee237f3c273a7d812be20874f5a")
#guard blake2fBytes (eip152Input "0000000b" "01") = hex
  ("60faa8f91624b2b718210df242b788c7ae887e953dce3c7f80862bc5e4f88d82" ++
   "7cada4d95d2c4ac41eb66b84fcdc0e12ab0c66f4d9d546ff8a0d712f324e1845")
#guard blake2fBytes (eip152Input "00000014" "01") = hex
  ("0c1b96fc9c06898bb49af24ef91a669143df8e847807765da43f8ad6c0ec5180" ++
   "e6ab033a21428e52c5d933345f81d8300a02158704935b7a020d990572ad9be0")
#guard blake2fBytes (eip152Input "00000017" "01") = hex
  ("307f79b2083b29ec66926bc36e1457f571f90b7cc0572faca1d9229ca35d704f" ++
   "73efee65f960489017168f67d9c9b3643752de57c6b70a7d6ebdda82282f5150")
