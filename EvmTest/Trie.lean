import EvmTest.TxSupport

/-!
Unit tests for `EvmLean.Trie`: hex-prefix encoding (vectors from the Ethereum wiki /
Yellow Paper appendix C) and the node structure built by `patricialize`, with a stand-in
hash. Root hashes against official vectors are in `EvmTest/TxIntegration.lean`.
-/

open EvmLean EvmLean.Trie EvmTest

namespace EvmTest.TrieTest

/-! ## Nibbles and hex-prefix encoding -/

#guard nibbles (hx "0x12ab") = [1, 2, 10, 11]
#guard nibbles .empty = []
#guard compact [1, 2, 3, 4, 5] false == hx "0x112345"
#guard compact [0, 1, 2, 3, 4, 5] false == hx "0x00012345"
#guard compact [0, 15, 1, 12, 11, 8] true == hx "0x200f1cb8"
#guard compact [15, 1, 12, 11, 8] true == hx "0x3f1cb8"
#guard compact [] true == hx "0x20"
#guard compact [] false == hx "0x00"

/-! ## Node structure -/

#guard commonPrefixLength [1, 2, 3] [1, 2, 4] = 2
#guard sharedPrefixLength [([1, 2, 3], .empty), ([1, 2, 4], .empty), ([1, 5], .empty)] = 1

-- Empty trie: `keccak(rlp(b""))`.
#guard emptyRoot fakeKeccak = fakeKeccak (hx "0x80")

-- One entry: a leaf holding the whole key.
#guard root fakeKeccak [(hx "0x12", hx "0xaa")] =
  fakeKeccak (Rlp.list [.bytes (hx "0x2012"), .bytes (hx "0xaa")]).encode

/-- Two short keys diverging at the first nibble: a branch with two inline leaves. -/
def twoLeaves : Rlp := patricialize fakeKeccak 3 [([1], hx "0xaa"), ([2], hx "0xbb")]

#guard twoLeaves.encode == (Rlp.list ((List.range 16).map (fun i =>
  if i = 1 then Rlp.list [.bytes (hx "0x20"), .bytes (hx "0xaa")]
  else if i = 2 then Rlp.list [.bytes (hx "0x20"), .bytes (hx "0xbb")]
  else .bytes .empty) ++ [.bytes .empty])).encode

/-- A shared prefix `[1, 2]` becomes an extension over a branch. -/
def extension : Rlp := patricialize fakeKeccak 4 [([1, 2, 3], hx "0xaa"), ([1, 2, 4], hx "0xbb")]

#guard match extension with
  | .list [.bytes k, _] => k == hx "0x0012"
  | _ => false

-- A key that is a prefix of another ends at the branch's value slot.
#guard match patricialize fakeKeccak 4 [([1], hx "0xaa"), ([1, 2], hx "0xbb")] with
  | .list [.bytes k, .list items] => k == hx "0x11" && items.length = 17 &&
      (match items.getLast? with | some (.bytes v) => v == hx "0xaa" | _ => false)
  | _ => false

-- Children whose encoding reaches 32 bytes are referenced by hash.
#guard match reference fakeKeccak (.bytes (Bytes.zeros 40)) with
  | .bytes h => h.size = 32
  | .list _ => false
#guard match reference fakeKeccak (.bytes (Bytes.zeros 10)) with
  | .bytes h => h.size = 10
  | .list _ => false

-- Order of entries does not matter.
#guard root fakeKeccak [(hx "0x01", hx "0xaa"), (hx "0x02", hx "0xbb"), (hx "0x0103", hx "0xcc")] =
  root fakeKeccak [(hx "0x0103", hx "0xcc"), (hx "0x02", hx "0xbb"), (hx "0x01", hx "0xaa")]

-- Index keys are `rlp(i)`: 0 ↦ 0x80, 1 ↦ 0x01.
#guard indexedRoot fakeKeccak [hx "0xaa", hx "0xbb"] =
  root fakeKeccak [(hx "0x80", hx "0xaa"), (hx "0x01", hx "0xbb")]

-- Account encoding: `[nonce, balance, storageRoot, codeHash]`.
#guard encodeAccount fakeKeccak { nonce := 1, balance := 2 } ==
  (Rlp.list [.nat 1, .nat 2, .bytes (Bytes.ofWord (emptyRoot fakeKeccak)),
    .bytes (Bytes.ofWord (fakeKeccak .empty))]).encode

end EvmTest.TrieTest
