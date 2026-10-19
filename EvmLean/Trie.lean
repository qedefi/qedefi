import EvmLean.Prelude.Rlp
import EvmLean.State.Account

/-!
# Merkle-Patricia trie roots

The root hash of a Modified Merkle-Patricia Trie over a finite key/value map, following
`src/ethereum/merkle_patricia_trie.py` in `ethereum/execution-specs`:

* keys are split into nibbles (`bytes_to_nibble_list`) and stored in nodes with hex-prefix
  encoding (`nibble_list_to_compact`);
* `patricialize` builds leaf, extension and branch nodes;
* `encode_internal_node` RLP-encodes a node and replaces it by its Keccak when the encoding
  is at least 32 bytes (shorter nodes are inlined in their parent);
* the root is the Keccak of the RLP encoding of the root node (for the empty trie,
  `keccak(rlp(b"")) = 0x56e8…b421`).

We compute roots directly from the full map (no incremental trie). Everything is
parameterised over the Keccak function, so roots are meaningful for any `Crypto`.

Secured tries (state, storage) hash their keys first; the transactions, receipts and
withdrawals tries are keyed by `rlp(index)`.
-/

namespace EvmLean.Trie

/-- A key as a list of nibbles (`bytes_to_nibble_list`). -/
def nibbles (b : ByteArray) : List Nat :=
  b.toList.flatMap fun x => [x.toNat / 16, x.toNat % 16]

/-- Pack an even-length nibble list two per byte. -/
def packNibbles : List Nat → List UInt8
  | a :: b :: rest => (16 * a + b).toUInt8 :: packNibbles rest
  | [a] => [(16 * a).toUInt8]
  | [] => []

/-- Hex-prefix encoding (`nibble_list_to_compact`): a flag nibble (bit 1: leaf, bit 0: odd
length), then the nibbles packed two per byte. -/
def compact (key : List Nat) (isLeaf : Bool) : ByteArray :=
  let flag := if isLeaf then 2 else 0
  match key with
  | [] => ⟨#[(16 * flag).toUInt8]⟩
  | k :: ks =>
    if key.length % 2 = 0 then ⟨(((16 * flag).toUInt8) :: packNibbles key).toArray⟩
    else ⟨(((16 * (flag + 1) + k).toUInt8) :: packNibbles ks).toArray⟩

/-- Length of the longest common prefix of two nibble lists. -/
def commonPrefixLength : List Nat → List Nat → Nat
  | a :: as, b :: bs => if a = b then commonPrefixLength as bs + 1 else 0
  | _, _ => 0

/-- Length of the longest prefix shared by all keys. -/
def sharedPrefixLength : List (List Nat × ByteArray) → Nat
  | [] => 0
  | (k, _) :: rest => rest.foldl (fun n (k', _) => min n (commonPrefixLength k k')) k.length

/-- `encode_internal_node`: how a child node is referenced from its parent — inline if its
encoding is shorter than 32 bytes, otherwise by its Keccak. -/
def reference (keccak256 : ByteArray → Word) (node : Rlp) : Rlp :=
  let enc := node.encode
  if enc.size < 32 then node else .bytes (Bytes.ofWord (keccak256 enc))

/-- `patricialize`: the (unhashed) node for `entries`, whose keys are the nibbles not yet
consumed by ancestors. Keys must be distinct. The empty trie is `b""`.

Each recursive call consumes at least one nibble of every key it passes on (an extension
consumes the shared prefix, a branch one nibble; keys exhausted at a branch become its
value), so `fuel = 1 + max key length` suffices (`root` supplies it). -/
def patricialize (keccak256 : ByteArray → Word) :
    Nat → List (List Nat × ByteArray) → Rlp
  | _, [] => .bytes .empty
  | _, [(k, v)] => .list [.bytes (compact k true), .bytes v]
  | 0, _ => .bytes .empty
  | fuel + 1, entries =>
    let p := sharedPrefixLength entries
    if p > 0 then
      let child := patricialize keccak256 fuel (entries.map fun (k, v) => (k.drop p, v))
      .list [.bytes (compact ((entries.head?.map (·.1)).getD [] |>.take p) false),
             reference keccak256 child]
    else
      let value := ((entries.find? (·.1.isEmpty)).map (·.2)).getD .empty
      let branch (i : Nat) : Rlp :=
        reference keccak256 (patricialize keccak256 fuel (entries.filterMap fun (k, v) =>
          match k with
          | n :: rest => if n = i then some (rest, v) else none
          | [] => none))
      .list ((List.range 16).map branch ++ [.bytes value])

/-- `root`: the root hash of the trie mapping each key to its (already encoded) value.
Keys must be distinct and values non-empty. -/
def root (keccak256 : ByteArray → Word) (entries : List (ByteArray × ByteArray)) : Word :=
  let entries := entries.map fun (k, v) => (nibbles k, v)
  let fuel := entries.foldl (fun n (k, _) => max n k.length) 0 + 1
  keccak256 (patricialize keccak256 fuel entries).encode

/-- Root of a secured trie: keys are replaced by their Keccak before insertion. -/
def securedRoot (keccak256 : ByteArray → Word) (entries : List (ByteArray × ByteArray)) : Word :=
  root keccak256 (entries.map fun (k, v) => (Bytes.ofWord (keccak256 k), v))

/-- Root of a trie keyed by `rlp(index)` (transactions, receipts, withdrawals). -/
def indexedRoot (keccak256 : ByteArray → Word) (values : List ByteArray) : Word :=
  root keccak256 ((List.range values.length).zip values |>.map fun (i, v) => ((Rlp.nat i).encode, v))

/-- `EMPTY_TRIE_ROOT`, given the hash function: `keccak(rlp(b""))`. -/
def emptyRoot (keccak256 : ByteArray → Word) : Word := root keccak256 []

/-- Root of an account's storage trie: `keccak(slot) ↦ rlp(value)`. Storage never holds
zero values, matching the reference's removal of default values. -/
def storageRoot (keccak256 : ByteArray → Word) (s : Storage) : Word :=
  securedRoot keccak256 (s.toList.map fun (k, v) => (Bytes.ofWord k, (Rlp.nat v.toNat).encode))

/-- `encode_account`: `rlp([nonce, balance, storageRoot, codeHash])`. -/
def encodeAccount (keccak256 : ByteArray → Word) (a : Account) : ByteArray :=
  (Rlp.list [.nat a.nonce, .nat a.balance.toNat, .bytes (Bytes.ofWord (storageRoot keccak256 a.storage)),
    .bytes (Bytes.ofWord (keccak256 a.code))]).encode

/-- The state root: secured trie `keccak(address) ↦ encode_account`. -/
def stateRoot (keccak256 : ByteArray → Word) (w : World) : Word :=
  securedRoot keccak256 (w.toList.map fun (a, acc) => (Bytes.ofAddress a, encodeAccount keccak256 acc))

end EvmLean.Trie
