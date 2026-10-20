import EvmTest.TxSupport

/-!
Integration tests for the transaction layer, blocks and tries that need the real
primitives (`Crypto.real`: Keccak, secp256k1) and, for the end-to-end block, the
interpreter.

Vectors: `TrieTests/trieanyorder.json` and `trieanyorder_secureTrie.json` from
`ethereum/tests`, the execution-specs constants `EMPTY_TRIE_ROOT` / `EMPTY_OMMER_HASH`, and
the BlockchainTests fixture `bcEIP4844-blobtransactions/blockWithAllTransactionTypes`.
-/

open EvmLean EvmLeanTest

namespace EvmLeanTest.TxIntegration

/-- The real Keccak-256. -/
def keccak : ByteArray → Word := Crypto.real.keccak256

/-! ## Constants -/

#guard keccak .empty = hw "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
#guard Trie.emptyRoot keccak =
  hw "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
#guard Block.emptyOmmerHash keccak =
  hw "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"

/-! ## `TrieTests/trieanyorder.json` (plain and secured) -/

/-- Key or value bytes as the trie tests write them: hex if `0x`-prefixed, else ASCII. -/
def enc (s : String) : ByteArray := if s.startsWith "0x" then hx s else s.toUTF8

/-- Root of a test trie. -/
def plain (kvs : List (String × String)) : Word :=
  Trie.root keccak (kvs.map fun (k, v) => (enc k, enc v))

/-- Root of a secured test trie. -/
def secured (kvs : List (String × String)) : Word :=
  Trie.securedRoot keccak (kvs.map fun (k, v) => (enc k, enc v))

/-- `singleItem`. -/
def singleItem : List (String × String) := [("A", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")]
/-- `dogs`. -/
def dogs : List (String × String) := [("doe", "reindeer"), ("dog", "puppy"), ("dogglesworth", "cat")]
/-- `puppy`. -/
def puppy : List (String × String) :=
  [("do", "verb"), ("horse", "stallion"), ("doge", "coin"), ("dog", "puppy")]
/-- `foo`. -/
def foo : List (String × String) := [("foo", "bar"), ("food", "bass")]
/-- `smallValues`. -/
def smallValues : List (String × String) := [("be", "e"), ("dog", "puppy"), ("bed", "d")]
/-- `testy`. -/
def testy : List (String × String) := [("test", "test"), ("te", "testy")]
/-- `hex`. -/
def hexKeys : List (String × String) := [("0x0045", "0x0123456789"), ("0x4500", "0x9876543210")]

#guard plain singleItem = hw "0xd23786fb4a010da3ce639d66d5e904a11dbc02746d1ce25029e53290cabf28ab"
#guard plain dogs = hw "0x8aad789dff2f538bca5d8ea56e8abe10f4c7ba3a5dea95fea4cd6e7c3a1168d3"
#guard plain puppy = hw "0x5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84"
#guard plain foo = hw "0x17beaa1648bafa633cda809c90c04af50fc8aed3cb40d16efbddee6fdf63c4c3"
#guard plain smallValues = hw "0x3f67c7a47520f79faa29255d2d3c084a7a6df0453116ed7232ff10277a8be68b"
#guard plain testy = hw "0x8452568af70d8d140f58d941338542f645fcca50094b20f3c3d8c3df49337928"
#guard plain hexKeys = hw "0x285505fcabe84badc8aa310e2aae17eddc7d120aabec8a476902c8184b3a3503"
#guard secured singleItem = hw "0xe9e2935138352776cad724d31c9fa5266a5c593bb97726dd2a908fe6d53284df"
#guard secured dogs = hw "0xd4cd937e4a4368d7931a9cf51686b7e10abb3dce38a39000fd7902a092b64585"
#guard secured puppy = hw "0x29b235a58c3c25ab83010c327d5932bcf05324b7d6b1185e650798034783ca9d"
#guard secured foo = hw "0x1385f23a33021025d9e87cca5c66c00de06178807b96a9acc92b7d651ccde842"
#guard secured smallValues = hw "0x826a4f9f9054a3e980e54b20da992c24fa20467f1ca635115ef4917be66e746f"
#guard secured testy = hw "0xaea54fb6c80499674248a462864c420c9d9f3b3d38c879c12425bade1ad76552"
#guard secured hexKeys = hw "0xbc11c02c8ab456db0c4d2728b6a2a6210d06f26a2ace4f7d8bdfc72ddf2630ab"

/-! ## Block hashes and roots of `blockWithAllTransactionTypes` -/

/-- The EIP-4788 beacon-roots contract code. -/
def beaconCode : ByteArray :=
  hx "0x3373fffffffffffffffffffffffffffffffffffffffe14604d57602036146024575f5ffd5b5f35801560495762001fff810690815414603c575f5ffd5b62001fff01545f5260205ff35b5f5ffd5b62001fff42064281555f359062001fff015500"

/-- The sender of every transaction in block 1. -/
def sender : Address := 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b

/-- The fixture's `pre` state. -/
def pre : World :=
  (∅ : World)
    |>.insert Block.beaconRootsAddress
      { nonce := 1, code := beaconCode, storage := (∅ : Storage).set 0x03b6 0x03b6 }
    |>.insert sender { balance := 0x01000000000000000000 }

/-- The fixture's `postState`. -/
def post : World :=
  (∅ : World)
    |>.insert Block.beaconRootsAddress
      { nonce := 1, code := beaconCode,
        storage := ((∅ : Storage).set 0x03b6 0x03b6).set 0x079e 0x079e }
    |>.insert 0x100000000000000000000000000000000000000a { balance := 0x10 }
    |>.insert sender { nonce := 4, balance := 0xfffffffffffb837c20 }
    |>.insert 0xba5e000000000000000000000000000000000000 { balance := 0x888150 }

#guard Block.headerHash keccak genesisBlock.header =
  hw "0x5eb7f6da0f3e237c62bcae48b7fb5f4506d392616b62890429c8b76b4a1d4104"
#guard Block.headerHash keccak block1.header =
  hw "0x6243e029fb6bfef5226d2688cf5c880984a97c28ab9889a7dfae09c9c42eacfa"
#guard Trie.stateRoot keccak pre = genesisBlock.header.stateRoot
#guard Trie.stateRoot keccak post = block1.header.stateRoot
#guard Trie.indexedRoot keccak (block1.transactions.map Transaction.encode) =
  block1.header.transactionsRoot
#guard Trie.indexedRoot keccak (block1.withdrawals.map Block.withdrawalEncode) =
  block1.header.withdrawalsRoot
-- Every transaction is a plain 21000-gas transfer without logs.
#guard Trie.indexedRoot keccak (block1.transactions.zipIdx.map fun (tx, i) =>
    Block.receiptEncode tx.typeByte { succeeded := true, cumulativeGasUsed := 21000 * (i + 1),
                                      bloom := Bytes.zeros 256, logs := #[] }) =
  block1.header.receiptRoot
#guard Block.logsBloom keccak #[] == block1.header.bloom

/-! ## Sender recovery (secp256k1) for all four transaction types -/

#guard block1.transactions.all fun tx => Tx.resolveSender Crypto.real tx none = .ok sender

/-! ## End to end: `state_transition` of block 1 (needs the interpreter) -/

/-- Import block 1 on top of the genesis, recovering senders from signatures. -/
def imported : Except Block.BlockError (Block.ChainHead × Array Receipt) :=
  Block.stateTransition (2 ^ 40) Crypto.real .cancun 1
    (Block.genesisHead keccak genesisBlock.header pre) block1 []

#guard match imported with
  | .ok (head, receipts) =>
    head.hash = hw "0x6243e029fb6bfef5226d2688cf5c880984a97c28ab9889a7dfae09c9c42eacfa" &&
      decide (head.world = post) && receipts.size = 4
  | .error _ => false

end EvmLeanTest.TxIntegration
