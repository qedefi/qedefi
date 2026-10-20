import EvmLean.Fork

/-!
# Opcodes

The instruction set and its byte encoding. Decoding is total: unassigned bytes (and opcodes
not yet active in the fork) decode to `invalid`.
-/

namespace EvmLean

set_option linter.missingDocs false in
/-- EVM instructions (lower-cased mnemonics); `push n` is `PUSHn`, `dup n` is `DUP(n+1)`. -/
inductive Opcode where
  | stop | add | mul | sub | div | sdiv | mod | smod | addmod | mulmod | exp | signextend
  | lt | gt | slt | sgt | eq | iszero | and | or | xor | not | byte | shl | shr | sar | clz
  | keccak256
  | address | balance | origin | caller | callvalue | calldataload | calldatasize
  | calldatacopy | codesize | codecopy | gasprice | extcodesize | extcodecopy
  | returndatasize | returndatacopy | extcodehash
  | blockhash | coinbase | timestamp | number | prevrandao | gaslimit | chainid
  | selfbalance | basefee | blobhash | blobbasefee
  | pop | mload | mstore | mstore8 | sload | sstore | jump | jumpi | pc | msize | gas
  | jumpdest | tload | tstore | mcopy
  | push (n : Fin 33)
  | dup (n : Fin 16)
  | swap (n : Fin 16)
  | log (n : Fin 5)
  | create | call | callcode | «return» | delegatecall | create2 | staticcall | revert
  | invalid | selfdestruct
  deriving DecidableEq, Repr, Inhabited

namespace Opcode

/-- Number of immediate bytes following the opcode (non-zero only for `PUSH1`–`PUSH32`). -/
def immediateSize : Opcode → Nat
  | push n => n.val
  | _ => 0

/-- Decode a byte. Opcodes introduced after `fork` decode to `invalid`. -/
def decode (fork : Fork) (b : UInt8) : Opcode :=
  match b with
  | 0x00 => stop | 0x01 => add | 0x02 => mul | 0x03 => sub | 0x04 => div | 0x05 => sdiv
  | 0x06 => mod | 0x07 => smod | 0x08 => addmod | 0x09 => mulmod | 0x0a => exp
  | 0x0b => signextend
  | 0x10 => lt | 0x11 => gt | 0x12 => slt | 0x13 => sgt | 0x14 => eq | 0x15 => iszero
  | 0x16 => and | 0x17 => or | 0x18 => xor | 0x19 => not | 0x1a => byte | 0x1b => shl
  | 0x1c => shr | 0x1d => sar
  | 0x1e => if fork ≥ .osaka then clz else invalid
  | 0x20 => keccak256
  | 0x30 => address | 0x31 => balance | 0x32 => origin | 0x33 => caller
  | 0x34 => callvalue | 0x35 => calldataload | 0x36 => calldatasize | 0x37 => calldatacopy
  | 0x38 => codesize | 0x39 => codecopy | 0x3a => gasprice | 0x3b => extcodesize
  | 0x3c => extcodecopy | 0x3d => returndatasize | 0x3e => returndatacopy
  | 0x3f => extcodehash
  | 0x40 => blockhash | 0x41 => coinbase | 0x42 => timestamp | 0x43 => number
  | 0x44 => prevrandao | 0x45 => gaslimit | 0x46 => chainid | 0x47 => selfbalance
  | 0x48 => basefee | 0x49 => blobhash | 0x4a => blobbasefee
  | 0x50 => pop | 0x51 => mload | 0x52 => mstore | 0x53 => mstore8 | 0x54 => sload
  | 0x55 => sstore | 0x56 => jump | 0x57 => jumpi | 0x58 => pc | 0x59 => msize
  | 0x5a => gas | 0x5b => jumpdest | 0x5c => tload | 0x5d => tstore | 0x5e => mcopy
  | 0xf0 => create | 0xf1 => call | 0xf2 => callcode | 0xf3 => «return»
  | 0xf4 => delegatecall | 0xf5 => create2 | 0xfa => staticcall | 0xfd => revert
  | 0xfe => invalid | 0xff => selfdestruct
  | b =>
    if h : 0x5f ≤ b.toNat ∧ b.toNat ≤ 0x7f then push ⟨b.toNat - 0x5f, by omega⟩
    else if h : 0x80 ≤ b.toNat ∧ b.toNat ≤ 0x8f then dup ⟨b.toNat - 0x80, by omega⟩
    else if h : 0x90 ≤ b.toNat ∧ b.toNat ≤ 0x9f then swap ⟨b.toNat - 0x90, by omega⟩
    else if h : 0xa0 ≤ b.toNat ∧ b.toNat ≤ 0xa4 then log ⟨b.toNat - 0xa0, by omega⟩
    else invalid

/-- The byte encoding of an opcode (`invalid` encodes as the designated `0xfe`). -/
def toByte : Opcode → UInt8
  | stop => 0x00 | add => 0x01 | mul => 0x02 | sub => 0x03 | div => 0x04 | sdiv => 0x05
  | mod => 0x06 | smod => 0x07 | addmod => 0x08 | mulmod => 0x09 | exp => 0x0a
  | signextend => 0x0b
  | lt => 0x10 | gt => 0x11 | slt => 0x12 | sgt => 0x13 | eq => 0x14 | iszero => 0x15
  | and => 0x16 | or => 0x17 | xor => 0x18 | not => 0x19 | byte => 0x1a | shl => 0x1b
  | shr => 0x1c | sar => 0x1d | clz => 0x1e
  | keccak256 => 0x20
  | address => 0x30 | balance => 0x31 | origin => 0x32 | caller => 0x33
  | callvalue => 0x34 | calldataload => 0x35 | calldatasize => 0x36 | calldatacopy => 0x37
  | codesize => 0x38 | codecopy => 0x39 | gasprice => 0x3a | extcodesize => 0x3b
  | extcodecopy => 0x3c | returndatasize => 0x3d | returndatacopy => 0x3e
  | extcodehash => 0x3f
  | blockhash => 0x40 | coinbase => 0x41 | timestamp => 0x42 | number => 0x43
  | prevrandao => 0x44 | gaslimit => 0x45 | chainid => 0x46 | selfbalance => 0x47
  | basefee => 0x48 | blobhash => 0x49 | blobbasefee => 0x4a
  | pop => 0x50 | mload => 0x51 | mstore => 0x52 | mstore8 => 0x53 | sload => 0x54
  | sstore => 0x55 | jump => 0x56 | jumpi => 0x57 | pc => 0x58 | msize => 0x59
  | gas => 0x5a | jumpdest => 0x5b | tload => 0x5c | tstore => 0x5d | mcopy => 0x5e
  | push n => (0x5f + n.val).toUInt8
  | dup n => (0x80 + n.val).toUInt8
  | swap n => (0x90 + n.val).toUInt8
  | log n => (0xa0 + n.val).toUInt8
  | create => 0xf0 | call => 0xf1 | callcode => 0xf2 | «return» => 0xf3
  | delegatecall => 0xf4 | create2 => 0xf5 | staticcall => 0xfa | revert => 0xfd
  | invalid => 0xfe | selfdestruct => 0xff

end Opcode

end EvmLean
