import EvmLeanTest.InterpreterUtil

/-!
# Interpreter unit tests: single-frame execution

Hand-assembled programs run through `processMessageCallWith` with the FAKE test crypto and
test precompiles (see `EvmLeanTest.InterpreterUtil`). Gas figures are computed by hand from
the Cancun schedule.
-/

open EvmLean EvmLean.Interpreter EvmLean.Test

namespace EvmLean.Test.InterpreterBasic

/-- Run `prog` followed by `retTop`, returning the output word. -/
def evalTop (prog : List Asm) (ctx : Context := ctx0) : Word :=
  outWord (runCode (asm (prog ++ retTop)) (ctx := ctx))

/-! ## Jump destination analysis -/

#guard validJumpDests (asm [.op .jumpdest]) = #[true]
-- A JUMPDEST byte inside PUSH1 data is not a destination; the one after it is.
#guard validJumpDests ⟨#[0x60, 0x5b, 0x5b]⟩ = #[false, false, true]
-- PUSH32 data hides 32 bytes, including JUMPDEST bytes.
#guard validJumpDests (asm [.pushN 32 0x5b5b5b, .op .jumpdest]) =
  (Array.replicate 33 false).push true
-- Truncated PUSH at the end of the code.
#guard validJumpDests ⟨#[0x5b, 0x62, 0x5b]⟩ = #[true, false, false]
-- PUSH0 has no immediate.
#guard validJumpDests ⟨#[0x5f, 0x5b]⟩ = #[false, true]
#guard isValidJumpDest #[true] (2 ^ 70) = false

/-! ## Arithmetic and gas -/

#guard evalTop [.push 2, .push 3, .op .add] = 5
#guard stackAfter (asm [.push 2, .push 3, .op .add]) 3 = some [5]
#guard stackAfter (asm [.push 2, .push 3]) 2 = some [3, 2]
-- PUSH1 2, PUSH1 3, ADD, PUSH0, MSTORE (3 + 3 memory), PUSH1 32, PUSH0, RETURN
#guard gasUsed 1000000 (runCode (asm ([.push 2, .push 3, .op .add] ++ retTop))) = some 22
#guard evalTop [.push 3, .push 10, .op .sub] = 7
#guard evalTop [.push 10, .push 3, .op .sub] = -7
#guard evalTop [.push 2, .push 10, .op .div] = 5
#guard evalTop [.push 0, .push 10, .op .div] = 0
#guard evalTop [.push 3, .push 10, .op .mod] = 1
#guard evalTop [.push 3, .push 2, .op .exp] = 8
#guard gasUsed 1000000 (runCode (asm [.push 3, .push 2, .op .exp])) = some (3 + 3 + 60)
#guard evalTop [.push 3, .push 10, .push 0, .op .sub, .op .sdiv] = -3
#guard evalTop [.push 1, .push 4, .op .shl] = 16
#guard evalTop [.push 2, .push 1, .op .lt] = 1
#guard evalTop [.push 0x1234, .push 31, .op .byte] = 0x34
#guard evalTop [.push 0xff, .push 0, .op .signextend] = -1
#guard evalTop [.push 7, .push 5, .push 4, .op .addmod] = 2
#guard evalTop [.push 0, .op .iszero] = 1
#guard evalTop [.push 0, .op .not] = -1
#guard evalTop [.push 1, .push 2, .push 3, .op (.dup 2)] = 1
#guard evalTop [.push 1, .push 2, .push 3, .op (.swap 1), .op .pop, .op .pop] = 3

/-! ## Memory -/

-- MSTORE at 0x10000: memory grows to 2049 words, cost 3·2049 + 2049²/512 = 14347.
#guard gasUsed 1000000 (runCode (asm [.push 1, .push 0x10000, .op .mstore])) =
  some (3 + 3 + 3 + 14347)
#guard evalTop [.push 1, .push 0x10000, .op .mstore, .op .msize] = 65568
#guard evalTop [.push 0xab, .push 31, .op .mstore8, .push 0, .op .mload] = 0xab
-- Huge offsets run out of gas without allocating.
#guard errorOf (runCode (asm [.push 1, .push (2 ^ 200), .op .mstore])) = some .outOfGas
#guard (runCode (asm [.push 1, .push (2 ^ 200), .op .mstore])).map (·.gasLeft) = some 0
#guard errorOf (runCode (asm [.push (2 ^ 256 - 1), .op .mload])) = some .outOfGas
-- Zero-length accesses never expand memory, whatever the offset.
#guard (runCode (asm [.push 0, .push (2 ^ 255), .op .«return»])).map
  (fun r => (r.success, r.output.size, 1000000 - r.gasLeft)) = some (true, 0, 2 + 3)
#guard evalTop [.push 0, .push (2 ^ 255), .push (2 ^ 255), .op .mcopy, .op .msize] = 0
-- MCOPY (EIP-5656)
#guard evalTop [.push 0x1122, .push 0, .op .mstore, .push 32, .push 0, .push 32, .op .mcopy,
  .push 32, .op .mload] = 0x1122
-- Overlapping MCOPY reads before writing.
#guard evalTop [.push 0x1122, .push 0, .op .mstore, .push 32, .push 0, .push 1, .op .mcopy,
  .push 1, .op .mload] = 0x1122

/-! ## Control flow and exceptional halts -/

-- Jump into PUSH data (byte 4 is the immediate 0x5b of PUSH1).
#guard errorOf (runCode (asm [.push 4, .op .jump, .pushN 1 0x5b, .op .stop])) =
  some .invalidJumpDestination
#guard (runCode (asm [.push 4, .op .jump, .pushN 1 0x5b, .op .stop])).map (·.gasLeft) = some 0
-- A real JUMPDEST.
#guard evalTop [.push 4, .op .jump, .op .invalid, .op .jumpdest, .push 9] = 9
-- JUMPI falls through on zero, jumps otherwise.
#guard evalTop [.push 0, .push 0xff, .op .jumpi, .push 1] = 1
#guard succeeded (runCode (asm [.push 1, .push 8, .op .jumpi, .op .invalid, .op .invalid,
  .op .invalid, .op .jumpdest]))
#guard errorOf (runCode (asm [.push 1, .push 100, .op .jumpi])) = some .invalidJumpDestination
-- Stack underflow / overflow.
#guard errorOf (runCode (asm [.op .add])) = some .stackUnderflow
#guard errorOf (runCode (asm [.push 1, .op (.dup 1)])) = some .stackUnderflow
#guard errorOf (runCode (asm [.push 1, .op (.swap 0)])) = some .stackUnderflow
#guard errorOf (runCode ⟨Array.replicate 1025 0x5f⟩) = some .stackOverflow
#guard gasUsed 1000000 (runCode ⟨Array.replicate 1024 0x5f⟩) = some 2048
-- Out of gas in an infinite loop.
#guard errorOf (runCode (asm [.op .jumpdest, .push 0, .op .jump]) (gas := 1000)) =
  some .outOfGas
-- Invalid and unassigned opcodes.
#guard errorOf (runCode (asm [.op .invalid])) = some .invalidOpcode
#guard errorOf (runCode ⟨#[0x0c]⟩) = some .invalidOpcode
-- CLZ (0x1e) is invalid in Cancun and active in Osaka.
#guard errorOf (runCode (asm [.push 1, .raw [0x1e]])) = some .invalidOpcode
#guard evalTop [.push 1, .raw [0x1e]] { ctx0 with fork := .osaka } = 255
-- Running off the end of the code is STOP.
#guard (runCode (asm [.push 1])).map (fun r => (r.success, r.output.size)) = some (true, 0)
-- Insufficient gas for the first instruction.
#guard errorOf (runCode (asm [.push 1]) (gas := 2)) = some .outOfGas

/-! ## Environment -/

#guard evalTop [.op .address] = Word.ofAddress contract
#guard evalTop [.op .caller] = Word.ofAddress sender
#guard evalTop [.op .origin] = 0
#guard evalTop [.op .selfbalance] = 1000
#guard evalTop [.push contract.toNat, .op .balance] = 1000
#guard evalTop [.op .codesize] = 7
-- BALANCE of a cold account costs 2600, then 100 once warm.
#guard gasUsed 1000000 (runCode (asm [.push other.toNat, .op .balance,
  .push other.toNat, .op .balance])) = some (3 + 2600 + 3 + 100)
#guard evalTop [.push 0xdead, .op .extcodehash] = 0
#guard evalTop [.push other.toNat, .op .extcodesize] = 0
#guard evalTop [.op .gas] = BitVec.ofNat 256 (1000000 - 2)
#guard evalTop [.op .pc, .op .pc] = 1
#guard evalTop [.push 4, .push 0, .push 0, .op .codecopy, .push 0, .op .mload] =
  BitVec.ofNat 256 (0x6004 * 2 ^ 240 + 0x5f5f * 2 ^ 224)

-- Calldata
#guard outWord (runMsg (mkWorld (asm ([.push 1, .op .calldataload] ++ retTop)))
  (callMsg contract (asm ([.push 1, .op .calldataload] ++ retTop)) (data := ⟨#[1, 2, 3]⟩))) =
  BitVec.ofNat 256 (0x0203 * 2 ^ 240)
#guard outWord (runMsg (mkWorld (asm ([.op .calldatasize] ++ retTop)))
  (callMsg contract (asm ([.op .calldatasize] ++ retTop)) (data := ⟨#[1, 2, 3]⟩))) = 3

-- EXTCODEHASH of an existing account is the (here: FAKE) hash of its code.
#guard evalTop [.push contract.toNat, .op .extcodehash] =
  fakeKeccak (asm ([.push contract.toNat, .op .extcodehash] ++ retTop))
-- KECCAK256 hashes memory through `ctx.crypto`.
#guard evalTop [.push 0x77, .push 0, .op .mstore, .push 32, .push 0, .op .keccak256] =
  fakeKeccak (Bytes.ofWord 0x77)

-- Block environment
/-- A block context at number 300 with 256 known ancestor hashes. -/
def blockCtx : Context :=
  { ctx0 with
    block := { number := 300, blockHashes := (List.range 256).map fun i => BitVec.ofNat 256 (1000 + i),
               excessBlobGas := 33384770, timestamp := 12345, chainId := 7, baseFee := 9 }
    tx := { blobVersionedHashes := #[0xaa, 0xbb], gasPrice := 11 } }
#guard evalTop [.push 299, .op .blockhash] blockCtx = 1000
#guard evalTop [.push 44, .op .blockhash] blockCtx = 1255
#guard evalTop [.push 43, .op .blockhash] blockCtx = 0
#guard evalTop [.push 300, .op .blockhash] blockCtx = 0
#guard evalTop [.push 1, .op .blobhash] blockCtx = 0xbb
#guard evalTop [.push 2, .op .blobhash] blockCtx = 0
#guard evalTop [.op .blobbasefee] blockCtx = 22026
#guard evalTop [.op .blobbasefee] = 1
#guard evalTop [.op .timestamp] blockCtx = 12345
#guard evalTop [.op .chainid] blockCtx = 7
#guard evalTop [.op .basefee] blockCtx = 9
#guard evalTop [.op .gasprice] blockCtx = 11
#guard evalTop [.op .number] blockCtx = 300

/-! ## Storage -/

/-- Run `prog` as `contract` with slot 0 initially `orig` and pre-warmed; return
(gas used, refund counter). -/
def sstoreCase (orig : Nat) (prog : List Asm) : Option (Nat × Int) :=
  let code := asm prog
  let w := mkWorld code [(contract, { nonce := 1, balance := 1000, code,
                                       storage := Storage.set ∅ 0 (BitVec.ofNat 256 orig) })]
  let msg := callMsg contract code (warmKeys := addStorageKey ∅ contract 0)
  (runMsg w msg).map fun r => (1000000 - r.gasLeft, r.refundCounter)

/-- `SSTORE` values `vs` into slot 0 in sequence. -/
def stores (vs : List Nat) : List Asm := vs.flatMap fun v => [.push v, .push 0, .op .sstore]

-- The EIP-3529 test table (slot pre-warmed; `PUSH1` encoding).
/-- Like `stores`, but always with `PUSH1` (as in the EIP's bytecode). -/
def stores1 (vs : List Nat) : List Asm := vs.flatMap fun v => [.pushN 1 v, .pushN 1 0, .op .sstore]
#guard sstoreCase 0 (stores1 [0, 0]) = some (212, 0)
#guard sstoreCase 0 (stores1 [0, 1]) = some (20112, 0)
#guard sstoreCase 0 (stores1 [1, 0]) = some (20112, 19900)
#guard sstoreCase 0 (stores1 [1, 2]) = some (20112, 0)
#guard sstoreCase 0 (stores1 [1, 1]) = some (20112, 0)
#guard sstoreCase 1 (stores1 [0, 0]) = some (3012, 4800)
#guard sstoreCase 1 (stores1 [0, 1]) = some (3012, 2800)
#guard sstoreCase 1 (stores1 [0, 2]) = some (3012, 0)
#guard sstoreCase 1 (stores1 [2, 0]) = some (3012, 4800)
#guard sstoreCase 1 (stores1 [2, 3]) = some (3012, 0)
#guard sstoreCase 1 (stores1 [2, 1]) = some (3012, 2800)
#guard sstoreCase 1 (stores1 [2, 2]) = some (3012, 0)
#guard sstoreCase 1 (stores1 [1, 0]) = some (3012, 4800)
#guard sstoreCase 1 (stores1 [1, 2]) = some (3012, 0)
#guard sstoreCase 1 (stores1 [1, 1]) = some (212, 0)
#guard sstoreCase 0 (stores1 [1, 0, 1]) = some (40118, 19900)
#guard sstoreCase 1 (stores1 [0, 1, 0]) = some (5918, 7600)

-- Cold slot: +2100.
#guard (runCode (asm (stores [1]))).map (1000000 - ·.gasLeft) = some (3 + 2 + 22100)
#guard slot (runCode (asm (stores [5]))) contract 0 = some 5
#guard evalTop (stores [5] ++ [.push 0, .op .sload]) = 5
-- EIP-2200 sentry: SSTORE needs strictly more than 2300 gas left.
/-- `SSTORE 1 → slot 0` (slot already 1, warm) with `gas` available. -/
def sentry (gas : Nat) : Option MessageResult :=
  let code := asm (stores [1])
  let w := mkWorld code [(contract, { nonce := 1, balance := 1000, code,
                                       storage := Storage.set ∅ 0 1 })]
  runMsg w (callMsg contract code gas (warmKeys := addStorageKey ∅ contract 0))
#guard errorOf (sentry (2300 + 5)) = some .outOfGas
#guard succeeded (sentry (2300 + 6))
-- Static context
#guard errorOf (runMsg (mkWorld (asm (stores [1]))) (callMsg contract (asm (stores [1]))
  (isStatic := true))) = some .writeInStaticContext

-- Transient storage (EIP-1153)
#guard evalTop [.push 42, .push 7, .op .tstore, .push 7, .op .tload] = 42
#guard (runCode (asm [.push 42, .push 7, .op .tstore])).map
  (fun r => getTransient r.transientStorage contract 7) = some 42
#guard errorOf (runMsg (mkWorld (asm [.push 42, .push 7, .op .tstore]))
  (callMsg contract (asm [.push 42, .push 7, .op .tstore]) (isStatic := true))) =
  some .writeInStaticContext

/-! ## Logs, return, revert -/

#guard (runCode (asm [.push 0xaa, .push 0, .op .mstore, .push 0x77, .push 32, .push 0,
    .op (.log 1)])).map (·.logs) =
  some #[{ address := contract, topics := #[0x77], data := Bytes.ofWord 0xaa }]
-- LOG2 gas: 375 + 2·375 + 8·32, plus pushes and memory.
#guard gasUsed 1000000 (runCode (asm [.push 1, .push 2, .push 32, .push 0, .op (.log 2)])) =
  some (3 + 3 + 3 + 2 + 375 + 750 + 256 + 3)
#guard errorOf (runMsg (mkWorld (asm [.push 0, .push 0, .op (.log 0)]))
  (callMsg contract (asm [.push 0, .push 0, .op (.log 0)]) (isStatic := true))) =
  some .writeInStaticContext

/-- Store 1 in slot 0, then revert with 0xdead. -/
def revertProg : List Asm :=
  stores [1] ++ [.push 0xdead, .push 0, .op .mstore, .push 32, .push 0, .op .revert]
#guard (runCode (asm revertProg)).map (fun r => (r.success, r.reverted, r.error.isNone)) =
  some (false, true, true)
#guard outWord (runCode (asm revertProg)) = 0xdead
#guard slot (runCode (asm revertProg)) contract 0 = some 0
-- REVERT keeps the remaining gas.
#guard gasUsed 1000000 (runCode (asm revertProg)) = some (3 + 2 + 22100 + 3 + 2 + 6 + 3 + 2)
#guard (runCode (asm revertProg)).map (·.refundCounter) = some 0
-- RETURNDATACOPY beyond the buffer halts exceptionally (EIP-211).
#guard errorOf (runCode (asm [.push 1, .push 0, .push 0, .op .returndatacopy])) =
  some .returnDataOutOfBounds
#guard succeeded (runCode (asm [.push 0, .push 0, .push 0, .op .returndatacopy]))

/-! ## Top-level special cases -/

-- A top-level call to a precompile runs it directly.
#guard (runMsg (mkWorld .empty) (callMsg 4 .empty (data := ⟨#[1, 2, 3]⟩))).map
  (fun r => (r.output, 1000000 - r.gasLeft)) = some (⟨#[1, 2, 3]⟩, 18)
#guard errorOf (runMsg (mkWorld .empty) (callMsg 1 .empty)) = some .precompileFailure
-- Unaffordable value.
#guard errorOf (runMsg (mkWorld .empty) (callMsg contract .empty (value := 2 ^ 40))) =
  some .insufficientFunds
-- Value is transferred to the callee.
#guard (runMsg (mkWorld .empty) (callMsg other .empty (value := 77))).map
  (·.world.balance other) = some 77
-- Fuel exhaustion is not an EVM outcome.
#guard (processMessageCallWith testPrecompiles 10 ctx0 (mkWorld .empty)
  ∅ (callMsg contract (asm [.op .jumpdest, .push 0, .op .jump]))).toOption.isNone

end EvmLean.Test.InterpreterBasic
