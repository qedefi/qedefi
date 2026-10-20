import EvmTest.InterpreterUtil

/-!
# Interpreter unit tests: calls, creation, self-destruct

`contract` (A) calls or creates; `other` (B) and `third` (C) are callees. Hashes are fake
(`fakeKeccak`).
-/

open EvmLean EvmLean.Interpreter EvmTest EvmTest.InterpreterUtil

namespace EvmTest.InterpreterCall
open EvmLean EvmTest.InterpreterUtil

/-- `CALL(gas, to, value, inOff, inSize, outOff, outSize)`. -/
def callAsm (gas : Nat) (to : Address) (value inOff inSize outOff outSize : Nat) : List Asm :=
  [.push outSize, .push outOff, .push inSize, .push inOff, .push value, .push to.toNat,
   .push gas, .op .call]

/-- A value-less call opcode (`DELEGATECALL`, `STATICCALL`). -/
def call6 (op : Opcode) (gas : Nat) (to : Address) (inOff inSize outOff outSize : Nat) :
    List Asm :=
  [.push outSize, .push outOff, .push inSize, .push inOff, .push to.toNat, .push gas, .op op]

/-- `CALLCODE(gas, to, value, …)`. -/
def callcodeAsm (gas : Nat) (to : Address) (value : Nat) : List Asm :=
  [.push 0, .push 0, .push 0, .push 0, .push value, .push to.toNat, .push gas, .op .callcode]

/-- A contract account with `code`. -/
def acct (code : List Asm) (balance : Word := 0) (storage : Storage := ∅) : Account :=
  { nonce := 1, balance, code := asm code, storage }

/-- Run A's `codeA` with B = `codeB` (and optionally C = `codeC`). -/
def runAB (codeA codeB : List Asm) (codeC : List Asm := []) (gas : Nat := 1000000)
    (value : Word := 0) (bStorage : Storage := ∅) : Option MessageResult :=
  let a := asm codeA
  runMsg (mkWorld a [(other, acct codeB (storage := bStorage)), (third, acct codeC)])
    (callMsg contract a gas value)

/-! ## CALL -/

/-- B records `CALLVALUE` and `CALLER`, then returns `0x42`. -/
def recorder : List Asm :=
  [.op .callvalue] ++ storeTop 0 ++ [.op .caller] ++ storeTop 1 ++ [.push 0x42] ++ retTop

/-- A calls B with value 5, stores the flag and the returned word. -/
def valueCaller : List Asm :=
  callAsm 100000 other 5 0 0 0 32 ++ storeTop 0 ++ [.push 0, .op .mload] ++ storeTop 1

#guard slot (runAB valueCaller recorder) other 0 = some 5
#guard slot (runAB valueCaller recorder) other 1 = some (Word.ofAddress contract)
#guard slot (runAB valueCaller recorder) contract 0 = some 1
#guard slot (runAB valueCaller recorder) contract 1 = some 0x42
#guard (runAB valueCaller recorder).map (fun r => (r.world.balance contract, r.world.balance other)) =
  some (995, 5)

-- Exact gas: a value-less call with zero gas to a cold, non-existent account.
#guard gasUsed 1000000 (runCode (asm (callAsm 0 0xdead 0 0 0 0 0))) = some (10 + 3 + 2 + 2600)
-- With value: + 9000 transfer + 25000 new account; the 2300 stipend comes back unused.
#guard gasUsed 1000000 (runCode (asm (callAsm 0 0xdead 1 0 0 0 0))) =
  some (8 + 3 + 3 + 2 + 36600 - 2300)
#guard (runCode (asm (callAsm 0 0xdead 1 0 0 0 0))).map (·.world.balance 0xdead) = some 1
-- Unused child gas is returned: B spends 5 of 1000.
#guard gasUsed 1000000 (runAB (callAsm 1000 other 0 0 0 0 0) [.push 1, .op .pop]) =
  some (16 + 2600 + 5)
-- EIP-150: a child asking for everything gets all but 1/64 of what is left after the
-- access cost (2600) and the output window's memory (3): 999983 − 2603 = 997380, minus
-- 997380/64 = 15584, gives 981796; GAS then reports 981794.
#guard outWord (runAB (callAsm (2 ^ 255) other 0 0 0 0 32 ++ [.push 0, .op .mload] ++ retTop)
  ([.op .gas] ++ retTop)) = 981794

-- Insufficient balance: flag 0, nothing executed, the call gas (with stipend) returned.
#guard outWord (runCode (asm (callAsm 0 0xdead 2000 0 0 0 0 ++ retTop))) = 0
#guard gasUsed 1000000 (runCode (asm (callAsm 0 0xdead 2000 0 0 0 0))) =
  some (8 + 3 + 3 + 2 + 36600 - 2300)
#guard (runCode (asm (callAsm 0 0xdead 2000 0 0 0 0))).map (·.world.contains 0xdead) =
  some false

-- Call depth: at depth 1024 a call pushes 0 without running; at 1023 it runs.
/-- Run `callAsm … ++ retTop` as a message at `depth`. -/
def atDepth (depth : Nat) : Option MessageResult :=
  let code := asm (callAsm 1000 other 0 0 0 0 0 ++ retTop)
  runMsg (mkWorld code [(other, acct [.op .stop])]) (callMsg contract code (depth := depth))
#guard outWord (atDepth 1024) = 0
#guard outWord (atDepth 1023) = 1
-- At the depth limit the call gas is returned (only the access cost is spent).
#guard (atDepth 1024).map (1000000 - ·.gasLeft) = some (16 + 2600 + 3 + 2 + 3 + 3 + 2)

/-! ## CALLCODE and DELEGATECALL -/

/-- B records `CALLER`, `CALLVALUE`, `ADDRESS` into slots 0–2. -/
def contextRecorder : List Asm :=
  [.op .caller] ++ storeTop 0 ++ [.op .callvalue] ++ storeTop 1 ++ [.op .address] ++ storeTop 2

-- DELEGATECALL keeps caller, value and storage of A.
#guard (runAB (call6 .delegatecall 100000 other 0 0 0 0 ++ storeTop 3) contextRecorder
    (value := 7)).map (fun r => [r.world.sload contract 0, r.world.sload contract 1,
      r.world.sload contract 2, r.world.sload contract 3, r.world.sload other 0]) =
  some [Word.ofAddress sender, 7, Word.ofAddress contract, 1, 0]
-- CALLCODE runs B's code on A's storage with A as caller.
#guard (runAB (callcodeAsm 100000 other 3) contextRecorder).map (fun r =>
    [r.world.sload contract 0, r.world.sload contract 1, r.world.sload contract 2,
     r.world.balance contract]) =
  some [Word.ofAddress contract, 3, Word.ofAddress contract, 1000]

/-! ## STATICCALL -/

#guard outWord (runAB (call6 .staticcall 100000 other 0 0 0 0 ++ retTop) (stores [1])) = 0
#guard slot (runAB (call6 .staticcall 100000 other 0 0 0 0 ++ retTop) (stores [1])) other 0 =
  some 0
-- The failed static child consumed all its gas.
#guard ((gasUsed 1000000 (runAB (call6 .staticcall 100000 other 0 0 0 0) (stores [1]))).map
  (fun x => decide (x > 100000))).getD false
#guard outWord (runAB (call6 .staticcall 100000 other 0 0 0 0 ++ retTop)
  [.push 0, .op .sload, .op .pop]) = 1
-- A value-bearing CALL inside a static context halts the callee.
#guard outWord (runAB (call6 .staticcall 100000 other 0 0 0 0 ++ retTop)
  (callAsm 0 third 1 0 0 0 0)) = 0
-- Staticness is inherited: B (static) calls C, whose SSTORE fails; B itself succeeds.
#guard (runAB (call6 .staticcall 100000 other 0 0 0 32 ++ [.push 0, .op .mload] ++ storeTop 5
    ++ retTop) (callAsm 50000 third 0 0 0 0 0 ++ retTop) (stores [1])).map
  (fun r => (Bytes.toWord r.output, r.world.sload contract 5, r.world.sload third 0)) =
  some (1, 0, 0)

/-! ## REVERT and exceptional halts in children -/

/-- B writes slot 0, then reverts with `0xbeef`. -/
def reverter : List Asm :=
  stores [1] ++ [.push 0xbeef, .push 0, .op .mstore, .push 32, .push 0, .op .revert]

/-- A calls B, records flag, `RETURNDATASIZE` and the output window. -/
def observer : List Asm :=
  callAsm 100000 other 0 0 0 0 32 ++ storeTop 0 ++ [.op .returndatasize] ++ storeTop 1
    ++ [.push 0, .op .mload] ++ storeTop 2

#guard (runAB observer reverter).map (fun r =>
    [r.world.sload contract 0, r.world.sload contract 1, r.world.sload contract 2,
     r.world.sload other 0]) = some [0, 32, 0xbeef, 0]
-- REVERT returns the child's unused gas.
#guard ((gasUsed 1000000 (runAB observer reverter)).map (fun x => decide (x < 100000))).getD false
-- An exceptional halt consumes all the child's gas and leaves no return data.
#guard (runAB observer [.op .invalid]).map (fun r =>
    [r.world.sload contract 0, r.world.sload contract 1]) = some [0, 0]
#guard ((gasUsed 1000000 (runAB observer [.op .invalid])).map (fun x => decide (x > 100000))).getD false
-- RETURNDATACOPY of the child's revert data.
#guard outWord (runAB (callAsm 100000 other 0 0 0 0 0 ++ [.op .pop, .push 32, .push 0, .push 0,
  .op .returndatacopy, .push 0, .op .mload] ++ retTop) reverter) = 0xbeef

-- Child logs and refunds are kept on success and dropped on failure.
#guard (runAB (callAsm 100000 other 0 0 0 0 0) [.push 0, .push 0, .op (.log 0)]).map
  (·.logs) = some #[{ address := other, topics := #[], data := .empty }]
#guard (runAB (callAsm 100000 other 0 0 0 0 0) [.push 0, .push 0, .op (.log 0), .op .invalid]).map
  (·.logs.size) = some 0
#guard (runAB (callAsm 100000 other 0 0 0 0 0) (stores [0]) (bStorage := Storage.set ∅ 0 1)).map
  (·.refundCounter) = some 4800
#guard (runAB (callAsm 100000 other 0 0 0 0 0) (stores [0] ++ [.push 0, .push 0, .op .revert])
  (bStorage := Storage.set ∅ 0 1)).map (·.refundCounter) = some 0
-- Warm accounts of a successful child stay warm in the parent; of a failed one, not.
#guard gasUsed 1000000 (runAB (callAsm 100000 other 0 0 0 0 0 ++ [.op .pop,
    .push third.toNat, .op .balance]) [.push third.toNat, .op .balance]) =
  some (16 + 2600 + (3 + 2600) + 2 + 3 + 100)
#guard gasUsed 1000000 (runAB (callAsm 100000 other 0 0 0 0 0 ++ [.op .pop,
    .push third.toNat, .op .balance]) [.push third.toNat, .op .balance, .push 0, .push 0,
    .op .revert]) =
  some (16 + 2600 + (3 + 2600 + 2 + 2) + 2 + 3 + 2600)

/-! ## Precompiles -/

#guard outWord (runCode (asm ([.push 0x1234, .push 0, .op .mstore] ++ callAsm 10000 4 0 0 32 32 32
  ++ [.op .pop, .push 32, .op .mload] ++ retTop))) = 0x1234
#guard outWord (runCode (asm (callAsm 10000 1 0 0 0 0 0 ++ retTop))) = 0
-- A failing precompile consumes the gas it was given.
#guard gasUsed 1000000 (runCode (asm (callAsm 10000 1 0 0 0 0 0))) = some (16 + 100 + 10000)
-- Value sent to a precompile is transferred.
#guard (runCode (asm (callAsm 10000 4 5 0 0 0 0))).map (·.world.balance 4) = some 5

/-! ## EIP-161 touched accounts -/

-- A successful call to an existing empty account touches it.
#guard (runMsg (mkWorld (asm (callAsm 0 other 0 0 0 0 0)) [(other, {})])
  (callMsg contract (asm (callAsm 0 other 0 0 0 0 0)))).map
  (·.touchedAccounts.contains other) = some true
#guard (runMsg (mkWorld .empty [(other, {})]) (callMsg other .empty)).map
  (·.touchedAccounts.contains other) = some true
-- RIPEMD-160 quirk: a failed call to an empty account at 0x03 still touches it.
#guard (runMsg (mkWorld (asm (callAsm 0 3 0 0 0 0 0)) [(3, {})])
  (callMsg contract (asm (callAsm 0 3 0 0 0 0 0)))).map
  (·.touchedAccounts.contains 3) = some true
#guard (runMsg (mkWorld (asm (callAsm 0 1 0 0 0 0 0)) [(1, {})])
  (callMsg contract (asm (callAsm 0 1 0 0 0 0 0)))).map
  (·.touchedAccounts.contains 1) = some false

/-! ## CREATE and CREATE2 -/

/-- Runtime code: return the word `0x42`. -/
def runtime : ByteArray := asm ([.push 0x42] ++ retTop)
/-- Init code: return `runtime` (8 bytes). -/
def initCode : ByteArray :=
  asm [.pushN 8 (Bytes.toNat runtime), .push 0, .op .mstore, .push 8, .push 24, .op .«return»]

#guard runtime.size = 8
#guard initCode.size = 16

/-- Put `code` (≤ 32 bytes) in memory right-aligned in word 0 and `CREATE` it with
`value`. -/
def createAsm (code : ByteArray) (value : Nat := 0) : List Asm :=
  [.pushN code.size (Bytes.toNat code), .push 0, .op .mstore, .push code.size,
   .push (32 - code.size), .push value, .op .create]

/-- As `createAsm`, with `CREATE2` and `salt`. -/
def create2Asm (code : ByteArray) (salt : Nat) : List Asm :=
  [.pushN code.size (Bytes.toNat code), .push 0, .op .mstore, .push salt, .push code.size,
   .push (32 - code.size), .push 0, .op .create2]

/-- Address of A's first `CREATE`. -/
def created : Address := createAddress fakeKeccak contract 1

#guard slot (runCode (asm (createAsm initCode ++ storeTop 0))) contract 0 =
  some (Word.ofAddress created)
#guard (runCode (asm (createAsm initCode))).map (fun r =>
    (r.world.code created, (r.world.account created).nonce, (r.world.account contract).nonce)) =
  some (runtime, 1, 2)
-- The created contract can be called.
#guard outWord (runCode (asm (createAsm initCode ++ [.push 64, .op .mstore, .push 32, .push 0,
  .push 0, .push 0, .push 0, .push 64, .op .mload, .push 100000, .op .call, .op .pop, .push 0,
  .op .mload] ++ retTop))) = 0x42
-- Endowment.
#guard (runCode (asm (createAsm initCode 100))).map (fun r =>
  (r.world.balance created, r.world.balance contract)) = some (100, 900)
-- CREATE2 address depends on the salt and the init code.
#guard slot (runCode (asm (create2Asm initCode 7 ++ storeTop 0))) contract 0 =
  some (Word.ofAddress (create2Address fakeKeccak contract 7 initCode))
#guard (runCode (asm (create2Asm initCode 7))).map
  (·.world.code (create2Address fakeKeccak contract 7 initCode)) = some runtime
-- Deterministic address derivation: with "hash" = identity-on-bytes the address is the
-- tail of the preimage, exposing the RLP / CREATE2 layout.
#guard createAddress Bytes.toWord 0xCA11 1 = 0xca1101
#guard createAddress Bytes.toWord 0xCA11 0 = 0xca1180
#guard createAddress Bytes.toWord 0xCA11 0x400 = 0xca11820400
#guard create2Address (fun b => Bytes.toWord (b.extract 0 32)) 0xCA11 0 .empty =
  BitVec.ofNat 160 (Bytes.toNat ((ByteArray.mk #[0xff] ++ Bytes.ofAddress 0xCA11
    ++ Bytes.zeros 11).extract 12 32))

-- Init code that reverts: 0 pushed, creator nonce still incremented, return data kept.
/-- `REVERT` with 32 bytes of data. -/
def revertInit : ByteArray :=
  asm [.push 0xaa, .push 0, .op .mstore, .push 32, .push 0, .op .revert]
#guard (runCode (asm (createAsm revertInit ++ storeTop 0 ++ [.op .returndatasize]
    ++ storeTop 1))).map (fun r => (r.world.sload contract 0, r.world.sload contract 1,
      (r.world.account contract).nonce, r.world.contains created)) =
  some (0, 32, 2, false)
-- EIP-3541: code starting with 0xEF is rejected.
/-- Init code returning the single byte `0xef`. -/
def efInit : ByteArray := asm [.push 0xef, .push 0, .op .mstore8, .push 1, .push 0, .op .«return»]
#guard (runCode (asm (createAsm efInit ++ storeTop 0))).map (fun r =>
  (r.world.sload contract 0, r.world.contains created)) = some (0, false)
-- EIP-170: 24576 bytes of code are fine, 24577 are not.
/-- Init code returning `n` zero bytes. -/
def zerosInit (n : Nat) : ByteArray := asm [.push n, .push 0, .op .«return»]
#guard (runCode (asm (createAsm (zerosInit 24576))) (gas := 10000000)).map
  (·.world.code created |>.size) = some 24576
#guard (runCode (asm (createAsm (zerosInit 24577) ++ storeTop 0)) (gas := 10000000)).map
  (fun r => (r.world.sload contract 0, r.world.contains created)) = some (0, false)
-- Code deposit costs 200 per byte: not enough gas for it fails the creation.
#guard (runCode (asm (createAsm (zerosInit 24576) ++ storeTop 0)) (gas := 4000000)).map
  (·.world.sload contract 0) = some 0
-- EIP-3860: init code above 49152 bytes halts the creator.
#guard errorOf (runCode (asm [.push 49153, .push 0, .push 0, .op .create])) =
  some .initCodeSizeExceeded
#guard (runCode (asm ([.push 49152, .push 0, .push 0, .op .create] ++ storeTop 0))).map
  (·.world.sload contract 0) = some (Word.ofAddress created)
-- Address collision: 0 pushed, nonce incremented, gas consumed.
#guard (runCode (asm (createAsm initCode ++ storeTop 0)) [(created, { nonce := 1 })]).map
  (fun r => (r.world.sload contract 0, (r.world.account contract).nonce)) = some (0, 2)
#guard (runCode (asm (createAsm initCode ++ storeTop 0)) [(created, { storage := Storage.set ∅ 1 1 })]).map
  (·.world.sload contract 0) = some 0
-- Soft failures (nonce at 2⁶⁴−1, unaffordable endowment) keep the nonce and the gas.
#guard (runCode (asm (createAsm initCode ++ storeTop 0))
    [(contract, { nonce := 2 ^ 64 - 1, balance := 1000, code := asm (createAsm initCode ++ storeTop 0) })]).map
  (fun r => (r.world.sload contract 0, (r.world.account contract).nonce)) = some (0, 2 ^ 64 - 1)
#guard (runCode (asm (createAsm initCode 2000 ++ storeTop 0))).map
  (fun r => (r.world.sload contract 0, (r.world.account contract).nonce)) = some (0, 1)
#guard ((gasUsed 1000000 (runCode (asm (createAsm initCode 2000)))).map (fun x => decide (x < 40000))).getD false
-- CREATE in a static context.
#guard errorOf (runMsg (mkWorld (asm (createAsm initCode)))
  (callMsg contract (asm (createAsm initCode)) (isStatic := true))) = some .writeInStaticContext

/-! ## Top-level creation -/

/-- Address of a top-level creation in the tests. -/
def newAddr : Address := 0xAAAA
#guard (runMsg (mkWorld .empty) (createMsg newAddr initCode)).map (fun r =>
  (r.output, r.world.code newAddr, (r.world.account newAddr).nonce, 1000000 - r.gasLeft)) =
  some (runtime, runtime, 1, 3 + 2 + 6 + 3 + 3 + 200 * 8)
#guard errorOf (runMsg (mkWorld .empty [(newAddr, { nonce := 1 })]) (createMsg newAddr initCode)) =
  some .addressCollision
#guard (runMsg (mkWorld .empty [(newAddr, { code := runtime })]) (createMsg newAddr initCode)).map
  (·.gasLeft) = some 0
#guard errorOf (runMsg (mkWorld .empty [(newAddr, { storage := Storage.set ∅ 0 1 })])
  (createMsg newAddr initCode)) = some .addressCollision
-- A pre-funded address is fine; the endowment is added.
#guard (runMsg (mkWorld .empty [(newAddr, { balance := 5 })]) (createMsg newAddr initCode
  (value := 10))).map (·.world.balance newAddr) = some 15
-- Failed top-level creation rolls back the nonce increment.
#guard (runMsg (mkWorld .empty) (createMsg newAddr revertInit)).map (fun r =>
  (r.reverted, r.world.contains newAddr, Bytes.toWord r.output)) = some (true, false, 0xaa)

/-! ## SELFDESTRUCT (EIP-6780) -/

-- A pre-existing contract only moves its balance; nothing is scheduled for deletion.
#guard (runCode (asm [.push other.toNat, .op .selfdestruct])).map (fun r =>
    (r.world.balance other, r.world.balance contract, r.world.code contract == asm [.push other.toNat, .op .selfdestruct],
     r.accountsToDelete.isEmpty)) = some (1000, 0, true, true)
-- Cold, dead beneficiary with value: 5000 + 2600 + 25000.
#guard gasUsed 1000000 (runCode (asm [.push other.toNat, .op .selfdestruct])) = some (3 + 32600)
-- Alive beneficiary: no new-account charge.
#guard gasUsed 1000000 (runCode (asm [.push other.toNat, .op .selfdestruct])
  [(other, { balance := 1 })]) = some (3 + 7600)
#guard errorOf (runMsg (mkWorld (asm [.push other.toNat, .op .selfdestruct]))
  (callMsg contract (asm [.push other.toNat, .op .selfdestruct]) (isStatic := true))) =
  some .writeInStaticContext

/-- Init code that self-destructs to `other`. -/
def sdInit : ByteArray := asm [.push other.toNat, .op .selfdestruct]
-- Created in the same transaction: scheduled for deletion, balance moved.
#guard (runCode (asm (createAsm sdInit 100 ++ storeTop 0))).map (fun r =>
    (r.accountsToDelete.contains created, r.world.balance other, r.world.balance created,
     r.world.sload contract 0)) = some (true, 100, 0, Word.ofAddress created)
-- Self-beneficiary of an account created in the transaction burns the balance.
#guard (runCode (asm (createAsm (asm [.op .address, .op .selfdestruct]) 100))).map (fun r =>
    (r.accountsToDelete.contains created, r.world.balance created)) = some (true, 0)
-- A top-level creation that self-destructs.
#guard (runMsg (mkWorld .empty) (createMsg newAddr sdInit (value := 7))).map (fun r =>
    (r.accountsToDelete.contains newAddr, r.world.balance other)) = some (true, 7)
-- A reverted frame's deletions are dropped.
#guard (runCode (asm (createAsm sdInit 100 ++ [.push 0, .push 0, .op .revert]))).map
  (·.accountsToDelete.isEmpty) = some true

end EvmTest.InterpreterCall

namespace EvmTest.InterpreterCall
open EvmLean EvmTest.InterpreterUtil

/-! ## Explicit call stack -/

/-- A calls B (`other`), which runs `PUSH1 1`. -/
def stackProbe : ByteArray := asm (callAsm 1000 other 0 0 0 0 0 ++ [.op .pop])
/-- The world for `stackProbe`. -/
def stackProbeWorld : World := mkWorld stackProbe [(other, acct [.push 1])]
-- Seven pushes, then the CALL step pushes B's frame.
#guard (stepN (callMsg contract stackProbe) stackProbeWorld 8).map
  (fun m => (m.parents.length, m.frame.msg.currentTarget, m.frame.msg.depth)) =
  some (1, other, 1)
-- B executes PUSH1 1 …
#guard (stepN (callMsg contract stackProbe) stackProbeWorld 9).map
  (fun m => (m.parents.length, m.frame.stack)) = some (1, [1])
-- … runs off its code, and A resumes after the CALL with the success flag.
#guard (stepN (callMsg contract stackProbe) stackProbeWorld 10).map
  (fun m => (m.parents.length, m.frame.stack, m.frame.pc)) =
  some (0, [1], asmSize (callAsm 1000 other 0 0 0 0 0))

/-! ## Output windows and return data -/

-- Only `retSize` bytes of the output are written; RETURNDATASIZE sees all of it.
#guard (runAB (callAsm 100000 other 0 0 0 0 1 ++ [.op .pop, .push 0, .op .mload] ++ storeTop 0
    ++ [.op .returndatasize] ++ storeTop 1) ([.push 0xabcd] ++ retTop)).map
  (fun r => (r.world.sload contract 0, r.world.sload contract 1)) =
  some (0, 32)
-- B returns the two bytes `ab cd`; the window (31, 2) puts `ab` at the end of word 0.
#guard (runAB (callAsm 100000 other 0 0 0 31 2 ++ [.op .pop, .push 0, .op .mload] ++ retTop)
    [.push 0xabcd, .push 0, .op .mstore, .push 2, .push 30, .op .«return»]).map
  (fun r => Bytes.toWord r.output) = some 0xab
-- After a successful CREATE the return-data buffer is empty.
#guard outWord (runCode (asm (callAsm 100000 other 0 0 0 0 0 ++ createAsm initCode
  ++ [.op .returndatasize] ++ retTop)) [(other, acct ([.push 1] ++ retTop))]) = 0

/-! ## Recursion -/

/-- Increments slot 0 of `contract`, then calls itself with all available gas. -/
def recurse : List Asm :=
  [.push 0, .op .sload, .push 1, .op .add, .push 0, .op .sstore]
    ++ callAsm (2 ^ 255) contract 0 0 0 0 0
#guard ((runCode (asm recurse) (gas := 3000000)).map
  (fun r => decide (r.world.sload contract 0 > 10))).getD false

end EvmTest.InterpreterCall
