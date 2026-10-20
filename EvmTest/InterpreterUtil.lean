import EvmLean.Interpreter

/-!
# Test utilities for the interpreter

* `fakeCrypto`: a **FAKE** `Crypto` built from trivial stand-in functions. It is *not*
  cryptography; it exists so that interpreter tests can run while the real hash
  implementations are developed elsewhere (`Crypto.real` cannot be evaluated until then).
  Only `keccak256` is exercised, as a deterministic, injective-enough mixing function.
* `testPrecompiles`: an identity precompile at `0x04` (the real gas formula) and
  always-failing precompiles at `0x01` and `0x03`; nothing else.
* `Asm`: a tiny assembler for hand-written bytecode.
* World/message builders and runners.
-/

namespace EvmTest.InterpreterUtil
open EvmLean

open EvmLean.Interpreter

/-- FAKE Keccak-256 stand-in (polynomial mixing modulo 2²⁵⁶). Not a hash function. -/
def fakeKeccak (b : ByteArray) : Word :=
  BitVec.ofNat 256 (b.foldl (fun acc x => (acc * 257 + x.toNat + 1) % 2 ^ 256) 1)

/-- A **FAKE** crypto bundle for tests. Every field is a trivial stand-in. -/
def fakeCrypto : Crypto where
  keccak256 := fakeKeccak
  sha256 := fun _ => Bytes.zeros 32
  ripemd160 := fun _ => Bytes.zeros 20
  blake2f := fun _ h _ _ _ _ => h
  ecrecover := fun _ _ _ _ => none
  bn254Add := fun _ => none
  bn254Mul := fun _ => none
  bn254Pairing := fun _ => none
  kzgVerify := fun _ _ _ _ => none
  bls12G1Add := fun _ => none
  bls12G1Msm := fun _ => none
  bls12G2Add := fun _ => none
  bls12G2Msm := fun _ => none
  bls12Pairing := fun _ => none
  bls12MapFpToG1 := fun _ => none
  bls12MapFp2ToG2 := fun _ => none
  p256Verify := fun _ _ _ _ _ => false

/-- Test precompiles: identity at `0x04` (15 + 3 per word); always failing at `0x01` and
`0x03` (the latter to exercise the RIPEMD-160 touched-account quirk). -/
def testPrecompiles : PrecompileImpl where
  isPrecompile a := a == 1 || a == 3 || a == 4
  run a input gas :=
    if a == 4 then
      let cost := 15 + 3 * Gas.words input.size
      if gas < cost then { success := false, gasLeft := 0, output := .empty }
      else { success := true, gasLeft := gas - cost, output := input }
    else { success := false, gasLeft := 0, output := .empty }

/-! ## Assembler -/

/-- An assembly item. -/
inductive Asm where
  /-- A plain opcode (for `push`, use `Asm.push`/`Asm.pushN`). -/
  | op (o : Opcode)
  /-- Push `v` with the smallest `PUSHn` (`PUSH0` for zero). -/
  | push (v : Nat)
  /-- Push `v` as exactly `n` bytes. -/
  | pushN (n : Nat) (v : Nat)
  /-- Raw bytes. -/
  | raw (bytes : List UInt8)

/-- Encode `PUSHn v`. -/
def encodePush (n v : Nat) : List UInt8 := (0x5f + n).toUInt8 :: (Bytes.ofNatBE n v).toList

/-- Encode one item. -/
def Asm.encode : Asm → List UInt8
  | .op o => [o.toByte]
  | .push v => encodePush (Gas.byteLength v) v
  | .pushN n v => encodePush n v
  | .raw bs => bs

/-- Assemble a program. -/
def asm (xs : List Asm) : ByteArray := ⟨(xs.flatMap Asm.encode).toArray⟩

/-- Byte length of an assembled program (for computing jump targets). -/
def asmSize (xs : List Asm) : Nat := (asm xs).size

/-- Return the top of the stack as a 32-byte word: `MSTORE` at 0, `RETURN 0 32`. -/
def retTop : List Asm := [.push 0, .op .mstore, .push 32, .push 0, .op .«return»]

/-- `SSTORE` the top of the stack into slot `k`. -/
def storeTop (k : Nat) : List Asm := [.push k, .op .sstore]

/-- `SSTORE` values `vs` into slot 0 in sequence. -/
def stores (vs : List Nat) : List Asm := vs.flatMap fun v => [.push v, .push 0, .op .sstore]

/-! ## Worlds, messages, runners -/

/-- Transaction sender. -/
def sender : Address := 0xCA11
/-- The contract under test. -/
def contract : Address := 0xC0DE
/-- A second contract. -/
def other : Address := 0xB0B
/-- A third contract. -/
def third : Address := 0x7171

/-- Address set from a list. -/
def addrSet (xs : List Address) : AddressSet := xs.foldl (fun s a => s.insert a) ∅

/-- A world with a funded sender and `contract` holding `code` and 1000 wei, plus extra
accounts. -/
def mkWorld (code : ByteArray) (extra : List (Address × Account) := []) : World :=
  let w : World := (∅ : World).insert sender { nonce := 1, balance := 1000000000 }
  let w := w.insert contract { nonce := 1, balance := 1000, code }
  extra.foldl (fun w (a, acc) => w.insert a acc) w

/-- The default test context (Cancun, fake crypto). -/
def ctx0 : Context := { crypto := fakeCrypto }

/-- A top-level call from `sender` to `to` running `code`. -/
def callMsg (to : Address) (code : ByteArray) (gas : Nat := 1000000) (value : Word := 0)
    (data : ByteArray := .empty) (warmKeys : StorageKeySet := ∅) (depth : Nat := 0)
    (isStatic : Bool := false) : Message where
  caller := sender
  target := some to
  currentTarget := to
  gas := gas
  value := value
  data := data
  codeAddress := some to
  code := code
  depth := depth
  shouldTransferValue := true
  isStatic := isStatic
  accessedAddresses := addrSet [sender, to, 1, 4]
  accessedStorageKeys := warmKeys

/-- A top-level creation from `sender` of a contract at `addr` with init code `code`. -/
def createMsg (addr : Address) (code : ByteArray) (gas : Nat := 1000000) (value : Word := 0) :
    Message where
  caller := sender
  target := none
  currentTarget := addr
  gas := gas
  value := value
  data := .empty
  codeAddress := none
  code := code
  depth := 0
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := addrSet [sender, addr, 1, 4]
  accessedStorageKeys := ∅

/-- Run a message with the test precompiles; `none` if fuel runs out. -/
def runMsg (world : World) (msg : Message) (ctx : Context := ctx0) (fuel : Nat := 100000) :
    Option MessageResult :=
  (processMessageCallWith testPrecompiles fuel ctx world ∅ msg).toOption

/-- Run `code` as `contract` (called by `sender`) in `mkWorld code extra`. -/
def runCode (code : ByteArray) (extra : List (Address × Account) := []) (gas : Nat := 1000000)
    (ctx : Context := ctx0) : Option MessageResult :=
  runMsg (mkWorld code extra) (callMsg contract code gas) ctx

/-- The output as a word (`0` if absent). -/
def outWord (r : Option MessageResult) : Word :=
  match r with
  | some r => Bytes.toWord r.output
  | none => 0

/-- Gas used by the top-level message (`gas - gasLeft`). -/
def gasUsed (gas : Nat) (r : Option MessageResult) : Option Nat := r.map fun r => gas - r.gasLeft

/-- Storage slot `k` of `a` after the message. -/
def slot (r : Option MessageResult) (a : Address) (k : Word) : Option Word :=
  r.map fun r => r.world.sload a k

/-- Did the message succeed? -/
def succeeded (r : Option MessageResult) : Bool := (r.map (·.success)).getD false

/-- The error of the message. -/
def errorOf (r : Option MessageResult) : Option ExceptionalHalt := r.bind (·.error)

/-- Machine after `n` steps from the initial machine of `msg` (or the final result). -/
def stepN (msg : Message) (world : World) (n : Nat) : Option Machine :=
  match initMachine testPrecompiles ctx0 world ∅ msg with
  | .inl _ => none
  | .inr m => go n m
where
  /-- Iterate. -/
  go : Nat → Machine → Option Machine
    | 0, m => some m
    | k + 1, m => match step m with
      | .running m' => go k m'
      | .done _ => none

/-- Stack of the executing frame after `n` steps of running `code` as `contract`. -/
def stackAfter (code : ByteArray) (n : Nat) : Option (List Word) :=
  (stepN (callMsg contract code) (mkWorld code) n).map (·.frame.stack)

end EvmTest.InterpreterUtil
