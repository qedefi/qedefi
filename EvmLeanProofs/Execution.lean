import EvmLeanProofs.Tactic

/-!
# Executing bytecode, for every `Crypto`

The interpreter is plain Lean, so the kernel can run it. The theorems below state the
outcome of executing real bytecode for an *arbitrary* `crypto : Crypto` (the program never
hashes), proved in two independent ways:

* `kernel_rfl`: the kernel evaluates the whole run with `crypto` free. This works because
  nothing inspects `crypto`; it takes well under a second.
* `evm_steps`: symbolic execution with the per-opcode step lemmas, which also works when
  the inputs are symbolic (see `EvmLeanProofs.Examples.Token`).

Why `rfl` and `decide` do not work here: `decide +kernel` rejects goals with free variables
(such as `crypto`), and `rfl`/`decide` check definitional equality in the elaborator
(`Meta.isDefEq`), which does not finish on a whole-program run even for `Crypto.real`
(> 150 s). The kernel itself has no difficulty with a free `crypto`.
-/

namespace EvmLean.Examples

open Interpreter

/-- `PUSH1 3 PUSH1 2 ADD PUSH0 SSTORE STOP`: store `2 + 3` in slot 0. -/
def addStore : ByteArray := ⟨#[0x60, 0x03, 0x60, 0x02, 0x01, 0x5f, 0x55, 0x00]⟩

/-- The contract under test. -/
def contract : Address := 0xC0DE

/-- A world containing only the contract. -/
def world : World := (∅ : World).insert contract { nonce := 1, code := addStore }

/-- A top-level call to the contract with 100 000 gas. -/
def msg : Message where
  caller := 0xCA11
  target := some contract
  currentTarget := contract
  gas := 100000
  value := 0
  data := .empty
  codeAddress := some contract
  code := addStore
  depth := 0
  shouldTransferValue := false
  isStatic := false
  accessedAddresses := ∅
  accessedStorageKeys := ∅

/-- Run `msg` against `world` with the given cryptography. -/
def result (crypto : Crypto) : Option MessageResult :=
  (Interpreter.processMessageCall 100 { crypto } world ∅ msg).toOption

/-- Running `addStore` succeeds and stores `5` in slot 0, whatever the cryptography. -/
theorem addStore_slot0 (crypto : Crypto) :
    (result crypto).map (fun r => (r.success, r.world.sload contract 0)) = some (true, 5) := by
  kernel_rfl

/-- Running `addStore` costs exactly 22 111 gas, whatever the cryptography: 3 + 3 + 3 + 2
for the arithmetic and 22 100 for a cold zero-to-nonzero `SSTORE` (EIP-2929 + EIP-2200). -/
theorem addStore_gas (crypto : Crypto) :
    (result crypto).map (fun r => msg.gas - r.gasLeft) = some 22111 := by
  kernel_decide

/-- The machine `processMessageCall` starts from. -/
def initial (crypto : Crypto) : Machine :=
  { ctx := { crypto }, precompiles := PrecompileImpl.standard { crypto }, world := world,
    transient := ∅, originalWorld := world, createdAccounts := ∅,
    frame := Frame.init msg (.call 0 0) (world, ∅), parents := [] }

/-- `processMessageCall` sets up `initial` (the contract is not a precompile, no value moves)
and runs it. -/
theorem processMessageCall_eq (crypto : Crypto) :
    Interpreter.processMessageCall 100 { crypto } world ∅ msg = run 100 (initial crypto) := rfl

/-- `addStore_slot0` again, by symbolic execution with the step lemmas. -/
theorem addStore_slot0' (crypto : Crypto) :
    (result crypto).map (fun r => (r.success, r.world.sload contract 0)) = some (true, 5) := by
  rw [result, processMessageCall_eq]
  simp only [initial, Frame.init, msg]
  evm_steps
  simp only [Option.map, Except.toOption, topLevelResult_world, World.sload_sstore_self]
  decide

end EvmLean.Examples
