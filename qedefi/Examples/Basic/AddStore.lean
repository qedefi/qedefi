import EvmLogic.Tactic.EvmStep
import EvmLogic.Step.Basic

/-!
# Executing bytecode, for every `Crypto`

The outcome of running real bytecode for an arbitrary `crypto` (the program never hashes),
proved by `kernel_rfl` (the kernel evaluates the run with `crypto` free) and by `evm_steps`
(symbolic execution, which also handles symbolic inputs). Plain `rfl`/`decide` fail here:
`kernel_decide` rejects free variables, and elaborator `isDefEq` does not finish.
-/

namespace Examples.Basic
open EvmLean EvmLean.Interpreter EvmLogic

/-- `PUSH1 3 PUSH1 2 ADD PUSH0 SSTORE STOP`: store `2 + 3` in slot 0. -/
def addStore : ByteArray := ⟨#[0x60, 0x03, 0x60, 0x02, 0x01, 0x5f, 0x55, 0x00]⟩

def contract : Address := 0xC0DE

def world : World := (∅ : World).insert contract { nonce := 1, code := addStore }

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

def result (crypto : Crypto) : Option MessageResult :=
  (Interpreter.processMessageCall 100 { crypto } world ∅ msg).toOption

/-- Running `addStore` succeeds and stores `5` in slot 0, whatever the cryptography. -/
theorem addStore_slot0 (crypto : Crypto) :
    (result crypto).map (fun r => (r.success, r.world.sload contract 0)) = some (true, 5) := by
  kernel_rfl

/-- Running `addStore` costs exactly 22 111 gas: 11 for the arithmetic and 22 100 for a cold
zero-to-nonzero `SSTORE`. -/
theorem addStore_gas (crypto : Crypto) :
    (result crypto).map (fun r => msg.gas - r.gasLeft) = some 22111 := by
  kernel_decide

def initial (crypto : Crypto) : Machine :=
  { ctx := { crypto }, precompiles := PrecompileImpl.standard { crypto }, world := world,
    transient := ∅, originalWorld := world, createdAccounts := ∅,
    frame := Frame.init msg (.call 0 0) (world, ∅), parents := [] }

theorem processMessageCall_eq (crypto : Crypto) :
    Interpreter.processMessageCall 100 { crypto } world ∅ msg = run 100 (initial crypto) :=
  processMessageCall_eq_run (.inl (show Fork.cancun < .prague by decide)) (by decide) (initMachine_call rfl rfl rfl rfl rfl) 100

/-- `addStore_slot0` again, by symbolic execution with the step lemmas. -/
theorem addStore_slot0' (crypto : Crypto) :
    (result crypto).map (fun r => (r.success, r.world.sload contract 0)) = some (true, 5) := by
  rw [result, processMessageCall_eq]
  simp only [initial, Frame.init, msg]
  evm_steps
  simp only [Option.map, Except.toOption, topLevelResult_world, World.sload_sstore_self]
  decide

/-! ## Memory: returning a word -/

/-- `PUSH1 42 PUSH0 MSTORE PUSH1 32 PUSH0 RETURN`: return the word 42. -/
def ret42 : ByteArray := ⟨#[0x60, 0x2a, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

def ret42Machine (ctx : Context) (g : Nat) (msg : Message) (w : World) : Machine where
  ctx := ctx
  precompiles := PrecompileImpl.standard ctx
  world := w
  transient := ∅
  originalWorld := w
  createdAccounts := ∅
  parents := []
  frame := { msg, code := ret42, jumpDests := validJumpDests ret42, gasLeft := g, sub := {},
             snapshot := (w, ∅), kind := .call 0 0 }

/-- `ret42` returns the word 42, for every context, gas amount ≥ 100, message and world. -/
theorem ret42_output (ctx : Context) (g : Nat) (hg : 100 ≤ g) (msg : Message) (w : World)
    (k : Nat) : ∃ r, run (k + 6) (ret42Machine ctx g msg w) = .ok r ∧
      Bytes.toWord r.output = 42 := by
  simp only [ret42Machine]
  evm_steps
  refine ⟨_, rfl, ?_⟩
  simp only [topLevelResult_output, Memory.read_storeWord, Bytes.toWord_ofWord]
  rfl

end Examples.Basic
