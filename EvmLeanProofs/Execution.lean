import EvmLean

/-!
# Executing bytecode in the kernel

The interpreter is plain Lean, so the kernel can run it: the theorems below state the
outcome of executing real bytecode and are checked by kernel evaluation (`decide +kernel`),
with no trust in the compiler.

They are stated for `Crypto.real`. Stating them for an arbitrary `Crypto` (the program
never hashes) does not yet go through by `rfl`: reduction with a free `crypto` gets stuck
and needs a simp set for `step`. That is future proof-library work.
-/

namespace EvmLean.Examples


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

/-- Run `msg` against `world` with the real cryptography. -/
def result : Option MessageResult :=
  (Interpreter.processMessageCall 100 { crypto := Crypto.real } world ∅ msg).toOption

/-- Running `addStore` succeeds and stores `5` in slot 0. -/
theorem addStore_slot0 : result.map (fun r => (r.success, r.world.sload contract 0)) =
    some (true, 5) := by
  decide +kernel

/-- Running `addStore` costs exactly 22 111 gas: 3 + 3 + 3 + 2 for the arithmetic and
22 100 for a cold zero-to-nonzero `SSTORE` (EIP-2929 + EIP-2200). -/
theorem addStore_gas : result.map (fun r => msg.gas - r.gasLeft) = some 22111 := by
  decide +kernel

end EvmLean.Examples
