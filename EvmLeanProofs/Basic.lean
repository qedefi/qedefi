import EvmLean

/-!
# Basic kernel checks

Concrete facts the kernel can establish by evaluation. These guard the design principle
that the semantics is kernel-reducible (no `opaque`, `partial`, `@[extern]`).

Use `decide +kernel` or `rfl` for concrete evaluation: plain `decide` goes through the
elaborator's reducer, which can be orders of magnitude slower on `ByteArray` code.
Every theorem here must depend only on the standard axioms (`#print axioms`).
-/

namespace EvmLean

/-- `ADD` is commutative. -/
theorem add_comm' (a b : Word) : a + b = b + a := BitVec.add_comm a b

/-- `MSTORE` then `MLOAD` at the same offset returns the stored word (concrete instance). -/
theorem mload_mstore_example : (Memory.storeWord {} 0 5).loadWord 0 = 5 := by decide +kernel

/-- Storing a word at offset 64 expands memory to 96 bytes. -/
theorem msize_mstore_example : (Memory.storeWord {} 64 (-1)).size = 96 := by decide +kernel

/-- `EXP` agrees with modular exponentiation (concrete instance). -/
theorem exp_example : Word.exp 3 1000 = BitVec.ofNat 256 (3 ^ 1000 % 2 ^ 256) := by decide +kernel

/-- `CLZ` (0x1e) is invalid before Osaka. -/
theorem decode_clz_cancun : Opcode.decode .cancun 0x1e = .invalid := by decide

/-- `CLZ` (0x1e) decodes from Osaka on. -/
theorem decode_clz_osaka : Opcode.decode .osaka 0x1e = .clz := by decide

end EvmLean
