import EvmLean

/-!
# Basic kernel checks

Concrete facts proved by kernel evaluation, guarding that the semantics stays kernel-reducible.
Use `decide +kernel` or `rfl`: plain `decide` is far slower on `ByteArray` code.
-/

namespace EvmLean

theorem add_comm' (a b : Word) : a + b = b + a := BitVec.add_comm a b

theorem mload_mstore_example : (Memory.storeWord {} 0 5).loadWord 0 = 5 := by decide +kernel

theorem msize_mstore_example : (Memory.storeWord {} 64 (-1)).size = 96 := by decide +kernel

theorem exp_example : Word.exp 3 1000 = BitVec.ofNat 256 (3 ^ 1000 % 2 ^ 256) := by decide +kernel

theorem decode_clz_cancun : Opcode.decode .cancun 0x1e = .invalid := by decide

theorem decode_clz_osaka : Opcode.decode .osaka 0x1e = .clz := by decide

end EvmLean
