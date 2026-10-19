import EvmLean.Prelude.Bytes

/-!
# Keccak-256

The pre-standard Keccak-256 used by Ethereum (padding `0x01`, not SHA3's `0x06`),
implemented in plain Lean.
-/

namespace EvmLean.Keccak

/-- Keccak-256 of `data`, as a big-endian word. -/
def hash256 (data : ByteArray) : Word := sorry

end EvmLean.Keccak
