import EvmLean.Prelude.Bytes

/-! # BLAKE2b compression function `F` (EIP-152), for precompile `0x09`. -/

namespace EvmLean.Blake2

/-- BLAKE2b `F` with a caller-chosen number of rounds: state `h`, message block `m`,
offset counters `t₀ t₁`, final-block flag. -/
def compress (rounds : Nat) (h : Vector UInt64 8) (m : Vector UInt64 16)
    (t₀ t₁ : UInt64) (final : Bool) : Vector UInt64 8 := sorry

end EvmLean.Blake2
