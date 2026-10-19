import EvmLean.Machine.Types

/-!
# Precompiled contracts

Addresses `0x01`–`0x0a` (Cancun). Each precompile charges its gas, then either succeeds
with output or fails exceptionally, consuming all gas.
-/

namespace EvmLean.Precompile

/-- Outcome of a precompile call. -/
structure Result where
  /-- `false` on exceptional failure (out of gas or invalid input). -/
  success : Bool
  /-- Gas left (zero on failure). -/
  gasLeft : Nat
  /-- Output (empty on failure). -/
  output : ByteArray
  deriving Inhabited

/-- Is `a` a precompile address in `fork`? -/
def isPrecompile (fork : Fork) (a : Address) : Bool := sorry

/-- Run the precompile at `a` on `input` with `gas` available. Callers must first check
`isPrecompile`. -/
def run (crypto : Crypto) (fork : Fork) (a : Address) (input : ByteArray) (gas : Nat) : Result := sorry

end EvmLean.Precompile
