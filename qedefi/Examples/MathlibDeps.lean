module

public import Batteries.Data.ByteArray
public import Mathlib.Data.BitVec
public import Mathlib.Data.FinEnum
public import Mathlib.Order.Lattice.Nat

/-!
# Mathlib modules the examples use directly

The example files are not in the module system, so they reach Mathlib through module-system
files. Most of what they use comes with the `QEDefi` modules they import; this module adds the
few remaining Mathlib modules (`BitVec` lemmas for event data, `FinEnum` for finite address
sets, `Nat` lattice lemmas, `ByteArray` lemmas), so no example imports all of Mathlib.
-/
