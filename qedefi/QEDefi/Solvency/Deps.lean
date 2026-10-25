module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.FinEnum

/-!
# Mathlib modules the solvency proofs use

The reentrancy examples are not in the module system, so they reach Mathlib's finite sums (and
their order lemmas) and the finite enumeration of addresses (`FinEnum (BitVec n)`, hence
`Fintype Address`) through this module-system file.
-/
