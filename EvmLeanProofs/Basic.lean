import EvmLean

/-! Kernel-checked sanity theorems. Every theorem here must depend only on the standard
axioms (`propext`, `Classical.choice`, `Quot.sound`); see `#print axioms`. -/

namespace EvmLean

/-- `ADD` is commutative. -/
theorem add_comm' (a b : Word) : a + b = b + a := BitVec.add_comm a b

end EvmLean
