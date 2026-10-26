import Verified.Solmate.ERC20.Permit

/-!
# Symbolic execution over a memory of symbolic size

Off its deployment chain, Solmate's `permit` copies a long `name` into memory before the rest of
its body runs, so the rest starts with a memory of symbolic size. Above a bound `B` (a numeral,
a multiple of 32) that every offset the code touches stays under, no instruction expands
memory. With the size written `B + 32 * t`, the `bg_*` lemmas evaluate the sizes and expansion
costs the stepping tactics produce, with numeral side conditions only (passed to `pwp_steps`);
the scoped `evm_gas` rule rewrites with them and with the size hypothesis, which must be named
`hMsz`, before the usual `evm_gas`.
-/

namespace Verified.Solmate.ERC20.Spec.PermitLongGas
open EvmLean EvmLean.Interpreter EvmLogic

variable {B t n c : Nat}

theorem bg_ceil (h : B % 32 = 0) : Gas.ceil32 (B + 32 * t) = B + 32 * t := by
  unfold Gas.ceil32; omega

theorem bg_ceil' (h : B % 32 = 0) : (B + 32 * t + 31) / 32 * 32 = B + 32 * t := by omega

theorem bg_max (h : n ≤ B) : max (B + 32 * t) n = B + 32 * t := by omega

theorem bg_max' (h : n ≤ B) : max n (B + 32 * t) = B + 32 * t := by omega

theorem bg_mod (h : B % 32 = 0) : (B + 32 * t) % 32 = 0 := by omega

theorem bg_words (h : B % 32 = 0) : (B + 32 * t) / 32 = B / 32 + t := by omega

theorem bg_maxw (h : n ≤ c) : max (c + t) n = c + t := by omega

theorem bg_mul : 32 * (c + t) = 32 * c + 32 * t := by omega

theorem bg_ite_self : (if B + 32 * t ≤ B then B else B + 32 * t) = B + 32 * t := by
  split <;> omega

theorem bg_le (h : n ≤ B) : (n ≤ B + 32 * t) = True := by
  simp only [eq_iff_iff, iff_true]; omega

theorem bg_le_false (h : n + 1 ≤ B) : (B + 32 * t ≤ n) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem bg_lew_false (h : n + 1 ≤ c) : (c + t ≤ n) = False := by
  simp only [eq_iff_iff, iff_false]; omega

/-- Expansions inside a memory of `size` bytes cost nothing and keep its size. -/
theorem extend_of_le {size : Nat} (h32 : size % 32 = 0) :
    ∀ (l : List (Nat × Nat)), (∀ p ∈ l, p.1 + p.2 ≤ size) →
      Gas.extendMemory size l = { cost := 0, newSize := size }
  | [], _ => rfl
  | (off, len) :: l, h => by
    have h1 := h (off, len) (by simp)
    have ih := extend_of_le h32 l (fun p hp => h p (by simp [hp]))
    unfold Gas.extendMemory at ih ⊢
    simp only [List.foldl_cons]
    have : (if len = 0 then ({ cost := 0, newSize := size } : Gas.ExtendMemory) else
        if Gas.ceil32 (off + len) ≤ Gas.ceil32 size then { cost := 0, newSize := size }
        else { cost := 0 + (Gas.memoryCost (Gas.ceil32 (off + len)) -
          Gas.memoryCost (Gas.ceil32 size)), newSize := Gas.ceil32 (off + len) }) =
        { cost := 0, newSize := size } := by
      split
      · rfl
      · have : Gas.ceil32 (off + len) ≤ Gas.ceil32 size := by unfold Gas.ceil32; omega
        simp only [this, ↓reduceIte]
    rw [this]; exact ih

theorem bg_ext1 {off len : Nat} (hB : B % 32 = 0) (h : off + len ≤ B) :
    Gas.extendMemory (B + 32 * t) [(off, len)] = { cost := 0, newSize := B + 32 * t } :=
  extend_of_le (by omega) _ (by simp; omega)

theorem bg_ext2 {off len off' len' : Nat} (hB : B % 32 = 0) (h : off + len ≤ B)
    (h' : off' + len' ≤ B) :
    Gas.extendMemory (B + 32 * t) [(off, len), (off', len')] =
      { cost := 0, newSize := B + 32 * t } :=
  extend_of_le (by omega) _ (by simp; omega)

theorem bg_expand {M : Memory} {off len : Nat} (hM : M.size = B + 32 * t) (hB : B % 32 = 0)
    (h : off + len ≤ B) : M.expand off len = M :=
  Memory.expand_eq_self_of_le (by omega) (by omega)

/-- `evm_gas` over a memory whose size hypothesis is `hMsz : M.size = B + 32 * t`: sizes and
expansion costs are evaluated by the `bg_*` lemmas first, then as `evm_gas` does. -/
syntax "pl_gas" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| pl_gas) => `(tactic| (
    simp only [memoryCost, outputCost, Memory.size_storeWord, Memory.size_expand,
      Memory.wordsAfter, Memory.words, hMsz, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
      Nat.reduceDiv, Nat.reduceEqDiff, Nat.reduceLeDiff, BitVec.reduceToNat, ↓reduceIte,
      bg_words, bg_maxw, bg_mul, bg_max, bg_max', max_self, bg_ceil, bg_ceil', bg_le,
      bg_le_false, bg_lew_false, le_refl, ite_self, bg_ite_self, bg_ext1, bg_ext2]
    evm_gas_bounds
    try dsimp only at *
    try simp only [memoryCost, outputCost, Gas.extendMemory, List.foldl, Gas.ceil32,
      Gas.memoryCost, Gas.words, Gas.memoryPerWord, Memory.size_storeWord, Memory.size_expand,
      Memory.size_empty, Memory.wordsAfter, Memory.words, Gas.logCost, Gas.logBase,
      Gas.logDataPerByte, Gas.logTopic, Gas.keccak256Cost, Gas.keccak256Base,
      Gas.keccak256PerWord, BitVec.reduceToNat, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
      Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def, ↓reduceIte] at ⊢
    try simp only [Gas.base, Gas.veryLow, Gas.low, Gas.mid, Gas.high, Gas.jumpdest, Gas.fastStep,
      Gas.callStipend, Gas.warmAccess, Gas.coldStorageAccess, List.length_cons,
      List.length_nil] at ⊢
    omega))

/-- `evm_gas` tries `pl_gas` first where this namespace is open (the stepping tactics call
`evm_gas` for their gas side conditions); the plain rule runs when it fails. -/
scoped macro_rules
  | `(tactic| evm_gas) => `(tactic| pl_gas)

/-- `pwp_steps` with the `bg_*` normalization. -/
syntax "plwp_steps" (ppSpace num)? (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| plwp_steps $[$n]? $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let n := n.getD (Lean.Syntax.mkNumLit "100000")
    `(tactic| pwp_steps $n [memoryCost, Memory.size_storeWord, Memory.size_expand,
      Memory.wordsAfter, Memory.words, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
      Nat.reduceDiv, Nat.reduceEqDiff, Nat.reduceLeDiff, BitVec.reduceToNat,
      bg_words, bg_maxw, bg_mul, bg_max, bg_max', max_self, bg_ceil, bg_ceil', bg_le,
      bg_le_false, bg_lew_false, le_refl, ite_self, bg_ite_self, bg_ext1, bg_ext2, bg_mod,
      Memory.expand_eq_self_of_le, $extra,*])

/-- `pwp_run_to` with the `bg_*` normalization. -/
syntax "plwp_run_to " num,+ (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| plwp_run_to $pcs,* $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| pwp_run_to $pcs,* [memoryCost, Memory.size_storeWord, Memory.size_expand,
      Memory.wordsAfter, Memory.words, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
      Nat.reduceDiv, Nat.reduceEqDiff, Nat.reduceLeDiff, BitVec.reduceToNat,
      bg_words, bg_maxw, bg_mul, bg_max, bg_max', max_self, bg_ceil, bg_ceil', bg_le,
      bg_le_false, bg_lew_false, le_refl, ite_self, bg_ite_self, bg_ext1, bg_ext2, bg_mod,
      Memory.expand_eq_self_of_le, $extra,*])

end Verified.Solmate.ERC20.Spec.PermitLongGas
