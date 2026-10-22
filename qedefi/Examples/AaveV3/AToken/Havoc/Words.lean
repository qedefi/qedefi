import Examples.AaveV3.AToken.Havoc.Ledger

/-!
# Word facts for the ledger proofs

The `_userState` words exactly as the AToken writes them, and the low 120 bits (the scaled
balance) of each: `additionalData = index` keeps them (`low120_indexWord`), `balance = n` sets
them to `n` (`low120_balanceWord`). Branch conditions of solc's checked arithmetic as `ℕ` facts
(`le_of_gt_iszero`, `toNat_add_of_gt_iszero`, …).
-/

namespace Examples.AaveV3.AToken.Havoc
open EvmLean EvmLogic

/-- `2¹²⁰ - 1`, solc's `uint120` mask. -/
abbrev mask120 : Word := 1329227995784915872903807060280344575#256
/-- `2¹²⁸ - 1`. -/
abbrev mask128 : Word := 340282366920938463463374607431768211455#256
/-- `2¹²⁸`. -/
abbrev pow128 : Word := 340282366920938463463374607431768211456#256
/-- `~(2¹²⁰ - 1)`. -/
abbrev nmask120 : Word :=
  115792089237316195423570985008687907853268655437644779123584680200852849295360#256

private theorem m120 : mask120 = BitVec.ofNat 256 (2 ^ 120 - 1) := rfl
private theorem m128 : mask128 = BitVec.ofNat 256 (2 ^ 128 - 1) := rfl
private theorem p128 : pow128 = BitVec.twoPow 256 128 := by decide
private theorem nm120 : nmask120 = ~~~(BitVec.ofNat 256 (2 ^ 120 - 1)) := by decide

theorem toNat_mask120_and (x : Word) : (mask120 &&& x).toNat = low120 x := by
  rw [m120, BitVec.toNat_and, Nat.and_comm, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by decide : 2 ^ 120 - 1 < 2 ^ 256), Nat.and_two_pow_sub_one_eq_mod]; rfl

theorem toNat_and_mask120 (x : Word) : (x &&& mask120).toNat = low120 x := by
  rw [BitVec.and_comm]; exact toNat_mask120_and x

theorem low120_eq_toNat (x : Word) (h : x.toNat < 2 ^ 120) : low120 x = x.toNat :=
  Nat.mod_eq_of_lt h

theorem low120_mask120_and (x : Word) : low120 (mask120 &&& x) = low120 x := by
  rw [low120_eq_toNat _ (by rw [toNat_mask120_and]; exact low120_lt x), toNat_mask120_and]

theorem testBit_low120 (x : Word) (i : Nat) :
    (low120 x).testBit i = (decide (i < 120) && x.getLsbD i) := by
  simp only [low120, Nat.testBit_mod_two_pow, BitVec.testBit_toNat]

/-- **The index write keeps the balance**: `_userState[u].additionalData = idx` as the code
computes it (`(W & (2¹²⁸-1)) | 2¹²⁸·(idx & (2¹²⁸-1))`) has the low 120 bits of `W`. -/
theorem low120_indexWord (W Y : Word) :
    low120 (mask128 &&& W ||| pow128 * Y) = low120 W := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_low120, testBit_low120]
  by_cases hi : i < 120
  · rw [m128, p128, BitVec.mul_comm, ← BitVec.shiftLeft_eq_mul_twoPow]
    simp only [hi, decide_true, Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_ofNat, BitVec.getLsbD_shiftLeft, Nat.testBit_two_pow_sub_one,
      show i < 128 by omega, show i < 256 by omega]
    simp
  · simp [hi]

/-- **The balance write**: `_userState[u].balance = n` as the code computes it
(`(n & (2¹²⁰-1)) | (X & ~(2¹²⁰-1))`) has the low 120 bits of `n`. -/
theorem low120_balanceWord (N X : Word) :
    low120 (mask120 &&& N ||| nmask120 &&& X) = low120 N := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_low120, testBit_low120]
  by_cases hi : i < 120
  · rw [m120, nm120]
    simp only [hi, decide_true, Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_ofNat, BitVec.getLsbD_not, Nat.testBit_two_pow_sub_one,
      show i < 256 by omega]
    simp
  · simp [hi]

/-! ## Branch conditions -/

theorem le_of_gt_iszero {x y : Word} (h : (Word.gt x y).iszero ≠ 0) : x.toNat ≤ y.toNat := by
  by_contra hlt
  have : Word.gt x y = 1#256 := (Word.gt_eq_one_iff x y).2 (by omega)
  rw [this] at h; exact h (by decide)

theorem lt_of_gt_ne {x y : Word} (h : Word.gt x y ≠ 0) : y.toNat < x.toNat := by
  by_contra hle
  apply h
  unfold Word.gt Word.ofBool
  simp [BitVec.ult, show ¬ y.toNat < x.toNat from hle]

/-- A checked `a + b` (solc: panic if `b > a + b`) does not wrap. -/
theorem toNat_add_of_gt_iszero {a b : Word} (h : (Word.gt b (a + b)).iszero ≠ 0) :
    (a + b).toNat = a.toNat + b.toNat := by
  have h1 := le_of_gt_iszero h
  rw [BitVec.toNat_add] at h1 ⊢
  have ha := a.isLt; have hb := b.isLt
  by_contra hne
  have : a.toNat + b.toNat ≥ 2 ^ 256 := by
    by_contra hlt; exact hne (Nat.mod_eq_of_lt (by omega))
  rw [show a.toNat + b.toNat = (a.toNat + b.toNat - 2 ^ 256) + 2 ^ 256 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h1
  omega

theorem toNat_sub_of_le {x y : Word} (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub]
  have := x.isLt
  rw [show 2 ^ 256 - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ 256 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-! ## Branch conditions as arithmetic (`word_omega`) -/

theorem ofBool_ne_zero (b : Bool) : Word.ofBool b ≠ 0 ↔ b = true := by
  cases b <;> simp [Word.ofBool]

theorem ofBool_eq_zero (b : Bool) : Word.ofBool b = 0 ↔ b = false := by
  cases b <;> simp [Word.ofBool]

theorem iszero_ne_zero_iff (x : Word) : x.iszero ≠ 0 ↔ x.toNat = 0 := by
  unfold Word.iszero; rw [ofBool_ne_zero]
  constructor
  · intro h; have := eq_of_beq h; subst this; rfl
  · intro h; have : x = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
    subst this; rfl

theorem iszero_eq_zero_iff (x : Word) : x.iszero = 0 ↔ x.toNat ≠ 0 := by
  have := iszero_ne_zero_iff x
  constructor
  · intro h h0; exact (this.2 h0) h
  · intro h; by_contra h'; exact h (this.1 h')

theorem gt_ne_zero_iff (x y : Word) : Word.gt x y ≠ 0 ↔ y.toNat < x.toNat := by
  unfold Word.gt; rw [ofBool_ne_zero]; simp [BitVec.ult]

theorem gt_eq_zero_iff (x y : Word) : Word.gt x y = 0 ↔ x.toNat ≤ y.toNat := by
  unfold Word.gt; rw [ofBool_eq_zero]; simp [BitVec.ult]

theorem lt_ne_zero_iff (x y : Word) : Word.lt x y ≠ 0 ↔ x.toNat < y.toNat := by
  unfold Word.lt; rw [ofBool_ne_zero]; simp [BitVec.ult]

theorem lt_eq_zero_iff (x y : Word) : Word.lt x y = 0 ↔ y.toNat ≤ x.toNat := by
  unfold Word.lt; rw [ofBool_eq_zero]; simp [BitVec.ult]

theorem toNat_eq_zero_iff (x : Word) : x.toNat = 0 ↔ x = 0 :=
  ⟨fun h => BitVec.eq_of_toNat_eq (by simpa using h), fun h => by rw [h]; rfl⟩

theorem iszero_gt_ne_zero_iff (x y : Word) : (Word.gt x y).iszero ≠ 0 ↔ x.toNat ≤ y.toNat := by
  rw [iszero_ne_zero_iff, toNat_eq_zero_iff, gt_eq_zero_iff]

theorem iszero_lt_ne_zero_iff (x y : Word) : (Word.lt x y).iszero ≠ 0 ↔ y.toNat ≤ x.toNat := by
  rw [iszero_ne_zero_iff, toNat_eq_zero_iff, lt_eq_zero_iff]

/-- `word_omega`: turn the branch conditions on words into `ℕ` facts, the words in the goal and
the facts into their `toNat`s (with `mod 2²⁵⁶` for `+`, `-`), add the bounds of the atoms, and
call `omega`. -/
macro "word_omega" : tactic => `(tactic| (
  set_option linter.unusedSimpArgs false in
  try simp only [iszero_gt_ne_zero_iff, iszero_lt_ne_zero_iff] at *
  set_option linter.unusedSimpArgs false in
  try simp only [gt_ne_zero_iff, gt_eq_zero_iff, lt_ne_zero_iff, lt_eq_zero_iff,
    iszero_ne_zero_iff, iszero_eq_zero_iff] at *
  set_option linter.unusedSimpArgs false in
  try simp only [low120, toNat_mask120_and, toNat_and_mask120, BitVec.toNat_add,
    BitVec.toNat_sub, BitVec.toNat_ofNat] at *
  omega))

end Examples.AaveV3.AToken.Havoc
