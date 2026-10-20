import EvmLean

/-!
# Word arithmetic facts

The EVM-specific corner cases of `EvmLean.Word` (division and remainder by zero, `EXP` as
modular exponentiation, comparisons as `0`/`1`), stated so that `simp` and `bv_decide`-free
`omega`/`bv_omega` proofs can use them. (`bv_decide` itself introduces an auxiliary axiom per
call, so it is not used in this library.)
-/

namespace EvmLean.Word

/-- `DIV` by zero is zero. -/
@[simp] theorem div_zero (x : Word) : Word.div x 0 = 0 := by
  simp [Word.div]

/-- `MOD` by zero is zero (unlike `BitVec`'s `x % 0 = x`). -/
@[simp] theorem mod_zero (x : Word) : Word.mod x 0 = 0 := by
  simp [Word.mod]

/-- `MOD` by a non-zero modulus is `BitVec` remainder. -/
theorem mod_of_ne_zero (x : Word) {y : Word} (h : y ≠ 0) : Word.mod x y = x % y := by
  unfold Word.mod
  split
  · contradiction
  · rfl

/-- `SDIV` by zero is zero. -/
@[simp] theorem sdiv_zero (x : Word) : Word.sdiv x 0 = 0 := by
  simp [Word.sdiv]

/-- `SMOD` by zero is zero (unlike `BitVec.srem`). -/
@[simp] theorem smod_zero (x : Word) : Word.smod x 0 = 0 := by
  simp [Word.smod]

/-- `SMOD` by a non-zero modulus is `BitVec.srem` (sign of the dividend). -/
theorem smod_of_ne_zero (x : Word) {y : Word} (h : y ≠ 0) : Word.smod x y = x.srem y := by
  unfold Word.smod
  split
  · contradiction
  · rfl

/-- `ADDMOD` with zero modulus is zero. -/
@[simp] theorem addmod_zero (x y : Word) : Word.addmod x y 0 = 0 := by
  simp [Word.addmod]

/-- `MULMOD` with zero modulus is zero. -/
@[simp] theorem mulmod_zero (x y : Word) : Word.mulmod x y 0 = 0 := by
  simp [Word.mulmod]

/-- `ADDMOD` computes `(x + y) mod n` without wrap-around. -/
theorem toNat_addmod (x y : Word) {n : Word} (h : n ≠ 0) :
    (Word.addmod x y n).toNat = (x.toNat + y.toNat) % n.toNat := by
  unfold Word.addmod
  split
  · contradiction
  · have hn : 0 < n.toNat := by
      rcases Nat.eq_zero_or_pos n.toNat with h' | h'
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h')) h
      · exact h'
    have : (x.toNat + y.toNat) % n.toNat < 2 ^ 256 :=
      Nat.lt_trans (Nat.mod_lt _ hn) n.isLt
    simp [Nat.mod_eq_of_lt this]

/-- `MULMOD` computes `(x * y) mod n` without wrap-around. -/
theorem toNat_mulmod (x y : Word) {n : Word} (h : n ≠ 0) :
    (Word.mulmod x y n).toNat = (x.toNat * y.toNat) % n.toNat := by
  unfold Word.mulmod
  split
  · contradiction
  · have hn : 0 < n.toNat := by
      rcases Nat.eq_zero_or_pos n.toNat with h' | h'
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h')) h
      · exact h'
    have : (x.toNat * y.toNat) % n.toNat < 2 ^ 256 :=
      Nat.lt_trans (Nat.mod_lt _ hn) n.isLt
    simp [Nat.mod_eq_of_lt this]

/-- `EXP` is `b ^ e` modulo `2²⁵⁶`. -/
theorem toNat_exp (b e : Word) : (Word.exp b e).toNat = b.toNat ^ e.toNat % 2 ^ 256 := by
  rw [Word.exp, BitVec.toNat_ofNat, Nat.powMod_def, Nat.mod_mod]

/-- `EXP` is `b ^ e` modulo `2²⁵⁶`, as a word. -/
theorem exp_eq_ofNat_pow (b e : Word) : Word.exp b e = BitVec.ofNat 256 (b.toNat ^ e.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_exp, BitVec.toNat_ofNat]

/-- `EXP` with exponent zero is one. -/
@[simp] theorem exp_zero (b : Word) : Word.exp b 0 = 1 := by
  rw [exp_eq_ofNat_pow]
  rfl

/-- `ofBool` is `0` or `1`. -/
@[simp] theorem ofBool_true : ofBool true = 1 := rfl

/-- `ofBool` is `0` or `1`. -/
@[simp] theorem ofBool_false : ofBool false = 0 := rfl

/-- `LT` is `1` exactly when `x < y` as numbers. -/
theorem lt_eq_one_iff (x y : Word) : Word.lt x y = 1 ↔ x.toNat < y.toNat := by
  unfold Word.lt ofBool
  split <;> simp_all [BitVec.ult]

/-- `LT` is `0` exactly when `x ≥ y` as numbers. -/
theorem lt_eq_zero_iff (x y : Word) : Word.lt x y = 0 ↔ y.toNat ≤ x.toNat := by
  unfold Word.lt ofBool
  split <;> simp_all [BitVec.ult]

/-- `GT` is `1` exactly when `x > y` as numbers. -/
theorem gt_eq_one_iff (x y : Word) : Word.gt x y = 1 ↔ y.toNat < x.toNat := by
  unfold Word.gt ofBool
  split <;> simp_all [BitVec.ult]

/-- `EQ` is `1` exactly when the words are equal. -/
theorem eq_eq_one_iff (x y : Word) : Word.eq x y = 1 ↔ x = y := by
  unfold Word.eq ofBool
  split <;> simp_all

/-- `ISZERO` is `1` exactly on zero. -/
theorem iszero_eq_one_iff (x : Word) : Word.iszero x = 1 ↔ x = 0 := by
  unfold Word.iszero ofBool
  split <;> simp_all

/-- `ISZERO` of `ISZERO` is the truth value of `x ≠ 0`. -/
theorem iszero_iszero (x : Word) : Word.iszero (Word.iszero x) = ofBool (x != 0) := by
  unfold Word.iszero ofBool
  by_cases h : x = 0 <;> simp [h]

/-- `SHL` by less than 256 is `BitVec` shift. -/
theorem shl_of_lt (s x : Word) (h : s.toNat < 256) : Word.shl s x = x <<< s.toNat := by
  simp [Word.shl, h]

/-- `SHL` by 256 or more is zero. -/
theorem shl_of_le (s x : Word) (h : 256 ≤ s.toNat) : Word.shl s x = 0 := by
  simp [Word.shl, Nat.not_lt.mpr h]

/-- `ofAddress` is injective. -/
theorem ofAddress_injective {a b : Address} (h : ofAddress a = ofAddress b) : a = b := by
  have := congrArg (BitVec.setWidth 160) h
  simpa [ofAddress] using this

/-- `toAddress` inverts `ofAddress`. -/
@[simp] theorem toAddress_ofAddress (a : Address) : toAddress (ofAddress a) = a := by
  simp [toAddress, ofAddress]

end EvmLean.Word
