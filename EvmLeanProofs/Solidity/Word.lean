import EvmLeanProofs.Word
import EvmLeanProofs.Solidity.SimpAttr

/-!
# Word idioms of solc output

solc 0.8.28 (legacy pipeline, optimizer on) builds some constants arithmetically and checks
ABI inputs with masks. The lemmas here evaluate these idioms on the symbolic values that
occur during symbolic execution; they are tagged `@[sol_norm]`.

* `addressMask`: `PUSH1 1 PUSH1 1 PUSH1 0xa0 SHL SUB` computes `2¹⁶⁰ - 1` (`shl_ofNat`
  evaluates the shift, `BitVec.reduceSub` the rest); `AND` with it is the identity on
  addresses (`ofAddress_and_addressMask`, `addressMask_and_ofAddress`), which is how
  `cleanup_address` and ABI address validation (`v == v & mask`) disappear.
* `eq_self`: `EQ x x = 1`, so the validation `JUMPI` is taken.

Literals are stated as `BitVec.ofNat 256 n` (`n#256`), the simp normal form produced by the
step lemmas (`BitVec.ofNat_eq_ofNat` turns `OfNat` literals into it).
-/

namespace EvmLean.Solidity

/-- `2¹⁶⁰ - 1`, the mask of an address in a word. -/
def addressMask : Word := BitVec.ofNat 256 (2 ^ 160 - 1)

/-- `addressMask` as the literal symbolic execution produces. -/
theorem addressMask_eq : addressMask = 1461501637330902918203684832716283019655932542975#256 :=
  rfl

/-- `SHL` of literals. -/
@[sol_norm] theorem shl_ofNat (s x : Nat) :
    Word.shl (BitVec.ofNat 256 s) (BitVec.ofNat 256 x) =
      if s % 2 ^ 256 < 256 then BitVec.ofNat 256 (x * 2 ^ (s % 2 ^ 256)) else 0 := by
  have hs : (BitVec.ofNat 256 s).toNat = s % 2 ^ 256 := BitVec.toNat_ofNat _ _
  by_cases h : s % 2 ^ 256 < 256
  · apply BitVec.eq_of_toNat_eq
    simp only [Word.shl, hs, h, ↓reduceIte, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    rw [Nat.mod_mul_mod]
  · simp only [h, ↓reduceIte]
    exact Word.shl_of_le _ _ (by omega)

/-- An address is unchanged by masking. -/
theorem ofAddress_and_mask (a : Address) : Word.ofAddress a &&& addressMask = Word.ofAddress a := by
  apply BitVec.eq_of_toNat_eq
  have h := a.isLt
  have h' : a.toNat < 2 ^ 256 := by omega
  simp only [addressMask, Word.ofAddress, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by decide : 2 ^ 160 - 1 < 2 ^ 256), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt h', Nat.mod_eq_of_lt h]

/-- `AND` with the address mask (literal form, mask on the right). -/
@[sol_norm] theorem ofAddress_and_addressMask (a : Address) :
    Word.ofAddress a &&& 1461501637330902918203684832716283019655932542975#256 =
      Word.ofAddress a :=
  ofAddress_and_mask a

/-- `AND` with the address mask (literal form, mask on the left). -/
@[sol_norm] theorem addressMask_and_ofAddress (a : Address) :
    1461501637330902918203684832716283019655932542975#256 &&& Word.ofAddress a =
      Word.ofAddress a := by
  rw [BitVec.and_comm]; exact ofAddress_and_mask a

/-- `EQ x x = 1`. -/
@[sol_norm] theorem eq_self (x : Word) : Word.eq x x = 1#256 := by
  simp [Word.eq, Word.ofBool]

end EvmLean.Solidity
