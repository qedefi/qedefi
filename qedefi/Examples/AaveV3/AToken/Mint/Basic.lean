import Examples.AaveV3.AToken.State
import EvmLogic.Tactic.Abstract
import EvmLogic.Tactic.Mcopy
import EvmLogic.Tactic.StepExt
import EvmLogic.Program.GasBound

/-!
# `AToken.mint`: word lemmas, the rewards-controller assumption, the postcondition

`mint(caller, onBehalfOf, scaledAmount, index)` (`ScaledBalanceTokenBase._mintScaled`, then
`MintableIncentivizedERC20._mint`) writes the proxy storage three times: the user's packed
`_userState` word with the new index (`index.toUint128()` in the high 128 bits), `_totalSupply`
(slot 54) plus the scaled amount, and the user's word again with the new balance in the low 120
bits. Then it calls `REWARDS_CONTROLLER.handleAction(user, oldSupply, oldBalance)`, an external
`CALL` to code the token does not control: its effect is an explicit hypothesis,
`HandleActionOk` (it succeeds and leaves the token's storage alone), the modelling gap of these
theorems.

This file has the word identities for solc's masks and checks (`rayGuard_eq_one` for
`WadRayMath.rayMulFloor`'s overflow guard, `toNat_rayMul`, the packing lemmas about
`userWordIndexed`/`userWordMinted`), `HandleActionOk`, `mintWorld` (the proxy storage after
the three writes) and the postcondition `MintOk`.
-/

namespace Examples.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter

/-! ## Checked arithmetic as solc compiles it -/

/-- `rayMulFloor`'s guard `or(iszero(b), iszero(gt(a, div(not(0), b))))` passes (is `1`) when
`a * b` does not overflow. -/
theorem rayGuard_eq_one {x y : Word} (h : x.toNat * y.toNat < 2 ^ 256) :
    (Word.iszero y ||| Word.iszero (Word.gt x
      (Word.div 115792089237316195423570985008687907853269984665640564039457584007913129639935#256 y)))
      = 1#256 := by
  have h' : ¬ (y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat) := by
    rw [overflow_test_iff']; omega
  by_cases hy : y = 0#256
  · subst hy
    rw [iszero_zero, gt_eq_ofBool]
    simp only [Word.ofBool]
    split <;> decide
  · have hdiv : (Word.div MAXW y).toNat = (2 ^ 256 - 1) / y.toNat := by
      simp only [Word.div, BitVec.toNat_udiv, toNat_MAXW]
    have hgt : Word.gt x (Word.div MAXW y) = 0#256 := by
      apply BitVec.eq_of_toNat_eq
      rw [gt_eq_ofBool, hdiv]
      have hy' : y.toNat ≠ 0 := fun e => hy (BitVec.eq_of_toNat_eq (by simpa using e))
      simp only [Word.ofBool]
      rw [decide_eq_false (by omega)]
      rfl
    rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639935#256 : Word)
      = MAXW from rfl, hgt, iszero_zero, iszero_of_ne hy]
    decide

theorem toNat_rayMul {x y : Word} (h : x.toNat * y.toNat < 2 ^ 256) :
    (Word.div (x * y) 1000000000000000000000000000#256).toNat =
      x.toNat * y.toNat / 1000000000000000000000000000 := by
  simp only [Word.div, BitVec.toNat_udiv, BitVec.toNat_mul, Nat.mod_eq_of_lt h]
  rfl

theorem gt_eq_zero_of_le {x : Word} {n : Nat} (h : x.toNat ≤ n) (hn : n < 2 ^ 256) :
    Word.gt x (BitVec.ofNat 256 n) = 0#256 := by
  rw [gt_eq_ofBool, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, decide_eq_false (by omega)]; rfl

theorem and_mask120_of_lt {x : Word} (h : x.toNat < 2 ^ 120) :
    x &&& 1329227995784915872903807060280344575#256 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1329227995784915872903807060280344575#256).toNat = 2 ^ 120 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

theorem mask120_and_of_lt {x : Word} (h : x.toNat < 2 ^ 120) :
    1329227995784915872903807060280344575#256 &&& x = x := by
  rw [BitVec.and_comm]; exact and_mask120_of_lt h

theorem iszero_iszero_iszero (x : Word) : Word.iszero (Word.iszero (Word.iszero x)) = Word.iszero x := by
  by_cases h : x = 0#256
  · subst h; decide
  · rw [iszero_of_ne h]; decide

/-! ## The packed `_userState` word

solc's two writes of the packed word (`State.lean`: `balanceField`, `delegationField`,
`indexField`) are `indexField.set` and `balanceField.set` (`userWordIndexed_eq`,
`userWordMinted_eq`); every fact below is a read-after-write law of `BitField`. -/

/-- The user's word after `_userState[u].additionalData = index.toUint128()`: the old low 128
bits (balance, delegation byte) and the index in the high 128 bits, as the code computes it. -/
def userWordIndexed (W idx : Word) : Word :=
  340282366920938463463374607431768211455#256 &&& W |||
    340282366920938463463374607431768211456#256 * (340282366920938463463374607431768211455#256 &&& idx)

/-- solc's index write is `indexField.set`. -/
theorem userWordIndexed_eq (W idx : Word) : userWordIndexed W idx = indexField.set W idx := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitField.getLsbD_set _ _ _ _ hi]
  simp only [userWordIndexed, indexField]
  rw [show (340282366920938463463374607431768211456#256 : Word) = BitVec.twoPow 256 128 by decide,
    show (340282366920938463463374607431768211455#256 : Word) = BitVec.ofNat 256 (2 ^ 128 - 1)
      from rfl, BitVec.mul_comm, ← BitVec.shiftLeft_eq_mul_twoPow]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and]
  by_cases h : i < 128
  · simp [h, show ¬ 128 ≤ i by omega]
  · simp [h, show i - 128 < 128 by omega, show 128 ≤ i by omega, show i < 128 + 128 by omega,
      show i - 128 < 256 by omega]

theorem low120_userWordIndexed (W idx : Word) :
    1329227995784915872903807060280344575#256 &&& userWordIndexed W idx =
      1329227995784915872903807060280344575#256 &&& W := by
  rw [mask120_and_eq_get, mask120_and_eq_get, userWordIndexed_eq,
    BitField.get_set_of_disjoint _ _ index_balance_disjoint]

/-- The user's word after `_mint` writes the new balance `N` (`uint120`) into the indexed word,
as the code computes it. -/
def userWordMinted (N W idx : Word) : Word :=
  1329227995784915872903807060280344575#256 &&& N |||
    115792089237316195423570985008687907853268655437644779123584680200852849295360#256 &&&
      userWordIndexed W idx

/-- solc's balance write is `balanceField.set`. -/
theorem userWordMinted_eq (N W idx : Word) :
    userWordMinted N W idx = balanceField.set (userWordIndexed W idx) N := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitField.getLsbD_set _ _ _ _ hi]
  simp only [userWordMinted, balanceField]
  rw [show (1329227995784915872903807060280344575#256 : Word) = BitVec.ofNat 256 (2 ^ 120 - 1)
      from rfl,
    show (115792089237316195423570985008687907853268655437644779123584680200852849295360#256 :
      Word) = ~~~(BitVec.ofNat 256 (2 ^ 120 - 1)) by decide]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and, Nat.zero_le, true_and,
    Nat.zero_add, Nat.sub_zero]
  by_cases h : i < 120 <;> simp [h]

theorem getLsbD_userWordMinted (N W idx : Word) (i : Nat) :
    (userWordMinted N W idx).getLsbD i =
      if i < 120 then N.getLsbD i else if i < 128 then W.getLsbD i
      else (decide (i < 256) && idx.getLsbD (i - 128)) := by
  by_cases hi : i < 256
  · rw [userWordMinted_eq, BitField.getLsbD_set _ _ _ _ hi, userWordIndexed_eq,
      BitField.getLsbD_set _ _ _ _ hi]
    simp only [balanceField, indexField, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]
    by_cases h1 : i < 120
    · simp [h1]
    · by_cases h2 : i < 128
      · simp [h1, h2, show ¬ 128 ≤ i by omega]
      · simp [h1, h2, show 128 ≤ i by omega, hi]
  · simp [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt hi), show ¬ i < 120 by omega,
      show ¬ i < 128 by omega, hi]

theorem toNat_userWordMinted_mod (N W idx : Word) :
    (userWordMinted N W idx).toNat % 2 ^ 120 = N.toNat % 2 ^ 120 := by
  have := BitField.toNat_get_set_self balanceField balanceField_valid (userWordIndexed W idx) N
  rw [BitField.toNat_get _ (by decide), ← userWordMinted_eq] at this
  simpa [balanceField] using this

theorem toNat_userWordMinted_div (N W idx : Word) :
    (userWordMinted N W idx).toNat / 2 ^ 128 = idx.toNat % 2 ^ 128 := by
  have hL : (indexField.get (userWordMinted N W idx)).toNat = idx.toNat % 2 ^ 128 := by
    rw [userWordMinted_eq, BitField.get_set_of_disjoint _ _ balance_index_disjoint,
      userWordIndexed_eq, BitField.toNat_get_set_self _ indexField_valid]; rfl
  have hR := BitField.toNat_get indexField (by decide) (userWordMinted N W idx)
  have hlt : (userWordMinted N W idx).toNat / 2 ^ 128 < 2 ^ 128 := by
    have := (userWordMinted N W idx).isLt; omega
  rw [hL] at hR
  simp only [indexField] at hR
  rw [hR, Nat.mod_eq_of_lt hlt]

theorem toNat_userWordMinted_deleg (N W idx : Word) :
    (userWordMinted N W idx).toNat / 2 ^ 120 % 2 ^ 8 = W.toNat / 2 ^ 120 % 2 ^ 8 := by
  have hL : delegationField.get (userWordMinted N W idx) = delegationField.get W := by
    rw [userWordMinted_eq, BitField.get_set_of_disjoint _ _ balance_delegation_disjoint,
      userWordIndexed_eq, BitField.get_set_of_disjoint _ _ index_delegation_disjoint]
  have := congrArg BitVec.toNat hL
  rw [BitField.toNat_get _ (by decide), BitField.toNat_get _ (by decide)] at this
  exact this

/-! ## The rewards controller (modelling assumption) -/

/-- **Modelling assumption on the rewards controller's code `rc`.** Called without value by
`token` with the calldata of `handleAction(user, totalSupply, userBalance)` (selector
`0x31873e2e`, 100 bytes), in any frame, it succeeds and leaves `token`'s storage unchanged.
Nothing else is assumed (gas use, other accounts' state, logs, return data are arbitrary). -/
def HandleActionOk (rc : ByteArray) (token : Address) : Prop :=
  ∀ (mc : Machine) (user : Address) (supply userBalance : Word), Fresh rc mc →
    mc.frame.msg.caller = token → mc.frame.msg.value = 0 →
    Abi.selectorOf mc.frame.msg.data = 0x31873e2e → mc.frame.msg.data.size = 100 →
    Bytes.toWord (readBytes mc.frame.msg.data 4 32) = Word.ofAddress user →
    Bytes.toWord (readBytes mc.frame.msg.data 36 32) = supply →
    Bytes.toWord (readBytes mc.frame.msg.data 68 32) = userBalance →
    Halts mc (fun mf o => (∃ out, o = .success out) ∧
      ∀ slot, mf.world.sload token slot = mc.world.sload token slot)

/-! ## The effect of `mint` -/

/-- The storage of `t` after `mint(_, u, amt, idx)`'s three writes: `_userState[u]` with the
new index, `_totalSupply + amt`, `_userState[u]` with the new balance `scaledBalance + amt`. -/
def mintWorld (crypto : Crypto) (w : World) (t u : Address) (amt idx : Word) : World :=
  ((w.sstore t (userStateSlot crypto u) (userWordIndexed (w.sload t (userStateSlot crypto u)) idx)
    ).sstore t 54#256 (amt + w.sload t 54#256)).sstore t (userStateSlot crypto u)
    (userWordMinted (amt + scaledBalance crypto w t u) (w.sload t (userStateSlot crypto u)) idx)

/-- A successful `mint(_, u, amt, idx)` in frame `m`: returns `scaledBalance == 0` (whether `u`
held nothing before), and the executing account's storage is `mintWorld`. -/
def MintOk (u : Address) (amt idx : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord (Word.iszero
    (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u))) ∧
  ∀ slot, mf.world.sload m.frame.msg.currentTarget slot =
    (mintWorld m.ctx.crypto m.world m.frame.msg.currentTarget u amt idx).sload
      m.frame.msg.currentTarget slot

end Examples.AaveV3.AToken
