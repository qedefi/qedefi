import Examples.AaveV3.AToken.State
import Examples.AaveV3.AToken.Tactic

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

/-! ## The packed `_userState` word -/

private theorem m120 : (1329227995784915872903807060280344575#256 : Word) = BitVec.ofNat 256 (2 ^ 120 - 1) := rfl
private theorem m128 : (340282366920938463463374607431768211455#256 : Word) = BitVec.ofNat 256 (2 ^ 128 - 1) := rfl
private theorem p128 : (340282366920938463463374607431768211456#256 : Word) = BitVec.twoPow 256 128 := by decide

/-- The user's word after `_userState[u].additionalData = index.toUint128()`: the old low 128
bits (balance, delegation byte) and the index in the high 128 bits, as the code computes it. -/
def userWordIndexed (W idx : Word) : Word :=
  340282366920938463463374607431768211455#256 &&& W |||
    340282366920938463463374607431768211456#256 * (340282366920938463463374607431768211455#256 &&& idx)

theorem low120_userWordIndexed (W idx : Word) :
    1329227995784915872903807060280344575#256 &&& userWordIndexed W idx =
      1329227995784915872903807060280344575#256 &&& W := by
  unfold userWordIndexed
  rw [m120, m128, p128, BitVec.mul_comm, ← BitVec.shiftLeft_eq_mul_twoPow]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and]
  by_cases h1 : i < 120
  · simp [h1, show i < 128 by omega]
  · simp [h1]

private theorem nm120 : (115792089237316195423570985008687907853268655437644779123584680200852849295360#256 : Word) =
    ~~~(BitVec.ofNat 256 (2 ^ 120 - 1)) := by decide

/-- The user's word after `_mint` writes the new balance `N` (`uint120`) into the indexed word,
as the code computes it. -/
def userWordMinted (N W idx : Word) : Word :=
  1329227995784915872903807060280344575#256 &&& N |||
    115792089237316195423570985008687907853268655437644779123584680200852849295360#256 &&&
      userWordIndexed W idx

theorem getLsbD_userWordMinted (N W idx : Word) (i : Nat) :
    (userWordMinted N W idx).getLsbD i =
      if i < 120 then N.getLsbD i else if i < 128 then W.getLsbD i
      else (decide (i < 256) && idx.getLsbD (i - 128)) := by
  unfold userWordMinted userWordIndexed
  rw [m120, m128, p128, nm120, BitVec.mul_comm, ← BitVec.shiftLeft_eq_mul_twoPow]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    BitVec.getLsbD_not, Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < 120
  · simp [h1, show i < 128 by omega, show i < 256 by omega]
  · by_cases h2 : i < 128
    · simp [h1, h2, show i < 256 by omega]
    · by_cases h3 : i < 256
      · simp [h1, h2, h3]
        exact fun _ => ⟨by omega, by omega⟩
      · simp [h1, h2, h3]

theorem toNat_userWordMinted_mod (N W idx : Word) :
    (userWordMinted N W idx).toNat % 2 ^ 120 = N.toNat % 2 ^ 120 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow, BitVec.testBit_toNat, getLsbD_userWordMinted]
  by_cases h : i < 120 <;> simp [h]

theorem toNat_userWordMinted_div (N W idx : Word) :
    (userWordMinted N W idx).toNat / 2 ^ 128 = idx.toNat % 2 ^ 128 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, BitVec.testBit_toNat, getLsbD_userWordMinted]
  simp only [show ¬(i + 128 < 120) by omega, show ¬(i + 128 < 128) by omega, ↓reduceIte,
    Nat.add_sub_cancel]
  by_cases h : i < 128
  · simp [h, show i + 128 < 256 by omega]
  · simp [h]
    intro; omega

theorem toNat_userWordMinted_deleg (N W idx : Word) :
    (userWordMinted N W idx).toNat / 2 ^ 120 % 2 ^ 8 = W.toNat / 2 ^ 120 % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, BitVec.testBit_toNat, getLsbD_userWordMinted]
  by_cases h : i < 8
  · simp only [show ¬(i + 120 < 120) by omega, show i + 120 < 128 by omega, ↓reduceIte, h,
      decide_true, Bool.true_and]
  · simp [h]

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
