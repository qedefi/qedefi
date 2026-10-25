import Verified.AaveV3.AToken.Mint.Basic

/-!
# `AToken.mint` by the Pool: reverts

`mint_reverts_of_zero`: a zero scaled amount reverts with `InvalidMintAmount()` and changes
nothing. `mint_reverts_of_cast`: a scaled amount of 2^120 or more never mints: whichever check
fails first (the checked `scaledBalance + amount`, `rayMulFloor`'s overflow guard, the
accrued-interest subtraction, `index.toUint128()`, finally `amount.toUint120()` after the
index write), the frame reverts, so its writes are rolled back.
-/

namespace Verified.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.AaveV3.Contracts
open Verified.Solmate.ERC20 (lt_size_four)

/-- `rayMulFloor`'s guard fails (is `0`) when `a * b` overflows. -/
theorem rayGuard_eq_zero {x y : Word} (h : 2 ^ 256 ≤ x.toNat * y.toNat) :
    (Word.iszero y ||| Word.iszero (Word.gt x
      (Word.div 115792089237316195423570985008687907853269984665640564039457584007913129639935#256 y)))
      = 0#256 := by
  have h' : y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat := by
    rw [overflow_test_iff']; omega
  have hy : y ≠ 0#256 := fun e => h'.1 (by rw [e]; rfl)
  have hdiv : (Word.div MAXW y).toNat = (2 ^ 256 - 1) / y.toNat := by
    simp only [Word.div, BitVec.toNat_udiv, toNat_MAXW]
  have hgt : Word.gt x (Word.div MAXW y) = 1#256 := by
    rw [gt_eq_ofBool, hdiv, decide_eq_true h'.2]; rfl
  rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639935#256 : Word)
    = MAXW from rfl, hgt, iszero_of_ne hy, iszero_one]
  decide

theorem gt_eq_one_of_lt {x : Word} {n : Nat} (h : n < x.toNat) (hn : n < 2 ^ 256) :
    Word.gt x (BitVec.ofNat 256 n) = 1#256 := by
  rw [gt_eq_ofBool, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, decide_eq_true h]; rfl

/-- The revert data of `InvalidMintAmount()`: its selector `0xccfad018`. -/
def invalidMintAmount : ByteArray := ⟨#[0xcc, 0xfa, 0xd0, 0x18]⟩

theorem invalidMintAmount_mem : ("InvalidMintAmount()", (0xccfad018 : UInt32)) ∈ AToken.errors := by
  decide

theorem read_invalidMintAmount (mem : Memory) (off : Nat) :
    (mem.storeWord off
        92714969087459791759437094555211621909296636002608906789850377158154126360576#256).read
      off 4 = invalidMintAmount := by
  simp only [reduceErrorSelector]; decide +kernel

/-- **`mint` of a zero scaled amount by the Pool** reverts with `InvalidMintAmount()` and
changes nothing. -/
theorem mint_reverts_of_zero (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xb3f1c93d)
    (hsize : 132 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    {c u : Address} {idx : Word}
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress c)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = Word.ofAddress u)
    (harg2 : Bytes.toWord (readBytes m.frame.msg.data 68 32) = 0#256)
    (harg3 : Bytes.toWord (readBytes m.frame.msg.data 100 32) = idx)
    (hc : m.frame.msg.caller = pool) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (RevertsWith invalidMintAmount 3000 m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
      (BitVec.ofNat 256 128)) = 1 := iszero_slt_calldatasize (by omega) (by omega)
  have hc' : Word.eq 773725381719276160229242488166406195640368342242#256
      (Word.ofAddress m.frame.msg.caller) = 1#256 := by rw [hc]; exact poolWord_eq_pool
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, hc',
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [read_invalidMintAmount]
  · dsimp only [outputMachine]
    evm_gas

/-- **`mint` of a scaled amount ≥ 2^120 by the Pool reverts** (in a non-static frame, so that
the index write before `toUint120` does not halt instead). -/
theorem mint_reverts_of_cast (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xb3f1c93d)
    (hsize : 132 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    {c u : Address} {amt idx : Word}
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress c)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = Word.ofAddress u)
    (harg2 : Bytes.toWord (readBytes m.frame.msg.data 68 32) = amt)
    (harg3 : Bytes.toWord (readBytes m.frame.msg.data 100 32) = idx)
    (hc : m.frame.msg.caller = pool) (hg : 100000 ≤ m.frame.gasLeft)
    (hamt : 2 ^ 120 ≤ amt.toNat) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
      (BitVec.ofNat 256 128)) = 1 := iszero_slt_calldatasize (by omega) (by omega)
  have hc' : Word.eq 773725381719276160229242488166406195640368342242#256
      (Word.ofAddress m.frame.msg.caller) = 1#256 := by rw [hc]; exact poolWord_eq_pool
  have hneg : 0#256 - amt ≠ 0#256 := by
    intro h
    have : amt = 0#256 := by have := congrArg (· + amt) h; simpa using this.symm
    subst this; simp at hamt
  obtain ⟨W, hW⟩ : ∃ W, m.world.sload m.frame.msg.currentTarget
      (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress u) ++ Bytes.ofWord 52#256)) = W :=
    ⟨_, rfl⟩
  obtain ⟨bal, hbal⟩ : ∃ b, 1329227995784915872903807060280344575#256 &&& W = b := ⟨_, rfl⟩
  obtain ⟨prev, hprev⟩ : ∃ p, 340282366920938463463374607431768211455#256 &&&
      W.div 340282366920938463463374607431768211456#256 = p := ⟨_, rfl⟩
  have hbal120 : bal.toNat < 2 ^ 120 := by
    rw [← hbal, mask120_and, BitVec.toNat_ofNat]; omega
  have hprev128 : prev.toNat < 2 ^ 128 := by
    rw [← hprev, mask128_and_div, BitVec.toNat_ofNat]
    have := W.isLt
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, hc',
    hW, hbal, hprev, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self,
    Memory.read_64]
  -- `scaledBalance + amt` overflows: `Panic(0x11)`
  by_cases h1 : 2 ^ 256 ≤ amt.toNat + bal.toNat
  · simp only [ERC20.gt_add_self_eq_one h1, iszero_one]
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, hc',
    hW, hbal, hprev, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self,
    Memory.read_64]
    exact ⟨_, rfl⟩
  simp only [ERC20.gt_add_self_eq_zero (Nat.lt_of_not_le h1), iszero_zero]
  have hba : (bal + amt).toNat = bal.toNat + amt.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  -- `rayMulFloor(scaledBalance + amt, index)` overflows: `revert(0, 0)`
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, hc',
    hW, hbal, hprev, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self,
    Memory.read_64]
  by_cases h2 : 2 ^ 256 ≤ (bal.toNat + amt.toNat) * idx.toNat
  · simp only [rayGuard_eq_zero (x := bal + amt) (y := idx) (by rw [hba]; exact h2)]
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, hc',
    hW, hbal, hprev, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self,
    Memory.read_64]
    exact ⟨_, rfl⟩
  have hmul : (bal.toNat + amt.toNat) * idx.toNat < 2 ^ 256 := Nat.lt_of_not_le h2
  have hBP : bal.toNat * prev.toNat < 2 ^ 256 := by
    have := Nat.mul_le_mul (Nat.le_of_lt hbal120) (Nat.le_of_lt hprev128)
    simp only [Nat.reducePow, Nat.reduceMul] at this ⊢; omega
  have hBI : bal.toNat * idx.toNat < 2 ^ 256 := by
    have := Nat.mul_le_mul_right idx.toNat (Nat.le_add_right bal.toNat amt.toNat); omega
  simp only [rayGuard_eq_one (x := bal + amt) (y := idx) (by rw [hba]; exact hmul)]
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, hc',
    hW, hbal, hprev, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self,
    Memory.read_64, rayGuard_eq_one hBP, rayGuard_eq_one hBI]
  -- the accrued interest `rayMul(balance, index) - rayMul(balance, previousIndex)` is negative:
  -- `Panic(0x11)`
  by_cases h3 : bal.toNat * idx.toNat / 1000000000000000000000000000 <
      bal.toNat * prev.toNat / 1000000000000000000000000000
  · simp only [gt_sub_self_of_lt (x := Word.div (bal * idx) 1000000000000000000000000000#256)
      (y := Word.div (bal * prev) 1000000000000000000000000000#256)
      (by rw [toNat_rayMul hBI, toNat_rayMul hBP]; exact h3), iszero_one]
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, hc',
    hW, hbal, hprev, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self,
    Memory.read_64]
    exact ⟨_, rfl⟩
  simp only [gt_sub_self_of_le (x := Word.div (bal * idx) 1000000000000000000000000000#256)
    (y := Word.div (bal * prev) 1000000000000000000000000000#256)
    (by rw [toNat_rayMul hBI, toNat_rayMul hBP]; exact Nat.le_of_not_lt h3), iszero_zero]
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, hc',
    hW, hbal, hprev, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self,
    Memory.read_64]
  -- `index.toUint128()` overflows: `SafeCastOverflowedUintDowncast(128, index)`
  by_cases h4 : 2 ^ 128 ≤ idx.toNat
  · simp only [gt_eq_one_of_lt (x := idx) (n := 2 ^ 128 - 1) (by omega) (by decide),
      iszero_one]
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, hc',
    hW, hbal, hprev, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self,
    Memory.read_64]
    exact ⟨_, rfl⟩
  simp only [gt_eq_zero_of_le (x := idx) (n := 2 ^ 128 - 1) (by omega) (by decide),
    iszero_zero]
  -- the index write, then `scaledAmount.toUint120()` overflows:
  -- `SafeCastOverflowedUintDowncast(120, scaledAmount)`
  have hc120 := gt_eq_one_of_lt (x := amt) (n := 2 ^ 120 - 1) (by omega) (by decide)
  simp only [Nat.reducePow, Nat.reduceSub] at hc120
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, hc',
    hW, hbal, hprev, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self,
    Memory.read_64, hc120, iszero_one]
  exact ⟨_, rfl⟩

end Verified.AaveV3.AToken
