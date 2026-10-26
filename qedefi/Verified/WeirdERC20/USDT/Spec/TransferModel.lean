import Verified.WeirdERC20.USDT.Spec.TransferRun
import Verified.WeirdERC20.USDT.Spec.Write

/-!
# USDT `transfer`: the model and the code's words

`usdt_call_transfer'`: the model's outcome of a transfer (no assumption on `basisPointsRate`:
a fee above the value fails like a short balance). The bridges from the words the code computes
(`pausedW`, `blackW`, `xferFee`, the owner it reads) to the abstraction's fields.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Verified.WeirdERC20.USDT.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626 Finsupp

/-! ## The model -/

/-- The fee of the model, as a function of the state's parameters. -/
theorem usdt_feeOf' (s : VState Address) (v : ℕ) :
    (Variant.usdt : Variant Address).feeOf s v = min (v * s.feeBps / 10000) s.feeMax := by
  simp [Variant.feeOf, Variant.usdt]

/-- **USDT `transfer`, complete outcome**, for any parameters. -/
theorem usdt_call_transfer' (s : VState Address) (c d : Address) (v : ℕ) :
    M.call s c (.transfer d v) =
      if s.paused = true ∨ s.blacklisted c = true then .halt .revert
      else if s.bal c < v ∨ MAX < v * s.feeBps ∨ v < min (v * s.feeBps / 10000) s.feeMax then
        .halt .invalid
      else .ok ((Variant.usdt : Variant Address).credit s c d v) .empty := by
  have hu : (Variant.usdt : Variant Address).units s v = v := by
    simp [Variant.units, Variant.usdt, Variant.standard]
  have hmo : (Variant.usdt : Variant Address).moveOk s c d v = (!s.paused && !s.blacklisted c) :=
    Variant.usdt_moveOk s c d v
  by_cases hg : s.paused = true ∨ s.blacklisted c = true
  · have hm : (Variant.usdt : Variant Address).moveOk s c d v = false := by
      rw [hmo]; rcases hg with h | h <;> simp [h]
    simp only [hg, ↓reduceIte, M, QEDefi.ERC20.Spec.USDT.usdtModel_call, Variant.call,
      Variant.step, Variant.transfer, hm, Bool.false_eq_true, Variant.failKind,
      Variant.guardOk, Bool.not_false]
    rfl
  · have hm : (Variant.usdt : Variant Address).moveOk s c d v = true := by
      rw [hmo]; push Not at hg; simp [hg.1, hg.2]
    simp only [hg, ↓reduceIte]
    by_cases ha : s.bal c < v ∨ MAX < v * s.feeBps ∨ v < min (v * s.feeBps / 10000) s.feeMax
    · have hs : (Variant.usdt : Variant Address).step s c (.transfer d v) = none := by
        simp only [Variant.step, Variant.transfer, hm, ↓reduceIte, Variant.move, hu,
          Variant.usdt_feeOverflow, usdt_feeOf']
        rcases ha with h | h | h
        · simp [h]
        · by_cases h' : s.bal c < v <;> simp [h, h']
        · by_cases h' : s.bal c < v <;> by_cases h'' : MAX < v * s.feeBps <;> simp [h, h', h'']
      have hk : (Variant.usdt : Variant Address).failKind s c (.transfer d v) = .invalid := by
        simp only [Variant.failKind, Variant.guardOk, hm, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte]
        split_ifs <;> simp [Variant.usdt]
      simp only [ha, ↓reduceIte, M, QEDefi.ERC20.Spec.USDT.usdtModel_call, Variant.call, hs, hk]
      rfl
    · push Not at ha
      obtain ⟨h1, h2, h3⟩ := ha
      have hs : (Variant.usdt : Variant Address).step s c (.transfer d v) =
          some ((Variant.usdt : Variant Address).credit s c d v) := by
        simp only [Variant.step, Variant.transfer, hm, ↓reduceIte, Variant.move, hu,
          Variant.usdt_feeOverflow, usdt_feeOf']
        simp [Nat.not_lt.2 h1, Nat.not_lt.2 h2, Nat.not_lt.2 h3]
      have hne : ¬ (s.bal c < v ∨ MAX < v * s.feeBps ∨ v < min (v * s.feeBps / 10000) s.feeMax) := by
        rintro (h | h | h) <;> omega
      simp only [hne, ↓reduceIte, M, QEDefi.ERC20.Spec.USDT.usdtModel_call, Variant.call, hs]
      simp [Variant.retData, Variant.usdt]

/-! ## The code's words -/

/-- An `isBlackListed` row as the code reads it. -/
theorem rowBool_get (x : Word) : rowBool.get x = 255#256 &&& x.div 1#256 := by
  apply BitVec.eq_of_toNat_eq
  simp only [rowBool, BitField.get, BitField.mask, Word.div, BitVec.toNat_and,
    BitVec.toNat_ushiftRight, BitVec.toNat_udiv, BitVec.toNat_ofNat]
  simp [Nat.and_comm]

/-- The owner word the code computes (`(slot0 / 1) & mask`, masked again). -/
theorem owner_mask (x : Word) :
    1461501637330902918203684832716283019655932542975#256 &&& x.div 1#256 =
      Word.ofAddress (Word.toAddress (ownerField.get x)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.ofAddress, Word.toAddress, ownerField, Field.get, Field.mask, Word.div,
    BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_udiv, BitVec.toNat_ofNat,
    BitVec.toNat_ushiftRight]
  rw [show (BitVec.allOnes 256).toNat >>> (256 - 8 * 20) = 2 ^ 160 - 1 by decide]
  simp only [Nat.mul_zero, Nat.shiftRight_zero]
  rw [show (1461501637330902918203684832716283019655932542975 : Nat) % 2 ^ 256 = 2 ^ 160 - 1 by
    decide, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    show (1 : Nat) % 2 ^ 256 = 1 by decide, Nat.div_one, Nat.mod_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide) :
      x.toNat % 2 ^ 160 < 2 ^ 256)]

theorem owner_mask2 (x : Word) :
    1461501637330902918203684832716283019655932542975#256 &&&
      (1461501637330902918203684832716283019655932542975#256 &&& x.div 1#256) =
      Word.ofAddress (Word.toAddress (ownerField.get x)) := by
  rw [owner_mask, addressMask_and_ofAddress]


/-! ## The state the code reads -/

section Words

variable {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}

theorem paused_iff : (readState crypto Act w t).paused = true ↔ pausedW w t ≠ 0#256 := by
  simp only [readState, pausedOf, pausedField_get]
  simp [bne_iff_ne]

theorem blacklisted_iff {a : Address} (ha : a ∈ Act) :
    (readState crypto Act w t).blacklisted a = true ↔ blackW crypto w t a ≠ 0#256 := by
  simp only [readState, blacklistedOf, rowBool_get, ha, decide_true, Bool.true_and]
  simp [bne_iff_ne]
  rfl

theorem bal_eq {a : Address} (ha : a ∈ Act) :
    (readState crypto Act w t).bal a = (w.sload t (balKey crypto a)).toNat := by
  simp only [readState, readMap_of_mem ha]; rfl

theorem bps_eq : (readState crypto Act w t).feeBps = (w.sload t 3#256).toNat := rfl

theorem maxFee_eq : (readState crypto Act w t).feeMax = (w.sload t 4#256).toNat := rfl

/-- The code's fee is the model's when `v · bps` fits a word. -/
theorem xferFee_toNat {v : ℕ} (hv : v < 2 ^ 256)
    (hno : v * (w.sload t 3#256).toNat < 2 ^ 256) :
    (xferFee w t (word v)).toNat =
      min (v * (readState crypto Act w t).feeBps / 10000) (readState crypto Act w t).feeMax := by
  rw [bps_eq, maxFee_eq]
  have hf : (fee0W w t (word v)).toNat = v * (w.sload t 3#256).toNat / 10000 := by
    simp only [fee0W, Word.div, BitVec.toNat_udiv, BitVec.toNat_mul, BitVec.toNat_ofNat,
      word]
    rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hno]
  unfold xferFee
  split_ifs with h
  · rw [hf] at h; omega
  · rw [hf] at h ⊢; omega

end Words


/-! ## The writes of a transfer -/

theorem balKey_eq (crypto : Crypto) (a : Address) :
    balKey crypto a = mappingSlot crypto (Word.ofAddress a) balancesSlot := rfl

/-- The owner's row as the code hashes it is the owner's `balances` row. -/
theorem ownerKey_eq (crypto : Crypto) (w : World) (t : Address) :
    ownerKey crypto w t = balKey crypto (ownerOf w t) := by
  simp only [ownerKey, owner_mask2, addressMask_and_ofAddress, ownerOf]
  rfl

section Writes

variable {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}

theorem total_bound {s : VState Address} (hsub : QEDefi.ERC20.Spec.YAMV2.SubSupply s)
    {a : Address} : s.bal a ≤ MAX :=
  le_trans (Token.le_total s.bal a) (le_trans hsub.1 hsub.2)

theorem total_bound2 {s : VState Address} (hsub : QEDefi.ERC20.Spec.YAMV2.SubSupply s)
    {a b : Address} (h : a ≠ b) : s.bal a + s.bal b ≤ MAX :=
  le_trans (QEDefi.ERC20.Spec.YAMV2.add_le_total h) (le_trans hsub.1 hsub.2)

/-- One write of an actor's balance, as the abstraction sees it. -/
theorem read_bal_write (hs : usdtAbs.Sound crypto Act) {a : Address} (ha : a ∈ Act)
    (hl : Live Act w t) (x : Word) :
    Live Act (w.sstore t (balKey crypto a) x) t ∧
    readState crypto Act (w.sstore t (balKey crypto a) x) t =
      { readState crypto Act w t with bal := (readState crypto Act w t).bal.update a x.toNat } := by
  obtain ⟨hl', hr⟩ := read_sstore_bal (token := t) hs ha hl x
  rw [read_eq_of_live hl', read_eq_of_live hl] at hr
  exact ⟨hl', hr⟩

/-- **The writes of a successful transfer.** With `v ≤ balance` and a fee `≤ v`, in a state
with the actors' supply bound: neither credit overflows, and the abstraction after the writes
is the model's `credit` (with the fee `feeOf`), the owner word the code logs is the owner's
address, and only the footprint changed. -/
theorem xfer_writes (hs : usdtAbs.Sound crypto Act) {c d : Address} (hc : c ∈ Act)
    (hd : d ∈ Act) (hl : Live Act w t)
    (hsub : QEDefi.ERC20.Spec.YAMV2.SubSupply (readState crypto Act w t)) {v : ℕ}
    (hv : v < 2 ^ 256) (hbal : v ≤ (readState crypto Act w t).bal c) {fee : Word}
    (hfee : fee.toNat ≤ v) :
    ((xferW1 crypto w t c (word v)).sload t (balKey crypto d)).toNat + (word v - fee).toNat <
      2 ^ 256 ∧
    (fee ≠ 0#256 → ((xferW2 crypto w t c d (word v) fee).sload t
      (ownerKey crypto (xferW2 crypto w t c d (word v) fee) t)).toNat + fee.toNat < 2 ^ 256) ∧
    (fee.toNat = (Variant.usdt : Variant Address).feeOf (readState crypto Act w t) v →
      read crypto Act (xferW3 crypto w t c d (word v) fee) t =
        (Variant.usdt : Variant Address).credit (readState crypto Act w t) c d v) ∧
    (1461501637330902918203684832716283019655932542975#256 &&&
      (1461501637330902918203684832716283019655932542975#256 &&&
        ((xferW3 crypto w t c d (word v) fee).sload t 0#256).div 1#256)) =
      Word.ofAddress (readState crypto Act w t).admin ∧
    FrameKeeps usdtAbs crypto Act t w (xferW3 crypto w t c d (word v) fee) := by
  set s := readState crypto Act w t with hs_def
  have hu : ∀ (s' : VState Address) (x : ℕ), (Variant.usdt : Variant Address).units s' x = x := by
    intro s' x; simp [Variant.units, Variant.usdt, Variant.standard]
  have hsink : (Variant.usdt : Variant Address).feeSink = .owner := rfl
  have ho : s.admin ∈ Act := hl.2.2
  have hvn : (word v).toNat = v := by simp only [word, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hv
  have hbc : s.bal c = (w.sload t (balKey crypto c)).toNat := bal_eq hc
  have hvf : (word v - fee).toNat = v - fee.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hvn]; exact hfee), hvn]
  -- the debit
  obtain ⟨hl1, hr1⟩ := read_bal_write (w := w) (t := t) hs hc hl
    (w.sload t (balKey crypto c) - word v)
  have hx1 : (w.sload t (balKey crypto c) - word v).toNat = s.bal c - v := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hvn]; omega), hvn, hbc]
  rw [hx1] at hr1
  set W1 := xferW1 crypto w t c (word v) with hW1
  have hA : (W1.sload t (balKey crypto d)).toNat = (s.bal.update c (s.bal c - v)) d := by
    rw [← bal_eq (w := W1) (t := t) hd, hr1]
  have hA' : (W1.sload t (balKey crypto d)).toNat = if d = c then s.bal c - v else s.bal d := by
    rw [hA, Finsupp.update_apply]
  have hadd : (W1.sload t (balKey crypto d)).toNat + (word v - fee).toNat < 2 ^ 256 := by
    rw [hA', hvf]
    split_ifs with hdc
    · have := total_bound hsub (a := c); simp only [MAX] at this; omega
    · have := total_bound2 hsub (Ne.symm hdc : c ≠ d) ; simp only [MAX] at this; omega
  -- the credit of `d`
  obtain ⟨hl2, hr2⟩ := read_bal_write (w := W1) (t := t) hs hd hl1
    (W1.sload t (balKey crypto d) + (word v - fee))
  have hx2 : (W1.sload t (balKey crypto d) + (word v - fee)).toNat =
      (s.bal.update c (s.bal c - v)) d + (v - fee.toNat) := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hadd, hA, hvf]
  rw [hr1, hx2] at hr2
  set W2 := xferW2 crypto w t c d (word v) fee with hW2
  have hown : ownerOf W2 t = s.admin := by
    have := congrArg VState.admin hr2
    simp only [readState] at this
    exact this
  have hok : ownerKey crypto W2 t = balKey crypto s.admin := by rw [ownerKey_eq, hown]
  set b2 := (s.bal.update c (s.bal c - v)).update d
    ((s.bal.update c (s.bal c - v)) d + (v - fee.toNat)) with hb2
  have hB : (W2.sload t (balKey crypto s.admin)).toNat = b2 s.admin := by
    rw [← bal_eq (w := W2) (t := t) ho, hr2]
  have hadd2 : fee ≠ 0#256 → (W2.sload t (ownerKey crypto W2 t)).toNat + fee.toNat <
      2 ^ 256 := by
    intro _
    rw [hok, hB, hb2]
    simp only [Finsupp.update_apply]
    have hm := total_bound hsub (a := c)
    simp only [MAX] at hm
    by_cases h1 : s.admin = d
    · simp only [h1, ↓reduceIte]
      by_cases h2 : d = c
      · simp only [h2, ↓reduceIte]; omega
      · simp only [h2, ↓reduceIte]
        have := total_bound2 hsub (Ne.symm h2 : c ≠ d); simp only [MAX] at this; omega
    · simp only [h1, ↓reduceIte]
      by_cases h2 : s.admin = c
      · simp only [h2, ↓reduceIte]; omega
      · simp only [h2, ↓reduceIte]
        have := total_bound2 hsub (Ne.symm h2 : c ≠ s.admin); simp only [MAX] at this; omega
  refine ⟨hadd, hadd2, ?_, ?_, ?_⟩
  · -- the abstraction after the writes is `credit`
    intro hff
    by_cases hf0 : fee = 0#256
    · have hz : fee.toNat = 0 := by rw [hf0]; rfl
      have hW3 : xferW3 crypto w t c d (word v) fee = W2 := by
        simp only [xferW3, hf0, ↓reduceIte]; rw [← hf0]
      rw [hW3, read_eq_of_live hl2, hr2]
      have hfo : (Variant.usdt : Variant Address).feeOf s v = 0 := by rw [← hff, hz]
      simp only [Variant.credit, hfo, hu, ↓reduceIte]
      congr 1
      ext x
      rw [hb2]
      simp only [Finsupp.update_apply, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
        Pi.sub_apply, Finsupp.single_apply, hz]
      split_ifs <;> subst_vars <;> first | omega | contradiction
    · obtain ⟨hl3, hr3⟩ := read_bal_write (w := W2) (t := t) hs ho hl2
        (W2.sload t (balKey crypto s.admin) + fee)
      have hW3 : xferW3 crypto w t c d (word v) fee =
          W2.sstore t (balKey crypto s.admin) (W2.sload t (balKey crypto s.admin) + fee) := by
        simp only [xferW3, hf0, ↓reduceIte]; rw [← hok]
      have hx3 : (W2.sload t (balKey crypto s.admin) + fee).toNat = b2 s.admin + fee.toNat := by
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by rw [← hok]; exact hadd2 hf0), hB]
      rw [hW3, read_eq_of_live hl3, hr3, hr2, hx3]
      have hfz : (Variant.usdt : Variant Address).feeOf s v ≠ 0 := by
        rw [← hff]; intro h; exact hf0 (BitVec.eq_of_toNat_eq (by simpa using h))
      simp only [Variant.credit, hfz, hu, hsink, ↓reduceIte]
      rw [← hff]
      congr 1
      ext x
      rw [hb2]
      simp only [Finsupp.update_apply, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
        Pi.sub_apply, Finsupp.single_apply]
      split_ifs <;> subst_vars <;> first | omega | contradiction
  · -- the owner word the code logs
    by_cases hf0 : fee = 0#256
    · have hW3 : xferW3 crypto w t c d (word v) fee = W2 := by
        simp only [xferW3, hf0, ↓reduceIte]; rw [← hf0]
      rw [hW3, owner_mask2]
      exact congrArg Word.ofAddress hown
    · obtain ⟨hl3, hr3⟩ := read_bal_write (w := W2) (t := t) hs ho hl2
        (W2.sload t (balKey crypto s.admin) + fee)
      have hW3 : xferW3 crypto w t c d (word v) fee =
          W2.sstore t (balKey crypto s.admin) (W2.sload t (balKey crypto s.admin) + fee) := by
        simp only [xferW3, hf0, ↓reduceIte]; rw [← hok]
      have h3 := congrArg VState.admin hr3
      simp only [readState] at h3
      rw [hW3, owner_mask2]
      exact congrArg Word.ofAddress (h3.trans hown)
  · -- only the footprint changed
    have hfp : ∀ a ∈ Act, footprint crypto Act (balKey crypto a) :=
      fun a ha => .inr (.inl ⟨a, ha, rfl⟩)
    have k2 : FrameKeeps usdtAbs crypto Act t w W2 :=
      FrameKeeps.sstore (FrameKeeps.sstore (frameKeeps_refl _ _ _ _) (hfp c hc) _) (hfp d hd) _
    by_cases hf0 : fee = 0#256
    · have hW3 : xferW3 crypto w t c d (word v) fee = W2 := by
        simp only [xferW3, hf0, ↓reduceIte]; rw [← hf0]
      rw [hW3]; exact k2
    · have hW3 : xferW3 crypto w t c d (word v) fee =
          W2.sstore t (balKey crypto s.admin) (W2.sload t (balKey crypto s.admin) + fee) := by
        simp only [xferW3, hf0, ↓reduceIte]; rw [← hok]
      rw [hW3]; exact FrameKeeps.sstore k2 (hfp _ ho) _

end Writes

end Verified.WeirdERC20.USDT.Spec
