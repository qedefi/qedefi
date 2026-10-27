import Verified.WeirdERC20.USDT.Spec.TransferFromHigh
import Verified.WeirdERC20.USDT.Spec.Transfer

/-!
# USDT's `transferFrom` satisfies `CallSpec`

`usdt_transferFrom`: in every frame `Start` admits, at any gas and with any value, an
ABI-encoded `transferFrom(src, dst, v)` whose addresses are actors ends as `usdtModel` says: it
reverts when the token is paused or `src` is blacklisted; it ends with `INVALID` when the
allowance (unless `MAX_UINT`) or `src`'s balance is short, `v · basisPointsRate` overflows or
the fee exceeds `v`; otherwise it spends the allowance (`usdtSpent`), moves the tokens as
`transfer` does (`Variant.credit`), returns no data and logs the model's `Transfer`s; with value,
in a static frame or below `g₀` it fails.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Verified.WeirdERC20.USDT.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626

/-! ## The model -/

/-- The model's failures of a `transferFrom` past its guards. -/
def TfFail (s : VState Address) (c src : Address) (v : ℕ) : Prop :=
  (s.allowance src c < MAX ∧ s.allowance src c < v) ∨ s.bal src < v ∨ MAX < v * s.feeBps ∨
    v < min (v * s.feeBps / 10000) s.feeMax

instance (s : VState Address) (c src : Address) (v : ℕ) : Decidable (TfFail s c src v) := by
  unfold TfFail; infer_instance

/-- **USDT `transferFrom`, complete outcome**, for any parameters (a fee above the value fails
like a short balance). -/
theorem usdt_call_transferFrom' (s : VState Address) (c src d : Address) (v : ℕ) :
    M.call s c (.transferFrom src d v) =
      if s.paused = true ∨ s.blacklisted src = true then .halt .revert
      else if TfFail s c src v then .halt .invalid
      else .ok ((Variant.usdt : Variant Address).credit (Variant.usdtSpent s src c v) src d v)
        .empty := by
  have hu : ∀ t : VState Address, (Variant.usdt : Variant Address).units t v = v := fun t => by
    simp [Variant.units, Variant.usdt, Variant.standard]
  have hsp : (Variant.usdt : Variant Address).spend s src c v =
      if s.allowance src c < MAX ∧ s.allowance src c < v then none
      else some (Variant.usdtSpent s src c v) := by
    unfold Variant.spend Variant.usdtSpent
    by_cases h1 : MAX ≤ s.allowance src c
    · simp [Variant.usdt, Variant.standard, Infinite.test, h1]
    · have h1' : s.allowance src c < MAX := by omega
      by_cases h2 : s.allowance src c < v <;>
        simp [Variant.usdt, Variant.standard, Infinite.test, h1, h1', h2]
  have hbs : (Variant.usdtSpent s src c v).bal = s.bal ∧
      (Variant.usdtSpent s src c v).feeBps = s.feeBps ∧
      (Variant.usdtSpent s src c v).feeMax = s.feeMax := by
    unfold Variant.usdtSpent; split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  have hfo : (Variant.usdt : Variant Address).feeOf (Variant.usdtSpent s src c v) v =
      min (v * s.feeBps / 10000) s.feeMax := by
    rw [usdt_feeOf', hbs.2.1, hbs.2.2]
  by_cases hg : s.paused = true ∨ s.blacklisted src = true
  · have hm : (Variant.usdt : Variant Address).moveOk s src d v = false := by
      rw [Variant.usdt_moveOk]; rcases hg with h | h <;> simp [h]
    have hs : (Variant.usdt : Variant Address).step s c (.transferFrom src d v) = none := by
      simp only [Variant.step, Variant.transferFrom, hm, Bool.false_eq_true, ↓reduceIte]
    have hk : (Variant.usdt : Variant Address).failKind s c (.transferFrom src d v) = .revert := by
      simp only [Variant.failKind, Variant.guardOk, hm, Bool.not_false, ↓reduceIte]; rfl
    simp only [hg, ↓reduceIte, M, QEDefi.ERC20.Spec.USDT.usdtModel_call, Variant.call, hs, hk]
    rfl
  · have hm : (Variant.usdt : Variant Address).moveOk s src d v = true := by
      rw [Variant.usdt_moveOk]; push Not at hg; simp [hg.1, hg.2]
    simp only [hg, ↓reduceIte]
    by_cases ha : TfFail s c src v
    · have hs : (Variant.usdt : Variant Address).step s c (.transferFrom src d v) = none := by
        simp only [Variant.step, Variant.transferFrom, hm, ↓reduceIte, hsp]
        by_cases h1 : s.allowance src c < MAX ∧ s.allowance src c < v
        · simp [h1]
        · simp only [h1, ↓reduceIte, Option.bind_some, Variant.move, hu,
            Variant.usdt_feeOverflow, hbs.1, hbs.2.1, hfo]
          rcases ha with h | h | h | h
          · exact absurd h h1
          · simp [h]
          · by_cases h' : s.bal src < v <;> simp [h, h']
          · by_cases h' : s.bal src < v <;> by_cases h'' : MAX < v * s.feeBps <;> simp [h, h', h'']
      have hk : (Variant.usdt : Variant Address).failKind s c (.transferFrom src d v) =
          .invalid := by
        simp only [Variant.failKind, Variant.guardOk, hm, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte]
        split_ifs <;> simp [Variant.usdt]
      simp only [ha, ↓reduceIte, M, QEDefi.ERC20.Spec.USDT.usdtModel_call, Variant.call, hs, hk]
      rfl
    · unfold TfFail at ha
      push Not at ha
      obtain ⟨h1, h2, h3, h4⟩ := ha
      have h1' : ¬ (s.allowance src c < MAX ∧ s.allowance src c < v) := by
        intro h; exact absurd (h1 h.1) (by omega)
      have hs : (Variant.usdt : Variant Address).step s c (.transferFrom src d v) =
          some ((Variant.usdt : Variant Address).credit (Variant.usdtSpent s src c v) src d v) := by
        simp only [Variant.step, Variant.transferFrom, hm, ↓reduceIte, hsp, h1', Option.bind_some,
          Variant.move, hu, Variant.usdt_feeOverflow, hbs.1, hbs.2.1, hfo]
        simp [Nat.not_lt.2 h2, Nat.not_lt.2 h3, Nat.not_lt.2 h4]
      have hne : ¬ TfFail s c src v := by
        unfold TfFail
        rintro (h | h | h | h)
        · exact h1' h
        · omega
        · omega
        · omega
      simp only [hne, ↓reduceIte, M, QEDefi.ERC20.Spec.USDT.usdtModel_call, Variant.call, hs]
      simp [Variant.retData, Variant.usdt]

/-! ## The allowance step on the words -/

theorem FrameKeeps.trans' {crypto : Crypto} {Act : Finset Address} {token : Address}
    {w w' w'' : World} (h : FrameKeeps usdtAbs crypto Act token w w')
    (h' : FrameKeeps usdtAbs crypto Act token w' w'') :
    FrameKeeps usdtAbs crypto Act token w w'' where
  own k hk := (h'.own k hk).trans (h.own k hk)
  code := h'.code.trans h.code
  nonce := h'.nonce.trans h.nonce
  balance := h'.balance.trans h.balance
  others b hb := (h'.others b hb).trans (h.others b hb)

theorem allowKey_eq (crypto : Crypto) (o sp : Address) :
    allowKey crypto o sp = mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp)
      allowedSlot := rfl

section Spend

variable {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}

theorem allow_eq {o sp : Address} (ho : o ∈ Act) (hsp : sp ∈ Act) :
    (readState crypto Act w t).allowance o sp = (w.sload t (allowKey crypto o sp)).toNat := by
  simp only [readState, readMap2, ho, hsp, and_self, ↓reduceIte]; rfl

theorem usdtSpent_fields (s : VState Address) (src c : Address) (v : ℕ) :
    (Variant.usdtSpent s src c v).bal = s.bal ∧ (Variant.usdtSpent s src c v).supply = s.supply ∧
    (Variant.usdtSpent s src c v).feeBps = s.feeBps ∧
    (Variant.usdtSpent s src c v).feeMax = s.feeMax ∧
    (Variant.usdtSpent s src c v).admin = s.admin := by
  unfold Variant.usdtSpent; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The allowance step.** With the allowance not short (unless `MAX_UINT`), the world after it
is in scope, reads as `usdtSpent`, and changed only the footprint. -/
theorem tf_spend (hs : usdtAbs.Sound crypto Act) {src c : Address} (hsrc : src ∈ Act)
    (hc : c ∈ Act) (hl : Live Act w t) {v : ℕ} (hv : v < 2 ^ 256)
    (hok : ¬ ((w.sload t (allowKey crypto src c)).toNat < 2 ^ 256 - 1 ∧
      (w.sload t (allowKey crypto src c)).toNat < v)) :
    Live Act (tfW0 crypto w t src c (word v)) t ∧
    readState crypto Act (tfW0 crypto w t src c (word v)) t =
      Variant.usdtSpent (readState crypto Act w t) src c v ∧
    FrameKeeps usdtAbs crypto Act t w (tfW0 crypto w t src c (word v)) := by
  have hvn := word_toNat' hv
  have hal := allow_eq (crypto := crypto) (w := w) (t := t) hsrc hc
  unfold tfW0
  split_ifs with h
  · obtain ⟨hl', hr⟩ := read_sstore_allow (token := t) hs hsrc hc hl
      (w.sload t (allowKey crypto src c) - word v)
    rw [← allowKey_eq] at hl' hr
    refine ⟨hl', ?_, ?_⟩
    · rw [← read_eq_of_live hl', hr, read_eq_of_live hl]
      have hle : v ≤ (w.sload t (allowKey crypto src c)).toNat := by
        by_contra hn; exact hok ⟨h, by omega⟩
      have hx : (w.sload t (allowKey crypto src c) - word v).toNat =
          (w.sload t (allowKey crypto src c)).toNat - v := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hvn]; exact hle), hvn]
      have hnm : ¬ MAX ≤ (w.sload t (allowKey crypto src c)).toNat := by
        simp only [MAX]; omega
      simp only [Variant.usdtSpent, hal, hx, hnm, ↓reduceIte]
    · exact FrameKeeps.sstore (frameKeeps_refl _ _ _ _)
        (.inr (.inr (.inl ⟨_, hsrc, _, hc, rfl⟩))) _
  · refine ⟨hl, ?_, frameKeeps_refl _ _ _ _⟩
    have hm : MAX ≤ (w.sload t (allowKey crypto src c)).toNat := by
      simp only [MAX]; omega
    simp only [Variant.usdtSpent, hal, hm, ↓reduceIte]

end Spend

/-! ## The failures -/

section Arith

variable {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}

/-- A SafeMath failure of the code is one of the model's failures (the credits do not overflow
under the supply bound). -/
theorem tf_arith (hs : usdtAbs.Sound crypto Act) {c src d : Address} (hc : c ∈ Act)
    (hsrc : src ∈ Act) (hd : d ∈ Act) (hl : Live Act w t)
    (hsub : QEDefi.ERC20.Spec.YAMV2.SubSupply (readState crypto Act w t)) {v : ℕ}
    (hv : v < 2 ^ 256) (h : tfArithFail crypto w t c src d (word v)) :
    TfFail (readState crypto Act w t) c src v := by
  by_contra hn
  unfold TfFail at hn
  push Not at hn
  obtain ⟨h0, h1, h2, h3⟩ := hn
  have hvn := word_toNat' hv
  have hal := allow_eq (crypto := crypto) (w := w) (t := t) hsrc hc
  have hok : ¬ ((w.sload t (allowKey crypto src c)).toNat < 2 ^ 256 - 1 ∧
      (w.sload t (allowKey crypto src c)).toNat < v) := by
    rintro ⟨ha, hb⟩; rw [← hal] at ha hb; exact absurd (h0 (by simp only [MAX]; omega)) (by omega)
  obtain ⟨hl0, hr0, -⟩ := tf_spend hs hsrc hc hl hv hok
  have hf := usdtSpent_fields (readState crypto Act w t) src c v
  have hno : v * (w.sload t 3#256).toNat < 2 ^ 256 := by
    rw [← bps_eq (crypto := crypto) (Act := Act)]; simp only [MAX] at h2; omega
  have hfee := xferFee_toNat (crypto := crypto) (Act := Act) hv hno
  have hsub0 : QEDefi.ERC20.Spec.YAMV2.SubSupply
      (readState crypto Act (tfW0 crypto w t src c (word v)) t) := by
    rw [hr0]; unfold QEDefi.ERC20.Spec.YAMV2.SubSupply; rw [hf.1, hf.2.1]; exact hsub
  have hb0 : v ≤ (readState crypto Act (tfW0 crypto w t src c (word v)) t).bal src := by
    rw [hr0, hf.1]; exact h1
  obtain ⟨ha1, ha2, -⟩ := xfer_writes hs hsrc hd hl0 hsub0 hv hb0
    (fee := xferFee w t (word v)) (by rw [hfee]; exact h3)
  unfold tfArithFail at h
  rw [hvn] at h
  rcases h with h | h | h | h | h | ⟨hz, h⟩
  · omega
  · exact hok h
  · rw [hfee] at h; omega
  · rw [← bal_eq (crypto := crypto) (Act := Act) (w := tfW0 crypto w t src c (word v)) hsrc, hr0,
      hf.1] at h
    omega
  · omega
  · have := ha2 hz; omega

/-- A model failure is a SafeMath failure of the code. -/
theorem tf_noarith (hs : usdtAbs.Sound crypto Act) {c src d : Address} (hc : c ∈ Act)
    (hsrc : src ∈ Act) (hl : Live Act w t) {v : ℕ} (hv : v < 2 ^ 256)
    (h : ¬ tfArithFail crypto w t c src d (word v)) :
    ¬ TfFail (readState crypto Act w t) c src v := by
  intro hm
  apply h
  have hvn := word_toNat' hv
  have hal := allow_eq (crypto := crypto) (w := w) (t := t) hsrc hc
  unfold tfArithFail
  rw [hvn]
  by_cases hok : (w.sload t (allowKey crypto src c)).toNat < 2 ^ 256 - 1 ∧
      (w.sload t (allowKey crypto src c)).toNat < v
  · exact .inr (.inl hok)
  obtain ⟨-, hr0, -⟩ := tf_spend hs hsrc hc hl hv hok
  have hf := usdtSpent_fields (readState crypto Act w t) src c v
  unfold TfFail at hm
  rw [bps_eq] at hm
  rcases hm with hm | hm | hm | hm
  · exact absurd ⟨by rw [← hal]; simp only [MAX] at hm; omega, by rw [← hal]; exact hm.2⟩ hok
  · right; right; right; left
    rw [← bal_eq (w := tfW0 crypto w t src c (word v)) hsrc, hr0, hf.1]; exact hm
  · left; simp only [MAX] at hm; omega
  · by_cases hno : v * (w.sload t 3#256).toNat < 2 ^ 256
    · right; right; left
      rw [xferFee_toNat (crypto := crypto) (Act := Act) hv hno, bps_eq]
      exact hm
    · left; omega

end Arith

/-- **`CallSpec` for `transferFrom(src, dst, v)`.** -/
theorem usdt_transferFrom (src dst : Address) (v : ℕ) :
    CallSpec USDT.runtimeCode usdtAbs M g₀ (.transferFrom src dst v) := by
  intro Act m hs henc ha
  obtain ⟨hv, hsel, hsize, harg⟩ := henc
  have hsrc : src ∈ Act := ha src (by simp [Call.addrs])
  have hd : dst ∈ Act := ha dst (by simp [Call.addrs])
  have hc : m.frame.msg.caller ∈ Act := hs.caller
  obtain ⟨hlive, hpre⟩ := live_of_start hs
  have hsub : QEDefi.ERC20.Spec.YAMV2.SubSupply (pre usdtAbs Act m) := hs.wf
  refine (halts_of_high hs.fresh (Post := TransferFromOut src dst (word v) m)
    (fun _ _ _ h => transferFromOut_halt h) (fun _ _ h => h)
    (transferFrom_high m hs.fresh _ src dst (word v) (by omega) hsel (by simpa using hsize)
      hs.size (harg 0 (by simp)) (harg 1 (by simp)) (harg 2 (by simp))
      (dep_of_start hs))).mono fun mf o _ h => ?_
  rcases h with ⟨hf, hlt⟩ | ⟨hval, hf⟩ | ⟨hst, hf⟩ | ⟨hval, hrest⟩
  · exact .inr ⟨hf, fun h => by unfold Normal at h; omega⟩
  · exact .inr ⟨hf, fun h => hval h.2.2⟩
  · exact .inr ⟨hf, fun h => by rw [h.2.1] at hst; cases hst⟩
  left
  have hw := world_of_start hs hval
  have hpre' : pre usdtAbs Act m =
      readState m.ctx.crypto Act m.world m.frame.msg.currentTarget := by
    rw [hpre, hw]
  have hlive' : Live Act m.world m.frame.msg.currentTarget := hw ▸ hlive
  rw [hpre'] at hsub ⊢
  rw [usdt_call_transferFrom']
  rcases hrest with ⟨hp, out, ho⟩ | ⟨hp, hb, out, ho⟩ | ⟨hp, hb, har, e, ho⟩ |
      ⟨hp, hb, hnar, ho, hwd, htr, hcr, hlog⟩
  · have hg : (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).paused = true ∨
        (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).blacklisted src = true :=
      .inl (paused_iff.2 hp)
    simp only [hg, ↓reduceIte]
    exact ⟨out, ho⟩
  · have hg : (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).paused = true ∨
        (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).blacklisted src = true :=
      .inr ((blacklisted_iff hsrc).2 hb)
    simp only [hg, ↓reduceIte]
    exact ⟨out, ho⟩
  · have hp' : ¬ (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).paused = true := by
      rw [paused_iff]; simpa using hp
    have hb' : ¬ (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).blacklisted
        src = true := by
      rw [blacklisted_iff hsrc]; simpa using hb
    have hg : ¬ ((readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).paused = true ∨
        (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).blacklisted src = true) := by
      tauto
    have ha := tf_arith hs.sound hc hsrc hd hlive' hsub hv har
    simp only [hg, ha, ↓reduceIte]
    exact ⟨e, ho⟩
  · have hp' : ¬ (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).paused = true := by
      rw [paused_iff]; simpa using hp
    have hb' : ¬ (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).blacklisted
        src = true := by
      rw [blacklisted_iff hsrc]; simpa using hb
    have hn := tf_noarith hs.sound hc hsrc hlive' hv hnar
    have hg : ¬ ((readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).paused = true ∨
        (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).blacklisted src = true) := by
      tauto
    simp only [hg, hn, ↓reduceIte]
    set w := m.world with hw_def
    set t := m.frame.msg.currentTarget with ht_def
    set crypto := m.ctx.crypto with hcr_def
    set c := m.frame.msg.caller with hc_def
    unfold TfFail at hn
    push Not at hn
    obtain ⟨hn0, hn1, hn2, hn3⟩ := hn
    have hal := allow_eq (crypto := crypto) (w := w) (t := t) hsrc hc
    have hok : ¬ ((w.sload t (allowKey crypto src c)).toNat < 2 ^ 256 - 1 ∧
        (w.sload t (allowKey crypto src c)).toNat < v) := by
      rintro ⟨h1, h2⟩; rw [← hal] at h1 h2
      exact absurd (hn0 (by simp only [MAX]; omega)) (by omega)
    obtain ⟨hl0, hr0, hk0⟩ := tf_spend hs.sound hsrc hc hlive' hv hok
    have hf := usdtSpent_fields (readState crypto Act w t) src c v
    have hno : v * (w.sload t 3#256).toNat < 2 ^ 256 := by
      rw [← bps_eq (crypto := crypto) (Act := Act)]; simp only [MAX] at hn2; omega
    have hfee := xferFee_toNat (crypto := crypto) (Act := Act) hv hno
    have hsub0 : QEDefi.ERC20.Spec.YAMV2.SubSupply
        (readState crypto Act (tfW0 crypto w t src c (word v)) t) := by
      rw [hr0]; unfold QEDefi.ERC20.Spec.YAMV2.SubSupply; rw [hf.1, hf.2.1]; exact hsub
    have hb0 : v ≤ (readState crypto Act (tfW0 crypto w t src c (word v)) t).bal src := by
      rw [hr0, hf.1]; exact hn1
    obtain ⟨-, -, hcr', hown, hkeep⟩ := xfer_writes hs.sound hsrc hd hl0 hsub0 hv hb0
      (fee := xferFee w t (word v)) (by rw [hfee]; exact hn3)
    have hff0 : (xferFee w t (word v)).toNat = (Variant.usdt : Variant Address).feeOf (readState crypto Act w t) v := by
      rw [hfee, usdt_feeOf']
    have hff : (xferFee w t (word v)).toNat = (Variant.usdt : Variant Address).feeOf
        (readState crypto Act (tfW0 crypto w t src c (word v)) t) v := by
      rw [hr0, hfee, usdt_feeOf', hf.2.2.1, hf.2.2.2.1]
    refine ⟨ho, ?_, ?_, htr, hcr, ?_⟩
    · show read _ _ _ _ = _
      rw [hwd, hcr' hff, hr0]
    · rw [hwd]; exact FrameKeeps.trans' hk0 hkeep
    · rw [hlog, hown, hr0, hf.2.2.2.2]
      simp only [M, QEDefi.ERC20.Spec.USDT.usdtModel_events, QEDefi.ERC20.Spec.USDT.usdtEvents,
        QEDefi.ERC20.Spec.USDT.usdtMoveEvents, xferLogs]
      have hvf : word (v - (Variant.usdt : Variant Address).feeOf (readState crypto Act w t) v) =
          word v - xferFee w t (word v) := by
        apply word_eq_of_toNat
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, word_toNat' hv, hfee]; exact hn3),
          word_toNat' hv, hff0]
      by_cases hf0 : xferFee w t (word v) = 0#256
      · have hz : (Variant.usdt : Variant Address).feeOf (readState crypto Act w t) v = 0 := by
          rw [← hff0, hf0]; rfl
        simp only [hz, hf0, ↓reduceIte, List.nil_append, List.map_cons, List.map_nil]
        rw [hz, hf0] at hvf
        rw [← hvf]
        simp [Spec.eventLog, transferLog, ← ht_def]
      · have hz : (Variant.usdt : Variant Address).feeOf (readState crypto Act w t) v ≠ 0 := by
          rw [← hff0]; intro h; exact hf0 (BitVec.eq_of_toNat_eq (by simpa using h))
        simp only [hz, hf0, ↓reduceIte, List.cons_append, List.nil_append, List.map_cons,
          List.map_nil]
        rw [← hvf, ← word_eq_of_toNat hff0]
        simp only [Spec.eventLog, transferLog]
        rw [Array.push_eq_append, Array.push_eq_append, Array.append_assoc]
        rfl

end Verified.WeirdERC20.USDT.Spec
