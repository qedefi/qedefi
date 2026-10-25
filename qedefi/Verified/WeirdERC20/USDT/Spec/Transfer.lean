import Verified.WeirdERC20.USDT.Spec.TransferHigh
import Verified.WeirdERC20.USDT.Spec.TransferModel
import Verified.WeirdERC20.USDT.Spec.Approve

/-!
# USDT's `transfer` satisfies `CallSpec`

`usdt_transfer`: in every frame `Start` admits, at any gas and with any value, an ABI-encoded
`transfer(dst, v)` whose recipient is an actor ends as `usdtModel` says: it reverts when the
token is paused or the caller is blacklisted; it ends with `INVALID` when the caller's balance
is short, `v · basisPointsRate` overflows or the fee exceeds `v` (SafeMath's `assert`s; the
credits cannot overflow under the actors' supply bound, `xfer_writes`); otherwise it debits the
caller, credits the recipient with `v - fee` and the owner with the fee (`Variant.credit`), returns
no data and logs the model's `Transfer`s; with value, in a static frame or below `g₀` it fails.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Verified.WeirdERC20.USDT.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626

section Arith

variable {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}

theorem word_toNat' {v : ℕ} (hv : v < 2 ^ 256) : (word v).toNat = v := by
  simp only [word, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hv

/-- A SafeMath failure of the code is one of the model's arithmetic failures (the credits do
not overflow under the supply bound). -/
theorem xfer_arith (hs : usdtAbs.Sound crypto Act) {c d : Address} (hc : c ∈ Act)
    (hd : d ∈ Act) (hl : Live Act w t)
    (hsub : QEDefi.ERC20.Spec.YAMV2.SubSupply (readState crypto Act w t)) {v : ℕ}
    (hv : v < 2 ^ 256) (h : xferArithFail crypto w t c d (word v)) :
    (readState crypto Act w t).bal c < v ∨ MAX < v * (readState crypto Act w t).feeBps ∨
      v < min (v * (readState crypto Act w t).feeBps / 10000) (readState crypto Act w t).feeMax := by
  by_contra hn
  push Not at hn
  obtain ⟨h1, h2, h3⟩ := hn
  have hvn := word_toNat' hv
  have hno : v * (w.sload t 3#256).toNat < 2 ^ 256 := by
    rw [← bps_eq (crypto := crypto) (Act := Act)]; simp only [MAX] at h2; omega
  have hf := xferFee_toNat (crypto := crypto) (Act := Act) hv hno
  obtain ⟨ha1, ha2, -⟩ := xfer_writes hs hc hd hl hsub hv h1 (fee := xferFee w t (word v))
    (by rw [hf]; exact h3)
  rw [bal_eq hc] at h1
  unfold xferArithFail at h
  rw [hvn] at h
  rcases h with h | h | h | h | ⟨h0, h⟩
  · omega
  · rw [hf] at h; omega
  · omega
  · omega
  · have := ha2 h0; omega

/-- A model failure is a SafeMath failure of the code. -/
theorem xfer_noarith {c d : Address} (hc : c ∈ Act) {v : ℕ} (hv : v < 2 ^ 256)
    (h : ¬ xferArithFail crypto w t c d (word v)) :
    ¬ ((readState crypto Act w t).bal c < v ∨ MAX < v * (readState crypto Act w t).feeBps ∨
      v < min (v * (readState crypto Act w t).feeBps / 10000)
        (readState crypto Act w t).feeMax) := by
  intro hm
  apply h
  have hvn := word_toNat' hv
  unfold xferArithFail
  rw [hvn]
  rw [bal_eq hc, bps_eq] at hm
  rcases hm with hm | hm | hm
  · exact .inr (.inr (.inl hm))
  · left; simp only [MAX] at hm; omega
  · by_cases hno : v * (w.sload t 3#256).toNat < 2 ^ 256
    · right; left
      rw [xferFee_toNat (crypto := crypto) (Act := Act) hv hno, bps_eq]
      exact hm
    · left; omega

end Arith


theorem word_eq_of_toNat {x : Word} {n : ℕ} (h : x.toNat = n) : word n = x := by
  apply BitVec.eq_of_toNat_eq
  rw [word_toNat' (h ▸ x.isLt), h]

/-- **`CallSpec` for `transfer(dst, v)`.** -/
theorem usdt_transfer (dst : Address) (v : ℕ) :
    CallSpec USDT.runtimeCode usdtAbs M g₀ (.transfer dst v) := by
  intro Act m hs henc ha
  obtain ⟨hv, hsel, hsize, harg⟩ := henc
  have hd : dst ∈ Act := ha dst (by simp [Call.addrs])
  have hc : m.frame.msg.caller ∈ Act := hs.caller
  obtain ⟨hlive, hpre⟩ := live_of_start hs
  have hsub : QEDefi.ERC20.Spec.YAMV2.SubSupply (pre usdtAbs Act m) := hs.wf
  refine (halts_of_high hs.fresh (Post := TransferOut dst (word v) m)
    (fun _ _ _ h => transferOut_halt h) (fun _ _ h => h)
    (transfer_high m hs.fresh _ dst (word v) (by omega) hsel (by simpa using hsize) hs.size
      (harg 0 (by simp)) (harg 1 (by simp)) (dep_of_start hs))).mono fun mf o _ h => ?_
  rcases h with ⟨hf, hlt⟩ | ⟨hval, hf⟩ | ⟨hst, hf⟩ | ⟨hval, hrest⟩
  · exact .inr ⟨hf, fun h => by unfold Normal at h; omega⟩
  · exact .inr ⟨hf, fun h => hval h.2.2⟩
  · exact .inr ⟨hf, fun h => by rw [h.2.1] at hst; cases hst⟩
  left
  have hw := world_of_start hs hval
  have hpre' : pre usdtAbs Act m = readState m.ctx.crypto Act m.world m.frame.msg.currentTarget := by
    rw [hpre, hw]
  have hlive' : Live Act m.world m.frame.msg.currentTarget := hw ▸ hlive
  rw [hpre'] at hsub ⊢
  rw [usdt_call_transfer']
  rcases hrest with ⟨hp, out, ho⟩ | ⟨hp, hb, out, ho⟩ | ⟨hp, hb, har, e, ho⟩ |
      ⟨hp, hb, hnar, ho, hwd, htr, hcr, hlog⟩
  · have hg : (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).paused = true ∨
        (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).blacklisted
          m.frame.msg.caller = true := .inl (paused_iff.2 hp)
    simp only [hg, ↓reduceIte]
    exact ⟨out, ho⟩
  · have hg : (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).paused = true ∨
        (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).blacklisted
          m.frame.msg.caller = true := .inr ((blacklisted_iff hc).2 hb)
    simp only [hg, ↓reduceIte]
    exact ⟨out, ho⟩
  · have hp' : ¬ (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).paused = true := by
      rw [paused_iff]; simpa using hp
    have hb' : ¬ (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).blacklisted
        m.frame.msg.caller = true := by
      rw [blacklisted_iff hc]; simpa using hb
    have hg : ¬ ((readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).paused = true ∨
        (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).blacklisted
          m.frame.msg.caller = true) := by tauto
    have ha := xfer_arith hs.sound hc hd hlive' hsub hv har
    simp only [hg, ha, ↓reduceIte]
    exact ⟨e, ho⟩
  · have hp' : ¬ (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).paused = true := by
      rw [paused_iff]; simpa using hp
    have hb' : ¬ (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).blacklisted
        m.frame.msg.caller = true := by
      rw [blacklisted_iff hc]; simpa using hb
    have hn := xfer_noarith hc hv hnar
    have hg : ¬ ((readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).paused = true ∨
        (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget).blacklisted
          m.frame.msg.caller = true) := by tauto
    simp only [hg, hn, ↓reduceIte]
    push Not at hn
    obtain ⟨hn1, hn2, hn3⟩ := hn
    have hno : v * (m.world.sload m.frame.msg.currentTarget 3#256).toNat < 2 ^ 256 := by
      rw [← bps_eq (crypto := m.ctx.crypto) (Act := Act)]; simp only [MAX] at hn2; omega
    have hf := xferFee_toNat (crypto := m.ctx.crypto) (Act := Act) hv hno
    obtain ⟨-, -, hcr', hown, hkeep⟩ := xfer_writes (fee := xferFee m.world
      m.frame.msg.currentTarget (word v)) hs.sound hc hd hlive' hsub hv hn1 (by rw [hf]; exact hn3)
    have hff : (xferFee m.world m.frame.msg.currentTarget (word v)).toNat =
        (Variant.usdt : Variant Address).feeOf
          (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget) v := by
      rw [hf, usdt_feeOf']
    refine ⟨ho, ?_, ?_, htr, hcr, ?_⟩
    · show read _ _ _ _ = _
      rw [hwd]; exact hcr' hff
    · rw [hwd]; exact hkeep
    · rw [hlog, hown]
      simp only [M, QEDefi.ERC20.Spec.USDT.usdtModel_events, QEDefi.ERC20.Spec.USDT.usdtEvents,
        QEDefi.ERC20.Spec.USDT.usdtMoveEvents, xferLogs]
      have hvf : word (v - (Variant.usdt : Variant Address).feeOf
          (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget) v) =
          word v - xferFee m.world m.frame.msg.currentTarget (word v) := by
        apply word_eq_of_toNat
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, word_toNat' hv, hf]; exact hn3),
          word_toNat' hv, hff]
      by_cases hf0 : xferFee m.world m.frame.msg.currentTarget (word v) = 0#256
      · have hz : (Variant.usdt : Variant Address).feeOf
            (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget) v = 0 := by
          rw [← hff, hf0]; rfl
        simp only [hz, hf0, ↓reduceIte, List.nil_append, List.map_cons, List.map_nil]
        rw [hz, hf0] at hvf
        rw [← hvf]
        simp [Spec.eventLog, transferLog]
      · have hz : (Variant.usdt : Variant Address).feeOf
            (readState m.ctx.crypto Act m.world m.frame.msg.currentTarget) v ≠ 0 := by
          rw [← hff]; intro h; exact hf0 (BitVec.eq_of_toNat_eq (by simpa using h))
        simp only [hz, hf0, ↓reduceIte, List.cons_append, List.nil_append, List.map_cons,
          List.map_nil]
        rw [← hvf, ← word_eq_of_toNat hff]
        simp only [Spec.eventLog, transferLog]
        rw [Array.push_eq_append, Array.push_eq_append, Array.append_assoc]
        rfl

end Verified.WeirdERC20.USDT.Spec
