import Verified.WeirdERC20.BNB.Spec.Approve
import Verified.Solady.Spec.Fallback
import EvmLogic.Tx.Frame

/-!
# BNB under the spec: unknown selectors and short calldata

BNB (solc 0.4.12) has a payable fallback `function() payable {}`: empty calldata, or a selector
none of the dispatcher's fifteen, stops with no output and no state change of its own, keeping
the ether the frame received, as the model's `other` call (`Fallback.accept`) does. The
dispatcher only tests `calldatasize == 0`; calldata of one to three bytes is read zero-padded,
and its padded selector (low byte zero) is none of BNB's (`selectorOf_short`).
-/

namespace Verified.WeirdERC20.BNB.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.BNB.Contracts
open Verified.Solady.Spec (LowHalts halts_split)
open Verified.Solady.Spec.AnyGas

/-- The selector of calldata shorter than four bytes, read zero-padded, has a zero low byte. -/
theorem selectorOf_short {data : ByteArray} (h : data.size < 4) :
    Abi.selectorOf data % 256 = 0 := by
  have hr : readBytes data 0 4 = ⟨#[Bytes.getD (readBytes data 0 4) 0, Bytes.getD (readBytes data 0 4) 1,
      Bytes.getD (readBytes data 0 4) 2, 0]⟩ := by
    apply Bytes.ext_getD
    · rw [readBytes_eq_readPadded, Bytes.size_readPadded]; rfl
    · intro j hj
      rw [readBytes_eq_readPadded, Bytes.size_readPadded] at hj
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
      · rfl
      · rfl
      · rfl
      · rw [readBytes_eq_readPadded, Bytes.getD_readPadded, Verified.Solady.Spec.ite_pos' (by omega),
          Bytes.getD_of_size_le (by omega)]
        rfl
  unfold Abi.selectorOf
  rw [hr, Bytes.toNat_eq_foldl, ← Array.foldl_toList]
  simp

theorem calldatasize_pos {n : ℕ} (h0 : 0 < n) (h : n < 2 ^ 64) : Word.iszero (ofNat n) = 0 := by
  apply iszero_of_ne
  intro h0'
  have := congrArg BitVec.toNat h0'
  simp [ofNat] at this
  omega

/-- The dispatcher's `EQ` tests all fail on an unknown selector. -/
theorem bnb_unknown {data : ByteArray} (h : Abi.selectorOf data ∉ sel) :
    let s := BitVec.ofNat 256 (Abi.selectorOf data)
    Word.eq 0xdd62ed3e#256 s = 0 ∧
    Word.eq 0x095ea7b3#256 s = 0 ∧
    Word.eq 0x70a08231#256 s = 0 ∧
    Word.eq 0x42966c68#256 s = 0 ∧
    Word.eq 0x313ce567#256 s = 0 ∧
    Word.eq 0xd7a78db8#256 s = 0 ∧
    Word.eq 0xcd4217c1#256 s = 0 ∧
    Word.eq 0x06fdde03#256 s = 0 ∧
    Word.eq 0x8da5cb5b#256 s = 0 ∧
    Word.eq 0x95d89b41#256 s = 0 ∧
    Word.eq 0x18160ddd#256 s = 0 ∧
    Word.eq 0xa9059cbb#256 s = 0 ∧
    Word.eq 0x23b872dd#256 s = 0 ∧
    Word.eq 0x6623fc46#256 s = 0 ∧
    Word.eq 0x3bed33ce#256 s = 0 := by
  have hs := Verified.Solady.Spec.selectorOf_lt data
  simp only [sel, BNB.selectors, List.map, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨Verified.Solady.Spec.eq_sel_ne (k := 0xdd62ed3e) hs (by decide) (by simpa using h1),
    Verified.Solady.Spec.eq_sel_ne (k := 0x095ea7b3) hs (by decide) (by simpa using h2),
    Verified.Solady.Spec.eq_sel_ne (k := 0x70a08231) hs (by decide) (by simpa using h3),
    Verified.Solady.Spec.eq_sel_ne (k := 0x42966c68) hs (by decide) (by simpa using h4),
    Verified.Solady.Spec.eq_sel_ne (k := 0x313ce567) hs (by decide) (by simpa using h5),
    Verified.Solady.Spec.eq_sel_ne (k := 0xd7a78db8) hs (by decide) (by simpa using h6),
    Verified.Solady.Spec.eq_sel_ne (k := 0xcd4217c1) hs (by decide) (by simpa using h7),
    Verified.Solady.Spec.eq_sel_ne (k := 0x06fdde03) hs (by decide) (by simpa using h8),
    Verified.Solady.Spec.eq_sel_ne (k := 0x8da5cb5b) hs (by decide) (by simpa using h9),
    Verified.Solady.Spec.eq_sel_ne (k := 0x95d89b41) hs (by decide) (by simpa using h10),
    Verified.Solady.Spec.eq_sel_ne (k := 0x18160ddd) hs (by decide) (by simpa using h11),
    Verified.Solady.Spec.eq_sel_ne (k := 0xa9059cbb) hs (by decide) (by simpa using h12),
    Verified.Solady.Spec.eq_sel_ne (k := 0x23b872dd) hs (by decide) (by simpa using h13),
    Verified.Solady.Spec.eq_sel_ne (k := 0x6623fc46) hs (by decide) (by simpa using h14),
    Verified.Solady.Spec.eq_sel_ne (k := 0x3bed33ce) hs (by decide) (by simpa using h15)⟩

/-- Short calldata reads as a selector none of BNB's (every one has a nonzero low byte). -/
theorem bnb_not_sel {data : ByteArray}
    (hd : data.size < 4 ∨ Abi.selectorOf data ∉ sel) : Abi.selectorOf data ∉ sel := by
  rcases hd with h | h
  · have h0 := selectorOf_short h
    intro hm
    simp only [sel, BNB.selectors, List.map, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp at h <;> omega
  · exact h

/-- The fallback's code-level end: success, no output, nothing changed by the code. -/
def FallPost (m : Machine) (mf : Machine) (o : Outcome) : Prop :=
  o = .success .empty ∧ mf.world = m.world ∧ mf.transient = m.transient ∧
    mf.createdAccounts = m.createdAccounts ∧ mf.frame.sub.logs = m.frame.sub.logs

set_option maxHeartbeats 0 in
theorem fallback_low (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hd : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel) :
    LowHalts m (FallPost m) := by
  intro H hF hok
  apply WP.halts_of_false
  by_cases h0 : m.frame.msg.data.size = 0
  · have hz : Word.iszero (ofNat m.frame.msg.data.size) = 1 := by rw [h0]; decide
    solady_fresh_intro
    hwp_steps [hz]
    exact pwp_stop (by pcode_fact) (hok _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := bnb_unknown (bnb_not_sel hd)
    have hsel' := div_selector m.frame.msg.data
    have hz := calldatasize_pos (n := m.frame.msg.data.size) (by omega) hsz
    solady_fresh_intro
    hwp_steps [hz, hsel', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
    exact pwp_stop (by pcode_fact) (hok _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

set_option maxHeartbeats 0 in
theorem fallback_high (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hd : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (FallPost m) := by
  simp only [g₀] at hg
  apply WP.halts_of_false
  by_cases h0 : m.frame.msg.data.size = 0
  · have hz : Word.iszero (ofNat m.frame.msg.data.size) = 1 := by rw [h0]; decide
    solady_fresh_intro
    pwp_steps [hz]
    exact pwp_stop (by pcode_fact) ⟨rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := bnb_unknown (bnb_not_sel hd)
    have hsel' := div_selector m.frame.msg.data
    have hz := calldatasize_pos (n := m.frame.msg.data.size) (by omega) hsz
    solady_fresh_intro
    pwp_steps [hz, hsel', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
    exact pwp_stop (by pcode_fact) ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem bnb_call_other (s : VState Address) (c : Address) (v : ℕ) :
    M.call s c (.other v) = .ok { s with ether := s.ether + v } .empty := by
  simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, QEDefi.ERC20.Spec.BNB.bnbGuard, Variant.call,
    Variant.step, Variant.fallbackCall, Variant.bnb, Variant.standard, Variant.retData]

/-- Moving ether into an account that does not end empty keeps its storage. -/
theorem bnb_moveEther_dst_storage {w : World} {src dst : Address} {v : Word} (hne : src ≠ dst)
    (hnz : w.balance dst + v ≠ 0) (k : Word) :
    (moveEther w src dst v).sload dst k = w.sload dst k := by
  have h1 := EvmLogic.Tx.account_modifyState_ne w
    (fun acc => { acc with balance := acc.balance - v }) (Ne.symm hne)
  unfold moveEther
  simp only [World.sload]
  rw [EvmLogic.Tx.account_modifyState_self _ _ ?_, h1]
  rw [h1]
  simp only [Account.isEmpty, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  exact .inl (.inr hnz)

/-- **The frame's world through the abstraction**: the snapshot's state with the value received
(`Start.launched`, `Start.value`). -/
theorem bnbRead_launched {Act : Finset Address} {m : Machine}
    (hs : Start BNB.runtimeCode bnbAbs M Act m) :
    bnbRead m.ctx.crypto Act m.world m.frame.msg.currentTarget =
      { pre bnbAbs Act m with ether := (pre bnbAbs Act m).ether + m.frame.msg.value.toNat } := by
  have hstore : ∀ k, m.world.sload m.frame.msg.currentTarget k =
      m.frame.snapshot.1.sload m.frame.msg.currentTarget k := by
    intro k
    rw [hs.launched]
    rcases hs.value with hv | ⟨htv, hne, hlt⟩
    · rw [transferValue_zero _ _ hv]
    · by_cases hv : m.frame.msg.value = 0
      · rw [transferValue_zero _ _ hv]
      · simp only [transferValue, htv, hv, ne_eq, not_false_eq_true, Bool.true_and,
          decide_true, ↓reduceIte]
        refine bnb_moveEther_dst_storage hne ?_ k
        intro h0
        have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt hlt] at this
        exact hv (BitVec.eq_of_toNat_eq (by simp at this ⊢; omega))
  have hether : (m.world.balance m.frame.msg.currentTarget).toNat =
      (m.frame.snapshot.1.balance m.frame.msg.currentTarget).toNat +
        m.frame.msg.value.toNat := by
    rw [hs.launched]
    rcases hs.value with hv | ⟨htv, hne, hlt⟩
    · rw [transferValue_zero _ _ hv, hv]; simp
    · by_cases hv : m.frame.msg.value = 0
      · rw [transferValue_zero _ _ hv, hv]; simp
      · simp only [transferValue, htv, hv, ne_eq, not_false_eq_true, Bool.true_and,
          decide_true, ↓reduceIte]
        rw [balance_moveEther _ _ hne]
        simp only [Ne.symm hne, ↓reduceIte]
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt hlt]
  simp only [pre, bnbAbs, bnbRead]
  rw [readMap_congr (fun k _ => hstore k), readMap_congr (fun k _ => hstore k),
    readMap2_congr (fun k _ => hstore k), readSlot_congr (hstore _), hstore, hether]

/-- **Empty calldata and unknown selectors** run the payable fallback: the value is kept, nothing
else changes, no output, no event, as the model's `other` call. -/
theorem fallback_spec : FallbackSpec BNB.runtimeCode bnbAbs M g₀ sel := by
  intro Act m hs hd
  refine halts_split (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => fallback_high m hs.fresh hs.size hd hG.1) (fallback_low m hs.fresh hs.size hd) ?_
  rintro mf o ⟨rfl, hw, ht, hc, hl⟩
  rw [bnb_call_other]
  refine ⟨rfl, ?_, ?_, ht, hc, ?_⟩
  · show bnbRead _ _ _ _ = _
    rw [hw, bnbRead_launched hs]
  · rw [hw]; exact frameKeeps_refl'
  · rw [hl]
    simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, QEDefi.ERC20.Spec.BNB.bnbEvents]

end Verified.WeirdERC20.BNB.Spec
