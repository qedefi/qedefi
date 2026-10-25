import Verified.Solmate.ERC20.Spec.ModelCalls
import Verified.Solmate.ERC20.Events
import Verified.Solmate.ERC4626.UnknownSelectors

/-!
# Solmate's `ERC20`: the exact outcomes in normal frames

Each ERC-20 call, view and operation of the deployed asset (`SolmateAsset.runtimeCodeWith ia`,
any immutables), in a frame with enough gas, not static and without value, ends exactly as
`solmateModel` says through `solmateAbs` (`transfer_normal`, …). These are the `Normal`
halves of the obligations; the frames outside `Normal` are in `Obligations.lean`.

The proofs reuse the asset's frame summaries with their logs (`transfer_halts_ok_events`, …)
and compare their worlds (`transferWorld`, …) with the model's state change row by row
(`read_sstore_bal`, …), under the actors' `ActorRows` hypothesis.
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Solmate QEDefi.Math Finsupp
open Verified.Solmate.Contracts Verified.Solmate.ERC20 QEDefi.ERC4626

/-- The deployed asset with immutables `ia`. -/
abbrev code (ia : SolmateAsset.Immutables) : ByteArray := SolmateAsset.runtimeCodeWith ia

/-- Solmate's model over addresses. -/
noncomputable abbrev M : TokenModel (VState Address) Address (Variant.Op Address) := solmateModel

variable {ia : SolmateAsset.Immutables} {Act : Finset Address} {m : Machine}

/-! ## The start of a frame -/

theorem world_eq_snapshot (hS : Start (code ia) solmateAbs M Act m)
    (hval : m.frame.msg.value = 0) : m.world = m.frame.snapshot.1 := by
  rw [hS.launched]; simp [transferValue, hval]

/-- The model state at the start, read from the frame's world (no value moved). -/
theorem pre_eq (hS : Start (code ia) solmateAbs M Act m) (hval : m.frame.msg.value = 0) :
    pre solmateAbs Act m = solmateRead m.ctx.crypto Act m.world m.frame.msg.currentTarget := by
  rw [world_eq_snapshot hS hval]; rfl

theorem bal_read {crypto : Crypto} {w : World} {token a : Address} (ha : a ∈ Act) :
    (solmateRead crypto Act w token).bal a =
      (w.sload token (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat :=
  readMap_of_mem ha w token 3#256

theorem allowance_read {crypto : Crypto} {w : World} {token o sp : Address} (ho : o ∈ Act)
    (hsp : sp ∈ Act) :
    (solmateRead crypto Act w token).allowance o sp =
      (w.sload token (ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp)).toNat := by
  simp [solmateRead, readMap2, ho, hsp, ERC20.allowanceSlot]; rfl

theorem supply_read {crypto : Crypto} {w : World} {token : Address} :
    (solmateRead crypto Act w token).supply = (w.sload token 2#256).toNat := rfl

/-- The well-formedness of the start state: the actors' balances sum to the supply, which is
at most `MAX`. -/
theorem wf_total (hS : Start (code ia) solmateAbs M Act m) :
    total (pre solmateAbs Act m).bal = (pre solmateAbs Act m).supply ∧
      (pre solmateAbs Act m).supply ≤ MAX := by
  have h := hS.wf
  simp only [M, solmateModel_wf, Variant.WF, Variant.standard, Bool.false_eq_true, ↓reduceIte,
    reduceCtorEq] at h
  have h0 : (pre solmateAbs Act m).frozen = 0 := rfl
  rw [h0] at h
  simpa [total] using h

/-! ## Calldata -/

theorem twoWordCall_of_args {data : ByteArray} {sel : Nat} {x y : Word}
    (h : Args data sel [x, y]) : TwoWordCall data sel x y :=
  ⟨h.selector, by have := h.size; simpa using this, by simpa using h.arg 0 (by simp),
    by simpa using h.arg 1 (by simp)⟩

theorem threeWordCall_of_args {data : ByteArray} {sel : Nat} {x y z : Word}
    (h : Args data sel [x, y, z]) : ThreeWordCall data sel x y z :=
  ⟨h.selector, by have := h.size; simpa using this, by simpa using h.arg 0 (by simp),
    by simpa using h.arg 1 (by simp), by simpa using h.arg 2 (by simp)⟩

theorem toNat_word {v : ℕ} (h : v < 2 ^ 256) : (word v).toNat = v := by
  simp only [word, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem eventLog_transfer (token src dst : Address) (v : ℕ) :
    eventLog token (.transfer src dst v) = transferLog token src dst (word v) := rfl

theorem eventLog_approval (token o sp : Address) (v : ℕ) :
    eventLog token (.approval o sp v) = approvalLog token o sp (word v) := rfl

theorem logs_one (L : Array Log) (x : Log) : L.push x = L ++ ([x] : List Log).toArray := by
  simp

/-! ## `transfer` -/

theorem layout_balances : ERC20.Layout.solmate.balances = 3#256 := rfl
theorem layout_allowances : ERC20.Layout.solmate.allowances = 4#256 := rfl

/-- The world after a `transfer` of `v ≤ balanceOf[c]` read back: the model's move. -/
theorem read_transferWorld {crypto : Crypto} {w : World} {token c d : Address} {v : ℕ}
    (hS : SolmateSound crypto Act) (hc : c ∈ Act) (hd : d ∈ Act)
    (hv : v ≤ (solmateRead crypto Act w token).bal c) (hv' : v < 2 ^ 256)
    (hov : c ≠ d → (solmateRead crypto Act w token).bal d + v < 2 ^ 256) :
    solmateRead crypto Act (ERC20.transferWorld crypto w token c d (word v)) token =
      { solmateRead crypto Act w token with
        bal := (solmateRead crypto Act w token).bal - single c v + single d v } ∧
    FrameKeeps solmateAbs crypto Act token w
      (ERC20.transferWorld crypto w token c d (word v)) := by
  have hbc : (w.sload token (mappingSlot crypto (Word.ofAddress c) 3#256)).toNat =
      (solmateRead crypto Act w token).bal c := (readMap_of_mem hc w token 3#256).symm
  have hbd : (w.sload token (mappingSlot crypto (Word.ofAddress d) 3#256)).toNat =
      (solmateRead crypto Act w token).bal d := (readMap_of_mem hd w token 3#256).symm
  have hle : word v ≤ w.sload token (mappingSlot crypto (Word.ofAddress c) 3#256) := by
    rw [BitVec.le_def, toNat_word hv', hbc]; exact hv
  have hX : (w.sload token (mappingSlot crypto (Word.ofAddress c) 3#256) - word v).toNat =
      (solmateRead crypto Act w token).bal c - v := by
    rw [BitVec.toNat_sub_of_le hle, hbc, toNat_word hv']
  have hY : (word v + (w.sstore token (mappingSlot crypto (Word.ofAddress c) 3#256)
      (w.sload token (mappingSlot crypto (Word.ofAddress c) 3#256) - word v)).sload token
        (mappingSlot crypto (Word.ofAddress d) 3#256)).toNat =
      ((solmateRead crypto Act w token).bal.update c
        ((solmateRead crypto Act w token).bal c - v)) d + v := by
    rw [update_apply, sload_sstore_token]
    by_cases hdc : d = c
    · subst hdc
      simp only [↓reduceIte]
      rw [BitVec.toNat_add, hX, toNat_word hv', Nat.mod_eq_of_lt (by omega)]
      omega
    · have hne : mappingSlot crypto (Word.ofAddress d) 3#256 ≠
          mappingSlot crypto (Word.ofAddress c) 3#256 :=
        fun e => hdc (hS.inj1 _ (by simp) _ (by simp) d hd c hc e).1
      simp only [hdc, ↓reduceIte, hne]
      have := hov (Ne.symm hdc)
      rw [BitVec.toNat_add, toNat_word hv', hbd, Nat.mod_eq_of_lt (by omega)]
      omega
  refine ⟨?_, ?_⟩
  · simp only [ERC20.transferWorld, ERC20.balanceSlot, layout_balances]
    rw [read_sstore_bal hS hd, read_sstore_bal hS hc, move_eq_update, hX, hY]
  · simp only [ERC20.transferWorld, ERC20.balanceSlot, layout_balances]
    exact frameKeeps_sstore (frameKeeps_sstore (frameKeeps_refl _ _ _ _) (footprint_bal hc))
      (footprint_bal hd)

theorem bal_add_lt (hS : Start (code ia) solmateAbs M Act m) {c d : Address} (hcd : c ≠ d)
    {v : ℕ} (hv : v ≤ (pre solmateAbs Act m).bal c) : (pre solmateAbs Act m).bal d + v < 2 ^ 256 := by
  have ⟨h1, h2⟩ := wf_total hS
  have := add_le_total (f := (pre solmateAbs Act m).bal) hcd
  unfold MAX at h2
  omega

theorem retBytes_true : retBytes (.word true) = Bytes.ofWord 1 := rfl

set_option maxHeartbeats 1000000 in
/-- **`transfer(dst, v)` in a normal frame** ends as the model says. -/
theorem transfer_normal (hS : Start (code ia) solmateAbs M Act m) {dst : Address} {v : ℕ}
    (hE : (Call.transfer dst v).Encodes m.frame.msg.data) (hdst : dst ∈ Act)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : 60000 ≤ m.frame.gasLeft) :
    Halts m fun mf o =>
      Matches solmateAbs Act m mf o
        (M.events (pre solmateAbs Act m) m.frame.msg.caller (.transfer dst v))
        (M.call (pre solmateAbs Act m) m.frame.msg.caller (.transfer dst v)) := by
  obtain ⟨hv, hargs⟩ := hE
  have hd := twoWordCall_of_args hargs
  have hc := hS.caller
  have hbc : (pre solmateAbs Act m).bal m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget
        (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)).toNat := by
    rw [pre_eq hS hval]; exact bal_read hc
  simp only [M, solmateModel_call, solmateModel_events, solmateEvents, call_transfer]
  split_ifs with hlt
  · refine (transfer_halts_revert m hS.fresh hval hd hS.size (by omega) ?_).mono
      fun mf o _ h => h.1
    rw [toNat_word hv, ← hbc]; exact hlt
  · have hle : v ≤ (pre solmateAbs Act m).bal m.frame.msg.caller := by omega
    refine (transfer_halts_ok_events m hS.fresh hval hst hd hS.size hg
      (by rw [toNat_word hv, ← hbc]; exact hle)).mono fun mf o _ ⟨hok, hl⟩ => ?_
    have hrw := read_transferWorld (crypto := m.ctx.crypto) (w := m.world)
      (token := m.frame.msg.currentTarget) (hS.sound) hc hdst
      (by rw [← pre_eq hS hval]; exact hle) hv
      (fun hcd => by rw [← pre_eq hS hval]; exact bal_add_lt hS hcd hle)
    refine ⟨hok.1, ?_, ?_, hok.2.2.1, hok.2.2.2.1, ?_⟩
    · show solmateRead _ _ _ _ = _
      rw [hok.2.1, hrw.1, pre_eq hS hval]
    · rw [hok.2.1]; exact hrw.2
    · rw [hl]; simp [eventLog_transfer]

/-! ## `transferFrom` -/

theorem frameKeeps_trans {crypto : Crypto} {token : Address} {w₁ w₂ w₃ : World}
    (h₁ : FrameKeeps solmateAbs crypto Act token w₁ w₂)
    (h₂ : FrameKeeps solmateAbs crypto Act token w₂ w₃) :
    FrameKeeps solmateAbs crypto Act token w₁ w₃ where
  own k hk := (h₂.own k hk).trans (h₁.own k hk)
  code := h₂.code.trans h₁.code
  nonce := h₂.nonce.trans h₁.nonce
  balance := h₂.balance.trans h₁.balance
  others b hb := (h₂.others b hb).trans (h₁.others b hb)

/-- The allowance step of `transferFrom` read back: `spendState`. -/
theorem read_spendWorld {crypto : Crypto} {w : World} {token o sp : Address} {v : ℕ}
    {s₁ : VState Address} (hS : SolmateSound crypto Act) (ho : o ∈ Act) (hsp : sp ∈ Act)
    (hv : v < 2 ^ 256) (h : spendState (solmateRead crypto Act w token) o sp v = some s₁) :
    solmateRead crypto Act (ERC20.spendWorld crypto w token o sp (word v)) token = s₁ ∧
    FrameKeeps solmateAbs crypto Act token w (ERC20.spendWorld crypto w token o sp (word v)) ∧
    (w.sload token (ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp) = ERC20.maxWord ∨
      v ≤ (w.sload token (ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp)).toNat) := by
  have ha := allowance_read (crypto := crypto) (w := w) (token := token) ho hsp
  unfold spendState at h
  simp only [ERC20.spendWorld]
  by_cases hmax : (solmateRead crypto Act w token).allowance o sp = MAX
  · simp only [hmax, ↓reduceIte, Option.some.injEq] at h
    subst h
    have : w.sload token (ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp) = ERC20.maxWord :=
      (eq_maxWord_iff _).2 (by rw [← ha]; exact hmax)
    rw [if_pos' this]
    exact ⟨rfl, frameKeeps_refl _ _ _ _, .inl this⟩
  · simp only [hmax, ↓reduceIte] at h
    split_ifs at h with hlt
    simp only [Option.some.injEq] at h
    subst h
    have hne : w.sload token (ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp) ≠
        ERC20.maxWord := fun e => hmax (by rw [ha]; exact (eq_maxWord_iff _).1 e)
    rw [if_neg' hne]
    have hle : word v ≤ w.sload token (ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp) := by
      rw [BitVec.le_def, toNat_word hv, ← ha]; omega
    refine ⟨?_, ?_, .inr (by rw [← ha]; omega)⟩
    · simp only [ERC20.allowanceSlot, layout_allowances] at hle ha ⊢
      rw [read_sstore_allowance hS ho hsp]
      congr 1
      rw [BitVec.toNat_sub_of_le hle, toNat_word hv, ← ha]
    · simp only [ERC20.allowanceSlot, layout_allowances]
      exact frameKeeps_sstore (frameKeeps_refl _ _ _ _) (footprint_allowance ho hsp)

theorem spendState_none {s : VState Address} {o sp : Address} {v : ℕ}
    (h : spendState s o sp v = none) : s.allowance o sp ≠ MAX ∧ s.allowance o sp < v := by
  unfold spendState at h
  split_ifs at h with h1 h2
  exact ⟨h1, h2⟩

theorem spendState_bal {s s₁ : VState Address} {o sp : Address} {v : ℕ}
    (h : spendState s o sp v = some s₁) : s₁.bal = s.bal := by
  unfold spendState at h
  split_ifs at h <;> cases h <;> rfl

set_option maxHeartbeats 1000000 in
/-- **`transferFrom(src, dst, v)` in a normal frame** ends as the model says. -/
theorem transferFrom_normal (hS : Start (code ia) solmateAbs M Act m) {src dst : Address} {v : ℕ}
    (hE : (Call.transferFrom src dst v).Encodes m.frame.msg.data) (hsrc : src ∈ Act)
    (hdst : dst ∈ Act) (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : 90000 ≤ m.frame.gasLeft) :
    Halts m fun mf o =>
      Matches solmateAbs Act m mf o
        (M.events (pre solmateAbs Act m) m.frame.msg.caller (.transferFrom src dst v))
        (M.call (pre solmateAbs Act m) m.frame.msg.caller (.transferFrom src dst v)) := by
  obtain ⟨hv, hargs⟩ := hE
  have hd := threeWordCall_of_args hargs
  have hc := hS.caller
  have hpre := pre_eq hS hval
  simp only [M, solmateModel_call, solmateModel_events, solmateEvents, call_transferFrom]
  cases hsp : spendState (pre solmateAbs Act m) src m.frame.msg.caller v with
  | none =>
    obtain ⟨h1, h2⟩ := spendState_none hsp
    have ha := allowance_read (crypto := m.ctx.crypto) (w := m.world)
      (token := m.frame.msg.currentTarget) hsrc hc
    rw [← hpre] at ha
    refine (transferFrom_halts_revert m hS.fresh hval hst hd hS.size hg ?_).mono
      fun mf o _ h => h.1
    rintro ⟨hal, -⟩
    rcases hal with h | h
    · exact h1 (by rw [ha]; exact (eq_maxWord_iff _).1 h)
    · rw [toNat_word hv, ← ha] at h; omega
  | some s₁ =>
    rw [hpre] at hsp
    obtain ⟨hr₁, hk₁, hal⟩ := read_spendWorld (hS.sound) hsrc hc hv hsp
    have hb₁ := spendState_bal hsp
    have hbsrc : (solmateRead m.ctx.crypto Act (ERC20.spendWorld m.ctx.crypto m.world
        m.frame.msg.currentTarget src m.frame.msg.caller (word v)) m.frame.msg.currentTarget).bal src =
        ((ERC20.spendWorld m.ctx.crypto m.world m.frame.msg.currentTarget src m.frame.msg.caller
          (word v)).sload m.frame.msg.currentTarget
          (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat := bal_read hsrc
    rw [hr₁] at hbsrc
    simp only
    split_ifs with hlt
    · refine (transferFrom_halts_revert m hS.fresh hval hst hd hS.size hg ?_).mono
        fun mf o _ h => h.1
      rintro ⟨-, hb⟩
      rw [toNat_word hv, ← hbsrc] at hb; omega
    · have hle : v ≤ s₁.bal src := by omega
      refine (transferFrom_halts_ok_events m hS.fresh hval hst hd hS.size hg
        (by rw [toNat_word hv]; exact hal)
        (by rw [toNat_word hv, ← hbsrc]; omega)).mono fun mf o _ ⟨hok, hl⟩ => ?_
      have hrw := read_transferWorld (crypto := m.ctx.crypto)
        (w := ERC20.spendWorld m.ctx.crypto m.world m.frame.msg.currentTarget src
          m.frame.msg.caller (word v))
        (token := m.frame.msg.currentTarget) (hS.sound) hsrc hdst
        (by rw [hr₁]; exact hle) hv
        (fun hcd => by
          rw [hr₁, hb₁, ← hpre]
          exact bal_add_lt hS hcd (by rw [hpre, ← hb₁]; exact hle))
      rw [hr₁] at hrw
      refine ⟨hok.1, ?_, ?_, hok.2.2.1, hok.2.2.2.1, ?_⟩
      · show solmateRead _ _ _ _ = _
        rw [hok.2.1]; exact hrw.1
      · rw [hok.2.1]; exact frameKeeps_trans hk₁ hrw.2
      · rw [hl]; simp [eventLog_transfer]

/-! ## `approve` -/

set_option maxHeartbeats 1000000 in
/-- **`approve(sp, v)` in a normal frame** ends as the model says. -/
theorem approve_normal (hS : Start (code ia) solmateAbs M Act m) {sp : Address} {v : ℕ}
    (hE : (Call.approve sp v).Encodes m.frame.msg.data) (hsp : sp ∈ Act)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : 40000 ≤ m.frame.gasLeft) :
    Halts m fun mf o =>
      Matches solmateAbs Act m mf o
        (M.events (pre solmateAbs Act m) m.frame.msg.caller (.approve sp v))
        (M.call (pre solmateAbs Act m) m.frame.msg.caller (.approve sp v)) := by
  obtain ⟨hv, hargs⟩ := hE
  have hd := twoWordCall_of_args hargs
  have hc := hS.caller
  simp only [M, solmateModel_call, solmateModel_events, solmateEvents, call_approve]
  refine (approve_halts_events m hS.fresh hval hst hd hS.size hg).mono
    fun mf o _ ⟨hok, hl⟩ => ⟨hok.1, ?_, ?_, hok.2.2.1, hok.2.2.2.1, ?_⟩
  · show solmateRead _ _ _ _ = _
    rw [hok.2.1, pre_eq hS hval]
    simp only [ERC20.approveWorld, ERC20.allowanceSlot, layout_allowances]
    rw [read_sstore_allowance hS.sound hc hsp, toNat_word hv]
  · rw [hok.2.1]
    simp only [ERC20.approveWorld, ERC20.allowanceSlot, layout_allowances]
    exact frameKeeps_sstore (frameKeeps_refl _ _ _ _) (footprint_allowance hc hsp)
  · rw [hl]; simp [eventLog_approval]

/-! ## Views -/

/-- What a view ends with: the word `x`, nothing changed. -/
def ViewOk (x : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord x) ∧ mf.world = m.world ∧ mf.transient = m.transient ∧
    mf.createdAccounts = m.createdAccounts ∧ mf.frame.sub.logs = m.frame.sub.logs

set_option maxHeartbeats 0 in
/-- `totalSupply()` of the asset in any frame, with everything it keeps. -/
theorem totalSupply_halts (m : Machine) (hf : Fresh (code ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x18160ddd) (hsize : 4 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (ViewOk (m.world.sload m.frame.msg.currentTarget 2#256) m) := by
  apply WP.halts_of_false

  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- `allowance(owner, spender)` of the asset in any frame, with everything it keeps. -/
theorem allowance_halts (m : Machine) (hf : Fresh (code ia) m) (hval : m.frame.msg.value = 0)
    {owner spender : Address}
    (hd : TwoWordCall m.frame.msg.data 0xdd62ed3e (Word.ofAddress owner) (Word.ofAddress spender))
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (ViewOk (m.world.sload m.frame.msg.currentTarget
      (ERC20.allowanceSlot m.ctx.crypto ERC20.Layout.solmate owner spender)) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **A view in a frame with enough gas and no value** returns the model's value and changes
nothing (static frames included). -/
theorem view_normal (hS : Start (code ia) solmateAbs M Act m) (vw : View)
    (hE : vw.Encodes m.frame.msg.data) (hA : ∀ a ∈ vw.addrs, a ∈ Act)
    (hval : m.frame.msg.value = 0) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m fun mf o =>
      ∃ x : Word, o = .success (Bytes.ofWord x) ∧ x.toNat = vw.value M (pre solmateAbs Act m) ∧
        mf.world = m.world ∧ mf.transient = m.transient ∧
        mf.createdAccounts = m.createdAccounts ∧ mf.frame.sub.logs = m.frame.sub.logs := by
  rw [pre_eq hS hval]
  cases vw with
  | balanceOf a =>
    have ha : a ∈ Act := hA a (by simp [View.addrs])
    have hargs : Args m.frame.msg.data 0x70a08231 [Word.ofAddress a] := hE
    refine (balanceOf_halts m hS.fresh a hval hargs.selector
      (by have := hargs.size; simpa using this) hS.size (by simpa using hargs.arg 0 (by simp))
      hg).mono fun mf o _ ⟨h1, h2, h3, h4, h5, _⟩ => ⟨_, h1, ?_, h2, h3, h4, h5⟩
    exact (bal_read ha).symm
  | allowance ow sp =>
    have ho : ow ∈ Act := hA ow (by simp [View.addrs])
    have hsp : sp ∈ Act := hA sp (by simp [View.addrs])
    refine (allowance_halts m hS.fresh hval (twoWordCall_of_args hE) hS.size hg).mono
      fun mf o _ ⟨h1, h2, h3, h4, h5⟩ => ⟨_, h1, ?_, h2, h3, h4, h5⟩
    exact (allowance_read ho hsp).symm
  | totalSupply =>
    have hargs : Args m.frame.msg.data 0x18160ddd [] := hE
    refine (totalSupply_halts m hS.fresh hval
      hargs.selector (by have := hargs.size; simpa using this) hS.size hg).mono
      fun mf o _ ⟨h1, h2, h3, h4, h5⟩ => ⟨_, h1, rfl, h2, h3, h4, h5⟩

/-! ## Value and unknown selectors -/

set_option maxHeartbeats 0 in
/-- **A call with value reverts** (the asset has no payable function), whatever the calldata. -/
theorem value_reverts (m : Machine) (hf : Fresh (code ia) m) (hval : m.frame.msg.value ≠ 0)
    (hg : 100 ≤ m.frame.gasLeft) : Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hz := iszero_of_ne hval
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hz]
  exact ⟨_, rfl⟩

/-- **Unknown selectors and short calldata revert** in a frame with enough gas, as the model's
fallback says (with or without value). -/
theorem fallback_normal (hS : Start (code ia) solmateAbs M Act m)
    (hsel : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ ERC4626.assetSelectors)
    (hg : 1000 ≤ m.frame.gasLeft) :
    Halts m fun mf o =>
      Matches solmateAbs Act m mf o
        (M.events (pre solmateAbs Act m) m.frame.msg.caller (.other m.frame.msg.value.toNat))
        (M.call (pre solmateAbs Act m) m.frame.msg.caller (.other m.frame.msg.value.toNat)) := by
  simp only [M, solmateModel_call, call_other]
  show Halts m fun _ o => ∃ out, o = .revert out
  by_cases hval : m.frame.msg.value = 0
  · rcases hsel with h | h
    · exact ERC4626.asset_short_reverts m hS.fresh hval h hg
    · by_cases h4 : m.frame.msg.data.size < 4
      · exact ERC4626.asset_short_reverts m hS.fresh hval h4 hg
      · exact ERC4626.asset_unknown_reverts m hS.fresh hval (by omega) hS.size hg h
  · exact value_reverts m hS.fresh hval (by omega)

end Verified.Solmate.ERC20.Spec
