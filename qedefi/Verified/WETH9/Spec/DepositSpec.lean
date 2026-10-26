import Verified.WETH9.Spec.Fallback
import Verified.WETH9.Spec.Calls
import EvmLogic.Tx.Frame

/-!
# WETH9's fallback and `deposit()` satisfy `FallbackSpec` and `OpSpec`

Both run `deposit()`: `balanceOf[caller] += value` (unchecked), `Deposit(caller, value)`, stop.
The model (`Variant.weth9.deposit`) adds the value to the caller's balance and to the ether read
in the snapshot; the frame's world already has the value moved (`Start.launched`). `Start.value`
makes the two agree: the value is zero, or it came from another account without wrapping the
token's balance, so the token's ether is the snapshot's plus the value and its storage is the
snapshot's (`moveEther_dst_storage`). The credit cannot wrap either: the caller's balance is at
most the ether (`Start.wf`).

`weth9_fallbackSpec`, `weth9_opSpec`, for every gas.
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.GasMono EvmLogic.Solidity Verified.WETH9.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.WETH9 QEDefi.Math

/-- Moving ether into an account that does not end empty keeps its storage. -/
theorem moveEther_dst_storage {w : World} {src dst : Address} {v : Word} (hne : src ≠ dst)
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

/-- **The world of a deposit, read through `weth9Abs`, is the model's deposit**, for a `Start`
frame (value zero, or moved from another account without wrapping). -/
theorem read_deposit {Act : Finset Address} {m : Machine}
    (hS : Start WETH9.runtimeCode weth9Abs weth9Model Act m) :
    weth9Read m.ctx.crypto Act (m.world.sstore m.frame.msg.currentTarget
        (mappingSlot m.ctx.crypto (Word.ofAddress m.frame.msg.caller) 3)
        (m.world.sload m.frame.msg.currentTarget
          (mappingSlot m.ctx.crypto (Word.ofAddress m.frame.msg.caller) 3) + m.frame.msg.value))
      m.frame.msg.currentTarget =
    { pre weth9Abs Act m with
      bal := (pre weth9Abs Act m).bal + Finsupp.single m.frame.msg.caller m.frame.msg.value.toNat,
      ether := (pre weth9Abs Act m).ether + m.frame.msg.value.toNat } := by
  have hc : m.frame.msg.caller ∈ Act := hS.caller
  have hR : ActorRows m.ctx.crypto Act [3] [4] [] := hS.sound
  have hwf := (weth9Model_wf _).1 hS.wf
  simp only [pre, weth9Abs, weth9Read] at hwf ⊢
  -- the frame's world: the snapshot's storage, the snapshot's ether plus the value
  have hstore : ∀ k, m.world.sload m.frame.msg.currentTarget k =
      m.frame.snapshot.1.sload m.frame.msg.currentTarget k := by
    intro k
    rw [hS.launched]
    rcases hS.value with hv | ⟨htv, hne, hlt⟩
    · rw [transferValue_zero _ _ hv]
    · by_cases hv : m.frame.msg.value = 0
      · rw [transferValue_zero _ _ hv]
      · simp only [transferValue, htv, hv, ne_eq, not_false_eq_true, Bool.true_and,
          decide_true, ↓reduceIte]
        refine moveEther_dst_storage hne ?_ k
        intro h0
        have := congrArg BitVec.toNat h0
        rw [QEDefi.Solvency.toNat_add_of_lt hlt] at this
        exact hv (BitVec.eq_of_toNat_eq (by simp at this ⊢; omega))
  have hether : (m.world.balance m.frame.msg.currentTarget).toNat =
      (m.frame.snapshot.1.balance m.frame.msg.currentTarget).toNat +
        m.frame.msg.value.toNat := by
    rw [hS.launched]
    rcases hS.value with hv | ⟨htv, hne, hlt⟩
    · rw [transferValue_zero _ _ hv, hv]; simp
    · by_cases hv : m.frame.msg.value = 0
      · rw [transferValue_zero _ _ hv, hv]; simp
      · simp only [transferValue, htv, hv, ne_eq, not_false_eq_true, Bool.true_and,
          decide_true, ↓reduceIte]
        rw [balance_moveEther _ _ hne]
        simp only [Ne.symm hne, ↓reduceIte]
        exact QEDefi.Solvency.toNat_add_of_lt hlt
  have hread : readMap m.ctx.crypto Act m.world m.frame.msg.currentTarget 3 =
      readMap m.ctx.crypto Act m.frame.snapshot.1 m.frame.msg.currentTarget 3 :=
    readMap_congr fun k _ => hstore k
  have hread2 : readMap2 m.ctx.crypto Act m.world m.frame.msg.currentTarget 4 =
      readMap2 m.ctx.crypto Act m.frame.snapshot.1 m.frame.msg.currentTarget 4 :=
    readMap2_congr fun k _ => hstore k
  -- the credit does not wrap
  have hbound : (m.frame.snapshot.1.sload m.frame.msg.currentTarget
      (mappingSlot m.ctx.crypto (Word.ofAddress m.frame.msg.caller) 3)).toNat +
      m.frame.msg.value.toNat < 2 ^ 256 := by
    have h1 := Token.le_total (readMap m.ctx.crypto Act m.frame.snapshot.1
      m.frame.msg.currentTarget 3) m.frame.msg.caller
    rw [readMap_of_mem hc] at h1
    have h2 : (m.world.balance m.frame.msg.currentTarget).toNat < 2 ^ 256 :=
      (m.world.balance _).isLt
    omega
  congr 1
  · ext a
    rw [readMap_sstore_bal hR hc, Token.add_single_apply, hread]
    by_cases ha : a = m.frame.msg.caller
    · subst ha
      rw [hstore, QEDefi.Solvency.toNat_add_of_lt hbound, readMap_of_mem hc]
    · simp [ha, Ne.symm ha]
  · rw [readMap2_sstore_bal hR hc, hread2]
  · rw [World.balance_sstore, hether]

theorem deposit_logs (sub : Substate) (T c : Address) (v : Word) :
    sub.logs.push (depositLog9 T c v) =
      sub.logs ++ (([depositEvent c v.toNat] : List (Event Address)).map
        (QEDefi.ERC20.Spec.eventLog T)).toArray := by
  rw [Array.push_eq_append]
  simp only [List.map_cons, List.map_nil, QEDefi.ERC20.Spec.eventLog, depositEvent, eventArg,
    word, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

theorem weth9_call_other (s : VState Address) (c : Address) (v : ℕ) :
    W9.call s c (.other v) =
      .ok { s with bal := s.bal + Finsupp.single c v, ether := s.ether + v } .empty := by
  simp [weth9Model, Variant.call, Variant.step, Variant.fallbackCall, Variant.deposit,
    Variant.retData, Variant.weth9, Variant.standard]

/-- **WETH9's fallback is exact** (`deposit()` with the frame's value), for every gas. -/
theorem weth9_fallbackSpec :
    FallbackSpec WETH9.runtimeCode weth9Abs weth9Model weth9Gas weth9Sel := by
  intro Act m hS hcase
  have hc : m.frame.msg.caller ∈ Act := hS.caller
  refine halts_of_low (g₀ := weth9Gas) hS.fresh
    (fun hg _ _ hfo => .inr ⟨fails_of_failed hfo, fun h => hg h.1⟩)
    (fun _ _ _ _ _ h => h) fun g hg => ?_
  have hg' : 50000 ≤ g := le_trans (by decide) hg
  have hstat : m.frame.msg.isStatic = true → ∀ (mf : Machine) (e : ExceptionalHalt),
      (fun mf o => Matches weth9Abs Act m mf o
        (weth9Model.events (pre weth9Abs Act m) m.frame.msg.caller
          (.other m.frame.msg.value.toNat))
        (weth9Model.call (pre weth9Abs Act m) m.frame.msg.caller
          (.other m.frame.msg.value.toNat)) ∨
        (QEDefi.ERC20.Spec.Fails o ∧
          ¬ (weth9Gas ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false))) mf (.halt e) :=
    fun hs _ _ => .inr ⟨trivial, fun h => absurd h.2 (by rw [hs]; decide)⟩
  have hok : ∀ mf, mf.world = m.world.sstore m.frame.msg.currentTarget
        (mappingSlot m.ctx.crypto (Word.ofAddress m.frame.msg.caller) 3)
        (m.world.sload m.frame.msg.currentTarget
          (mappingSlot m.ctx.crypto (Word.ofAddress m.frame.msg.caller) 3) +
          m.frame.msg.value) →
      mf.transient = m.transient → mf.createdAccounts = m.createdAccounts →
      mf.frame.sub.logs = m.frame.sub.logs.push
        (depositLog9 m.frame.msg.currentTarget m.frame.msg.caller m.frame.msg.value) →
      Matches weth9Abs Act m mf (.success .empty)
        (weth9Model.events (pre weth9Abs Act m) m.frame.msg.caller
          (.other m.frame.msg.value.toNat))
        (weth9Model.call (pre weth9Abs Act m) m.frame.msg.caller
          (.other m.frame.msg.value.toNat)) := by
    intro mf hw ht hcr hl
    simp only [Matches, weth9Model, Variant.model_call, Variant.model_events]
    rw [show (Variant.weth9 : Variant Address).call = W9.call from rfl, weth9_call_other]
    refine ⟨rfl, ?_, ?_, ht, hcr, ?_⟩
    · rw [hw]; exact read_deposit hS
    · rw [hw]; exact frameKeeps_sstore (footprint_bal hc) _
    · rw [hl]; exact deposit_logs _ _ _ _
  by_cases hsz : m.frame.msg.data.size < 4
  · exact fallback_short_low hsz hg' (hstat) fun _ mf hw ht hcr hl => .inl (hok mf hw ht hcr hl)
  · have hsel : Abi.selectorOf m.frame.msg.data ∉ weth9Sel := by
      rcases hcase with h | h
      · exact absurd h hsz
      · exact h
    exact fallback_unknown_low (by omega) hS.size hsel hg' hstat
      fun _ mf hw ht hcr hl => .inl (hok mf hw ht hcr hl)

/-- **WETH9's `deposit()` is the model's `Op.deposit`**, for every gas. -/
theorem weth9_opSpec :
    OpSpec WETH9.runtimeCode weth9Abs weth9Model weth9Gas weth9Ops weth9OpAddrs := by
  intro Act m e hS hdec _
  have hc : m.frame.msg.caller ∈ Act := hS.caller
  simp only [weth9Ops] at hdec
  split at hdec
  · rename_i hd
    cases hdec
    refine halts_of_low (g₀ := weth9Gas) hS.fresh
      (fun hg _ _ hfo => .inr ⟨fails_of_failed hfo, fun h => hg h.1⟩)
      (fun _ _ _ _ _ h => h) fun g hg => ?_
    refine deposit_low hd.2 hd.1 hS.size (le_trans (by decide) hg)
      (fun hs _ _ => .inr ⟨trivial, fun h => absurd h.2 (by rw [hs]; decide)⟩) ?_
    intro _ mf hw ht hcr _
    left
    simp only [OpMatches, weth9Model, Variant.model_op, Variant.stepOp, Variant.deposit,
      Variant.weth9, Variant.standard, ↓reduceIte]
    refine ⟨⟨_, rfl⟩, ?_, ?_, ht, hcr⟩
    · rw [hw]; exact read_deposit hS
    · rw [hw]; exact frameKeeps_sstore (footprint_bal hc) _
  · cases hdec

end Verified.WETH9.Spec
