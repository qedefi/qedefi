module

public import Defi.ERC20.Variant

/-!
# Properties of the ERC-20 variants

* **Return conventions** (`safe_call`, `decoded_call_empty`, `unchecked_call_returnFalse`):
  a `SafeTransferLib`/`SafeERC20` caller sees exactly the state change of the call, for every
  return and failure convention; a `returns (bool)` decoder rejects every call of a function
  returning nothing (all USDT transfers and approvals, BNB transfers); a caller ignoring the
  return data continues after a `returnFalse` failure as if it had succeeded.
* **Supply invariant** `Variant.WF`, preserved by every operation of every `Sane` variant
  (`WF_exec`): `Σ bal = totalSupply ≤ MAX` for stored supplies (fees paid to the owner stay in
  `Σ bal`, burned fees leave both sides, `destroyBlackFunds` burns); `Σ bal ≤ ether` for
  WETH9 (the ether backing); `Σ gons = TOTAL_GONS` with `scale = TOTAL_GONS / supply` for a
  rebasing token, whose fragment balances then sum to at most the supply
  (`sum_balanceOf_le_supply`).
* **Exact effects** of a transfer: without fee every variant moves exactly `v` in the
  `balanceOf` view, rebasing included (`move_balanceOf`); with a fee the recipient gets
  `v − fee` and the fee goes to the owner or leaves the supply (`move_fee_dst`,
  `move_fee_supply`).
* **Approvals**: USDT's `approve` succeeds iff `v = 0 ∨ allowance = 0` (`usdt_approve_isSome_iff`);
  BNB's `approve(·, 0)` always fails (`bnb_approve_zero`).
-/

@[expose] public noncomputable section

namespace Defi.ERC20
open Defi.Math Finsupp Defi.ERC20.Token

namespace Variant

variable {A : Type} [DecidableEq A] [Zero A] (V : Variant A)

/-! ## Return conventions -/

theorem safe_failWith {σ : Type} (s : σ) (k : OnFail) : (failWith s k).safe = none := by
  cases k <;> rfl

theorem safe_retData (s : VState A) (c : Call A) : (Result.ok s (V.retData c)).safe = some s := by
  cases c <;> simp only [retData] <;> (try split_ifs) <;> rfl

/-- A `SafeTransferLib`/`SafeERC20` caller sees exactly the state change of the call, whatever
the return-data and failure conventions. -/
theorem safe_call (s : VState A) (c : A) (op : Call A) : (V.call s c op).safe = V.step s c op := by
  unfold call
  cases V.step s c op with
  | none => exact safe_failWith _ _
  | some s' => exact V.safe_retData s' op

theorem decoded_failWith {σ : Type} (s : σ) (k : OnFail) : (failWith s k).decoded = none := by
  cases k <;> rfl

/-- A `returns (bool)` decoder rejects every outcome of a function that returns nothing. -/
theorem decoded_call_empty (s : VState A) (c : A) (op : Call A)
    (h : V.retData op = .empty) : (V.call s c op).decoded = none := by
  unfold call
  cases V.step s c op with
  | none => exact decoded_failWith _ _
  | some s' => simp only [h]; rfl

theorem retData_transfer_empty (h : V.returns .transfer = .empty) (d : A) (v : ℕ) :
    V.retData (.transfer d v) = .empty := by
  simp [retData, h]

theorem retData_transferFrom_empty (h : V.returns .transferFrom = .empty) (src d : A) (v : ℕ) :
    V.retData (.transferFrom src d v) = .empty := by
  simp [retData, h]

theorem retData_approve_empty (h : V.returns .approve = .empty) (sp : A) (v : ℕ) :
    V.retData (.approve sp v) = .empty := by
  simp [retData, h]

/-- Every USDT `transfer`, `transferFrom` and `approve` reverts in a caller that decodes a
`bool` (solc ≥ 0.4.22 `IERC20` interface), whatever the state. -/
theorem usdt_decoded_eq_none (s : VState A) (c : A) (op : Call A) (hop : ∀ value, op ≠ .other value) :
    ((usdt : Variant A).call s c op).decoded = none := by
  apply decoded_call_empty
  cases op with
  | other value => exact absurd rfl (hop value)
  | _ => simp [retData, usdt]

/-- BNB's `transfer` reverts in a `bool`-decoding caller (its `transferFrom` does not). -/
theorem bnb_decoded_transfer (s : VState A) (c d : A) (v : ℕ) :
    ((bnb : Variant A).call s c (.transfer d v)).decoded = none :=
  decoded_call_empty _ _ _ _ (by simp [retData, bnb])

/-- A caller ignoring the return data continues, unchanged, after a call that "failed" by
returning `false`: it proceeds as if the tokens had moved. -/
theorem unchecked_call_returnFalse (s : VState A) (c : A) (op : Call A)
    (hf : V.arithFail = .returnFalse) (hg : V.guardOk s c op = true) (hs : V.step s c op = none) :
    (V.call s c op).unchecked = some s := by
  simp [call, hs, hg, hf, failWith, Result.unchecked]

/-- USDT fails with `INVALID` (all gas consumed) on an insufficient balance, once its guards
(pause, blacklist) pass. -/
theorem usdt_call_invalid (s : VState A) (c d : A) (v : ℕ)
    (hg : (usdt : Variant A).moveOk s c d v = true) (hb : s.bal c < v) :
    (usdt : Variant A).call s c (.transfer d v) = .halt .invalid := by
  have hs : (usdt : Variant A).step s c (.transfer d v) = none := by
    simp [step, transfer, move, units, usdt, standard, hb]
  simp only [call, hs, guardOk, hg, ↓reduceIte]
  rfl

/-- BNB's fallback accepts every unknown selector (a "phantom" `permit(…)`): success, empty
return data, no effect on balances or allowances. -/
theorem bnb_phantom (s : VState A) (c : A) (value : ℕ) :
    (bnb : Variant A).call s c (.other value) = .ok { s with ether := s.ether + value } .empty := by
  simp [call, step, fallbackCall, bnb, retData]

/-! ## Approvals -/

/-- **USDT approve race guard.** `approve(sp, v)` succeeds iff `v = 0` or the current
allowance is `0`. -/
theorem usdt_approve_isSome_iff (s : VState A) (c sp : A) (v : ℕ) :
    ((usdt : Variant A).approve s c sp v).isSome ↔ (v = 0 ∨ s.allowance c sp = 0) := by
  by_cases hv : v = 0 <;> by_cases ha : s.allowance c sp = 0 <;>
    simp [approve, approveOk, usdt, standard, hv, ha]

/-- With the guard, `approve(x)` followed by `approve(y)` (both nonzero, nothing in between)
always fails. -/
theorem approve_approve_eq_none (hg : V.approveGuard = true) (s : VState A) (c sp : A) {x y : ℕ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (V.approve s c sp x).bind (fun s' => V.approve s' c sp y) = none := by
  unfold approve
  split_ifs with h1
  · simp [approveOk, hg, hy, hx, VState.setAllowance]
  · rfl

/-- The reset pattern (`approve(0)`, then `approve(y)`) always works on USDT. -/
theorem usdt_approve_reset (s : VState A) (c sp : A) (y : ℕ) :
    ((usdt : Variant A).approve s c sp 0).bind (fun s' => (usdt : Variant A).approve s' c sp y) =
      some ((s.setAllowance c sp 0).setAllowance c sp y) := by
  simp [approve, approveOk, usdt, standard, VState.setAllowance]

/-- On BNB the reset pattern fails: `approve(·, 0)` reverts, so an allowance can never be
lowered to `0`. -/
theorem bnb_approve_zero (s : VState A) (c sp : A) : (bnb : Variant A).approve s c sp 0 = none := by
  simp [approve, approveOk, bnb, standard]

/-! ## Field bookkeeping -/

theorem credit_fields (s : VState A) (src dst : A) (v : ℕ) :
    (V.credit s src dst v).scale = s.scale ∧ (V.credit s src dst v).ether = s.ether ∧
      (V.credit s src dst v).allowance = s.allowance ∧ (V.credit s src dst v).admin = s.admin ∧
      (V.credit s src dst v).self = s.self ∧ (V.credit s src dst v).feeBps = s.feeBps ∧
      (V.credit s src dst v).feeMax = s.feeMax := by
  unfold credit
  split_ifs
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases V.feeSink <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem move_eq_some {s s' : VState A} {src dst : A} {v : ℕ} :
    V.move s src dst v = some s' ↔
      V.units s v ≤ s.bal src ∧ V.feeOf s v ≤ v ∧ s' = V.credit s src dst v := by
  unfold move
  split_ifs with h1 h2
  · simp only [false_iff, not_and]; omega
  · simp only [false_iff, not_and]; omega
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨by omega, by omega, rfl⟩
    · rintro ⟨-, -, rfl⟩; rfl

/-- What `spend` changes: only allowances. -/
theorem spend_eq_some {s s' : VState A} {o sp : A} {v : ℕ} (h : V.spend s o sp v = some s') :
    s'.bal = s.bal ∧ s'.supply = s.supply ∧ s'.scale = s.scale ∧ s'.ether = s.ether ∧
      s'.admin = s.admin ∧ s'.self = s.self ∧ s'.feeBps = s.feeBps ∧ s'.feeMax = s.feeMax ∧
      s'.paused = s.paused ∧ s'.blacklisted = s.blacklisted := by
  unfold spend at h
  split_ifs at h <;> cases h <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem transferFrom_eq_some {s s' : VState A} {c src dst : A} {v : ℕ}
    (h : V.transferFrom s c src dst v = some s') :
    ∃ s1, V.spend s src c v = some s1 ∧ V.move s1 src dst v = some s' := by
  unfold transferFrom at h
  split_ifs at h
  exact Option.bind_eq_some_iff.1 h

theorem units_of_not_rebasing (hr : V.rebasing = false) (s : VState A) (v : ℕ) : V.units s v = v := by
  simp [units, hr]

theorem balanceOf_of_not_rebasing (hr : V.rebasing = false) (s : VState A) (a : A) :
    V.balanceOf s a = s.bal a := by
  simp [balanceOf, hr]

/-! ## Exact effects -/

/-- Without fee and rebasing, a transfer is the `Token` balance move. -/
theorem move_exact {s s' : VState A} {src dst : A} {v : ℕ} (hr : V.rebasing = false)
    (hf : V.feeOf s v = 0) (h : V.move s src dst v = some s') :
    v ≤ s.bal src ∧ s'.bal = s.bal - single src v + single dst v ∧ s'.supply = s.supply := by
  obtain ⟨h1, -, rfl⟩ := (V.move_eq_some).1 h
  rw [units_of_not_rebasing V hr] at h1
  have hb : (V.credit s src dst v).bal = s.bal - single src v + single dst v := by
    simp only [credit, hf, ↓reduceIte, units_of_not_rebasing V hr]
  exact ⟨h1, hb, by simp only [credit, hf, ↓reduceIte]⟩

/-- **Exact effect in the `balanceOf` view**, for every variant without fee (rebasing ones
included, given a positive scale): `src` loses `v`, `dst` gains `v`, nobody else changes. -/
theorem move_balanceOf {s s' : VState A} {src dst : A} {v : ℕ} (hf : V.feeOf s v = 0)
    (hk : V.rebasing = true → 0 < s.scale) (h : V.move s src dst v = some s') :
    v ≤ V.balanceOf s src ∧ s'.scale = s.scale ∧
      (src ≠ dst → V.balanceOf s' src = V.balanceOf s src - v) ∧
      (src ≠ dst → V.balanceOf s' dst = V.balanceOf s dst + v) ∧
      (∀ x, x ≠ src → x ≠ dst → V.balanceOf s' x = V.balanceOf s x) ∧
      (src = dst → V.balanceOf s' src = V.balanceOf s src) := by
  obtain ⟨h1, -, rfl⟩ := (V.move_eq_some).1 h
  have hsc := (V.credit_fields s src dst v).1
  have hb : (V.credit s src dst v).bal = s.bal - single src (V.units s v) + single dst (V.units s v) := by
    simp only [credit, hf, ↓reduceIte]
  refine ⟨?_, hsc, ?_, ?_, ?_, ?_⟩
  · unfold balanceOf; unfold units at h1
    split_ifs at h1 ⊢ with hr
    · exact (Nat.le_div_iff_mul_le (hk hr)).2 h1
    · exact h1
  · intro hne
    unfold balanceOf; rw [hb, hsc, move_apply_src _ _ hne]; unfold units at h1 ⊢
    split_ifs at h1 ⊢ with hr
    · rw [show v * s.scale = s.scale * v from Nat.mul_comm _ _]; exact Nat.sub_mul_div _ _ _
    · rfl
  · intro hne
    unfold balanceOf; rw [hb, hsc, move_apply_dst _ _ hne]; unfold units
    split_ifs with hr
    · exact Nat.add_mul_div_right _ _ (hk hr)
    · rfl
  · intro x hx1 hx2
    unfold balanceOf; rw [hb, hsc, move_apply_other _ _ (Ne.symm hx1) (Ne.symm hx2)]
  · rintro rfl
    unfold balanceOf; rw [hb, hsc, move_self h1]

/-- With a fee, the recipient (not the payer, not the fee owner) receives `v − fee`. -/
theorem move_fee_dst {s s' : VState A} {src dst : A} {v : ℕ} (hr : V.rebasing = false)
    (h : V.move s src dst v = some s') (hsd : src ≠ dst)
    (hda : V.feeSink = .owner → dst ≠ s.admin) :
    s'.bal dst = s.bal dst + v - V.feeOf s v := by
  obtain ⟨-, -, rfl⟩ := (V.move_eq_some).1 h
  simp only [credit, units_of_not_rebasing V hr]
  split_ifs with hf
  · rw [hf, move_apply_dst _ _ hsd]; rfl
  · cases hk : V.feeSink with
    | owner =>
      simp only
      rw [add_single_apply, sub_single_apply, move_apply_dst _ _ hsd]
      simp [Ne.symm (hda hk)]
    | burn =>
      simp only
      rw [sub_single_apply, move_apply_dst _ _ hsd]
      simp

/-- The payer (not the fee owner) loses exactly `v`. -/
theorem move_fee_src {s s' : VState A} {src dst : A} {v : ℕ} (hr : V.rebasing = false)
    (h : V.move s src dst v = some s') (hsd : src ≠ dst)
    (hsa : V.feeSink = .owner → src ≠ s.admin) :
    s'.bal src = s.bal src - v := by
  obtain ⟨-, -, rfl⟩ := (V.move_eq_some).1 h
  simp only [credit, units_of_not_rebasing V hr]
  split_ifs with hf
  · rw [move_apply_src _ _ hsd]
  · cases hk : V.feeSink with
    | owner =>
      simp only
      rw [add_single_apply, sub_single_apply, move_apply_src _ _ hsd]
      simp [Ne.symm (hsa hk), Ne.symm hsd]
    | burn =>
      simp only
      rw [sub_single_apply, move_apply_src _ _ hsd]
      simp [Ne.symm hsd]

/-- A burned fee leaves the supply; an owner fee does not. -/
theorem move_fee_supply {s s' : VState A} {src dst : A} {v : ℕ}
    (h : V.move s src dst v = some s') :
    s'.supply = s.supply - (if V.feeSink = .burn then V.feeOf s v else 0) := by
  obtain ⟨-, -, rfl⟩ := (V.move_eq_some).1 h
  by_cases hf : V.feeOf s v = 0
  · simp [credit, hf]
  · cases hk : V.feeSink <;> simp [credit, hf, hk]

/-- The two shapes of a non-rebasing transfer's result (`f = 0` is the second with nothing
burned). -/
theorem credit_cases (hr : V.rebasing = false) (s : VState A) (src dst : A) (v : ℕ) :
    ((V.credit s src dst v).bal = s.bal - single src v + single dst v - single dst (V.feeOf s v) +
        single s.admin (V.feeOf s v) ∧ (V.credit s src dst v).supply = s.supply) ∨
    ((V.credit s src dst v).bal = s.bal - single src v + single dst v - single dst (V.feeOf s v) ∧
        (V.credit s src dst v).supply = s.supply - V.feeOf s v) := by
  by_cases hf : V.feeOf s v = 0
  · right; simp [credit, hf, units_of_not_rebasing V hr]
  · cases hk : V.feeSink
    · left; simp [credit, hf, hk, units_of_not_rebasing V hr]
    · right; simp [credit, hf, hk, units_of_not_rebasing V hr]

/-! ## The supply invariant -/

/-- The supply invariant of a variant. -/
def WF (s : VState A) : Prop :=
  if V.rebasing then
    total s.bal = V.totalGons ∧ 0 < s.supply ∧ s.supply ≤ V.maxSupply ∧
      s.scale = V.totalGons / s.supply
  else if V.supply = .ether then total s.bal ≤ s.ether
  else total s.bal = s.supply ∧ s.supply ≤ MAX

/-- Policy combinations under which `WF` is an invariant: a rebasing token has no fee, no
mint/burn, no blacklist burn, a stored supply and a positive cap with `cap² ≤ TOTAL_GONS`; an
ether-backed token has no mint. -/
structure Sane : Prop where
  /-- Rebasing tokens charge no fee. -/
  rebasing_fee : V.rebasing = true → V.fee = .none
  /-- Rebasing tokens cannot mint. -/
  rebasing_mint : V.rebasing = true → V.mintAuth = .nobody
  /-- Rebasing tokens cannot burn. -/
  rebasing_burn : V.rebasing = true → V.burnAuth = .nobody
  /-- Rebasing tokens have no `destroyBlackFunds`. -/
  rebasing_blacklist : V.rebasing = true → V.blacklist = false
  /-- Rebasing tokens store their supply. -/
  rebasing_stored : V.rebasing = true → V.supply = .stored
  /-- The rebase cap is positive and `cap² ≤ TOTAL_GONS`. -/
  rebasing_cap : V.rebasing = true → 0 < V.maxSupply ∧ V.maxSupply ^ 2 ≤ V.totalGons
  /-- Ether-backed tokens cannot mint. -/
  ether_mint : V.supply = .ether → V.mintAuth = .nobody

theorem WF_congr {s s' : VState A} (h1 : s'.bal = s.bal) (h2 : s'.supply = s.supply)
    (h3 : s'.scale = s.scale) (h4 : s'.ether = s.ether) (hw : V.WF s) : V.WF s' := by
  unfold WF at *; rw [h1, h2, h3, h4]; exact hw

theorem WF_ether_le {s s' : VState A} (h1 : s'.bal = s.bal) (h2 : s'.supply = s.supply)
    (h3 : s'.scale = s.scale) (h4 : s.ether ≤ s'.ether) (hw : V.WF s) : V.WF s' := by
  unfold WF at *; rw [h1, h2, h3]
  split_ifs at hw ⊢
  · exact hw
  · exact le_trans hw h4
  · exact hw

theorem total_move {b : A →₀ ℕ} {src dst : A} {g : ℕ} (h : g ≤ b src) :
    total (b - single src g + single dst g) = total b := by
  rw [total_add_single, total_sub_single h]
  have := le_total b src
  omega

theorem le_move_dst {b : A →₀ ℕ} {src dst : A} {g : ℕ} (h : g ≤ b src) :
    g ≤ (b - single src g + single dst g) dst := by
  by_cases hsd : src = dst
  · subst hsd; rw [move_self h]; exact h
  · rw [move_apply_dst _ _ hsd]; omega

theorem WF_credit {s : VState A} {src dst : A} {v : ℕ} (hV : V.Sane) (hw : V.WF s)
    (h1 : V.units s v ≤ s.bal src) (h2 : V.feeOf s v ≤ v) : V.WF (V.credit s src dst v) := by
  obtain ⟨hsc, het, -⟩ := V.credit_fields s src dst v
  by_cases hr : V.rebasing = true
  · have hf : V.feeOf s v = 0 := by simp [feeOf, hV.rebasing_fee hr]
    have hb : (V.credit s src dst v).bal =
        s.bal - single src (V.units s v) + single dst (V.units s v) := by
      simp only [credit, hf, ↓reduceIte]
    have hs : (V.credit s src dst v).supply = s.supply := by simp only [credit, hf, ↓reduceIte]
    unfold WF at hw ⊢; simp only [hr, ↓reduceIte] at hw ⊢
    rw [hb, hs, hsc, total_move h1]; exact hw
  · have hr' : V.rebasing = false := by simpa using hr
    rw [units_of_not_rebasing V hr'] at h1
    have hd := le_move_dst (dst := dst) h1
    have htot := total_move (dst := dst) h1
    have hfd := le_trans h2 hd
    have hle := le_total (s.bal - single src v + single dst v) dst
    unfold WF at hw ⊢; simp only [hr', Bool.false_eq_true, ↓reduceIte] at hw ⊢
    rw [het]
    rcases V.credit_cases hr' s src dst v with ⟨hb, hs⟩ | ⟨hb, hs⟩
    · rw [hb, hs, total_add_single, total_sub_single hfd, htot]
      split_ifs at hw ⊢ <;> omega
    · rw [hb, hs, total_sub_single hfd, htot]
      split_ifs at hw ⊢ <;> omega

theorem WF_move {s s' : VState A} {src dst : A} {v : ℕ} (hV : V.Sane) (hw : V.WF s)
    (h : V.move s src dst v = some s') : V.WF s' := by
  obtain ⟨h1, h2, rfl⟩ := (V.move_eq_some).1 h
  exact V.WF_credit hV hw h1 h2

theorem WF_spend {s s' : VState A} {o sp : A} {v : ℕ} (hw : V.WF s)
    (h : V.spend s o sp v = some s') : V.WF s' := by
  obtain ⟨h1, h2, h3, h4, -⟩ := V.spend_eq_some h
  exact V.WF_congr h1 h2 h3 h4 hw

theorem WF_transfer {s s' : VState A} {c d : A} {v : ℕ} (hV : V.Sane) (hw : V.WF s)
    (h : V.transfer s c d v = some s') : V.WF s' := by
  unfold transfer at h
  split_ifs at h
  exact V.WF_move hV hw h

theorem WF_transferFrom {s s' : VState A} {c src d : A} {v : ℕ} (hV : V.Sane) (hw : V.WF s)
    (h : V.transferFrom s c src d v = some s') : V.WF s' := by
  obtain ⟨s1, h1, h2⟩ := V.transferFrom_eq_some h
  exact V.WF_move hV (V.WF_spend hw h1) h2

theorem WF_approve {s s' : VState A} {c sp : A} {v : ℕ} (hw : V.WF s)
    (h : V.approve s c sp v = some s') : V.WF s' := by
  unfold approve at h
  split_ifs at h
  cases h
  exact V.WF_congr rfl rfl rfl rfl hw

theorem WF_deposit {s s' : VState A} {c : A} {v : ℕ} (hV : V.Sane) (hw : V.WF s)
    (h : V.deposit s c v = some s') : V.WF s' := by
  unfold deposit at h
  split_ifs at h with he
  cases h
  have hr : V.rebasing = false := by
    cases hr : V.rebasing
    · rfl
    · have := hV.rebasing_stored hr; rw [this] at he; cases he
  unfold WF at hw ⊢
  simp only [hr, he, Bool.false_eq_true, ↓reduceIte] at hw ⊢
  rw [total_add_single]; omega

theorem WF_withdraw {s s' : VState A} {c : A} {w : ℕ} {ok : Bool} (hV : V.Sane) (hw : V.WF s)
    (h : V.withdraw s c w ok = some s') : V.WF s' := by
  unfold withdraw at h
  split_ifs at h with he h1 h2 h3
  cases h
  have he' : V.supply = .ether := by simpa using he
  have hr : V.rebasing = false := by
    cases hr : V.rebasing
    · rfl
    · have := hV.rebasing_stored hr; rw [this] at he'; cases he'
  have := le_total s.bal c
  unfold WF at hw ⊢
  simp only [hr, he', Bool.false_eq_true, ↓reduceIte] at hw ⊢
  rw [total_sub_single (by omega)]
  omega

theorem WF_fallbackCall {s s' : VState A} {c : A} {v : ℕ} (hV : V.Sane) (hw : V.WF s)
    (h : V.fallbackCall s c v = some s') : V.WF s' := by
  unfold fallbackCall at h
  cases hk : V.fallback <;> simp only [hk, reduceCtorEq] at h
  · cases h
    exact V.WF_ether_le (s := s) rfl rfl rfl (Nat.le_add_right _ _) hw
  · exact V.WF_deposit hV hw h

theorem WF_step {s s' : VState A} {c : A} {op : Call A} (hV : V.Sane) (hw : V.WF s)
    (h : V.step s c op = some s') : V.WF s' := by
  cases op with
  | transfer d v => exact V.WF_transfer hV hw h
  | transferFrom src d v => exact V.WF_transferFrom hV hw h
  | approve sp v => exact V.WF_approve hw h
  | other v => exact V.WF_fallbackCall hV hw h

theorem WF_mint {s s' : VState A} {c d : A} {v : ℕ} (hV : V.Sane) (hw : V.WF s)
    (h : V.mint s c d v = some s') : V.WF s' := by
  unfold mint at h
  split_ifs at h with h0 h1 h2 h3
  cases h
  have hr : V.rebasing = false := by
    cases hr : V.rebasing
    · rfl
    · rw [hV.rebasing_mint hr] at h0; simp [Auth.allows] at h0
  have he : V.supply ≠ .ether := by
    intro he; rw [hV.ether_mint he] at h0; simp [Auth.allows] at h0
  unfold WF at hw ⊢
  simp only [hr, he, Bool.false_eq_true, ↓reduceIte, units] at hw ⊢
  rw [total_add_single]; omega

theorem WF_burn {s s' : VState A} {c src : A} {v : ℕ} (hV : V.Sane) (hw : V.WF s)
    (h : V.burn s c src v = some s') : V.WF s' := by
  unfold burn at h
  split_ifs at h with h0 h1 h2 h3
  cases h
  have hr : V.rebasing = false := by
    cases hr : V.rebasing
    · rfl
    · rw [hV.rebasing_burn hr] at h0; simp [Auth.allows] at h0
  have h3' : v ≤ s.bal src := by simpa [units, hr] using h3
  have := le_total s.bal src
  unfold WF at hw ⊢
  simp only [hr, Bool.false_eq_true, ↓reduceIte, units] at hw ⊢
  rw [total_sub_single h3']
  split_ifs at hw ⊢ <;> omega

theorem WF_destroyBlackFunds {s s' : VState A} {c u : A} (hV : V.Sane) (hw : V.WF s)
    (h : V.destroyBlackFunds s c u = some s') : V.WF s' := by
  unfold destroyBlackFunds at h
  split_ifs at h with h0
  cases h
  have hr : V.rebasing = false := by
    cases hr : V.rebasing
    · rfl
    · rw [hV.rebasing_blacklist hr] at h0; simp at h0
  have := le_total s.bal u
  unfold WF at hw ⊢
  simp only [hr, Bool.false_eq_true, ↓reduceIte] at hw ⊢
  rw [total_sub_single le_rfl]
  split_ifs at hw ⊢ <;> omega

theorem WF_rebase {s s' : VState A} {c : A} {S : ℕ} (hV : V.Sane) (hw : V.WF s)
    (h : V.rebase s c S = some s') : V.WF s' := by
  unfold rebase at h
  split_ifs at h with h0
  cases h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
  obtain ⟨⟨hr, -⟩, hS⟩ := h0
  have hc := (hV.rebasing_cap hr).1
  unfold WF at hw ⊢
  simp only [hr, ↓reduceIte] at hw ⊢
  exact ⟨hw.1, lt_min hS hc, min_le_right _ _, by trivial⟩

theorem WF_setPaused {s s' : VState A} {c : A} {b : Bool} (hw : V.WF s)
    (h : V.setPaused s c b = some s') : V.WF s' := by
  unfold setPaused at h
  split_ifs at h
  cases h
  exact V.WF_congr (s := s) rfl rfl rfl rfl hw

theorem WF_setBlacklisted {s s' : VState A} {c u : A} {b : Bool} (hw : V.WF s)
    (h : V.setBlacklisted s c u b = some s') : V.WF s' := by
  unfold setBlacklisted at h
  split_ifs at h
  cases h
  exact V.WF_congr (s := s) rfl rfl rfl rfl hw

theorem WF_setParams {s s' : VState A} {c : A} {b m : ℕ} (hw : V.WF s)
    (h : V.setParams s c b m = some s') : V.WF s' := by
  unfold setParams at h
  split_ifs at h
  cases h
  exact V.WF_congr (s := s) rfl rfl rfl rfl hw

/-- `WF` is preserved by every operation of a `Sane` variant. -/
theorem WF_stepOp {s s' : VState A} {op : Op A} (hV : V.Sane) (hw : V.WF s)
    (h : V.stepOp s op = some s') : V.WF s' := by
  cases op with
  | call c op => exact V.WF_step hV hw h
  | mint c d v => exact V.WF_mint hV hw h
  | burn c src v => exact V.WF_burn hV hw h
  | deposit c v => exact V.WF_deposit hV hw h
  | withdraw c w ok => exact V.WF_withdraw hV hw h
  | receiveEther v => cases h; exact V.WF_ether_le (s := s) rfl rfl rfl (Nat.le_add_right _ _) hw
  | setPaused c b => exact V.WF_setPaused hw h
  | setBlacklisted c u b => exact V.WF_setBlacklisted hw h
  | destroyBlackFunds c u => exact V.WF_destroyBlackFunds hV hw h
  | setParams c b m => exact V.WF_setParams hw h
  | rebase c S => exact V.WF_rebase hV hw h

/-- **Supply invariant.** Any sequence of operations, by any callers, preserves `WF`. -/
theorem WF_exec {s : VState A} (hV : V.Sane) (hw : V.WF s) (ops : List (Op A)) :
    V.WF (V.exec s ops) := by
  induction ops generalizing s with
  | nil => exact hw
  | cons op ops ih =>
    apply ih
    cases h : V.stepOp s op with
    | none => exact hw
    | some s' => exact V.WF_stepOp hV hw h

/-! ## Rebasing: the fragment view is bounded by the supply -/

theorem sum_div_mul_le (b : A →₀ ℕ) (k : ℕ) :
    (b.sum fun _ g => g / k) * k ≤ total b := by
  unfold Finsupp.sum total
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun _ _ => Nat.div_mul_le_self _ _

/-- For a rebasing token, `Σₐ balanceOf a = Σₐ ⌊gons a / scale⌋ ≤ totalSupply`: the fragment
balances never add up to more than the supply (they can add up to less). -/
theorem sum_balanceOf_le_supply {s : VState A} (hV : V.Sane) (hw : V.WF s)
    (hr : V.rebasing = true) : (s.bal.sum fun _ g => g / s.scale) ≤ s.supply := by
  unfold WF at hw
  simp only [hr, ↓reduceIte] at hw
  obtain ⟨htot, hpos, hcap, hsc⟩ := hw
  obtain ⟨-, hsq⟩ := hV.rebasing_cap hr
  set S := s.supply
  set TG := V.totalGons
  have hSS : S * S ≤ TG := by
    calc S * S ≤ V.maxSupply * V.maxSupply := Nat.mul_le_mul hcap hcap
      _ = V.maxSupply ^ 2 := by ring
      _ ≤ TG := hsq
  have hSk : S ≤ s.scale := by rw [hsc]; exact (Nat.le_div_iff_mul_le hpos).2 hSS
  have hk : 0 < s.scale := lt_of_lt_of_le hpos hSk
  have hlt : TG < S * (TG / S + 1) := Nat.lt_mul_div_succ TG hpos
  have key : (s.bal.sum fun _ g => g / s.scale) * s.scale < (S + 1) * s.scale := by
    calc (s.bal.sum fun _ g => g / s.scale) * s.scale ≤ total s.bal := sum_div_mul_le _ _
      _ = TG := htot
      _ < S * (TG / S + 1) := hlt
      _ = S * s.scale + S := by rw [← hsc]; ring
      _ ≤ S * s.scale + s.scale := Nat.add_le_add_left hSk _
      _ = (S + 1) * s.scale := by ring
  exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_right key)

/-- After a rebase to `S` (within the cap), every balance is `gons / (TOTAL_GONS / S)`; no
gons move. -/
theorem rebase_balanceOf {s s' : VState A} {c : A} {S : ℕ} (hr : V.rebasing = true)
    (h : V.rebase s c S = some s') (hS : S ≤ V.maxSupply) (a : A) :
    V.balanceOf s' a = s.bal a / (V.totalGons / S) ∧ s'.supply = S := by
  unfold rebase at h
  split_ifs at h
  cases h
  simp [balanceOf, hr, min_eq_left hS]

/-! ## WETH9: ether backing -/

/-- **Ether backing.** Every sequence of WETH9 operations (deposits, withdrawals, transfers,
approvals, forced ether, unknown selectors) keeps `Σ balanceOf ≤ address(this).balance`. -/
theorem weth9_backed_exec {s : VState A} (hw : total s.bal ≤ s.ether) (ops : List (Op A)) :
    total ((weth9 : Variant A).exec s ops).bal ≤ ((weth9 : Variant A).exec s ops).ether := by
  have hV : (weth9 : Variant A).Sane :=
    ⟨by simp [weth9, standard], by simp [weth9, standard], by simp [weth9, standard],
      by simp [weth9, standard], by simp [weth9, standard], by simp [weth9, standard],
      fun _ => rfl⟩
  have h := (weth9 : Variant A).WF_exec hV (s := s)
    (by unfold WF; simpa [weth9, standard] using hw) ops
  unfold WF at h
  simpa [weth9, standard] using h

/-- WETH9's `totalSupply()` (the ether balance) is at least the sum of the balances. -/
theorem weth9_sum_le_totalSupply (s : VState A) (hw : total s.bal ≤ s.ether) :
    total s.bal ≤ (weth9 : Variant A).totalSupply s := by
  simpa [totalSupply, weth9, standard] using hw

/-- WETH9 `deposit` credits the depositor exactly `value` and adds `value` wei. -/
theorem weth9_deposit (s : VState A) (c : A) (v : ℕ) :
    (weth9 : Variant A).deposit s c v =
      some { s with bal := s.bal + single c v, ether := s.ether + v } := by
  simp [deposit, weth9, standard]

/-- A WETH9 holder with `wad ≤ balance` can always withdraw (if its code accepts the ether),
given the backing: the debit and the ether payment are exact. -/
theorem weth9_withdraw {s : VState A} {c : A} {wad : ℕ} (hw : total s.bal ≤ s.ether)
    (hb : wad ≤ s.bal c) :
    (weth9 : Variant A).withdraw s c wad true =
      some { s with bal := s.bal - single c wad, ether := s.ether - wad } := by
  have := le_total s.bal c
  have h1 : ¬ s.bal c < wad := by omega
  have h2 : ¬ s.ether < wad := by omega
  simp [withdraw, weth9, standard, h1, h2]

/-! ## The instances are sane -/

theorem standard_sane : (standard : Variant A).Sane :=
  ⟨by simp [standard], by simp [standard], by simp [standard], by simp [standard],
    by simp [standard], by simp [standard], by simp [standard]⟩

theorem oz_sane : (oz : Variant A).Sane :=
  ⟨by simp [oz, standard], by simp [oz, standard], by simp [oz, standard],
    by simp [oz, standard], by simp [oz, standard], by simp [oz, standard],
    by simp [oz, standard]⟩

theorem solady_sane (p : A) : (solady p).Sane :=
  ⟨by simp [solady, standard], by simp [solady, standard], by simp [solady, standard],
    by simp [solady, standard], by simp [solady, standard], by simp [solady, standard],
    by simp [solady, standard]⟩

theorem weth9_sane : (weth9 : Variant A).Sane :=
  ⟨by simp [weth9, standard], by simp [weth9, standard], by simp [weth9, standard],
    by simp [weth9, standard], by simp [weth9, standard], by simp [weth9, standard],
    fun _ => rfl⟩

theorem usdt_sane : (usdt : Variant A).Sane :=
  ⟨by simp [usdt, standard], by simp [usdt, standard], by simp [usdt, standard],
    by simp [usdt, standard], by simp [usdt, standard], by simp [usdt, standard],
    by simp [usdt, standard]⟩

theorem bnb_sane : (bnb : Variant A).Sane :=
  ⟨by simp [bnb, standard], by simp [bnb, standard], by simp [bnb, standard],
    by simp [bnb, standard], by simp [bnb, standard], by simp [bnb, standard],
    by simp [bnb, standard]⟩

theorem sta_sane : (sta : Variant A).Sane :=
  ⟨by simp [sta, standard], by simp [sta, standard], by simp [sta, standard],
    by simp [sta, standard], by simp [sta, standard], by simp [sta, standard],
    by simp [sta, standard]⟩

theorem ampl_sane : (ampl : Variant A).Sane :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => ⟨by norm_num [ampl], by norm_num [ampl, amplTotalGons, MAX]⟩,
    by simp [ampl, standard]⟩

/-- STA's fee is `⌈v/100⌉`. -/
theorem sta_feeOf (s : VState A) (v : ℕ) : (sta : Variant A).feeOf s v = (v + 99) / 100 := by
  simp only [feeOf, sta]
  omega

end Variant

end Defi.ERC20
