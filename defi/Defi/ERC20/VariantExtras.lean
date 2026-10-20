module

public import Defi.ERC20.VariantProps
public import Defi.ERC20.Permit

/-!
# The extra entry points of the variants

* **Fee overflow.** USDT computes `v.mul(basisPointsRate)` with SafeMath before anything else
  in `BasicToken.transfer`/`StandardToken.transferFrom`; an overflow is an `assert`, i.e.
  `INVALID`. `usdt_call_transfer`/`usdt_call_transferFrom` give the complete outcome of a USDT
  transfer: `REVERT` iff paused or the sender (`transferFrom`: `from`) is blacklisted, otherwise
  `INVALID` iff the balance (allowance) is short or `MAX < v · bps`, otherwise success with no
  return data. The overflow needs `v > MAX/19 ≈ 6.1·10⁷⁵` (`setParams` caps `bps < 20`) and is
  unreachable while `19 · totalSupply ≤ MAX` (`usdt_overflow_unreachable`). STA's
  `cut(v) = ceil(v, 100).mul(100) / 10000` overflows iff `MAX < ⌈v/100⌉·100·100`, i.e. from
  `v ≈ MAX/100` on (`sta_feeOverflow_iff`), with `INVALID`, while a short balance reverts.
* **BNB.** `freeze`/`unfreeze` are holder-level (any holder, for itself; not owner-only) and
  move tokens to a second ledger: `totalSupply = Σ balanceOf + Σ freezeOf`
  (`bnb_supply_exec`), so `Σ balanceOf < totalSupply` while anything is frozen; freezing is
  undone exactly by unfreezing (`bnb_freeze_unfreeze`). `withdrawEther` is owner-only
  (`bnb_withdrawEther_not_owner`), and no other operation lowers the ether balance
  (`bnb_ether_le_stepOp`): ether sent with phantom calls belongs to the owner.
* **STA allowance helpers** (`upAllowance`/`downAllowance`, present in the source; there is no
  `increaseAllowance`): spender `0` reverts, overflow/underflow is `INVALID` (`sta_adjust_*`);
  `destroyFrom` spends even an infinite allowance (`sta_burnFrom`). AMPL's
  `decreaseAllowance` saturates at `0` and never fails (`ampl_decreaseAllowance`).
* **AMPL `transferAll`** moves all gons, dust included: the sender ends with `0` gons, the
  recipient's balance grows by the reported value or by one more (`ampl_transferAll_balanceOf`);
  a `transfer` of the full `balanceOf` instead leaves the dust behind (`ampl_transfer_dust`).
* **EIP-2612.** Solmate's `permit` is `PermitToken.permit` (`standard_permit`). On a variant
  without `permit` the call reaches the fallback: WETH9 and BNB report success and change
  nothing (`weth9_permit_phantom`, `bnb_permit_phantom`), so a `permit`-then-`transferFrom`
  integration spends a pre-existing allowance without any signature
  (`weth9_permit_then_transferFrom`); USDT, STA, OZ revert. AMPL accepts a failed signature
  recovery for `owner = 0` (`ampl_permit_zero_owner`), Solmate does not.
* **WETH9's ether send.** `withdraw` debits first and then `CALL`s the caller with a 2300-gas
  stipend; `withdrawWith` takes the callee's reaction as a function of the (already debited)
  state. With the stipend the callee can only accept or reject (`withdraw_eq_withdrawWith`):
  no `SSTORE` (EIP-2200 sentry), no value-carrying `CALL`, so no reentrant state change of
  WETH9 (or any contract); only `TSTORE`/logs, and WETH9 reads no transient storage. A
  rejection reverts the whole withdrawal (`weth9_withdraw_reject`). Even an unbounded
  reentrant callee could not break the backing (`weth9_backed_withdrawWith`) or withdraw the
  same funds twice (`weth9_reentrant_withdraw`): checks-effects-interactions.
-/

@[expose] public noncomputable section

namespace Defi.ERC20
open Defi.Math Finsupp Defi.ERC20.Token

namespace Variant

variable {A : Type} [DecidableEq A] [Zero A]

/-! ## Fee overflow -/

theorem usdt_moveOk (s : VState A) (src dst : A) (v : ℕ) :
    (usdt : Variant A).moveOk s src dst v = (!s.paused && !s.blacklisted src) := by
  simp [moveOk, usdt, standard]

omit [DecidableEq A] [Zero A] in
theorem usdt_feeOverflow (s : VState A) (v : ℕ) :
    (usdt : Variant A).feeOverflow s v = decide (MAX < v * s.feeBps) := by
  simp [feeOverflow, usdt]

omit [DecidableEq A] [Zero A] in
theorem usdt_feeOf (s : VState A) (v : ℕ) :
    (usdt : Variant A).feeOf s v = min (v * s.feeBps / 10000) s.feeMax := by
  simp [feeOf, usdt]

omit [DecidableEq A] [Zero A] in
theorem usdt_feeOf_le (s : VState A) (v : ℕ) (hb : s.feeBps ≤ 10000) :
    (usdt : Variant A).feeOf s v ≤ v := by
  rw [usdt_feeOf]
  refine le_trans (min_le_left _ _) (Nat.div_le_of_le_mul ?_)
  rw [Nat.mul_comm 10000]
  exact Nat.mul_le_mul_left _ hb

/-- **USDT `transfer`, complete outcome.** `REVERT` iff paused or the caller is blacklisted;
then `INVALID` iff the balance is short or `v · basisPointsRate` overflows; otherwise success
with no return data (for any `bps ≤ 10000`; `setParams` enforces `bps < 20`). -/
theorem usdt_call_transfer (s : VState A) (c d : A) (v : ℕ) (hb : s.feeBps ≤ 10000) :
    (usdt : Variant A).call s c (.transfer d v) =
      if s.paused = true ∨ s.blacklisted c = true then .halt .revert
      else if s.bal c < v ∨ MAX < v * s.feeBps then .halt .invalid
      else .ok ((usdt : Variant A).credit s c d v) .empty := by
  have hfee := usdt_feeOf_le s v hb
  have hu : (usdt : Variant A).units s v = v := by simp [units, usdt, standard]
  by_cases hg : s.paused = true ∨ s.blacklisted c = true
  · have hm : (usdt : Variant A).moveOk s c d v = false := by
      rw [usdt_moveOk]; rcases hg with h | h <;> simp [h]
    have hs : (usdt : Variant A).step s c (.transfer d v) = none := by
      simp only [step, transfer, hm, Bool.false_eq_true, ↓reduceIte]
    have hk : (usdt : Variant A).failKind s c (.transfer d v) = .revert := by
      simp only [failKind, guardOk, hm, Bool.not_false, ↓reduceIte]; rfl
    simp only [call, hs, hk, hg, ↓reduceIte]; rfl
  · have hm : (usdt : Variant A).moveOk s c d v = true := by
      rw [usdt_moveOk]; push Not at hg; simp [hg.1, hg.2]
    simp only [hg, ↓reduceIte]
    by_cases ha : s.bal c < v ∨ MAX < v * s.feeBps
    · have hs : (usdt : Variant A).step s c (.transfer d v) = none := by
        simp only [step, transfer, hm, ↓reduceIte, move, hu, usdt_feeOverflow]
        rcases ha with h | h
        · simp [h]
        · by_cases h' : s.bal c < v <;> simp [h, h']
      have hk : (usdt : Variant A).failKind s c (.transfer d v) = .invalid := by
        simp only [failKind, guardOk, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        split_ifs <;> simp [usdt]
      simp only [call, hs, hk, ha, ↓reduceIte]; rfl
    · push Not at ha
      have hs : (usdt : Variant A).step s c (.transfer d v) = some ((usdt : Variant A).credit s c d v) := by
        simp only [step, transfer, hm, ↓reduceIte, move, hu, usdt_feeOverflow]
        simp [Nat.not_lt.2 ha.1, Nat.not_lt.2 ha.2, Nat.not_lt.2 hfee]
      have hr : (usdt : Variant A).retData (.transfer d v) = .empty := by simp [retData, usdt]
      simp only [call, hs, hr, Nat.not_lt.2 ha.1, Nat.not_lt.2 ha.2, or_self, ↓reduceIte]

/-- The allowance step of a USDT `transferFrom`: infinite (`≥ MAX`) allowances are kept. -/
def usdtSpent (s : VState A) (src c : A) (v : ℕ) : VState A :=
  if MAX ≤ s.allowance src c then s else s.setAllowance src c (s.allowance src c - v)

/-- **USDT `transferFrom`, complete outcome.** `REVERT` iff paused or `from` is blacklisted (the
spender and the recipient are not checked); then `INVALID` iff the allowance (unless infinite)
or the balance is short or `v · bps` overflows; otherwise success with no return data. -/
theorem usdt_call_transferFrom (s : VState A) (c src d : A) (v : ℕ) (hb : s.feeBps ≤ 10000) :
    (usdt : Variant A).call s c (.transferFrom src d v) =
      if s.paused = true ∨ s.blacklisted src = true then .halt .revert
      else if (s.allowance src c < MAX ∧ s.allowance src c < v) ∨ s.bal src < v ∨
          MAX < v * s.feeBps then .halt .invalid
      else .ok ((usdt : Variant A).credit (usdtSpent s src c v) src d v) .empty := by
  have hu : ∀ t : VState A, (usdt : Variant A).units t v = v := fun t => by
    simp [units, usdt, standard]
  have hsp : (usdt : Variant A).spend s src c v =
      if s.allowance src c < MAX ∧ s.allowance src c < v then none else some (usdtSpent s src c v) := by
    unfold spend usdtSpent
    by_cases h1 : MAX ≤ s.allowance src c
    · simp [usdt, standard, Infinite.test, h1]
    · have h1' : s.allowance src c < MAX := by omega
      by_cases h2 : s.allowance src c < v <;> simp [usdt, standard, Infinite.test, h1, h1', h2]
  have hbs : (usdtSpent s src c v).bal = s.bal ∧ (usdtSpent s src c v).feeBps = s.feeBps ∧
      (usdtSpent s src c v).feeMax = s.feeMax := by
    unfold usdtSpent; split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  have hfee : (usdt : Variant A).feeOf (usdtSpent s src c v) v ≤ v :=
    usdt_feeOf_le _ v (hbs.2.1 ▸ hb)
  by_cases hg : s.paused = true ∨ s.blacklisted src = true
  · have hm : (usdt : Variant A).moveOk s src d v = false := by
      rw [usdt_moveOk]; rcases hg with h | h <;> simp [h]
    have hs : (usdt : Variant A).step s c (.transferFrom src d v) = none := by
      simp only [step, transferFrom, hm, Bool.false_eq_true, ↓reduceIte]
    have hk : (usdt : Variant A).failKind s c (.transferFrom src d v) = .revert := by
      simp only [failKind, guardOk, hm, Bool.not_false, ↓reduceIte]; rfl
    simp only [call, hs, hk, hg, ↓reduceIte]; rfl
  · have hm : (usdt : Variant A).moveOk s src d v = true := by
      rw [usdt_moveOk]; push Not at hg; simp [hg.1, hg.2]
    simp only [hg, ↓reduceIte]
    by_cases ha : (s.allowance src c < MAX ∧ s.allowance src c < v) ∨ s.bal src < v ∨
        MAX < v * s.feeBps
    · have hs : (usdt : Variant A).step s c (.transferFrom src d v) = none := by
        simp only [step, transferFrom, hm, ↓reduceIte, hsp]
        by_cases h1 : s.allowance src c < MAX ∧ s.allowance src c < v
        · simp [h1]
        · simp only [h1, ↓reduceIte, Option.bind_some, move, hu, usdt_feeOverflow, hbs.1, hbs.2.1]
          rcases ha with h | h | h
          · exact absurd h h1
          · simp [h]
          · by_cases h' : s.bal src < v <;> simp [h, h']
      have hk : (usdt : Variant A).failKind s c (.transferFrom src d v) = .invalid := by
        simp only [failKind, guardOk, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        split_ifs <;> simp [usdt]
      simp only [call, hs, hk, ha, ↓reduceIte]; rfl
    · push Not at ha
      obtain ⟨h1, h2, h3⟩ := ha
      have h1' : ¬ (s.allowance src c < MAX ∧ s.allowance src c < v) := by
        intro h; exact absurd (h1 h.1) (by omega)
      have hs : (usdt : Variant A).step s c (.transferFrom src d v) =
          some ((usdt : Variant A).credit (usdtSpent s src c v) src d v) := by
        simp only [step, transferFrom, hm, ↓reduceIte, hsp, h1', Option.bind_some, move, hu,
          usdt_feeOverflow, hbs.1, hbs.2.1]
        simp [Nat.not_lt.2 h2, Nat.not_lt.2 h3, Nat.not_lt.2 hfee]
      have hr : (usdt : Variant A).retData (.transferFrom src d v) = .empty := by
        simp [retData, usdt]
      have hne : ¬ ((s.allowance src c < MAX ∧ s.allowance src c < v) ∨ s.bal src < v ∨
          MAX < v * s.feeBps) := by
        rintro (h | h | h)
        · exact h1' h
        · omega
        · omega
      simp only [call, hs, hr, hne, ↓reduceIte]

omit [DecidableEq A] [Zero A] in
/-- With `bps < 20` the fee multiplication cannot overflow for `v ≤ MAX / 19`. -/
theorem usdt_feeOverflow_false {s : VState A} {v : ℕ} (hb : s.feeBps < 20) (hv : 19 * v ≤ MAX) :
    (usdt : Variant A).feeOverflow s v = false := by
  rw [usdt_feeOverflow]
  have : v * s.feeBps ≤ 19 * v := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
  simp only [decide_eq_false_iff_not, not_lt]
  omega

omit [Zero A] in
/-- **The USDT fee overflow is unreachable at realistic supplies.** In a well-formed state with
`bps < 20` and `19 · totalSupply ≤ MAX`, no transfer that passes the balance check overflows. -/
theorem usdt_overflow_unreachable {s : VState A} {c : A} {v : ℕ} (hw : (usdt : Variant A).WF s)
    (hb : s.feeBps < 20) (hS : 19 * s.supply ≤ MAX) (hv : v ≤ s.bal c) :
    (usdt : Variant A).feeOverflow s v = false := by
  apply usdt_feeOverflow_false hb
  unfold WF at hw
  simp only [usdt, standard, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hw
  have := Token.le_total s.bal c
  omega

omit [DecidableEq A] [Zero A] in
/-- **STA's `cut` overflows iff `MAX < ⌈v/100⌉ · 100 · 100`**, i.e. the `.mul(basePercent)` step
fails from `v ≈ MAX/100` on (long before `ceil`'s `v + 100`). -/
theorem sta_feeOverflow_iff (s : VState A) (v : ℕ) :
    (sta : Variant A).feeOverflow s v = true ↔ MAX < (v + 99) / 100 * 10000 := by
  simp only [feeOverflow, sta, Bool.or_eq_true, decide_eq_true_eq]
  unfold MAX
  omega

/-- STA: a short balance reverts, but a fee overflow (balance sufficient, recipient nonzero) is
`INVALID` (0.5.0 SafeMath `assert`). -/
theorem sta_call_transfer_overflow {s : VState A} {c d : A} {v : ℕ} (hd : d ≠ 0)
    (hv : v ≤ s.bal c) (ho : MAX < (v + 99) / 100 * 10000) :
    (sta : Variant A).call s c (.transfer d v) = .halt .invalid := by
  have hof : (sta : Variant A).feeOverflow s v = true := (sta_feeOverflow_iff s v).2 ho
  have hu : (sta : Variant A).units s v = v := by simp [units, sta, standard]
  have hm : (sta : Variant A).moveOk s c d v = true := by simp [moveOk, sta, standard, hd]
  have hs : (sta : Variant A).step s c (.transfer d v) = none := by
    simp [step, transfer, hm, move, hu, hof, Nat.not_lt.2 hv]
  have hk : (sta : Variant A).failKind s c (.transfer d v) = .invalid := by
    simp [failKind, guardOk, hm, overflows, hu, hv, hof]
  simp only [call, hs, hk]; rfl

theorem sta_call_transfer_short {s : VState A} {c d : A} {v : ℕ} (hd : d ≠ 0)
    (hv : s.bal c < v) : (sta : Variant A).call s c (.transfer d v) = .halt .revert := by
  have hu : (sta : Variant A).units s v = v := by simp [units, sta, standard]
  have hm : (sta : Variant A).moveOk s c d v = true := by simp [moveOk, sta, standard, hd]
  have hs : (sta : Variant A).step s c (.transfer d v) = none := by
    simp [step, transfer, hm, move, hu, hv]
  have hk : (sta : Variant A).failKind s c (.transfer d v) = .revert := by
    simp only [failKind, guardOk, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, overflows, hu,
      Nat.not_le.2 hv, decide_false, Bool.false_and]
    rfl
  simp only [call, hs, hk]; rfl

/-! ## BNB: the frozen ledger and the contract's ether -/

omit [DecidableEq A] [Zero A] in
theorem bnb_freeze (s : VState A) (c : A) (v : ℕ) :
    (bnb : Variant A).freeze s c v =
      if s.bal c < v ∨ v = 0 ∨ MAX < s.frozen c + v then none
      else some { s with bal := s.bal - single c v, frozen := s.frozen + single c v } := by
  unfold freeze
  by_cases h1 : s.bal c < v <;> by_cases h2 : v = 0 <;> by_cases h3 : MAX < s.frozen c + v <;>
    simp [bnb, standard, h1, h2, h3]

omit [DecidableEq A] [Zero A] in
theorem bnb_unfreeze (s : VState A) (c : A) (v : ℕ) :
    (bnb : Variant A).unfreeze s c v =
      if s.frozen c < v ∨ v = 0 ∨ MAX < s.bal c + v then none
      else some { s with frozen := s.frozen - single c v, bal := s.bal + single c v } := by
  unfold unfreeze
  by_cases h1 : s.frozen c < v <;> by_cases h2 : v = 0 <;> by_cases h3 : MAX < s.bal c + v <;>
    simp [bnb, standard, h1, h2, h3]

omit [Zero A] in
/-- **Freezing is undone exactly by unfreezing** (for a balance that fits in a word, as under
`WF`). -/
theorem bnb_freeze_unfreeze {s s1 : VState A} {c : A} {v : ℕ} (hb : s.bal c ≤ MAX)
    (h : (bnb : Variant A).freeze s c v = some s1) : (bnb : Variant A).unfreeze s1 c v = some s := by
  rw [bnb_freeze] at h
  split_ifs at h with h1
  cases h
  push Not at h1
  obtain ⟨h1, h2, -⟩ := h1
  rw [bnb_unfreeze]
  have e1 : (s.frozen + single c v) c = s.frozen c + v := by simp
  have e2 : (s.bal - single c v) c = s.bal c - v := by simp
  have hn : ¬ ((s.frozen + single c v) c < v ∨ v = 0 ∨ MAX < (s.bal - single c v) c + v) := by
    rw [e1, e2]; omega
  simp only [hn, ↓reduceIte, add_tsub_cancel_right, sub_single_add_single h1]

/-- **BNB's supply identity.** Every operation sequence keeps `Σ balanceOf + Σ freezeOf =
totalSupply ≤ MAX`. -/
theorem bnb_supply_exec {s : VState A} (hw : total s.bal + total s.frozen = s.supply)
    (hS : s.supply ≤ MAX) (ops : List (Op A)) :
    total ((bnb : Variant A).exec s ops).bal + total ((bnb : Variant A).exec s ops).frozen =
        ((bnb : Variant A).exec s ops).supply ∧ ((bnb : Variant A).exec s ops).supply ≤ MAX := by
  have h := (bnb : Variant A).WF_exec bnb_sane (s := s)
    (by unfold WF; simpa [bnb, standard] using ⟨hw, hS⟩) ops
  unfold WF at h
  simpa [bnb, standard] using h

omit [Zero A] in
/-- While anything is frozen, the balances add up to strictly less than `totalSupply` (the
ERC-20 identity `Σ balanceOf = totalSupply` fails). -/
theorem bnb_sum_lt_supply {s : VState A} (hw : total s.bal + total s.frozen = s.supply) {a : A}
    (ha : s.frozen a ≠ 0) : total s.bal < (bnb : Variant A).totalSupply s := by
  have := Token.le_total s.frozen a
  simp only [totalSupply, bnb, standard]
  omega

omit [Zero A] in
/-- `withdrawEther` by anyone but the owner reverts. -/
theorem bnb_withdrawEther_not_owner (s : VState A) {c : A} (v : ℕ) (ok : Bool) (hc : c ≠ s.admin) :
    (bnb : Variant A).withdrawEther s c v ok = none := by
  simp [withdrawEther, hc]

omit [Zero A] in
/-- The owner withdraws any amount up to the contract's ether, if its code accepts it. -/
theorem bnb_withdrawEther (s : VState A) {v : ℕ} (hv : v ≤ s.ether) :
    (bnb : Variant A).withdrawEther s s.admin v true = some { s with ether := s.ether - v } := by
  simp [withdrawEther, bnb, standard, Nat.not_lt.2 hv]

omit [DecidableEq A] [Zero A] in
theorem ether_fallbackCall {V : Variant A} {s s' : VState A} {c : A} {v : ℕ}
    (h : V.fallbackCall s c v = some s') : s.ether ≤ s'.ether := by
  unfold fallbackCall at h
  cases hk : V.fallback <;> simp only [hk, reduceCtorEq] at h
  · cases h; exact Nat.le_add_right _ _
  · unfold deposit at h; split_ifs at h; cases h; exact Nat.le_add_right _ _

/-- Only `withdraw` (WETH9) and `withdrawEther` (BNB) lower the contract's ether. -/
theorem ether_le_stepOp {V : Variant A} {s s' : VState A} {op : Op A}
    (h : V.stepOp s op = some s') :
    s.ether ≤ s'.ether ∨ (∃ c w ok, op = .withdraw c w ok) ∨ (∃ c v ok, op = .withdrawEther c v ok) := by
  cases op with
  | call c op =>
    left
    cases op with
    | transfer d v =>
      simp only [stepOp, step, transfer] at h
      split_ifs at h
      obtain ⟨-, -, -, rfl⟩ := (V.move_eq_some).1 h
      exact (V.credit_fields _ _ _ _).2.1.ge
    | transferFrom src d v =>
      obtain ⟨s1, h1, h2⟩ := V.transferFrom_eq_some h
      obtain ⟨-, -, -, e4, -⟩ := V.spend_eq_some h1
      obtain ⟨-, -, -, rfl⟩ := (V.move_eq_some).1 h2
      rw [(V.credit_fields _ _ _ _).2.1, e4]
    | approve sp v =>
      simp only [stepOp, step, approve] at h
      split_ifs at h; cases h; exact le_rfl
    | other v => exact ether_fallbackCall h
    | permit o sp v live rec =>
      simp only [stepOp, step, permit] at h
      split_ifs at h
      · exact ether_fallbackCall h
      · cases h; exact le_rfl
  | mint c d v => left; simp only [stepOp, mint] at h; split_ifs at h; cases h; exact le_rfl
  | burn c src v => left; simp only [stepOp, burn] at h; split_ifs at h; cases h; exact le_rfl
  | deposit c v =>
    left; simp only [stepOp, deposit] at h; split_ifs at h; cases h; exact Nat.le_add_right _ _
  | withdraw c w ok => exact Or.inr (Or.inl ⟨c, w, ok, rfl⟩)
  | receiveEther v => left; cases h; exact Nat.le_add_right _ _
  | setPaused c b => left; simp only [stepOp, setPaused] at h; split_ifs at h; cases h; exact le_rfl
  | setBlacklisted c u b =>
    left; simp only [stepOp, setBlacklisted] at h; split_ifs at h; cases h; exact le_rfl
  | destroyBlackFunds c u =>
    left; simp only [stepOp, destroyBlackFunds] at h; split_ifs at h; cases h; exact le_rfl
  | setParams c b m => left; simp only [stepOp, setParams] at h; split_ifs at h; cases h; exact le_rfl
  | rebase c S => left; simp only [stepOp, rebase] at h; split_ifs at h; cases h; exact le_rfl
  | freeze c v => left; simp only [stepOp, freeze] at h; split_ifs at h; cases h; exact le_rfl
  | unfreeze c v => left; simp only [stepOp, unfreeze] at h; split_ifs at h; cases h; exact le_rfl
  | withdrawEther c v ok => exact Or.inr (Or.inr ⟨c, v, ok, rfl⟩)
  | adjustAllowance c sp up x =>
    left; simp only [stepOp, adjustAllowance] at h
    cases hk : V.helpers <;> simp only [hk, reduceCtorEq] at h <;> split_ifs at h <;> cases h <;>
      exact le_rfl
  | burnFrom c src v => left; simp only [stepOp, burnFrom] at h; split_ifs at h; cases h; exact le_rfl
  | transferAll c d => left; simp only [stepOp, transferAll] at h; split_ifs at h; cases h; exact le_rfl
  | transferAllFrom c src d =>
    left; simp only [stepOp, transferAllFrom] at h
    split_ifs at h
    obtain ⟨s1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    exact (V.spend_eq_some h1).2.2.2.1.ge

/-- **Only the owner takes BNB's ether.** An operation that lowers the contract's ether
balance is `withdrawEther` by the owner. -/
theorem bnb_ether_le_stepOp {s s' : VState A} {op : Op A} (h : (bnb : Variant A).stepOp s op = some s') :
    s.ether ≤ s'.ether ∨ ∃ v, op = .withdrawEther s.admin v true := by
  rcases ether_le_stepOp h with h1 | ⟨c, w, ok, rfl⟩ | ⟨c, v, ok, rfl⟩
  · exact Or.inl h1
  · simp [stepOp, withdraw, bnb, standard] at h
  · by_cases hc : c = s.admin
    · subst hc
      cases ok
      · simp [stepOp, withdrawEther] at h
      · exact Or.inr ⟨v, rfl⟩
    · simp [stepOp, bnb_withdrawEther_not_owner _ _ _ hc] at h

/-! ## Allowance helpers and `destroyFrom` -/

/-- STA `upAllowance(sp, x)`: fails iff `sp = 0` or the sum overflows. -/
theorem sta_upAllowance (s : VState A) (c sp : A) (x : ℕ) :
    (sta : Variant A).adjustAllowance s c sp true x =
      if sp = 0 ∨ MAX < s.allowance c sp + x then none
      else some (s.setAllowance c sp (s.allowance c sp + x)) := by
  by_cases h1 : sp = 0 <;> by_cases h2 : MAX < s.allowance c sp + x <;>
    simp [adjustAllowance, sta, h1, h2]

/-- STA `downAllowance(sp, x)`: fails iff `sp = 0` or `x` exceeds the allowance. -/
theorem sta_downAllowance (s : VState A) (c sp : A) (x : ℕ) :
    (sta : Variant A).adjustAllowance s c sp false x =
      if sp = 0 ∨ s.allowance c sp < x then none
      else some (s.setAllowance c sp (s.allowance c sp - x)) := by
  by_cases h1 : sp = 0 <;> by_cases h2 : s.allowance c sp < x <;>
    simp [adjustAllowance, sta, h1, h2]

/-- STA's helpers fail with `REVERT` for spender `0` and with `INVALID` (SafeMath `assert`)
on overflow or underflow. -/
theorem sta_adjustFail (sp : A) :
    (sta : Variant A).adjustFail sp = if sp = 0 then .revert else .invalid := by
  simp [adjustFail, sta]

/-- AMPL `decreaseAllowance` saturates at `0` and never fails. -/
theorem ampl_decreaseAllowance (s : VState A) (c sp : A) (x : ℕ) :
    (ampl : Variant A).adjustAllowance s c sp false x =
      some (s.setAllowance c sp (s.allowance c sp - x)) := by
  simp [adjustAllowance, ampl]

/-- AMPL `increaseAllowance` fails (`REVERT`) iff the sum overflows; any spender, `0` included. -/
theorem ampl_increaseAllowance (s : VState A) (c sp : A) (x : ℕ) :
    (ampl : Variant A).adjustAllowance s c sp true x =
      if MAX < s.allowance c sp + x then none
      else some (s.setAllowance c sp (s.allowance c sp + x)) := by
  by_cases h : MAX < s.allowance c sp + x <;> simp [adjustAllowance, ampl, h]

omit [Zero A] in
/-- STA `destroyFrom(src, v)`: fails iff the allowance is short, `v = 0` or the balance is
short; spends `v` of allowance (even of an infinite one) and burns `v`. -/
theorem sta_burnFrom (s : VState A) (c src : A) (v : ℕ) :
    (sta : Variant A).burnFrom s c src v =
      if s.allowance src c < v ∨ v = 0 ∨ s.bal src < v then none
      else some { s.setAllowance src c (s.allowance src c - v) with
                  supply := s.supply - v, bal := s.bal - single src v } := by
  unfold burnFrom
  by_cases h1 : s.allowance src c < v <;> by_cases h2 : v = 0 <;> by_cases h3 : s.bal src < v <;>
    simp [sta, standard, units, h1, h2, h3]

/-! ## AMPL `transferAll` -/

/-- **`transferAll` moves the dust.** The sender ends with `0` gons; the recipient's balance
grows by the sender's reported balance (the `Transfer` event's value) or by one more. -/
theorem ampl_transferAll_balanceOf {s s' : VState A} {c d : A} (hcd : c ≠ d) (hk : 0 < s.scale)
    (h : (ampl : Variant A).transferAll s c d = some s') :
    s'.bal c = 0 ∧ (ampl : Variant A).balanceOf s' c = 0 ∧
      (ampl : Variant A).balanceOf s d + (ampl : Variant A).balanceOf s c ≤
        (ampl : Variant A).balanceOf s' d ∧
      (ampl : Variant A).balanceOf s' d ≤
        (ampl : Variant A).balanceOf s d + (ampl : Variant A).balanceOf s c + 1 := by
  unfold transferAll at h
  split_ifs at h
  cases h
  have e1 : (s.bal - single c (s.bal c) + single d (s.bal c)) c = 0 := by
    rw [move_apply_src _ _ hcd]; omega
  have e2 : (s.bal - single c (s.bal c) + single d (s.bal c)) d = s.bal d + s.bal c :=
    move_apply_dst _ _ hcd
  simp only [balanceOf, ampl, ↓reduceIte, e1, e2, Nat.zero_div, true_and]
  rw [Nat.add_div hk]
  split_ifs <;> omega

/-- A `transfer` of the full `balanceOf` instead leaves the dust: `gons mod gonsPerFragment`
stays with the sender, whose balance reads `0`. -/
theorem ampl_transfer_dust {s s' : VState A} {c d : A} (hcd : c ≠ d)
    (h : (ampl : Variant A).transfer s c d ((ampl : Variant A).balanceOf s c) = some s') :
    s'.bal c = s.bal c % s.scale ∧ (ampl : Variant A).balanceOf s' c = 0 := by
  unfold transfer at h
  split_ifs at h
  obtain ⟨h1, -, -, rfl⟩ := ((ampl : Variant A).move_eq_some).1 h
  have hsc := ((ampl : Variant A).credit_fields s c d ((ampl : Variant A).balanceOf s c)).1
  have hf : (ampl : Variant A).feeOf s ((ampl : Variant A).balanceOf s c) = 0 := by
    simp [feeOf, ampl, standard]
  have hm := Nat.mod_add_div (s.bal c) s.scale
  have hb : (ampl : Variant A).credit s c d ((ampl : Variant A).balanceOf s c) =
      { s with bal := s.bal - single c (s.bal c / s.scale * s.scale) +
                        single d (s.bal c / s.scale * s.scale) } := by
    unfold credit; simp only [hf, ↓reduceIte]; simp only [units, balanceOf, ampl, ↓reduceIte]
  have e : (s.bal c / s.scale * s.scale) = s.scale * (s.bal c / s.scale) := Nat.mul_comm _ _
  have hc : ((ampl : Variant A).credit s c d ((ampl : Variant A).balanceOf s c)).bal c =
      s.bal c % s.scale := by
    rw [hb]; simp only; rw [move_apply_src _ _ hcd]; omega
  refine ⟨hc, ?_⟩
  have hv : ∀ t : VState A, (ampl : Variant A).balanceOf t c = t.bal c / t.scale := fun _ => rfl
  rw [hv, hc, hsc]
  rcases Nat.eq_zero_or_pos s.scale with h0 | h0
  · simp [h0]
  · exact Nat.div_eq_of_lt (Nat.mod_lt _ h0)

/-! ## EIP-2612 `permit` -/

/-- **Solmate's `permit` is `PermitToken.permit`**, with validity "deadline not passed and
`ecrecover` returns the owner, which is not `0`". -/
theorem standard_permit (s : VState A) (c o sp : A) (v : ℕ) (live : Bool) (rec : ℕ → A) :
    (standard : Variant A).permit s c o sp v live rec =
      (PermitToken.permit ⟨s.toToken, s.nonces⟩ o sp v
          (fun n => live = true ∧ rec n = o ∧ o ≠ 0)).map
        fun p => { s.withToken p.token with nonces := p.nonces } := by
  unfold permit PermitToken.permit
  by_cases hl : live = true <;> by_cases hr : rec (s.nonces o) = o <;> by_cases ho : o = 0 <;>
    simp [standard, permitOk, hl, hr, ho]
  repeat' constructor

/-- Solmate rejects the zero owner even when signature recovery fails (returns `0`). -/
theorem standard_permit_zero_owner (s : VState A) (c sp : A) (v : ℕ) (live : Bool) :
    (standard : Variant A).permit s c 0 sp v live (fun _ => 0) = none := by
  simp [permit, permitOk, standard]

/-- **AMPL accepts a failed signature recovery for `owner = 0`** (`ecrecover` returns `0`, and
there is no zero check): any caller sets `allowance[0][sp]`. -/
theorem ampl_permit_zero_owner (s : VState A) (c sp : A) (v : ℕ) (hn : s.nonces 0 < MAX) :
    (ampl : Variant A).permit s c 0 sp v true (fun _ => 0) =
      some { s.setAllowance 0 sp v with nonces := s.nonces.update 0 (s.nonces 0 + 1) } := by
  have : ¬ MAX ≤ s.nonces 0 := by omega
  simp [permit, permitOk, ampl, standard, this, PermitToken.permit_nonce_of_lt hn]

/-- AMPL's nonce increment is checked: a permit at nonce `MAX` reverts (Solmate's wraps to `0`). -/
theorem ampl_permit_nonce_max (s : VState A) (c o sp : A) (v : ℕ) (live : Bool) (rec : ℕ → A)
    (hn : s.nonces o = MAX) : (ampl : Variant A).permit s c o sp v live rec = none := by
  simp [permit, permitOk, ampl, standard, hn]

theorem standard_permit_wraps (s : VState A) (c o sp : A) (v : ℕ) (hn : s.nonces o = MAX)
    (ho : o ≠ 0) (rec : ℕ → A) (hr : rec MAX = o) :
    (standard : Variant A).permit s c o sp v true rec =
      some { s.setAllowance o sp v with nonces := s.nonces.update o 0 } := by
  have : (MAX + 1) % U256 = 0 := by rw [MAX_add_one, Nat.mod_self]
  simp [permit, permitOk, standard, hn, ho, hr, this]

/-- **Phantom `permit` on WETH9.** The selector reaches the depositing fallback with no value:
success, no return data, and the state is unchanged — whatever the signature. -/
theorem weth9_permit_phantom (s : VState A) (c o sp : A) (v : ℕ) (live : Bool) (rec : ℕ → A) :
    (weth9 : Variant A).call s c (.permit o sp v live rec) = .ok s .empty := by
  have : (weth9 : Variant A).step s c (.permit o sp v live rec) = some s := by
    simp [step, permit, weth9, standard, fallbackCall, deposit]
  simp [call, this, retData]

/-- The same on BNB (payable fallback). -/
theorem bnb_permit_phantom (s : VState A) (c o sp : A) (v : ℕ) (live : Bool) (rec : ℕ → A) :
    (bnb : Variant A).call s c (.permit o sp v live rec) = .ok s .empty := by
  have : (bnb : Variant A).step s c (.permit o sp v live rec) = some s := by
    simp [step, permit, bnb, standard, fallbackCall]
  simp [call, this, retData]

/-- Without `permit` and without a fallback (USDT, STA, OpenZeppelin's mock) the call reverts. -/
theorem permit_none_revert {V : Variant A} (hp : V.permitRule = .none) (hf : V.fallback = .revert)
    (hg : V.guardFail = .revert) (s : VState A) (c o sp : A) (v : ℕ) (live : Bool)
    (rec : ℕ → A) : V.call s c (.permit o sp v live rec) = .halt .revert := by
  have hs : V.step s c (.permit o sp v live rec) = none := by
    simp [step, permit, hp, fallbackCall, hf]
  have hk : V.failKind s c (.permit o sp v live rec) = .revert := by
    simp [failKind, guardOk, hp, hf, hg]
  simp only [call, hs, hk]; rfl

/-- **`permit` then `transferFrom` on WETH9 needs no signature.** An integration that calls
`permit(o, …)` and then `transferFrom(o, …)` (through `SafeTransferLib`) moves `o`'s tokens
whenever `o` has a standing allowance for it, whatever signature it was given. -/
theorem weth9_permit_then_transferFrom (s : VState A) (c o sp : A) (v : ℕ) (live : Bool)
    (rec : ℕ → A) (src d : A) (w : ℕ) :
    ((weth9 : Variant A).call s c (.permit o sp v live rec)).safe.bind
        (fun s1 => ((weth9 : Variant A).call s1 c (.transferFrom src d w)).safe) =
      (weth9 : Variant A).transferFrom s c src d w := by
  rw [weth9_permit_phantom]
  show (Option.some s).bind _ = _
  rw [Option.bind_some, safe_call]
  rfl

/-! ## WETH9: the ether send in `withdraw` -/

/-- `withdraw(wad)` with the recipient's reaction `callee` to the ether: a function of the token
state it can observe (already debited), returning the state after its own calls, or `none` if
it fails (then the whole withdrawal reverts). -/
def withdrawWith (V : Variant A) (s : VState A) (caller : A) (wad : ℕ) (callee : VState A → Option (VState A)) :
    Option (VState A) :=
  if V.supply ≠ .ether then none
  else if s.bal caller < wad then none
  else if s.ether < wad then none
  else callee { s with bal := s.bal - single caller wad, ether := s.ether - wad }

omit [DecidableEq A] [Zero A] in
/-- The callees possible under the 2300-gas stipend: accept or reject, leaving every contract's
storage as it is (with ≤ 2300 gas no frame can `SSTORE` or send value; `TSTORE` and logs are
possible but not part of the token's state, and WETH9 never reads transient storage). -/
def stipend (ok : Bool) : VState A → Option (VState A) := fun t => if ok then some t else none

omit [DecidableEq A] [Zero A] in
theorem withdraw_eq_withdrawWith (V : Variant A) (s : VState A) (c : A) (wad : ℕ) (ok : Bool) :
    V.withdraw s c wad ok = V.withdrawWith s c wad (stipend ok) := by
  unfold withdraw withdrawWith stipend
  cases ok <;> simp

omit [DecidableEq A] [Zero A] in
/-- A rejected ether send reverts the withdrawal (the debit is undone). -/
theorem weth9_withdraw_reject (s : VState A) (c : A) (wad : ℕ) :
    (weth9 : Variant A).withdraw s c wad false = none := by
  simp [withdraw]

/-- **Checks-effects-interactions: backing.** Even a callee with unbounded gas that reenters
WETH9 with any operations keeps `Σ balanceOf ≤ address(this).balance`. -/
theorem weth9_backed_withdrawWith {s s' : VState A} {c : A} {wad : ℕ} {ops : List (Op A)}
    (hw : total s.bal ≤ s.ether)
    (h : (weth9 : Variant A).withdrawWith s c wad (fun t => some ((weth9 : Variant A).exec t ops)) =
      some s') : total s'.bal ≤ s'.ether := by
  unfold withdrawWith at h
  split_ifs at h with h0 h1 h2
  cases h
  apply weth9_backed_exec
  have := Token.le_total s.bal c
  simp only
  rw [total_sub_single (by omega)]
  omega

omit [DecidableEq A] [Zero A] in
/-- **No double withdrawal.** A reentrant `withdraw` by the same account sees the debited
balance: it fails for more than what is left. -/
theorem weth9_reentrant_withdraw {s : VState A} {c : A} {wad w : ℕ} (ok : Bool)
    (hw : s.bal c - wad < w) :
    (weth9 : Variant A).withdraw { s with bal := s.bal - single c wad, ether := s.ether - wad } c w ok =
      none := by
  have : (s.bal - single c wad) c < w := by simpa using hw
  have he : ¬ ((weth9 : Variant A).supply ≠ .ether) := by simp [weth9, standard]
  unfold withdraw
  simp only [he, this, ↓reduceIte]

end Variant

end Defi.ERC20
