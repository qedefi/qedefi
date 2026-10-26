module

public import QEDefi.ERC20.Spec.Model
public import QEDefi.ERC20.VariantExtras
public import QEDefi.ERC20.Spec.Instances.YAMV2
public import QEDefi.ERC20.Spec.VariantLaws

/-!
# USDT as a token model

`usdtModel` is mainnet `TetherToken` (solc 0.4.18) as a `TokenModel`: the policy record
`Variant.usdt` (no return data, `INVALID` on a short balance or allowance and on the SafeMath
overflow of the fee, the approve race guard, a capped basis-point fee paid to the owner, pause
and blacklist on transfers, owner-only `issue`/`redeem`, `destroyBlackFunds`) with USDT's event
rule `usdtEvents`, read off the verified source (`contracts/mainnet/USDT/source/`):

* `transfer(to, v)` by `c` (`BasicToken.transfer`) and `transferFrom(from, to, v)`
  (`StandardToken.transferFrom`) emit `Transfer(src, owner, fee)` when the fee is nonzero, then
  `Transfer(src, to, v − fee)`, where `src` is the payer (`c`, resp. `from`), `owner` the fee
  sink and `fee = min(v · basisPointsRate / 10⁴, maximumFee)`, all as in the state before the
  call (the allowance step changes neither);
* `approve(spender, v)` emits `Approval(c, spender, v)`;
* everything else emits no ERC-20 event (`issue`, `redeem`, `destroyBlackFunds`, the admin
  entry points emit their own events, which the bytecode spec of other entry points does not
  check; unknown selectors revert).

**The pause guard.** `pause()` is `onlyOwner whenNotPaused` and `unpause()` is
`onlyOwner whenPaused`: the code reverts on a `pause()` when already paused and on an
`unpause()` when not paused, while `Variant.usdt`'s `setPaused` succeeds for the owner whatever
the current flag. **`Variant.usdt` is wrong for those operations**, and `usdtModel` adds the
guard (`usdtOpGuard`: `setPaused c b` fails when `paused = b`). Every call and every other
operation is `Variant.usdt`'s (`usdtModel_op_of_ne`); `usdtModel_laws` decides the laws for the
guarded model.

The model's invariant is the supply bound as the actors see it (`YAMV2.SubSupply`:
`Σ bal ≤ supply ≤ MAX` over the balances in the state) instead of the record's `Variant.WF`
(`Σ bal = supply`), which holds only when the actors hold every token. It is what the bytecode
needs: SafeMath's `add` on a recipient's balance (and on the owner's, for the fee and `issue`)
cannot overflow, and `redeem`'s and `destroyBlackFunds`'s supply checks are implied by the
balance checks.

The deprecation forwarding (`deprecate(a)`, after which every entry point forwards to the token
at `a`) is not part of this model: it is the two-contract system of `VariantDeprecation.lean`.
The storage abstraction of the bytecode spec (`Verified.WeirdERC20.USDT.Spec`) represents only
non-deprecated deployments.
-/

@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.USDT
open QEDefi.ERC20 QEDefi.ERC20.Variant

variable {A : Type} [DecidableEq A] [Zero A]

/-- The two `Transfer` events of a USDT transfer of `v` paid by `src` to `dst` in state `s`:
the fee to the owner (only when it is nonzero), then the rest to `dst`. -/
def usdtMoveEvents (s : VState A) (src dst : A) (v : ℕ) : List (Event A) :=
  let fee := (usdt : Variant A).feeOf s v
  (if fee = 0 then [] else [.transfer src s.admin fee]) ++ [.transfer src dst (v - fee)]

/-- **USDT's events**: `Transfer`s of a transfer (`usdtMoveEvents`), `Approval` of an approve. -/
def usdtEvents (s : VState A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => usdtMoveEvents s caller dst v
  | .transferFrom src dst v => usdtMoveEvents s src dst v
  | .approve sp v => [.approval caller sp v]
  | .other _ => []
  | .permit .. => []

/-- USDT's `whenNotPaused`/`whenPaused` guard on `pause()`/`unpause()`: setting the pause flag
to the value it already has fails. -/
def usdtOpGuard (s : VState A) : Op A → Bool
  | .setPaused _ b => decide (s.paused = b)
  | _ => false

/-- **USDT as a token model**: `Variant.usdt` with USDT's events, its operations guarded by
`usdtOpGuard`, and the actors' supply bound as its invariant. -/
def usdtModel : TokenModel (VState A) A (Op A) :=
  { (usdt : Variant A).model usdtEvents with
    op := fun s e => if usdtOpGuard s e then none else (usdt : Variant A).stepOp s e
    wf := YAMV2.SubSupply }

@[simp] theorem usdtModel_call : (usdtModel : TokenModel (VState A) A (Op A)).call =
    (usdt : Variant A).call := rfl

@[simp] theorem usdtModel_events : (usdtModel : TokenModel (VState A) A (Op A)).events =
    usdtEvents := rfl

theorem usdtModel_op (s : VState A) (e : Op A) :
    (usdtModel : TokenModel (VState A) A (Op A)).op s e =
      if usdtOpGuard s e then none else (usdt : Variant A).stepOp s e := rfl

/-- **Off `setPaused` the model's operations are `Variant.usdt`'s.** -/
theorem usdtModel_op_of_ne (s : VState A) {e : Op A} (he : ∀ c b, e ≠ .setPaused c b) :
    (usdtModel : TokenModel (VState A) A (Op A)).op s e = (usdt : Variant A).stepOp s e := by
  rw [usdtModel_op]
  cases e <;> first | rfl | exact absurd rfl (he _ _)

/-- `pause()`/`unpause()`: the owner sets the flag, which must change. -/
theorem usdtModel_op_setPaused (s : VState A) (c : A) (b : Bool) :
    (usdtModel : TokenModel (VState A) A (Op A)).op s (.setPaused c b) =
      if c = s.admin ∧ s.paused ≠ b then some { s with paused := b } else none := by
  rw [usdtModel_op]
  by_cases h1 : c = s.admin <;> by_cases h2 : s.paused = b <;>
    simp [usdtOpGuard, h1, h2, Variant.stepOp, Variant.setPaused, usdt, Variant.standard]

@[simp] theorem usdtModel_wf : (usdtModel : TokenModel (VState A) A (Op A)).wf =
    YAMV2.SubSupply := rfl

@[simp] theorem usdtModel_balanceOf (s : VState A) (a : A) :
    (usdtModel : TokenModel (VState A) A (Op A)).balanceOf s a = s.bal a := rfl

@[simp] theorem usdtModel_totalSupply (s : VState A) :
    (usdtModel : TokenModel (VState A) A (Op A)).totalSupply s = s.supply := rfl

@[simp] theorem usdtModel_allowance (s : VState A) (o sp : A) :
    (usdtModel : TokenModel (VState A) A (Op A)).allowance s o sp = s.allowance o sp := rfl

/-! ## The laws of the guarded model

The calls, the views and so every law but `WFInvariant` are `Variant.usdt`'s, decided by
`usdt_laws`; the invariant is the actors' supply bound, which every call and every operation
keeps (a fee goes back to the owner; `issue`, `redeem` and `destroyBlackFunds` move the supply
with the balances; the guard only adds failures). -/

section Laws

open QEDefi.Math Finsupp QEDefi.ERC20.Token QEDefi.ERC20.Spec.VariantLaws

/-- A transfer's credit keeps the supply bound (the fee is paid to the owner). -/
theorem usdt_subSupply_credit {s : VState A} {src dst : A} {v : ℕ} (hw : YAMV2.SubSupply s)
    (h1 : v ≤ s.bal src) (h2 : (usdt : Variant A).feeOf s v ≤ v) :
    YAMV2.SubSupply ((usdt : Variant A).credit s src dst v) := by
  have hr : (usdt : Variant A).rebasing = false := rfl
  have hd := Variant.le_move_dst (dst := dst) h1
  have htot := Variant.total_move (dst := dst) h1
  have hfd := le_trans h2 hd
  have hle := le_total (s.bal - single src v + single dst v) dst
  obtain ⟨hw1, hw2⟩ := hw
  rcases (usdt : Variant A).credit_cases hr s src dst v with ⟨hb, hs⟩ | ⟨hb, hs⟩
  · refine ⟨?_, ?_⟩
    · rw [hb, hs, total_add_single, total_sub_single hfd, htot]; omega
    · rw [hs]; exact hw2
  · refine ⟨?_, ?_⟩
    · rw [hb, hs, total_sub_single hfd, htot]; omega
    · rw [hs]; omega

/-- Every successful `Variant.usdt` call keeps the supply bound. -/
theorem usdt_subSupply_step {s s' : VState A} {c : A} {op : Call A} (hw : YAMV2.SubSupply s)
    (h : (usdt : Variant A).step s c op = some s') : YAMV2.SubSupply s' := by
  have hr : (usdt : Variant A).rebasing = false := rfl
  cases op with
  | transfer d v =>
    simp only [Variant.step, Variant.transfer] at h
    split_ifs at h
    obtain ⟨h1, -, h2, rfl⟩ := (usdt : Variant A).move_eq_some.1 h
    rw [Variant.units_of_not_rebasing _ hr] at h1
    exact usdt_subSupply_credit hw h1 h2
  | transferFrom src d v =>
    obtain ⟨s1, h1, h2⟩ := (usdt : Variant A).transferFrom_eq_some h
    obtain ⟨hb, hs, -⟩ := (usdt : Variant A).spend_eq_some h1
    have hw1 : YAMV2.SubSupply s1 := by unfold YAMV2.SubSupply; rw [hb, hs]; exact hw
    obtain ⟨h3, -, h4, rfl⟩ := (usdt : Variant A).move_eq_some.1 h2
    rw [Variant.units_of_not_rebasing _ hr] at h3
    exact usdt_subSupply_credit hw1 h3 h4
  | approve sp v =>
    simp only [Variant.step, Variant.approve] at h
    split_ifs at h
    cases h
    exact hw
  | other value => simp [Variant.step, Variant.fallbackCall, usdt, Variant.standard] at h
  | permit o sp v live rec =>
    simp [Variant.step, Variant.permit, Variant.fallbackCall, usdt, Variant.standard] at h

/-- Every successful `Variant.usdt` operation keeps the supply bound. -/
theorem usdt_subSupply_stepOp {s s' : VState A} {e : Op A} (hw : YAMV2.SubSupply s)
    (h : (usdt : Variant A).stepOp s e = some s') : YAMV2.SubSupply s' := by
  have hr : (usdt : Variant A).rebasing = false := rfl
  cases e with
  | call c op => exact usdt_subSupply_step hw h
  | mint c d v => exact YAMV2.subSupply_mint hr hw h
  | burn c src v => exact YAMV2.subSupply_burn hr hw h
  | adjustAllowance c sp up x =>
    simp only [Variant.stepOp] at h
    exact YAMV2.subSupply_adjust hw h
  | receiveEther v => cases h; exact hw
  | setPaused c b =>
    simp only [Variant.stepOp, Variant.setPaused] at h
    split_ifs at h
    cases h
    exact hw
  | setBlacklisted c u b =>
    simp only [Variant.stepOp, Variant.setBlacklisted] at h
    split_ifs at h
    cases h
    exact hw
  | setParams c b m =>
    simp only [Variant.stepOp, Variant.setParams] at h
    split_ifs at h
    cases h
    exact hw
  | destroyBlackFunds c u =>
    simp only [Variant.stepOp, Variant.destroyBlackFunds] at h
    split_ifs at h
    cases h
    have := le_total s.bal u
    obtain ⟨hw1, hw2⟩ := hw
    refine ⟨?_, ?_⟩
    · show total (s.bal - single u (s.bal u)) ≤ s.supply - s.bal u
      rw [total_sub_single le_rfl]; omega
    · show s.supply - s.bal u ≤ MAX
      omega
  | deposit c v => simp [Variant.stepOp, Variant.deposit, usdt, Variant.standard] at h
  | withdraw c w ok => simp [Variant.stepOp, Variant.withdraw, usdt, Variant.standard] at h
  | rebase c S => simp [Variant.stepOp, Variant.rebase, usdt, Variant.standard] at h
  | freeze c v => simp [Variant.stepOp, Variant.freeze, usdt, Variant.standard] at h
  | unfreeze c v => simp [Variant.stepOp, Variant.unfreeze, usdt, Variant.standard] at h
  | withdrawEther c v ok =>
    simp [Variant.stepOp, Variant.withdrawEther, usdt, Variant.standard] at h
  | burnFrom c src v => simp [Variant.stepOp, Variant.burnFrom, usdt, Variant.standard] at h
  | transferAll c d => simp [Variant.stepOp, Variant.transferAll, usdt, Variant.standard] at h
  | transferAllFrom c src d =>
    simp [Variant.stepOp, Variant.transferAllFrom, usdt, Variant.standard] at h

/-- **The laws of USDT** (with the pause guard and the actors' supply bound as invariant): those
of `usdt_laws`, which are about the calls alone; not exact in every state of the supply bound
(it contains the well-formed witness of `usdt_fee_witness`); `WFInvariant` for the supply
bound. Refutations need two accounts (`Nontrivial A`). -/
theorem usdtModel_laws [Nontrivial A] :
    ¬ (usdtModel : TokenModel (VState A) A (Op A)).ReturnsTrue ∧
      (usdtModel : TokenModel (VState A) A (Op A)).NoFalseReturn ∧
      ¬ (usdtModel : TokenModel (VState A) A (Op A)).RevertsOnly ∧
      (usdtModel : TokenModel (VState A) A (Op A)).ExactMoves (NoFee usdt) ∧
      (usdtModel : TokenModel (VState A) A (Op A)).ExactMoves (fun s => s.feeBps = 0) ∧
      ¬ (usdtModel : TokenModel (VState A) A (Op A)).ExactMoves YAMV2.SubSupply ∧
      (usdtModel : TokenModel (VState A) A (Op A)).SupplyFixed ∧
      (usdtModel : TokenModel (VState A) A (Op A)).DebitAuth ∧
      (usdtModel : TokenModel (VState A) A (Op A)).AllowanceAuth ∧
      (usdtModel : TokenModel (VState A) A (Op A)).WFInvariant := by
  obtain ⟨hR, hN, hRv, hE, hE0, hEw, hS, hD, hA, -⟩ := usdt_laws (A := A) (ev := usdtEvents)
  refine ⟨hR, hN, hRv, hE, hE0, fun h => hEw (law_exactMoves_mono (fun s hs => ?_) h), hS, hD,
    hA, ⟨fun s caller c s' r hw h => ?_, fun s e s' hw h => ?_⟩⟩
  · have hr : (usdt : Variant A).rebasing = false := rfl
    have he : (usdt : Variant A).supply = .stored := rfl
    unfold Variant.WF at hs
    simp only [hr, he, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hs
    exact ⟨by omega, hs.2⟩
  · rcases law_call_eq_ok _ h with ⟨hs, -⟩ | ⟨-, rfl, -⟩
    · exact usdt_subSupply_step hw hs
    · exact hw
  · rw [usdtModel_op] at h
    split_ifs at h
    exact usdt_subSupply_stepOp hw h

end Laws

end QEDefi.ERC20.Spec.USDT
