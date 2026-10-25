import Verified.OpenZeppelin.ERC20.Spec.Abs

/-!
# `Variant.oz`'s outcomes and the callee summaries' conditions

The observable outcome of each `Variant.oz` call (`oz_call_*`: the `Token.oz*` operation, return
data `true`, `REVERT` on failure), and the conditions of the callee summaries
(`Callee*.lean`), stated on the full storage view, in terms of the actors' view: they read only
the rows of the call's accounts (`*_none_of`, `transferFromCond_iff_actors`).
-/

namespace Verified.OpenZeppelin.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Solidity EvmLogic.Solidity.ERC20 QEDefi.ERC20 QEDefi.ERC20.Spec
open QEDefi.Math EvmLean.Interpreter EvmLogic.Program

/-! ## The model's outcomes -/

theorem oz_call_transfer (s : VState Address) (c d : Address) (v : ℕ) :
    (Variant.oz : Variant Address).call s c (.transfer d v) =
      match s.toToken.ozTransfer c d v with
      | some t' => .ok (s.withToken t') (.word true)
      | none => .halt .revert := by
  simp only [Variant.call, Variant.step]
  rw [Variant.oz_transfer]
  cases s.toToken.ozTransfer c d v <;>
    simp [Variant.failWith, Variant.failKind, Variant.oz, Variant.standard, Variant.retData,
      Variant.overflows, Variant.feeOverflow]

theorem oz_call_transferFrom (s : VState Address) (c src d : Address) (v : ℕ) :
    (Variant.oz : Variant Address).call s c (.transferFrom src d v) =
      match s.toToken.ozTransferFrom c src d v with
      | some t' => .ok (s.withToken t') (.word true)
      | none => .halt .revert := by
  simp only [Variant.call, Variant.step]
  rw [Variant.oz_transferFrom]
  cases s.toToken.ozTransferFrom c src d v <;>
    simp [Variant.failWith, Variant.failKind, Variant.oz, Variant.standard, Variant.retData,
      Variant.overflows, Variant.feeOverflow]

theorem oz_call_approve (s : VState Address) (c sp : Address) (v : ℕ) :
    (Variant.oz : Variant Address).call s c (.approve sp v) =
      match s.toToken.ozApprove c sp v with
      | some t' => .ok (s.withToken t') (.word true)
      | none => .halt .revert := by
  simp only [Variant.call, Variant.step]
  rw [Variant.oz_approve]
  cases s.toToken.ozApprove c sp v <;>
    simp [Variant.failWith, Variant.failKind, Variant.oz, Variant.standard, Variant.retData,
      Variant.overflows]

theorem oz_call_other (s : VState Address) (c : Address) (v : ℕ) :
    (Variant.oz : Variant Address).call s c (.other v) = .halt .revert := by
  simp [Variant.call, Variant.step, Variant.fallbackCall, Variant.failWith, Variant.failKind,
    Variant.oz, Variant.standard, Variant.guardOk]

/-! ## The callee summaries' conditions -/

variable {crypto : Crypto} {Act : Finset Address} {w : World} {token : Address}

theorem view_balanceOf_eq {a : Address} (ha : a ∈ Act) :
    (view crypto Layout.oz w token).balanceOf a = (actorView crypto Act w token).balanceOf a :=
  (actorView_balanceOf ha).symm

theorem ozTransfer_none_of {c d : Address} {amount : Word} (hc : c ∈ Act)
    (h : Model.ozTransfer (actorView crypto Act w token) c d amount = none) :
    Model.ozTransfer (view crypto Layout.oz w token) c d amount = none := by
  unfold Model.ozTransfer Model.transfer at *
  rw [view_balanceOf_eq hc]
  split <;> simp_all

theorem ozApprove_none_of {o sp : Address} {amount : Word} {s s' : State}
    (h : Model.ozApprove s o sp amount = none) : Model.ozApprove s' o sp amount = none := by
  unfold Model.ozApprove at *
  split <;> simp_all

theorem ozMint_none_of {d : Address} {amount : Word}
    (h : Model.ozMint (actorView crypto Act w token) d amount = none) :
    Model.ozMint (view crypto Layout.oz w token) d amount = none := by
  unfold Model.ozMint at *
  have : (view crypto Layout.oz w token).totalSupply =
      (actorView crypto Act w token).totalSupply := rfl
  rw [this]
  split <;> simp_all

theorem ozBurn_none_of {src : Address} {amount : Word} (hs : src ∈ Act)
    (h : Model.ozBurn (actorView crypto Act w token) src amount = none) :
    Model.ozBurn (view crypto Layout.oz w token) src amount = none := by
  unfold Model.ozBurn at *
  rw [view_balanceOf_eq hs]
  split <;> simp_all

/-- With the actors' rows distinct, `TransferFromCond` is the success of `Model.ozTransferFrom`
on the actors' view. -/
theorem transferFromCond_iff_actors (m : Machine) (src dst : Address) (amount : Word)
    (hR : ozSound m.ctx.crypto Act) (hs : src ∈ Act) (hc : m.frame.msg.caller ∈ Act) :
    TransferFromCond m src dst amount ↔
      (Model.ozTransferFrom (actorView m.ctx.crypto Act m.world m.frame.msg.currentTarget)
        m.frame.msg.caller src dst amount).isSome := by
  have hb : (ozSpendWorld m.ctx.crypto Layout.oz m.world m.frame.msg.currentTarget src
      m.frame.msg.caller amount).sload m.frame.msg.currentTarget
        (balanceSlot m.ctx.crypto Layout.oz src) =
      m.world.sload m.frame.msg.currentTarget (balanceSlot m.ctx.crypto Layout.oz src) := by
    simp only [ozSpendWorld]
    split
    · rfl
    · rw [allowanceWorld, World.sload_sstore_ne_key _ _ _ (bal_ne_allow hR hs hs hc)]
  unfold TransferFromCond
  rw [hb, ← actorView_allowance (w := m.world) (token := m.frame.msg.currentTarget) hs hc,
    ← actorView_balanceOf (w := m.world) (token := m.frame.msg.currentTarget) hs]
  generalize actorView m.ctx.crypto Act m.world m.frame.msg.currentTarget = s
  unfold Model.ozTransferFrom Model.ozSpend
  by_cases hmax : s.allowance src m.frame.msg.caller = maxWord
  · simp only [hmax, true_or, true_and, ↓reduceIte, Option.bind_some]
    unfold Model.ozTransfer Model.transfer
    by_cases hs : src = 0 <;> by_cases hd : dst = 0 <;>
      simp only [hs, hd, ↓reduceIte, Option.isSome_none, ne_eq, not_true_eq_false,
        not_false_eq_true, false_and, and_false, true_and] <;> simp
  · simp only [hmax, false_or, ↓reduceIte]
    by_cases hle : amount.toNat ≤ (s.allowance src m.frame.msg.caller).toNat
    · unfold Model.ozApprove Model.ozTransfer Model.transfer
      by_cases hs : src = 0 <;> by_cases hc : m.frame.msg.caller = 0 <;>
        by_cases hd : dst = 0 <;>
        simp only [hs, hd, hc, hle, ↓reduceIte, Option.bind_some,
          Option.isSome_none, ne_eq, not_true_eq_false, not_false_eq_true, false_and, and_false,
          true_and, Model.approve, State.setAllowance] <;> simp
    · simp [hle]

/-- `Variant.oz`'s invariant is `Token.WF` of the ledger. -/
theorem wf_toToken {s : VState Address} (h : (Variant.oz : Variant Address).WF s)
    (hf : s.frozen = 0) : s.toToken.WF := by
  simp only [Variant.WF, Variant.oz, Variant.standard, Bool.false_eq_true, ↓reduceIte,
    reduceCtorEq] at h
  rw [hf] at h
  simp only [total, Finsupp.sum_zero_index, Nat.add_zero] at h
  exact h

end Verified.OpenZeppelin.ERC20.Spec
