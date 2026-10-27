module

public import QEDefi.ERC20.Spec.VariantLaws

/-!
# AMPL (`UFragments`) as a token model

`amplModel` is `Variant.ampl` with the events of `UFragments`
(`contracts/mainnet/AMPL/source/contracts/UFragments.sol`, solc 0.7.6, behind its proxy), on a
state that also holds the `Ownable` owner (`AState`), with the owner's and the monetary
policy's entry points as operations (`AmplOp`).

**Calls** are `Variant.ampl`'s, on the `VState` part (the owner is untouched):

* `transfer(dst, v)` logs `Transfer(caller, dst, v)` with the fragment amount `v` (not gons);
* `transferFrom(src, dst, v)` logs `Transfer(src, dst, v)` (spending the allowance logs no
  `Approval`);
* `approve(sp, v)` logs `Approval(caller, sp, v)`;
* `permit(o, sp, v, …)` logs `Approval(o, sp, v)`;
* an unknown selector reverts (no fallback in `UFragments`).

**Operations** (`AmplOp`): `Variant.ampl`'s (`transferAll`, `transferAllFrom`,
`adjustAllowance`, …), and the privileged entry points as the code runs them:

* `setMonetaryPolicy(p)` by the owner sets the monetary policy (`admin`) to `p`;
* `transferOwnership(o)` by the owner, `o ≠ 0`, sets the owner to `o`;
  `renounceOwnership()` by the owner sets it to `0`;
* `rebase(epoch, Δ)` by the monetary policy (`rebaseOp`): `Δ = 0` changes nothing; otherwise the
  supply moves by the signed `Δ` with `SafeMath` (failing below `0`, above `2²⁵⁶ − 1`, and for
  `Δ = −2²⁵⁵`, whose `SafeMathInt.abs` reverts), is capped at `MAX_SUPPLY = 2¹²⁸ − 1`, and
  `gonsPerFragment` becomes `TOTAL_GONS / supply` (failing at supply `0`). Balances (gons) are
  untouched: every `balanceOf` changes. `rebase` logs no `Transfer`.

`Variant.ampl`'s own `rebase` (`Variant.Op.rebase`, to an absolute supply) is still an
operation (`.base`), but no entry point decodes to it.

**Laws** (`amplModel_laws`): those of `Variant.ampl` (`ampl_laws`), every call law transported
through the `VState` part (`amplModel_call`); `WFInvariant` also for the new operations (the
owner's leave the `VState` part's invariant, `rebase` keeps `0 < supply ≤ MAX_SUPPLY` and
`scale = TOTAL_GONS / supply`).
-/
@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.AMPL

open QEDefi.ERC20 QEDefi.Math QEDefi.ERC20.Spec.VariantLaws

variable {A : Type} [DecidableEq A] [Zero A]

/-- The events of `UFragments` for a successful call by `caller`. -/
def amplEvents (_s : VState A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => [.transfer caller dst v]
  | .transferFrom src dst v => [.transfer src dst v]
  | .approve sp v => [.approval caller sp v]
  | .other _ => []
  | .permit o sp v _ _ => [.approval o sp v]

/-- **AMPL's state**: `Variant.ampl`'s (`admin` the monetary policy) and the `Ownable` owner. -/
structure AState (A : Type) extends VState A where
  /-- `Ownable._owner`. -/
  owner : A

/-- `allowance[o][sp] := v`. -/
def AState.setAllowance (s : AState A) (o sp : A) (v : ℕ) : AState A :=
  { s with toVState := s.toVState.setAllowance o sp v }

/-- A result of the `VState` part, the owner kept. -/
def liftR (s : AState A) : Result (VState A) → Result (AState A)
  | .ok v r => .ok { s with toVState := v } r
  | .halt h => .halt h

/-- AMPL's other entry points. -/
inductive AmplOp (A : Type) where
  /-- An operation of `Variant.ampl`. -/
  | base (o : Variant.Op A)
  /-- `setMonetaryPolicy(p)` by `caller`. -/
  | setMonetaryPolicy (caller p : A)
  /-- `transferOwnership(o)` by `caller`. -/
  | transferOwnership (caller o : A)
  /-- `renounceOwnership()` by `caller`. -/
  | renounceOwnership (caller : A)
  /-- `rebase(epoch, Δ)` by `caller`, with the signed supply delta `Δ`. -/
  | rebase (caller : A) (delta : ℤ)

/-- `rebase`'s new supply before the cap: `S ± |Δ|` with `SafeMath`, failing for
`Δ = −2²⁵⁵` (`SafeMathInt.abs`). -/
def rebaseSupply (S : ℕ) (d : ℤ) : Option ℕ :=
  if d < 0 then
    if d = -2 ^ 255 then none else if S < d.natAbs then none else some (S - d.natAbs)
  else if MAX < S + d.toNat then none else some (S + d.toNat)

/-- **`rebase(epoch, Δ)` by `caller`**, as `UFragments` computes it. -/
def rebaseOp (s : AState A) (c : A) (d : ℤ) : Option (AState A) :=
  if c ≠ s.admin then none
  else if d = 0 then some s
  else match rebaseSupply s.supply d with
    | none => none
    | some S1 =>
      if min S1 (Variant.ampl : Variant A).maxSupply = 0 then none
      else some { s with
        supply := min S1 (Variant.ampl : Variant A).maxSupply
        scale := Variant.amplTotalGons / min S1 (Variant.ampl : Variant A).maxSupply }

/-- The operations. -/
def amplOp (s : AState A) : AmplOp A → Option (AState A)
  | .base o => ((Variant.ampl : Variant A).stepOp s.toVState o).map fun v => { s with toVState := v }
  | .setMonetaryPolicy c p => if c = s.owner then some { s with admin := p } else none
  | .transferOwnership c o => if c = s.owner ∧ o ≠ 0 then some { s with owner := o } else none
  | .renounceOwnership c => if c = s.owner then some { s with owner := 0 } else none
  | .rebase c d => rebaseOp s c d

/-- **AMPL** (`UFragments`). -/
def amplModel : TokenModel (AState A) A (AmplOp A) where
  balanceOf s := (Variant.ampl : Variant A).balanceOf s.toVState
  totalSupply s := (Variant.ampl : Variant A).totalSupply s.toVState
  allowance s := (Variant.ampl : Variant A).allowanceOf s.toVState
  call s caller c := liftR s ((Variant.ampl : Variant A).call s.toVState caller c)
  events s := amplEvents s.toVState
  op := amplOp
  wf s := (Variant.ampl : Variant A).WF s.toVState

/-- The calls are `Variant.ampl`'s on the `VState` part. -/
theorem amplModel_call (s : AState A) (caller : A) (c : Call A) :
    amplModel.call s caller c = liftR s ((Variant.ampl : Variant A).call s.toVState caller c) :=
  rfl

/-! ## The laws, through the `VState` part -/

/-- The `Variant.ampl` model the calls go through. -/
abbrev M0 : TokenModel (VState A) A (Variant.Op A) := (Variant.ampl : Variant A).model amplEvents

theorem liftR_ok {s s' : AState A} {r : Result (VState A)} {d : RetData}
    (h : liftR s r = .ok s' d) : ∃ v, r = .ok v d ∧ s' = { s with toVState := v } := by
  cases r with
  | ok v d' => cases h; exact ⟨v, rfl, rfl⟩
  | halt _ => cases h

theorem liftR_halt {s : AState A} {r : Result (VState A)} {k : Halt}
    (h : liftR s r = .halt k) : r = .halt k := by
  cases r with
  | ok _ _ => cases h
  | halt _ => cases h; rfl

theorem call_ok {s s' : AState A} {caller : A} {c : Call A} {d : RetData}
    (h : amplModel.call s caller c = .ok s' d) :
    M0.call s.toVState caller c = .ok s'.toVState d ∧ s' = { s with toVState := s'.toVState } := by
  obtain ⟨v, hv, rfl⟩ := liftR_ok h
  exact ⟨hv, rfl⟩

/-- The state `v` with the owner `0`. -/
def ext (v : VState A) : AState A := { toVState := v, owner := 0 }

theorem call_ext {v v' : VState A} {caller : A} {c : Call A} {d : RetData}
    (h : M0.call v caller c = .ok v' d) :
    amplModel.call (ext v) caller c = .ok (ext v') d := by
  change liftR (ext v) ((Variant.ampl : Variant A).call v caller c) = _
  rw [show (Variant.ampl : Variant A).call v caller c = .ok v' d from h]
  rfl

theorem returnsTrue [Nontrivial A] : (amplModel : TokenModel (AState A) A _).ReturnsTrue := fun _ c x _ r hb h =>
  (ampl_laws (A := A) (ev := amplEvents)).1 _ c x _ r hb (call_ok h).1

theorem noFalseReturn [Nontrivial A] : (amplModel : TokenModel (AState A) A _).NoFalseReturn := fun _ c x _ h =>
  (ampl_laws (A := A) (ev := amplEvents)).2.1 _ c x _ (call_ok h).1

theorem revertsOnly [Nontrivial A] : (amplModel : TokenModel (AState A) A _).RevertsOnly := fun _ c x k h =>
  (ampl_laws (A := A) (ev := amplEvents)).2.2.1 _ c x k (liftR_halt h)

theorem exactMoves_of {P : VState A → Prop} (h : (M0 : TokenModel (VState A) A _).ExactMoves P) :
    (amplModel : TokenModel (AState A) A _).ExactMoves (fun s => P s.toVState) :=
  ⟨fun _ c d v _ r hP hcd hc hr => h.1 _ c d v _ r hP hcd (call_ok hc).1 hr,
    fun _ c a d v _ r hP had hc hr => h.2 _ c a d v _ r hP had (call_ok hc).1 hr⟩

theorem not_exactMoves_of {P : VState A → Prop}
    (h : ¬ (M0 : TokenModel (VState A) A _).ExactMoves P) :
    ¬ (amplModel : TokenModel (AState A) A _).ExactMoves (fun s => P s.toVState) := by
  intro hE
  apply h
  refine ⟨fun v c d x v' r hP hcd hc hr => ?_, fun v c a d x v' r hP had hc hr => ?_⟩
  · exact hE.1 (ext v) c d x (ext v') r hP hcd (call_ext hc) hr
  · exact hE.2 (ext v) c a d x (ext v') r hP had (call_ext hc) hr

theorem supplyFixed [Nontrivial A] : (amplModel : TokenModel (AState A) A _).SupplyFixed :=
  fun _ c x _ r hb h => (ampl_laws (A := A) (ev := amplEvents)).2.2.2.2.2.2.1 _ c x _ r hb
    (call_ok h).1

theorem debitAuth [Nontrivial A] : (amplModel : TokenModel (AState A) A _).DebitAuth :=
  fun _ c x _ r o h ho hlt => (ampl_laws (A := A) (ev := amplEvents)).2.2.2.2.2.2.2.1 _ c x _ r o
    (call_ok h).1 ho hlt

theorem not_allowanceAuth [Nontrivial A] :
    ¬ (amplModel : TokenModel (AState A) A _).AllowanceAuth := by
  intro hA
  apply (ampl_laws (A := A) (ev := amplEvents)).2.2.2.2.2.2.2.2.1
  intro v c x v' r o sp h ho hne
  exact hA (ext v) c x (ext v') r o sp (call_ext h) ho hne

/-- `rebase` keeps the invariant. -/
theorem rebaseOp_wf {s s' : AState A} {c : A} {d : ℤ}
    (hw : (Variant.ampl : Variant A).WF s.toVState) (h : rebaseOp s c d = some s') :
    (Variant.ampl : Variant A).WF s'.toVState := by
  unfold rebaseOp at h
  split at h
  · cases h
  split at h
  · cases h; exact hw
  split at h
  · cases h
  rename_i S1 _
  split at h
  · cases h
  rename_i hz
  cases h
  have hr : (Variant.ampl : Variant A).rebasing = true := rfl
  unfold Variant.WF at hw ⊢
  simp only [hr, ↓reduceIte] at hw ⊢
  obtain ⟨htot, -, -, -⟩ := hw
  refine ⟨htot, Nat.pos_of_ne_zero hz, min_le_right _ _, rfl⟩

theorem wfInvariant [Nontrivial A] : (amplModel : TokenModel (AState A) A _).WFInvariant := by
  refine ⟨fun _ c x _ r hw h => ?_, fun s e s' hw h => ?_⟩
  · exact (ampl_laws (A := A) (ev := amplEvents)).2.2.2.2.2.2.2.2.2.1 _ c x _ r hw (call_ok h).1
  · cases e with
    | base o =>
      simp only [amplModel, amplOp, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      exact (ampl_laws (A := A) (ev := amplEvents)).2.2.2.2.2.2.2.2.2.2 _ o v hw hv
    | setMonetaryPolicy c p =>
      simp only [amplModel, amplOp] at h
      split at h
      · cases h; exact hw
      · cases h
    | transferOwnership c o =>
      simp only [amplModel, amplOp] at h
      split at h
      · cases h; exact hw
      · cases h
    | renounceOwnership c =>
      simp only [amplModel, amplOp] at h
      split at h
      · cases h; exact hw
      · cases h
    | rebase c d => exact rebaseOp_wf hw h

/-- **The laws of AMPL**: those of `Variant.ampl` (`ampl_laws`): every law but `AllowanceAuth`
(the zero owner's `permit` with a failed recovery) and `ExactMoves` in arbitrary states (at
scale `0`, not well formed); the invariant is kept by every call and every operation, the
owner's and `rebase` included. -/
theorem amplModel_laws [Nontrivial A] :
    (amplModel : TokenModel (AState A) A _).ReturnsTrue ∧
      (amplModel : TokenModel (AState A) A _).NoFalseReturn ∧
      (amplModel : TokenModel (AState A) A _).RevertsOnly ∧
      (amplModel : TokenModel (AState A) A _).ExactMoves (fun s => 0 < s.scale) ∧
      (amplModel : TokenModel (AState A) A _).ExactMoves (amplModel : TokenModel (AState A) A _).wf ∧
      ¬ (amplModel : TokenModel (AState A) A _).ExactMoves (fun _ => True) ∧
      (amplModel : TokenModel (AState A) A _).SupplyFixed ∧
      (amplModel : TokenModel (AState A) A _).DebitAuth ∧
      ¬ (amplModel : TokenModel (AState A) A _).AllowanceAuth ∧
      (amplModel : TokenModel (AState A) A _).WFInvariant := by
  have hl := ampl_laws (A := A) (ev := amplEvents)
  exact ⟨returnsTrue, noFalseReturn, revertsOnly,
    exactMoves_of (P := fun v => 0 < v.scale) hl.2.2.2.1,
    exactMoves_of (P := (Variant.ampl : Variant A).WF) hl.2.2.2.2.1,
    not_exactMoves_of (P := fun _ => True) hl.2.2.2.2.2.1,
    supplyFixed, debitAuth, not_allowanceAuth, wfInvariant⟩

end QEDefi.ERC20.Spec.AMPL
