import Examples.OpenZeppelin.ERC20.Transfer
import Examples.OpenZeppelin.ERC20.Approve
import Examples.OpenZeppelin.ERC20.TransferFrom
import Examples.OpenZeppelin.ERC20.MintBurn
import Examples.OpenZeppelin.ERC20.Views
import QEDefi.ERC20.RepOz

/-!
# `OzAsset` refines the `Token.oz*` ledger operations

The deployed OpenZeppelin `ERC20Mock`, called at top level, against the `ℕ` ledger model of
`QEDefi.ERC20` (`Token.ozTransfer`, `ozApprove`, `ozTransferFrom`, `ozMint`, `ozBurn`; these are
`Variant.oz`'s operations by `Variant.oz_transfer` etc.): when the token's storage represents a
well-formed ledger `t` (`Rep`, `Token.WF`), the call succeeds exactly when the model does, the
new storage represents the model's result (allowances in unwritten slots, `RepOn`), other
accounts are untouched, and a revert leaves the world unchanged. Each theorem composes the
bytecode refinement (`*_spec`, against `ERC20.Model.oz*`) with `QEDefi.ERC20.RepOz`.
-/

namespace Examples.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Solidity EvmLogic.Solidity.ERC20 EvmLean.Interpreter
open QEDefi.ERC20 QEDefi.Math Examples.OpenZeppelin.Contracts

variable {ctx : Context} {w : World} {tr : TransientStorage} {token caller : Address}
  {amount : Word} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}
  {t : Token Address}

/-- The storage view of the token, `Layout.oz`. -/
abbrev ozView (crypto : Crypto) (w : World) (token : Address) : ERC20.State :=
  view crypto Layout.oz w token

/-- **`transfer` refines `Token.ozTransfer`.** -/
theorem transfer_refines {dst : Address}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 100000 ≤ gas)
    (hc : BalanceSlotOk ctx.crypto Layout.oz caller) (hd : BalanceSlotOk ctx.crypto Layout.oz dst)
    (fuel : Nat) (hfuel : 400 ≤ fuel) (hr : Rep (ozView ctx.crypto w token) t) (hw : t.WF) :
    ∃ r, processMessageCall fuel ctx w tr
        (transferCall token caller dst amount gas warmAddrs warmKeys) = .ok r ∧
      match t.ozTransfer caller dst amount.toNat with
      | some t' => r.success = true ∧ r.output = Bytes.ofWord 1 ∧
        RepOn (fun o sp => allowanceSlot ctx.crypto Layout.oz o sp ≠
            balanceSlot ctx.crypto Layout.oz caller ∧
          allowanceSlot ctx.crypto Layout.oz o sp ≠ balanceSlot ctx.crypto Layout.oz dst)
          (ozView ctx.crypto r.world token) t' ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨r, hrun, hpost⟩ := transfer_spec (w := w) (tr := tr) (amount := amount)
    (warmAddrs := warmAddrs) (warmKeys := warmKeys) hdeleg hpre hgas hc hd fuel hfuel
  refine ⟨r, hrun, ?_⟩
  have hiff := ozTransfer_isSome_iff hr caller dst amount
  split
  · rename_i t' ht
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [ht]))
    rw [hm] at hpost
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hpost
    exact ⟨h0, h1, RepOn.of_eq h2 h3 (fun o sp hp => h4 o sp hp.1 hp.2)
      (rep_ozTransfer hr hw hm ht), h5⟩
  · rename_i ht
    have hm : Model.ozTransfer (ozView ctx.crypto w token) caller dst amount = none := by
      simpa [ht] using hiff
    rw [hm] at hpost
    exact hpost

/-- **`approve` refines `Token.ozApprove`.** -/
theorem approve_refines {spender : Address}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 100000 ≤ gas)
    (ha : AllowanceSlotOk ctx.crypto Layout.oz caller spender)
    (fuel : Nat) (hfuel : 400 ≤ fuel) (hr : Rep (ozView ctx.crypto w token) t) :
    ∃ r, processMessageCall fuel ctx w tr
        (approveCall token caller spender amount gas warmAddrs warmKeys) = .ok r ∧
      match t.ozApprove caller spender amount.toNat with
      | some t' => r.success = true ∧ r.output = Bytes.ofWord 1 ∧
        RepOn (fun o sp => (o = caller ∧ sp = spender) ∨
            allowanceSlot ctx.crypto Layout.oz o sp ≠
              allowanceSlot ctx.crypto Layout.oz caller spender)
          (ozView ctx.crypto r.world token) t' ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨r, hrun, hpost⟩ := approve_spec (w := w) (tr := tr) (amount := amount)
    (warmAddrs := warmAddrs) (warmKeys := warmKeys) hdeleg hpre hgas ha fuel hfuel
  refine ⟨r, hrun, ?_⟩
  have hiff := ozApprove_isSome_iff (s := ozView ctx.crypto w token) (t := t) caller spender
    amount amount.toNat
  split
  · rename_i t' ht
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [ht]))
    rw [hm] at hpost
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hpost
    exact ⟨h0, h1, RepOn.of_eq h2 h3 h4 (rep_ozApprove hr rfl hm ht), h5⟩
  · rename_i ht
    have hm : Model.ozApprove (ozView ctx.crypto w token) caller spender amount = none := by
      simpa [ht] using hiff
    rw [hm] at hpost
    exact hpost

/-- **`transferFrom` refines `Token.ozTransferFrom`** (`caller` is the spender). -/
theorem transferFrom_refines {src dst : Address}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 100000 ≤ gas)
    (hs : BalanceSlotOk ctx.crypto Layout.oz src) (hd : BalanceSlotOk ctx.crypto Layout.oz dst)
    (ha : AllowanceSlotOk ctx.crypto Layout.oz src caller)
    (fuel : Nat) (hfuel : 600 ≤ fuel) (hr : Rep (ozView ctx.crypto w token) t) (hw : t.WF) :
    ∃ r, processMessageCall fuel ctx w tr
        (transferFromCall token caller src dst amount gas warmAddrs warmKeys) = .ok r ∧
      match t.ozTransferFrom caller src dst amount.toNat with
      | some t' => r.success = true ∧ r.output = Bytes.ofWord 1 ∧
        RepOn (fun o sp => allowanceSlot ctx.crypto Layout.oz o sp ≠
            balanceSlot ctx.crypto Layout.oz src ∧
          allowanceSlot ctx.crypto Layout.oz o sp ≠ balanceSlot ctx.crypto Layout.oz dst ∧
          ((o = src ∧ sp = caller) ∨
            allowanceSlot ctx.crypto Layout.oz o sp ≠ allowanceSlot ctx.crypto Layout.oz src caller))
          (ozView ctx.crypto r.world token) t' ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨r, hrun, hpost⟩ := transferFrom_spec (w := w) (tr := tr) (amount := amount)
    (warmAddrs := warmAddrs) (warmKeys := warmKeys) hdeleg hpre hgas hs hd ha fuel hfuel
  refine ⟨r, hrun, ?_⟩
  have hiff := ozTransferFrom_isSome_iff hr caller src dst amount
  split
  · rename_i t' ht
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [ht]))
    rw [hm] at hpost
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hpost
    exact ⟨h0, h1, RepOn.of_eq h2 h3 (fun o sp hp => h4 o sp hp.1 hp.2.1 hp.2.2)
      (rep_ozTransferFrom hr hw hm ht), h5⟩
  · rename_i ht
    have hm : Model.ozTransferFrom (ozView ctx.crypto w token) caller src dst amount = none := by
      simpa [ht] using hiff
    rw [hm] at hpost
    exact hpost

/-- **`mint` refines `Token.ozMint`** (any caller: `ERC20Mock.mint` is unrestricted). -/
theorem mint_refines {dst : Address}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 100000 ≤ gas)
    (hd : BalanceSlotOk ctx.crypto Layout.oz dst) (hk : SupplySlotOk ctx.crypto Layout.oz)
    (fuel : Nat) (hfuel : 400 ≤ fuel) (hr : Rep (ozView ctx.crypto w token) t) (hw : t.WF) :
    ∃ r, processMessageCall fuel ctx w tr
        (mintCall token caller dst amount gas warmAddrs warmKeys) = .ok r ∧
      match t.ozMint dst amount.toNat with
      | some t' => r.success = true ∧ r.output = .empty ∧
        RepOn (fun o sp => allowanceSlot ctx.crypto Layout.oz o sp ≠ Layout.oz.totalSupply ∧
          allowanceSlot ctx.crypto Layout.oz o sp ≠ balanceSlot ctx.crypto Layout.oz dst)
          (ozView ctx.crypto r.world token) t' ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨r, hrun, hpost⟩ := mint_spec (w := w) (tr := tr) (amount := amount) (caller := caller)
    (warmAddrs := warmAddrs) (warmKeys := warmKeys) hdeleg hpre hgas hd hk fuel hfuel
  refine ⟨r, hrun, ?_⟩
  have hiff := ozMint_isSome_iff hr dst amount
  split
  · rename_i t' ht
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [ht]))
    rw [hm] at hpost
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hpost
    exact ⟨h0, h1, RepOn.of_eq h2 h3 (fun o sp hp => h4 o sp hp.1 hp.2)
      (rep_ozMint hr hw hm ht), h5⟩
  · rename_i ht
    have hm : Model.ozMint (ozView ctx.crypto w token) dst amount = none := by
      simpa [ht] using hiff
    rw [hm] at hpost
    exact hpost

/-- **`burn` refines `Token.ozBurn`** (any caller: `ERC20Mock.burn` is unrestricted). -/
theorem burn_refines {src : Address}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 100000 ≤ gas)
    (hs : BalanceSlotOk ctx.crypto Layout.oz src) (hk : SupplySlotOk ctx.crypto Layout.oz)
    (fuel : Nat) (hfuel : 400 ≤ fuel) (hr : Rep (ozView ctx.crypto w token) t) (hw : t.WF) :
    ∃ r, processMessageCall fuel ctx w tr
        (burnCall token caller src amount gas warmAddrs warmKeys) = .ok r ∧
      match t.ozBurn src amount.toNat with
      | some t' => r.success = true ∧ r.output = .empty ∧
        RepOn (fun o sp => allowanceSlot ctx.crypto Layout.oz o sp ≠ Layout.oz.totalSupply ∧
          allowanceSlot ctx.crypto Layout.oz o sp ≠ balanceSlot ctx.crypto Layout.oz src)
          (ozView ctx.crypto r.world token) t' ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨r, hrun, hpost⟩ := burn_spec (w := w) (tr := tr) (amount := amount) (caller := caller)
    (warmAddrs := warmAddrs) (warmKeys := warmKeys) hdeleg hpre hgas hs hk fuel hfuel
  refine ⟨r, hrun, ?_⟩
  have hiff := ozBurn_isSome_iff hr src amount
  split
  · rename_i t' ht
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [ht]))
    rw [hm] at hpost
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hpost
    exact ⟨h0, h1, RepOn.of_eq h2 h3 (fun o sp hp => h4 o sp hp.1 hp.2)
      (rep_ozBurn hr hw hm ht), h5⟩
  · rename_i ht
    have hm : Model.ozBurn (ozView ctx.crypto w token) src amount = none := by
      simpa [ht] using hiff
    rw [hm] at hpost
    exact hpost

/-! ## Views against the ledger -/

/-- **`totalSupply()`** returns the ledger's supply. -/
theorem totalSupply_refines (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 10000 ≤ gas) (fuel : Nat)
    (hfuel : 200 ≤ fuel) {P : Address → Address → Prop}
    (hr : RepOn P (ozView ctx.crypto w token) t) :
    ∃ r, processMessageCall fuel ctx w tr
        (callMsg OzAsset.runtimeCode token caller totalSupplyCalldata gas warmAddrs warmKeys) =
          .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord (BitVec.ofNat 256 t.totalSupply) ∧
      r.world = w := by
  obtain ⟨r, hrun, h1, h2, h3⟩ := totalSupply_spec (w := w) (tr := tr) (caller := caller)
    (warmAddrs := warmAddrs) (warmKeys := warmKeys) hdeleg hpre hgas fuel hfuel
  exact ⟨r, hrun, h1, by rw [h2, ← hr.totalSupply, ofNat_toNat_word], h3⟩

/-- **`balanceOf(a)`** returns the ledger's balance of `a`. -/
theorem balanceOf_refines (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 10000 ≤ gas) (a : Address)
    (fuel : Nat) (hfuel : 200 ≤ fuel) {P : Address → Address → Prop}
    (hr : RepOn P (ozView ctx.crypto w token) t) :
    ∃ r, processMessageCall fuel ctx w tr
        (callMsg OzAsset.runtimeCode token caller (balanceOfCalldata a) gas warmAddrs warmKeys) =
          .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord (BitVec.ofNat 256 (t.balanceOf a)) ∧
      r.world = w := by
  obtain ⟨r, hrun, h1, h2, h3⟩ := balanceOf_spec (w := w) (tr := tr) (caller := caller)
    (warmAddrs := warmAddrs) (warmKeys := warmKeys) hdeleg hpre hgas a fuel hfuel
  exact ⟨r, hrun, h1, by rw [h2, ← hr.balanceOf a, ofNat_toNat_word], h3⟩

/-- **`allowance(o, sp)`** returns the ledger's allowance, for a represented entry. -/
theorem allowance_refines (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 10000 ≤ gas) (o sp : Address)
    (fuel : Nat) (hfuel : 200 ≤ fuel) {P : Address → Address → Prop}
    (hr : RepOn P (ozView ctx.crypto w token) t) (hp : P o sp) :
    ∃ r, processMessageCall fuel ctx w tr
        (callMsg OzAsset.runtimeCode token caller (allowanceCalldata o sp) gas warmAddrs
          warmKeys) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord (BitVec.ofNat 256 (t.allowance o sp)) ∧
      r.world = w := by
  obtain ⟨r, hrun, h1, h2, h3⟩ := allowance_spec (w := w) (tr := tr) (caller := caller)
    (warmAddrs := warmAddrs) (warmKeys := warmKeys) hdeleg hpre hgas o sp fuel hfuel
  exact ⟨r, hrun, h1, by rw [h2, ← hr.allowance o sp hp, ofNat_toNat_word], h3⟩

end Examples.OpenZeppelin.ERC20
