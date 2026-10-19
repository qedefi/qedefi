import EvmLeanSpecs.Refinement.SharesModel
import EvmLeanSpecs.Refinement.SharesTransfer
import EvmLeanSpecs.Refinement.SharesApprove
import EvmLeanSpecs.Refinement.SharesTransferFromRevert
import EvmLeanSpecs.Refinement.SharesViews

/-!
# The vault's share token refines the `Token` model

End-to-end refinement theorems for the share-token functions of the **compiled Solmate vault**
(`Contracts.SolmateVault`, `MockERC4626`, solc 0.8.28) deployed with **arbitrary immutables**
`i` (any asset, chain id, domain separator, decimals; `SharesCode.code i`), against the share
ledger operations of the abstract model (`EvmLeanSpecs.Vault.Token`, used as
`Solmate.State.shares` by `Solmate.step`'s `.transfer`, `.transferFrom`, `.approve`).

Each theorem is about `processMessageCall` of a top-level call (any `Crypto`, context without
EIP-7702 authorizations or before Prague, world, transient storage, caller, arguments, warm
sets, enough gas and fuel) from a world whose share storage, read through `Erc20.view`
(Solmate layout), represents a ledger `t` (`Rep`); state-changing functions also need
`t.WF` (balances sum to `totalSupply ≤ MAX`, the model's invariant `Solmate.Inv`), which makes
the unchecked word additions exact. Then:

* **success** (the model op returns `some t'`): the call succeeds, returns ABI `true`, the
  world is the exact one the bytecode produces (`transferWorld`, …), its share view represents
  `t'` (`RepOn`: `totalSupply` and every balance; allowances for every entry whose slot is not
  a written slot — nested-mapping frames are only available pointwise), and every other
  storage slot of every account is unchanged;
* **revert** (`none`): the call reverts and the world is unchanged.

Hypotheses on the hash are explicit and local: `BalanceSlotOk` for the balance entries
written and `AllowanceSlotOk` for the allowance entry written (`EvmLeanProofs.Solidity.Keccak`).

The views (`totalSupply`, `balanceOf`, `allowance`, `decimals`) return the represented values
and leave the world unchanged. `name()` / `symbol()` are not covered (string copies with
`MCOPY`, for which the symbolic executor has no step lemma yet).
-/

namespace EvmLeanSpecs.Refinement.Shares

open EvmLean Interpreter Solidity Contracts Erc20 EvmLeanSpecs.Vault

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller : Address} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

/-! ## Storage frames -/

/-- An `SSTORE` changes one slot of one account. -/
theorem sload_sstore_frame {w : World} {a b : Address} {key k v : Word} (h : b ≠ a ∨ k ≠ key) :
    (w.sstore a key v).sload b k = w.sload b k := by
  rw [World.sload_sstore]
  have : ¬ (b = a ∧ k = key) := by rintro ⟨rfl, rfl⟩; rcases h with h | h <;> exact h rfl
  simp [this]

/-- `transfer` writes only the two balance slots. -/
theorem sload_transferWorld {crypto : Crypto} {w : World} {token src dst b : Address}
    {amount k : Word}
    (h : b ≠ token ∨ (k ≠ balanceSlot crypto Layout.solmate src ∧
      k ≠ balanceSlot crypto Layout.solmate dst)) :
    (transferWorld crypto w token src dst amount).sload b k = w.sload b k := by
  simp only [transferWorld, Examples.SolmateAssetTransfer.transferWorld]
  rw [sload_sstore_frame (by rcases h with h | h; exact .inl h; exact .inr h.2),
    sload_sstore_frame (by rcases h with h | h; exact .inl h; exact .inr h.1)]

/-- The allowance step writes only the allowance slot. -/
theorem sload_spendWorld {crypto : Crypto} {w : World} {token o sp b : Address} {amount k : Word}
    (h : b ≠ token ∨ k ≠ allowanceSlot crypto Layout.solmate o sp) :
    (spendWorld crypto w token o sp amount).sload b k = w.sload b k := by
  simp only [spendWorld]
  split
  · rfl
  · exact sload_sstore_frame h

/-! ## `transfer` -/

set_option maxHeartbeats 1000000 in
/-- **`transfer(dst, amount)` refines `Token.transfer`.** Needs `BalanceSlotOk` for `caller`
and `dst` (a self-transfer is allowed). -/
theorem transfer_refines {dst : Address} {amount : Word}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false) (hgas : 100000 ≤ gas)
    (hc : BalanceSlotOk ctx.crypto Layout.solmate caller)
    (hdst : BalanceSlotOk ctx.crypto Layout.solmate dst)
    {t : Token Address} (hr : Rep (view ctx.crypto Layout.solmate w vault) t) (hw : t.WF)
    (fuel : Nat) (hfuel : 400 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (vaultCall i vault caller (transferData dst amount) gas warmAddrs warmKeys) = .ok r ∧
      match t.transfer caller dst amount.toNat with
      | some t' =>
        r.success = true ∧ r.output = Bytes.ofWord 1 ∧
        r.world = transferWorld ctx.crypto w vault caller dst amount ∧
        RepOn (fun o sp => allowanceSlot ctx.crypto Layout.solmate o sp ≠
              balanceSlot ctx.crypto Layout.solmate caller ∧
            allowanceSlot ctx.crypto Layout.solmate o sp ≠ balanceSlot ctx.crypto Layout.solmate dst)
          (view ctx.crypto Layout.solmate r.world vault) t' ∧
        (∀ b k, b ≠ vault ∨ (k ≠ balanceSlot ctx.crypto Layout.solmate caller ∧
            k ≠ balanceSlot ctx.crypto Layout.solmate dst) → r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 400 := ⟨fuel - 400, by omega⟩
  rw [processMessageCall_vaultCall hdeleg hpre]
  split
  · rename_i t' hT
    have hv := (Token.transfer_eq_some.1 hT).1
    have hbal : amount.toNat ≤ ((view ctx.crypto Layout.solmate w vault).balanceOf caller).toNat := by
      rw [hr.balanceOf caller]; exact hv
    obtain ⟨r, hrun, hs, ho, hwld⟩ := transfer_ok (i := i) (tr := tr) (dst := dst)
      (warmAddrs := warmAddrs) (warmKeys := warmKeys) hgas hbal k
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1
      ((transfer_isSome_iff hr caller dst amount).2 (by simp [hT]))
    obtain ⟨h1, h2, h3, -⟩ := Examples.SolmateAssetTransfer.view_transferWorld hc hdst hm
    refine ⟨r, hrun, hs, ho, hwld, ?_, fun b k' hk => by rw [hwld]; exact sload_transferWorld hk⟩
    rw [hwld]
    exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1 hp.2) (rep_transfer hr hw hm hT)
  · rename_i hT
    have hlt : ((view ctx.crypto Layout.solmate w vault).balanceOf caller).toNat < amount.toNat := by
      rw [hr.balanceOf caller]
      unfold Token.transfer at hT
      split at hT
      · assumption
      · cases hT
    exact transfer_revert hgas hlt k

/-! ## `approve` -/

set_option maxHeartbeats 1000000 in
/-- **`approve(spender, amount)` refines `Token.approve`.** Needs `AllowanceSlotOk` for the
written entry `allowance[caller][spender]`. -/
theorem approve_refines {spender : Address} {amount : Word}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false) (hgas : 100000 ≤ gas)
    (ha : AllowanceSlotOk ctx.crypto Layout.solmate caller spender)
    {t : Token Address} (hr : Rep (view ctx.crypto Layout.solmate w vault) t)
    (fuel : Nat) (hfuel : 300 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (vaultCall i vault caller (approveData spender amount) gas warmAddrs warmKeys) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = approveWorld ctx.crypto w vault caller spender amount ∧
      RepOn (fun o sp => (o = caller ∧ sp = spender) ∨
          allowanceSlot ctx.crypto Layout.solmate o sp ≠
            allowanceSlot ctx.crypto Layout.solmate caller spender)
        (view ctx.crypto Layout.solmate r.world vault) (t.approve caller spender amount.toNat) ∧
      (∀ b k, b ≠ vault ∨ k ≠ allowanceSlot ctx.crypto Layout.solmate caller spender →
        r.world.sload b k = w.sload b k) := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 300 := ⟨fuel - 300, by omega⟩
  rw [processMessageCall_vaultCall hdeleg hpre]
  obtain ⟨r, hrun, hs, ho, hwld⟩ := approve_ok (i := i) (tr := tr) (spender := spender)
    (amount := amount) (warmAddrs := warmAddrs) (warmKeys := warmKeys) (vault := vault)
    (caller := caller) (w := w) (ctx := ctx) hgas k
  obtain ⟨h1, h2, h3, -⟩ := view_approveWorld (w := w) (token := vault) (amount := amount) ha
  refine ⟨r, hrun, hs, ho, hwld, ?_, fun b k' hk => by rw [hwld]; exact sload_sstore_frame hk⟩
  rw [hwld]
  exact RepOn.of_eq h1 h2 h3 (rep_approve hr caller spender amount)

/-! ## `transferFrom` -/

/-- `Model.spend` keeps the balances. -/
theorem Model_spend_balanceOf {s s₁ : Erc20.State} {o sp : Address} {amount : Word}
    (h : Erc20.Model.spend s o sp amount = some s₁) : s₁.balanceOf = s.balanceOf := by
  unfold Erc20.Model.spend at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

/-- The allowance condition of `Token.spend`, through `Rep`. -/
theorem allowance_cond_of_spend {s : Erc20.State} {t t₁ : Token Address} (hr : Rep s t)
    {o sp : Address} {amount : Word} (h : t.spend o sp amount.toNat = some t₁) :
    s.allowance o sp = maxWord ∨ amount.toNat ≤ (s.allowance o sp).toNat := by
  rw [eq_maxWord_iff, hr.allowance o sp trivial]
  unfold Token.spend at h
  split at h
  · exact .inl ‹_›
  · split at h
    · cases h
    · exact .inr (by omega)

/-- The balance of `src` after the allowance step, through the abstraction. -/
theorem balance_spendWorld {crypto : Crypto} {w : World} {token src sp : Address} {amount : Word}
    (ha : AllowanceSlotOk crypto Layout.solmate src sp) {s₁ : Erc20.State}
    (hm : Erc20.Model.spend (view crypto Layout.solmate w token) src sp amount = some s₁) :
    (spendWorld crypto w token src sp amount).sload token (balanceSlot crypto Layout.solmate src) =
      (view crypto Layout.solmate w token).balanceOf src := by
  obtain ⟨-, e2, -, -⟩ := view_spendWorld (w := w) (token := token) ha hm
  have := congrFun e2 src
  rw [Model_spend_balanceOf hm] at this
  exact this

set_option maxHeartbeats 1000000 in
/-- **`transferFrom(src, dst, amount)` refines `Token.transferFrom`.** Needs `BalanceSlotOk` for
`src` and `dst` and `AllowanceSlotOk` for the spent entry `allowance[src][caller]`. -/
theorem transferFrom_refines {src dst : Address} {amount : Word}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false) (hgas : 100000 ≤ gas)
    (hs : BalanceSlotOk ctx.crypto Layout.solmate src)
    (hd : BalanceSlotOk ctx.crypto Layout.solmate dst)
    (ha : AllowanceSlotOk ctx.crypto Layout.solmate src caller)
    {t : Token Address} (hr : Rep (view ctx.crypto Layout.solmate w vault) t) (hw : t.WF)
    (fuel : Nat) (hfuel : 500 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (vaultCall i vault caller (transferFromData src dst amount) gas warmAddrs warmKeys) =
        .ok r ∧
      match t.transferFrom caller src dst amount.toNat with
      | some t' =>
        r.success = true ∧ r.output = Bytes.ofWord 1 ∧
        r.world = transferFromWorld ctx.crypto w vault caller src dst amount ∧
        RepOn (fun o sp => allowanceSlot ctx.crypto Layout.solmate o sp ≠
              balanceSlot ctx.crypto Layout.solmate src ∧
            allowanceSlot ctx.crypto Layout.solmate o sp ≠ balanceSlot ctx.crypto Layout.solmate dst ∧
            ((o = src ∧ sp = caller) ∨ allowanceSlot ctx.crypto Layout.solmate o sp ≠
              allowanceSlot ctx.crypto Layout.solmate src caller))
          (view ctx.crypto Layout.solmate r.world vault) t' ∧
        (∀ b k, b ≠ vault ∨ (k ≠ balanceSlot ctx.crypto Layout.solmate src ∧
            k ≠ balanceSlot ctx.crypto Layout.solmate dst ∧
            k ≠ allowanceSlot ctx.crypto Layout.solmate src caller) →
          r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 500 := ⟨fuel - 500, by omega⟩
  rw [processMessageCall_vaultCall hdeleg hpre]
  split
  · rename_i t' hT
    obtain ⟨t₁, hsp, htr⟩ := Option.bind_eq_some_iff.1 hT
    obtain ⟨s₁, hm₁⟩ := Option.isSome_iff_exists.1
      ((spend_isSome_iff hr src caller amount).2 (by simp [hsp]))
    have hal := allowance_cond_of_spend hr hsp
    have hbal : amount.toNat ≤ ((spendWorld ctx.crypto w vault src caller amount).sload vault
        (balanceSlot ctx.crypto Layout.solmate src)).toNat := by
      rw [balance_spendWorld ha hm₁, hr.balanceOf src, ← (Token.spend_eq_some hsp).1]
      exact (Token.transfer_eq_some.1 htr).1
    obtain ⟨r, hrun, hsu, ho, hwld⟩ := transferFrom_ok (i := i) (tr := tr) (dst := dst)
      (warmAddrs := warmAddrs) (warmKeys := warmKeys) hgas hal hbal k
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1
      ((transferFrom_isSome_iff hr caller src dst amount).2 (by simp [hT]))
    obtain ⟨h1, h2, h3, -⟩ := view_transferFromWorld hs hd ha hm
    refine ⟨r, hrun, hsu, ho, hwld, ?_, fun b k' hk => ?_⟩
    · rw [hwld]
      exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1 hp.2.1 hp.2.2)
        (rep_transferFrom hr hw hm hT)
    · rw [hwld, transferFromWorld,
        sload_transferWorld (by rcases hk with h | h; exact .inl h; exact .inr ⟨h.1, h.2.1⟩),
        sload_spendWorld (by rcases hk with h | h; exact .inl h; exact .inr h.2.2)]
  · rename_i hT
    cases hsp : t.spend src caller amount.toNat with
    | none =>
      -- the allowance is finite and too small
      unfold Token.spend at hsp
      have ha' := hr.allowance src caller trivial
      split at hsp
      · cases hsp
      · rename_i hmax
        split at hsp
        · rename_i hlt
          have hmax' : (view ctx.crypto Layout.solmate w vault).allowance src caller ≠ maxWord :=
            fun h => hmax (by rw [← ha', (eq_maxWord_iff _).1 h])
          have hlt' : ((view ctx.crypto Layout.solmate w vault).allowance src caller).toNat <
              amount.toNat := by rw [ha']; exact hlt
          exact transferFrom_revert_allowance hgas hmax' hlt' k
        · cases hsp
    | some t₁ =>
      have htr : t₁.transfer src dst amount.toNat = none := by
        unfold Token.transferFrom at hT
        rw [hsp] at hT
        simpa using hT
      obtain ⟨s₁, hm₁⟩ := Option.isSome_iff_exists.1
        ((spend_isSome_iff hr src caller amount).2 (by simp [hsp]))
      have hal := allowance_cond_of_spend hr hsp
      have hbal : ((spendWorld ctx.crypto w vault src caller amount).sload vault
          (balanceSlot ctx.crypto Layout.solmate src)).toNat < amount.toNat := by
        rw [balance_spendWorld ha hm₁, hr.balanceOf src, ← (Token.spend_eq_some hsp).1]
        unfold Token.transfer at htr
        split at htr
        · assumption
        · cases htr
      exact transferFrom_revert_balance hgas hal hbal k

/-! ## Views -/

set_option maxHeartbeats 1000000 in
/-- **`totalSupply()`** returns the represented `totalSupply`; the world is unchanged. -/
theorem totalSupply_refines {P : Address → Address → Prop}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false) (hgas : 10000 ≤ gas)
    {t : Token Address} (hr : RepOn P (view ctx.crypto Layout.solmate w vault) t)
    (fuel : Nat) (hfuel : 100 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (vaultCall i vault caller totalSupplyData gas warmAddrs warmKeys) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord (BitVec.ofNat 256 t.totalSupply) ∧
      r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 100 := ⟨fuel - 100, by omega⟩
  rw [processMessageCall_vaultCall hdeleg hpre]
  obtain ⟨r, h1, h2, h3, h4⟩ := totalSupply_ok (i := i) (tr := tr) (vault := vault)
    (caller := caller) (w := w) (ctx := ctx) (warmAddrs := warmAddrs) (warmKeys := warmKeys) hgas k
  refine ⟨r, h1, h2, ?_, h4⟩
  rw [h3, ← hr.totalSupply, BitVec.ofNat_toNat, BitVec.setWidth_eq]

set_option maxHeartbeats 1000000 in
/-- **`balanceOf(a)`** returns the represented balance; the world is unchanged. -/
theorem balanceOf_refines {P : Address → Address → Prop} {a : Address}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false) (hgas : 10000 ≤ gas)
    {t : Token Address} (hr : RepOn P (view ctx.crypto Layout.solmate w vault) t)
    (fuel : Nat) (hfuel : 200 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (vaultCall i vault caller (balanceOfData a) gas warmAddrs warmKeys) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord (BitVec.ofNat 256 (t.balanceOf a)) ∧
      r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 200 := ⟨fuel - 200, by omega⟩
  rw [processMessageCall_vaultCall hdeleg hpre]
  obtain ⟨r, h1, h2, h3, h4⟩ := balanceOf_ok (i := i) (tr := tr) (vault := vault) (a := a)
    (caller := caller) (w := w) (ctx := ctx) (warmAddrs := warmAddrs) (warmKeys := warmKeys) hgas k
  refine ⟨r, h1, h2, ?_, h4⟩
  rw [h3, ← hr.balanceOf a, BitVec.ofNat_toNat, BitVec.setWidth_eq]

set_option maxHeartbeats 1000000 in
/-- **`allowance(owner, spender)`** returns the represented allowance (for an entry covered by
the representation); the world is unchanged. -/
theorem allowance_refines {P : Address → Address → Prop} {owner spender : Address}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false) (hgas : 10000 ≤ gas)
    {t : Token Address} (hr : RepOn P (view ctx.crypto Layout.solmate w vault) t)
    (hP : P owner spender) (fuel : Nat) (hfuel : 200 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (vaultCall i vault caller (allowanceData owner spender) gas warmAddrs warmKeys) = .ok r ∧
      r.success = true ∧
      r.output = Bytes.ofWord (BitVec.ofNat 256 (t.allowance owner spender)) ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 200 := ⟨fuel - 200, by omega⟩
  rw [processMessageCall_vaultCall hdeleg hpre]
  obtain ⟨r, h1, h2, h3, h4⟩ := allowance_ok (i := i) (tr := tr) (vault := vault)
    (owner := owner) (spender := spender) (caller := caller) (w := w) (ctx := ctx)
    (warmAddrs := warmAddrs) (warmKeys := warmKeys) hgas k
  refine ⟨r, h1, h2, ?_, h4⟩
  rw [h3, ← hr.allowance owner spender hP, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Masking to `uint8` keeps a value below 256. -/
theorem and_255 {x : Word} (h : x.toNat < 256) : x &&& 255#256 = x := by
  apply BitVec.eq_of_toNat_eq
  have h255 : (255#256).toNat = 2 ^ 8 - 1 := by simp
  rw [BitVec.toNat_and, h255, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by simpa using h)]

set_option maxHeartbeats 1000000 in
/-- **`decimals()`** returns the `decimals` immutable (a `uint8`); the world is unchanged. -/
theorem decimals_refines (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false) (hgas : 10000 ≤ gas)
    (hdec : i.decimals.toNat < 256) (fuel : Nat) (hfuel : 100 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (vaultCall i vault caller decimalsData gas warmAddrs warmKeys) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord i.decimals ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 100 := ⟨fuel - 100, by omega⟩
  rw [processMessageCall_vaultCall hdeleg hpre]
  obtain ⟨r, h1, h2, h3, h4⟩ := decimals_ok (i := i) (tr := tr) (vault := vault)
    (caller := caller) (w := w) (ctx := ctx) (warmAddrs := warmAddrs) (warmKeys := warmKeys) hgas k
  refine ⟨r, h1, h2, ?_, h4⟩
  rw [h3, and_255 hdec]

end EvmLeanSpecs.Refinement.Shares
