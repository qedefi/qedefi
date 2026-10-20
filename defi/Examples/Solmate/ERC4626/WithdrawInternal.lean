import Examples.Solmate.ERC20.Spec

/-!
# `withdraw` / `redeem` as world transformations, and their relation to the model

The bytecode of `withdraw` and `redeem` (Solmate `ERC4626`, `MockERC4626`) is a fixed chain of
storage effects, each of which may revert the call. This file names them at the level of the
world (`World`, words), exactly as the compiled code performs them, and proves once that the
chain refines the model's (`Vault.Solmate.withdraw` / `redeem`):

| step | code | world (this file) | model |
|---|---|---|---|
| allowance | `if (msg.sender != owner) { … allowance[owner][msg.sender] = allowed - shares; }` | `spendStep` (`Erc20.spendWorld`) | `spendIfNotOwner` |
| hook | `beforeWithdrawHookCalledCounter++` (slot 6, checked) | `bumpStep` | `bump` |
| burn | `balanceOf[owner] -= shares` (checked); `totalSupply -= shares` (unchecked) | `burnStep` | `Token.burn` |
| payout | `asset.safeTransfer(receiver, assets)`: the asset's `transfer` from the vault | `payStep` (`transferWorld` in the asset) | `Token.transfer` |

`withdrawWorld?` / `redeemWorld?` chain them after the conversion (`previewWithdrawN`, and for
`redeem` `convertToAssetsN` with the `ZERO_ASSETS` check), returning the final world and the
returned word, or `none` for a revert. The bytecode theorems (`Withdraw`, `Redeem`) show that the
compiled functions compute exactly these; `withdrawWorld?_refines` / `redeemWorld?_refines`
show that they refine the model.

## Hypotheses on Keccak (`OutSlots`)

Writes are to the allowance entry `allowance[owner][caller]` (only when `caller ≠ owner`),
slot 6, `balanceOf[owner]` and slot 2 of the vault, and the vault's and the receiver's balance
slots of the asset. The abstraction reads every balance and the counters, so: no balance row
of the vault hashes to the written fixed slots 2 or 6 (`KeccakAvoids`, one target per slot
against the `2¹⁶⁰` rows: plausible); the written balance slot of `owner` is fresh
(`BalanceSlotOk`) and not slot 7; the written allowance slot is fresh (`AllowanceSlotOk`) and
not slot 6 or 7; the asset's written balance slots are fresh (`BalanceSlotOk` of the vault and
the receiver). Allowances are only known pointwise afterwards (`RepOn`), for the entries whose
slot is none of the written ones (`OutAllowances`, `TransferAllowances`).
-/

namespace EvmLeanSpecs.Refinement.Out

open EvmLean EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Erc20 hiding transferWorld
open EvmLean.Solidity.Erc20 (transferWorld view_transferWorld)
open EvmLeanSpecs.Refinement EvmLeanSpecs.Refinement.Shares
open EvmLeanSpecs.Vault

/-! ## The steps -/

/-- The allowance step: nothing when `caller = owner`; otherwise Solmate's spend of
`allowance[owner][caller]` (nothing for an infinite allowance, else a checked subtraction). -/
def spendStep (crypto : Crypto) (w : World) (vault owner caller : Address) (amount : Word) :
    Option World :=
  if caller = owner then some w
  else
    let a := w.sload vault (allowanceSlot crypto Layout.solmate owner caller)
    if a ≠ maxWord ∧ a.toNat < amount.toNat then none
    else some (spendWorld crypto w vault owner caller amount)

/-- `beforeWithdrawHookCalledCounter++` (slot 6), checked. -/
def bumpStep (w : World) (vault : Address) : Option World :=
  if w.sload vault 6#256 = MAXW then none
  else some (w.sstore vault 6#256 (1#256 + w.sload vault 6#256))

/-- Solmate `_burn(src, amount)`: `balanceOf[src] -= amount` (checked), then
`totalSupply -= amount` (unchecked, read after the first write). -/
def burnStep (crypto : Crypto) (w : World) (vault src : Address) (amount : Word) :
    Option World :=
  let k := balanceSlot crypto Layout.solmate src
  if (w.sload vault k).toNat < amount.toNat then none
  else
    let w₁ := w.sstore vault k (w.sload vault k - amount)
    some (w₁.sstore vault 2#256 (w₁.sload vault 2#256 - amount))

/-- The asset's `transfer(to, amount)` from the vault: reverts when the vault's balance does
not cover `amount`. -/
def payStep (crypto : Crypto) (w : World) (asset vault dst : Address) (amount : Word) :
    Option World :=
  if (w.sload asset (balanceSlot crypto Layout.solmate vault)).toNat < amount.toNat then none
  else some (transferWorld crypto w asset vault dst amount)

/-- **`withdraw(assets, receiver, owner)` from `caller`, as the bytecode performs it**: the
final world and the returned `shares` word, or `none` for a revert. -/
def withdrawWorld? (crypto : Crypto) (w : World) (vault asset caller : Address) (assets : Word)
    (receiver owner : Address) : Option (World × Word) :=
  (previewWithdrawN (w.sload vault 2#256).toNat
      (w.sload asset (balanceSlot crypto Layout.solmate vault)).toNat assets.toNat).bind fun v =>
  (spendStep crypto w vault owner caller (BitVec.ofNat 256 v)).bind fun w₁ =>
  (bumpStep w₁ vault).bind fun w₂ =>
  (burnStep crypto w₂ vault owner (BitVec.ofNat 256 v)).bind fun w₃ =>
  (payStep crypto w₃ asset vault receiver assets).map fun w₄ => (w₄, BitVec.ofNat 256 v)

/-- **`redeem(shares, receiver, owner)` from `caller`, as the bytecode performs it**: the final
world and the returned `assets` word, or `none` for a revert. -/
def redeemWorld? (crypto : Crypto) (w : World) (vault asset caller : Address) (shares : Word)
    (receiver owner : Address) : Option (World × Word) :=
  (spendStep crypto w vault owner caller shares).bind fun w₁ =>
  (convertToAssetsN (w₁.sload vault 2#256).toNat
      (w₁.sload asset (balanceSlot crypto Layout.solmate vault)).toNat shares.toNat).bind fun v =>
  if v = 0 then none else
  (bumpStep w₁ vault).bind fun w₂ =>
  (burnStep crypto w₂ vault owner shares).bind fun w₃ =>
  (payStep crypto w₃ asset vault receiver (BitVec.ofNat 256 v)).map fun w₄ =>
    (w₄, BitVec.ofNat 256 v)

/-! ## Hypotheses and the relation after the call -/

/-- The Keccak hypotheses of `withdraw` / `redeem` from `caller` for `owner`, paying `receiver`
(see the module docstring): pointwise freshness of every written hashed slot, and no balance row
of the vault at the written fixed slots 2 and 6. -/
structure OutSlots (crypto : Crypto) (vault caller owner receiver : Address) : Prop where
  /-- No balance row is slot 2 (`totalSupply`) or slot 6 (the hook counter). -/
  rows : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256]
  /-- The burnt balance slot is fresh. -/
  ownerOk : BalanceSlotOk crypto Layout.solmate owner
  /-- … and is not the `afterDeposit` counter. -/
  owner7 : balanceSlot crypto Layout.solmate owner ≠ 7#256
  /-- The spent allowance slot is fresh (only written when `caller ≠ owner`). -/
  allowOk : caller ≠ owner → AllowanceSlotOk crypto Layout.solmate owner caller
  /-- … and is neither counter. -/
  allow67 : caller ≠ owner → allowanceSlot crypto Layout.solmate owner caller ≠ 6#256 ∧
    allowanceSlot crypto Layout.solmate owner caller ≠ 7#256
  /-- The vault's balance slot in the asset (debited) is fresh. -/
  vaultOk : BalanceSlotOk crypto Layout.solmate vault
  /-- The receiver's balance slot in the asset (credited) is fresh. -/
  receiverOk : BalanceSlotOk crypto Layout.solmate receiver

/-- The share allowances known after `withdraw` / `redeem`: entries whose slot is none of the
written slots (the spent entry itself is known). -/
def OutAllowances (crypto : Crypto) (caller owner : Address) (o sp : Address) : Prop :=
  (caller = owner ∨ (o = owner ∧ sp = caller) ∨
      allowanceSlot crypto Layout.solmate o sp ≠ allowanceSlot crypto Layout.solmate owner caller) ∧
    allowanceSlot crypto Layout.solmate o sp ≠ 6#256 ∧
    allowanceSlot crypto Layout.solmate o sp ≠ balanceSlot crypto Layout.solmate owner ∧
    allowanceSlot crypto Layout.solmate o sp ≠ 2#256

/-- **The refinement relation after writes**: as `Refines`, with the share allowances known
for the entries satisfying `P` and the asset allowances for those satisfying `Q`
(`Shares.RepOn`). `RefinesOn ⊤ ⊤` is `Refines` (`refinesOn_top`). -/
structure RefinesOn (P Q : Address → Address → Prop) (crypto : Crypto) (w : World)
    (vault asset : Address) (s : Solmate.State Address) : Prop where
  /-- The vault's address. -/
  self : s.self = vault
  /-- The share ledger. -/
  shares : RepOn P (view crypto Layout.solmate w vault) s.shares
  /-- The asset ledger. -/
  asset : RepOn Q (view crypto Layout.solmate w asset) s.asset
  /-- `afterDepositHookCalledCounter` (slot 7). -/
  afterDeposit : (w.sload vault 7#256).toNat = s.afterDepositCount
  /-- `beforeWithdrawHookCalledCounter` (slot 6). -/
  beforeWithdraw : (w.sload vault 6#256).toNat = s.beforeWithdrawCount

/-- With every allowance known, `RefinesOn` is `Refines`. -/
theorem refinesOn_top {crypto : Crypto} {w : World} {vault asset : Address}
    {s : Solmate.State Address} :
    RefinesOn (fun _ _ => True) (fun _ _ => True) crypto w vault asset s ↔
      Refines crypto w vault asset s :=
  ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-! ## Storage reads after the writes -/

section Lemmas

variable {crypto : Crypto}

/-- The Solmate `totalSupply` slot. -/
theorem solmate_totalSupply : Layout.solmate.totalSupply = 2#256 := rfl

/-- `if` with a false condition (a non-deprecated `if_neg`). -/
theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-- `if` with a true condition (a non-deprecated `if_pos`). -/
theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

/-- `MAXW` is `maxWord`. -/
theorem MAXW_eq_maxWord : MAXW = maxWord := by decide

/-- A word is `MAXW` iff its value is `MAX`. -/
theorem eq_MAXW_iff (x : Word) : x = MAXW ↔ x.toNat = MAX := by
  rw [MAXW_eq_maxWord]; exact eq_maxWord_iff x

/-- No balance row hashes to a slot listed in `rows`. -/
theorem balanceSlot_ne_of_avoids {slots : List Word} (h : KeccakAvoids crypto (AddressKeyed [3#256]) slots)
    (a : Address) {k : Word} (hk : k ∈ slots) : balanceSlot crypto Layout.solmate a ≠ k :=
  mappingSlot_ne_of_avoids h ⟨a, 3#256, by simp, rfl⟩ hk

/-- Writing a fixed slot `k ≠ 2` that no balance row hashes to: the total supply and the balances
are unchanged, allowances unless their slot is `k`. -/
theorem repOn_sstore_fixed {w : World} {vault : Address} {k v : Word}
    (hrow : ∀ a, balanceSlot crypto Layout.solmate a ≠ k) (h2 : k ≠ 2#256)
    {P : Address → Address → Prop} {t : Token Address}
    (hr : RepOn P (view crypto Layout.solmate w vault) t) :
    RepOn (fun o sp => P o sp ∧ allowanceSlot crypto Layout.solmate o sp ≠ k)
      (view crypto Layout.solmate (w.sstore vault k v) vault) t := by
  refine ⟨?_, fun a => ?_, fun o sp hp => ?_⟩
  · simp only [view, solmate_totalSupply]
    rw [World.sload_sstore_ne_key _ _ _ (fun e => h2 e.symm)]
    exact hr.totalSupply
  · simp only [view]
    rw [World.sload_sstore_ne_key _ _ _ (hrow a)]
    exact hr.balanceOf a
  · simp only [view]
    rw [World.sload_sstore_ne_key _ _ _ hp.2]
    exact hr.allowance o sp hp.1

/-- Frame of one `SSTORE`. -/
theorem sload_sstore_of_ne {w : World} {a b : Address} {k k' v : Word} (h : b ≠ a ∨ k' ≠ k) :
    (w.sstore a k v).sload b k' = w.sload b k' :=
  sload_sstore_frame h


/-- **The allowance step refines `spendIfNotOwner`.** -/
theorem spendStep_spec {w : World} {vault owner caller : Address} {amount : Word}
    (ha : caller ≠ owner → AllowanceSlotOk crypto Layout.solmate owner caller)
    {t : Token Address} (hr : Rep (view crypto Layout.solmate w vault) t) :
    match Solmate.spendIfNotOwner t caller owner amount.toNat with
    | some t₁ => ∃ w₁, spendStep crypto w vault owner caller amount = some w₁ ∧
        RepOn (fun o sp => caller = owner ∨ (o = owner ∧ sp = caller) ∨
            allowanceSlot crypto Layout.solmate o sp ≠
              allowanceSlot crypto Layout.solmate owner caller)
          (view crypto Layout.solmate w₁ vault) t₁ ∧
        (∀ b k, b ≠ vault ∨ caller = owner ∨
            k ≠ allowanceSlot crypto Layout.solmate owner caller → w₁.sload b k = w.sload b k)
    | none => spendStep crypto w vault owner caller amount = none := by
  by_cases hco : caller = owner
  · simp only [Solmate.spendIfNotOwner, hco, ne_eq, not_true_eq_false, ↓reduceIte]
    exact ⟨w, by simp [spendStep], hr.mono fun _ _ _ => trivial, fun _ _ _ => rfl⟩
  · have hsp : Solmate.spendIfNotOwner t caller owner amount.toNat =
        t.spend owner caller amount.toNat := by
      simp [Solmate.spendIfNotOwner, hco]
    rw [hsp]
    have hal := hr.allowance owner caller trivial
    simp only [view] at hal
    split
    · rename_i t₁ ht
      obtain ⟨s₁, hm⟩ := Option.isSome_iff_exists.1
        ((spend_isSome_iff hr owner caller amount).2 (by simp [ht]))
      have hcond := allowance_cond_of_spend hr ht
      obtain ⟨h1, h2, h3, h4⟩ := view_spendWorld (w := w) (token := vault) (ha hco) hm
      refine ⟨_, ?_, RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp (hp.resolve_left hco))
        (rep_spend hr hm ht), fun b k hk => ?_⟩
      · simp only [spendStep, hco, ↓reduceIte]
        rw [ite_neg']
        rintro ⟨hmax, hlt⟩
        rcases hcond with h | h
        · exact hmax h
        · simp only [view] at h; omega
      · rcases hk with hb | hk | hk
        · exact h4 b k hb
        · exact absurd hk hco
        · exact sload_spendWorld (.inr hk)
    · rename_i ht
      simp only [spendStep, hco, ↓reduceIte]
      rw [ite_pos']
      unfold Token.spend at ht
      split at ht
      · cases ht
      · rename_i hmax
        split at ht
        · rename_i hlt
          refine ⟨fun h => hmax ?_, by rw [hal]; exact hlt⟩
          rw [← hal, (eq_maxWord_iff _).1 h]
        · cases ht

/-- **The hook counter step refines `bump`.** -/
theorem bumpStep_spec {w : World} {vault : Address}
    (hrow : ∀ a, balanceSlot crypto Layout.solmate a ≠ 6#256)
    {P : Address → Address → Prop} {t : Token Address}
    (hr : RepOn P (view crypto Layout.solmate w vault) t) :
    match Solmate.bump (w.sload vault 6#256).toNat with
    | some c => ∃ w₂, bumpStep w vault = some w₂ ∧ (w₂.sload vault 6#256).toNat = c ∧
        RepOn (fun o sp => P o sp ∧ allowanceSlot crypto Layout.solmate o sp ≠ 6#256)
          (view crypto Layout.solmate w₂ vault) t ∧
        (∀ b k, b ≠ vault ∨ k ≠ 6#256 → w₂.sload b k = w.sload b k)
    | none => bumpStep w vault = none := by
  have hlt := (w.sload vault 6#256).isLt
  split
  · rename_i c hc
    simp only [Solmate.bump, checkedAdd] at hc
    split at hc
    · cases hc
    · rename_i hle
      cases hc
      have hne : w.sload vault 6#256 ≠ MAXW := by
        rw [Ne, eq_MAXW_iff]; unfold MAX at *; omega
      refine ⟨w.sstore vault 6#256 (1#256 + w.sload vault 6#256), by simp [bumpStep, hne], ?_,
        repOn_sstore_fixed hrow (by decide) hr, fun b k hk => sload_sstore_of_ne hk⟩
      rw [World.sload_sstore_self, BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat]
      unfold MAX at hle
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  · rename_i hc
    simp only [Solmate.bump, checkedAdd] at hc
    split at hc
    · rename_i hgt
      have : w.sload vault 6#256 = MAXW := by
        rw [eq_MAXW_iff]; unfold MAX at *; omega
      simp [bumpStep, this]
    · cases hc

/-- **The burn step refines `Token.burn`.** -/
theorem burnStep_spec {w : World} {vault src : Address} {amount : Word}
    (hown : BalanceSlotOk crypto Layout.solmate src)
    (hrow : ∀ a, balanceSlot crypto Layout.solmate a ≠ 2#256)
    {P : Address → Address → Prop} {t : Token Address}
    (hr : RepOn P (view crypto Layout.solmate w vault) t) (hw : t.WF) :
    match t.burn src amount.toNat with
    | some t' => ∃ w₃, burnStep crypto w vault src amount = some w₃ ∧
        RepOn (fun o sp => P o sp ∧
            allowanceSlot crypto Layout.solmate o sp ≠ balanceSlot crypto Layout.solmate src ∧
            allowanceSlot crypto Layout.solmate o sp ≠ 2#256)
          (view crypto Layout.solmate w₃ vault) t' ∧
        (∀ b k, b ≠ vault ∨ (k ≠ balanceSlot crypto Layout.solmate src ∧ k ≠ 2#256) →
          w₃.sload b k = w.sload b k)
    | none => burnStep crypto w vault src amount = none := by
  have hb := hr.balanceOf src
  have hts := hr.totalSupply
  simp only [view, solmate_totalSupply] at hb hts
  split
  · rename_i t' ht
    obtain ⟨hle, rfl⟩ := Token.burn_eq_some.1 ht
    have hle' : amount.toNat ≤ (w.sload vault (balanceSlot crypto Layout.solmate src)).toNat := by
      rw [hb]; exact hle
    have hbt := Token.balanceOf_le_totalSupply hw src
    have h2ne : (2#256 : Word) ≠ balanceSlot crypto Layout.solmate src := fun e => hown.2 e.symm
    refine ⟨_, by simp only [burnStep]; rw [ite_neg' (by omega)], ⟨?_, fun a => ?_, ?_⟩, ?_⟩
    · simp only [view, solmate_totalSupply]
      rw [World.sload_sstore_self, World.sload_sstore_ne_key _ _ _ h2ne,
        BitVec.toNat_sub_of_le (BitVec.le_def.2 (by omega)), hts]
    · simp only [view]
      rw [World.sload_sstore_ne_key _ _ _ (hrow a), Token.sub_single_apply]
      by_cases has : src = a
      · subst has
        rw [World.sload_sstore_self, ite_pos' rfl, BitVec.toNat_sub_of_le (BitVec.le_def.2 hle'),
          hb]
      · rw [World.sload_sstore_ne_key _ _ _ (balanceSlot_ne hown (Ne.symm has)), ite_neg' has]
        exact hr.balanceOf a
    · rintro o sp ⟨hp, h1, h2⟩
      simp only [view]
      rw [World.sload_sstore_ne_key _ _ _ h2, World.sload_sstore_ne_key _ _ _ h1]
      exact hr.allowance o sp hp
    · intro b k hk
      rw [sload_sstore_of_ne (hk.imp id (·.2)), sload_sstore_of_ne (hk.imp id (·.1))]
  · rename_i ht
    simp only [burnStep]
    rw [ite_pos']
    unfold Token.burn at ht
    split at ht
    · rwa [hb]
    · cases ht

/-- **The payout step refines `Token.transfer`** of the asset, from the vault. -/
theorem payStep_spec {w : World} {asset vault dst : Address} {amount : Word}
    (hv : BalanceSlotOk crypto Layout.solmate vault)
    (hto : BalanceSlotOk crypto Layout.solmate dst)
    {t : Token Address} (hr : Rep (view crypto Layout.solmate w asset) t) (hw : t.WF) :
    match t.transfer vault dst amount.toNat with
    | some t' => payStep crypto w asset vault dst amount =
          some (transferWorld crypto w asset vault dst amount) ∧
        RepOn (TransferAllowances crypto vault dst)
          (view crypto Layout.solmate (transferWorld crypto w asset vault dst amount) asset) t'
    | none => payStep crypto w asset vault dst amount = none := by
  have hb := hr.balanceOf vault
  simp only [view] at hb
  split
  · rename_i t' hT
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1
      ((transfer_isSome_iff hr vault dst amount).2 (by simp [hT]))
    have hle := (Token.transfer_eq_some.1 hT).1
    obtain ⟨h1, h2, h3, -⟩ := view_transferWorld (token := asset) hv hto hm
    refine ⟨by simp only [payStep]; rw [ite_neg' (by omega)], ?_⟩
    exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1 hp.2) (rep_transfer hr hw hm hT)
  · rename_i hT
    simp only [payStep]
    rw [ite_pos']
    unfold Token.transfer at hT
    split at hT
    · rwa [hb]
    · cases hT

/-- `ceilDivN z d ≤ z` for a non-zero divisor. -/
theorem ceilDivN_le {z d : Nat} (hd : d ≠ 0) : ceilDivN z d ≤ z := by
  unfold ceilDivN
  split
  · rename_i h
    have hd1 : 1 < d := by
      rcases Nat.lt_or_ge 1 d with h' | h'
      · exact h'
      · have : d = 1 := by omega
        subst this; rw [Nat.mod_one] at h; exact absurd h (Nat.lt_irrefl 0)
    have hz : 0 < z := by
      rcases Nat.eq_zero_or_pos z with h' | h'
      · subst h'; rw [Nat.zero_mod] at h; exact absurd h (Nat.lt_irrefl 0)
      · exact h'
    have := Nat.div_lt_self hz hd1
    omega
  · have := Nat.div_le_self z d
    omega

/-- A product that passes Solmate's overflow test fits in a word. -/
theorem mul_le_of_guard {x y : Nat} (h : ¬ (y ≠ 0 ∧ MAXN / y < x)) : x * y ≤ MAXN := by
  by_cases hy : y = 0
  · subst hy; simp
  · have : x ≤ MAXN / y := by omega
    exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hy)).1 this

/-- The result of `previewWithdraw` fits in a word. -/
theorem previewWithdrawN_lt {S T x v : Nat} (hx : x < 2 ^ 256)
    (h : previewWithdrawN S T x = some v) : v < 2 ^ 256 := by
  unfold previewWithdrawN at h
  split at h
  · cases h; exact hx
  · unfold mulDivUpN at h
    split at h
    · cases h
    · rename_i hc
      cases h
      have h1 := mul_le_of_guard (fun h => hc (.inr h))
      have h2 := ceilDivN_le (z := x * S) (d := T) (fun h => hc (.inl h))
      unfold MAXN at h1
      omega

/-- The result of `convertToAssets` fits in a word. -/
theorem convertToAssetsN_lt {S T x v : Nat} (hx : x < 2 ^ 256)
    (h : convertToAssetsN S T x = some v) : v < 2 ^ 256 := by
  unfold convertToAssetsN at h
  split at h
  · cases h; exact hx
  · unfold mulDivDownN at h
    split at h
    · cases h
    · rename_i hc
      cases h
      have h1 := mul_le_of_guard (fun h => hc (.inr h))
      have h2 := Nat.div_le_self (x * T) S
      unfold MAXN at h1
      omega

/-- `toNat` of `ofNat` of a value that fits. -/
theorem toNat_ofNat_of_lt {v : Nat} (h : v < 2 ^ 256) : (BitVec.ofNat 256 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The spent ledger stays well formed. -/
theorem WF_spendIfNotOwner {t t₁ : Token Address} {caller owner : Address} {v : Nat}
    (hw : t.WF) (h : Solmate.spendIfNotOwner t caller owner v = some t₁) : t₁.WF := by
  unfold Solmate.spendIfNotOwner at h
  split at h
  · exact Token.WF_spend hw h
  · cases h; exact hw

end Lemmas

/-! ## The chains refine the model -/

section Chains

variable {crypto : Crypto} {w : World} {vault asset caller receiver owner : Address}
  {s : Solmate.State Address}

/-- The model's total supply and total assets of a represented state are the storage words. -/
theorem refines_reads (hr : Refines crypto w vault asset s) :
    s.totalSupply = (w.sload vault 2#256).toNat ∧
      s.totalAssets = (w.sload asset (balanceSlot crypto Layout.solmate vault)).toNat := by
  have h1 := hr.shares.totalSupply
  have h2 := hr.asset.balanceOf vault
  simp only [view] at h1 h2
  refine ⟨h1.symm, ?_⟩
  simp only [Solmate.State.totalAssets, hr.self, h2]

/-- `previewWithdraw` of a represented state. -/
theorem previewWithdraw_of_refines (hr : Refines crypto w vault asset s) (x : Nat) :
    s.previewWithdraw x = previewWithdrawN (w.sload vault 2#256).toNat
      (w.sload asset (balanceSlot crypto Layout.solmate vault)).toNat x := by
  obtain ⟨h1, h2⟩ := refines_reads hr
  simp only [Solmate.State.previewWithdraw, h1, h2, previewWithdrawN, mulDivUpN_eq]

/-- `previewRedeem` of a represented state. -/
theorem previewRedeem_of_refines (hr : Refines crypto w vault asset s) (x : Nat) :
    s.previewRedeem x = convertToAssetsN (w.sload vault 2#256).toNat
      (w.sload asset (balanceSlot crypto Layout.solmate vault)).toNat x := by
  obtain ⟨h1, h2⟩ := refines_reads hr
  simp only [Solmate.State.previewRedeem, Solmate.State.convertToAssets, h1, h2,
    convertToAssetsN, mulDivDownN_eq]

/-- The common tail of `withdraw` and `redeem` after the allowance step: hook, burn, payout. -/
theorem tail_refines (hr : Refines crypto w vault asset s) (hinv : Solmate.Inv s) (hne : asset ≠ vault)
    (hk : OutSlots crypto vault caller owner receiver) {w₁ : World} {t₁ : Token Address}
    (hr₁ : RepOn (fun o sp => caller = owner ∨ (o = owner ∧ sp = caller) ∨
            allowanceSlot crypto Layout.solmate o sp ≠
              allowanceSlot crypto Layout.solmate owner caller)
          (view crypto Layout.solmate w₁ vault) t₁)
    (hf₁ : ∀ b k, b ≠ vault ∨ caller = owner ∨
        k ≠ allowanceSlot crypto Layout.solmate owner caller → w₁.sload b k = w.sload b k)
    (hw₁ : t₁.WF) (sh as : Word) (r : Nat) (R : Word) :
    match (Solmate.bump s.beforeWithdrawCount).bind fun c =>
        (t₁.burn owner sh.toNat).bind fun sh₂ =>
        (s.asset.transfer s.self receiver as.toNat).map fun a =>
          (({ s with asset := a, shares := sh₂, beforeWithdrawCount := c } :
            Solmate.State Address), r)
    with
    | some (s', r') => r' = r ∧ ∃ w', ((bumpStep w₁ vault).bind fun w₂ =>
          (burnStep crypto w₂ vault owner sh).bind fun w₃ =>
          (payStep crypto w₃ asset vault receiver as).map fun w₄ => (w₄, R)) = some (w', R) ∧
        RefinesOn (OutAllowances crypto caller owner) (TransferAllowances crypto vault receiver)
          crypto w' vault asset s'
    | none => ((bumpStep w₁ vault).bind fun w₂ =>
          (burnStep crypto w₂ vault owner sh).bind fun w₃ =>
          (payStep crypto w₃ asset vault receiver as).map fun w₄ => (w₄, R)) = none := by
  have hrow2 : ∀ a, balanceSlot crypto Layout.solmate a ≠ 2#256 :=
    fun a => balanceSlot_ne_of_avoids hk.rows a (by simp)
  have hrow6 : ∀ a, balanceSlot crypto Layout.solmate a ≠ 6#256 :=
    fun a => balanceSlot_ne_of_avoids hk.rows a (by simp)
  have hn6 : caller = owner ∨ (6#256 : Word) ≠ allowanceSlot crypto Layout.solmate owner caller := by
    by_cases hco : caller = owner
    · exact .inl hco
    · exact .inr (hk.allow67 hco).1.symm
  have hn7 : caller = owner ∨ (7#256 : Word) ≠ allowanceSlot crypto Layout.solmate owner caller := by
    by_cases hco : caller = owner
    · exact .inl hco
    · exact .inr (hk.allow67 hco).2.symm
  have hc6 : w₁.sload vault 6#256 = w.sload vault 6#256 := hf₁ _ _ (.inr hn6)
  have hB := bumpStep_spec (w := w₁) (vault := vault) hrow6 hr₁
  have hbw : (w.sload vault 6#256).toNat = s.beforeWithdrawCount := hr.beforeWithdraw
  rw [hc6, hbw] at hB
  cases hb : Solmate.bump s.beforeWithdrawCount with
  | none =>
    rw [hb] at hB
    simp only [Option.bind_none, hB]
  | some c =>
    rw [hb] at hB
    obtain ⟨w₂, hw₂, hc₂, hr₂, hf₂⟩ := hB
    have hBu := burnStep_spec (w := w₂) (vault := vault) (amount := sh) hk.ownerOk hrow2 hr₂ hw₁
    simp only [Option.bind_some, hw₂]
    cases hbu : t₁.burn owner sh.toNat with
    | none =>
      rw [hbu] at hBu
      simp only [Option.bind_none, hBu]
    | some t₂ =>
      rw [hbu] at hBu
      obtain ⟨w₃, hw₃, hr₃, hf₃⟩ := hBu
      simp only [Option.bind_some, hw₃]
      have hfa : ∀ k, w₃.sload asset k = w.sload asset k := fun k => by
        rw [hf₃ _ _ (.inl hne), hf₂ _ _ (.inl hne), hf₁ _ _ (.inl hne)]
      have hra : Rep (view crypto Layout.solmate w₃ asset) s.asset := by
        have : view crypto Layout.solmate w₃ asset = view crypto Layout.solmate w asset := by
          simp only [view, hfa]
        rw [this]; exact hr.asset
      have hP := payStep_spec (amount := as) hk.vaultOk hk.receiverOk hra hinv.1
      rw [hr.self]
      cases hT : s.asset.transfer vault receiver as.toNat with
      | none =>
        rw [hT] at hP
        simp only [Option.map_none, hP]
      | some ta =>
        rw [hT] at hP
        obtain ⟨hpay, hra'⟩ := hP
        simp only [Option.map_some, hpay]
        have hfv : ∀ k, (transferWorld crypto w₃ asset vault receiver as).sload vault k =
            w₃.sload vault k := fun k => sload_transferWorld (.inl (Ne.symm hne))
        refine ⟨trivial, _, rfl, ⟨rfl, ?_, hra', ?_, ?_⟩⟩
        · have : view crypto Layout.solmate (transferWorld crypto w₃ asset vault receiver as) vault =
              view crypto Layout.solmate w₃ vault := by simp only [view, hfv]
          rw [this]
          exact hr₃.mono fun o sp ⟨hA, h6, hb', h2⟩ => ⟨⟨hA, h6⟩, hb', h2⟩
        · rw [hfv, hf₃ _ _ (.inr ⟨hk.owner7.symm, by decide⟩), hf₂ _ _ (.inr (by decide)),
            hf₁ _ _ (.inr hn7)]
          exact (hr.afterDeposit : (w.sload vault 7#256).toNat = s.afterDepositCount)
        · rw [hfv, hf₃ _ _ (.inr ⟨(hrow6 owner).symm, by decide⟩)]
          exact hc₂

/-- **`withdraw`: the bytecode's chain refines the model.** From a world refining `s` (with the
model's invariant), the model's `withdraw` and `withdrawWorld?` succeed together; on success the
returned words agree and the final world refines the model's final state. -/
theorem withdrawWorld?_refines (hr : Refines crypto w vault asset s) (hinv : Solmate.Inv s)
    (hne : asset ≠ vault) (hk : OutSlots crypto vault caller owner receiver) (assets : Word) :
    match Solmate.withdraw s caller assets.toNat receiver owner with
    | some (s', v) => ∃ w', withdrawWorld? crypto w vault asset caller assets receiver owner =
          some (w', BitVec.ofNat 256 v) ∧
        RefinesOn (OutAllowances crypto caller owner) (TransferAllowances crypto vault receiver)
          crypto w' vault asset s'
    | none => withdrawWorld? crypto w vault asset caller assets receiver owner = none := by
  unfold Solmate.withdraw withdrawWorld?
  rw [previewWithdraw_of_refines hr]
  cases hp : previewWithdrawN (w.sload vault 2#256).toNat
      (w.sload asset (balanceSlot crypto Layout.solmate vault)).toNat assets.toNat with
  | none => simp
  | some v =>
    have hv := toNat_ofNat_of_lt (previewWithdrawN_lt assets.isLt hp)
    simp only [Option.bind_some]
    have hS := spendStep_spec (w := w) (vault := vault) (amount := BitVec.ofNat 256 v)
      hk.allowOk hr.shares
    rw [hv] at hS
    cases hsp : Solmate.spendIfNotOwner s.shares caller owner v with
    | none =>
      rw [hsp] at hS
      simp [hS]
    | some t₁ =>
      rw [hsp] at hS
      obtain ⟨w₁, hw₁, hr₁, hf₁⟩ := hS
      simp only [Option.bind_some, hw₁]
      have hT := tail_refines hr hinv hne hk hr₁ hf₁ (WF_spendIfNotOwner hinv.2 hsp)
        (BitVec.ofNat 256 v) assets v (BitVec.ofNat 256 v)
      rw [hv] at hT
      revert hT
      split
      · rintro ⟨rfl, w', hw', hR⟩
        exact ⟨w', hw', hR⟩
      · exact id

/-- **`redeem`: the bytecode's chain refines the model.** As `withdrawWorld?_refines`. -/
theorem redeemWorld?_refines (hr : Refines crypto w vault asset s) (hinv : Solmate.Inv s)
    (hne : asset ≠ vault) (hk : OutSlots crypto vault caller owner receiver) (shares : Word) :
    match Solmate.redeem s caller shares.toNat receiver owner with
    | some (s', v) => ∃ w', redeemWorld? crypto w vault asset caller shares receiver owner =
          some (w', BitVec.ofNat 256 v) ∧
        RefinesOn (OutAllowances crypto caller owner) (TransferAllowances crypto vault receiver)
          crypto w' vault asset s'
    | none => redeemWorld? crypto w vault asset caller shares receiver owner = none := by
  unfold Solmate.redeem redeemWorld?
  have hS := spendStep_spec (w := w) (vault := vault) (amount := shares) hk.allowOk hr.shares
  cases hsp : Solmate.spendIfNotOwner s.shares caller owner shares.toNat with
  | none =>
    rw [hsp] at hS
    simp [hS]
  | some t₁ =>
    rw [hsp] at hS
    obtain ⟨w₁, hw₁, hr₁, hf₁⟩ := hS
    simp only [Option.bind_some, hw₁]
    have h2 : w₁.sload vault 2#256 = w.sload vault 2#256 := by
      apply hf₁
      by_cases hco : caller = owner
      · exact .inr (.inl hco)
      · exact .inr (.inr fun e => (hk.allowOk hco).2.2 e.symm)
    have ha : w₁.sload asset (balanceSlot crypto Layout.solmate vault) =
        w.sload asset (balanceSlot crypto Layout.solmate vault) := hf₁ _ _ (.inl hne)
    rw [h2, ha, ← previewRedeem_of_refines hr]
    cases hp : s.previewRedeem shares.toNat with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      by_cases hv0 : v = 0
      · simp [hv0]
      · simp only [hv0, ↓reduceIte]
        have hvlt := convertToAssetsN_lt shares.isLt
          (by rw [← previewRedeem_of_refines hr]; exact hp)
        have hT := tail_refines hr hinv hne hk hr₁ hf₁ (WF_spendIfNotOwner hinv.2 hsp)
          shares (BitVec.ofNat 256 v) v (BitVec.ofNat 256 v)
        rw [toNat_ofNat_of_lt hvlt] at hT
        revert hT
        split
        · rintro ⟨rfl, w', hw', hR⟩
          exact ⟨w', hw', hR⟩
        · exact id

end Chains

end EvmLeanSpecs.Refinement.Out
