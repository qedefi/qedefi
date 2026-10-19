import EvmLeanSpecs.Refinement.DepositInternal

/-!
# `deposit` / `mint`: the world they produce, seen through the abstraction

Both entry points do the same three writes, in this order (Solmate `ERC4626` with
`MockERC4626`'s hook):

1. the asset's `transferFrom(caller, vault, assets)` with the vault as spender
   (`Erc20.transferFromWorld` on the asset's storage, `safeTransferFrom_wp`);
2. `_mint(receiver, shares)` on the vault's storage (`mintWorld`, `mintShares_wp`):
   `totalSupply += shares` (checked), `balanceOf[receiver] += shares`;
3. `afterDepositHookCalledCounter++` (slot 7, checked; `bumpWorld`, `afterDeposit_wp`).

`depositWorld` is that world. `refinesAllow_depositWorld` relates it to the model: when the
model's `Token.transferFrom` of the asset ledger, `Token.mint` of the share ledger and `bump`
of the counter all succeed, the world after the three writes represents the model's new state
(`RefinesAllow`: both ledgers as `Shares.RepOn`, the two counters exactly).

## Hypotheses (all on the hash, all of the "fresh slot" kind)

* `BalanceSlotOk` of the caller and of the vault (the two asset balances written), of the
  receiver (the share balance written); `AllowanceSlotOk` of `allowance[caller][vault]` in the
  asset (the allowance written);
* `KeccakAvoids crypto (AddressKeyed [3]) [2, 6, 7]`: no balance slot is the `totalSupply`
  slot or a hook-counter slot. Writing slot 2 (or 7) changes the balance of every address whose
  balance slot is 2 (or 7), and the share view must keep *every* balance; writing the
  receiver's balance must not change counter 6. One target against `2¹⁶⁰` candidates each:
  plausible (see `EvmLeanProofs.Solidity.Keccak`).
* `Token.WF` of both ledgers (`Solmate.Inv`): the unchecked `balanceOf[receiver] += shares`
  does not wrap.
* the vault and the asset are different accounts.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault Shares

/-! ## The conversions fit in a word -/

/-- A `mulDivDown` result fits in a word. -/
theorem mulDivDownN_lt {x y d v : ℕ} (h : mulDivDownN x y d = some v) : v < 2 ^ 256 := by
  unfold mulDivDownN MAXN at h
  split at h
  · cases h
  · rename_i hc
    cases h
    by_cases hy : y = 0
    · subst hy; simp
    · have hx : x ≤ (2 ^ 256 - 1) / y := by omega
      have := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hy)).1 hx
      have := Nat.div_le_self (x * y) d
      omega

/-- A `mulDivUp` result fits in a word. -/
theorem mulDivUpN_lt {x y d v : ℕ} (h : mulDivUpN x y d = some v) : v < 2 ^ 256 := by
  unfold mulDivUpN MAXN ceilDivN at h
  split at h
  · cases h
  · rename_i hc
    cases h
    have hd : d ≠ 0 := fun e => hc (.inl e)
    have hxy : x * y ≤ 2 ^ 256 - 1 := by
      by_cases hy : y = 0
      · subst hy; simp
      · have hx : x ≤ (2 ^ 256 - 1) / y := by omega
        exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hy)).1 hx
    have h1 := Nat.div_le_self (x * y) d
    by_cases hd1 : d = 1
    · subst hd1; simp only [Nat.mod_one, Nat.lt_irrefl, ↓reduceIte, Nat.div_one]; omega
    · split
      · rename_i hr
        have : x * y / d < x * y := Nat.div_lt_self (by
          rcases Nat.eq_zero_or_pos (x * y) with h0 | h0
          · rw [h0] at hr; simp at hr
          · exact h0) (by omega)
        omega
      · omega

/-- `convertToShares` of a word fits in a word. -/
theorem convertToSharesN_lt {S T x v : ℕ} (hx : x < 2 ^ 256)
    (h : convertToSharesN S T x = some v) : v < 2 ^ 256 := by
  unfold convertToSharesN at h
  split at h
  · cases h; exact hx
  · exact mulDivDownN_lt h

/-- `previewMint` of a word fits in a word. -/
theorem previewMintN_lt {S T x v : ℕ} (hx : x < 2 ^ 256)
    (h : previewMintN S T x = some v) : v < 2 ^ 256 := by
  unfold previewMintN at h
  split at h
  · cases h; exact hx
  · exact mulDivUpN_lt h

/-! ## The model's `deposit` / `mint`, step by step -/

section Steps

variable {s : Solmate.State Address} {c r : Address} {a v : ℕ} {t' sh : Token Address}

/-- `deposit` reverts when `previewDeposit` does. -/
theorem deposit_none_preview (h : s.previewDeposit a = none) : Solmate.deposit s c a r = none := by
  simp [Solmate.deposit, h]

/-- `deposit` reverts on zero shares (`ZERO_SHARES`). -/
theorem deposit_none_zero (h : s.previewDeposit a = some 0) : Solmate.deposit s c a r = none := by
  simp [Solmate.deposit, h]

/-- `deposit` reverts when the asset's `transferFrom` does. -/
theorem deposit_none_transfer (h : s.previewDeposit a = some v)
    (ht : s.asset.transferFrom s.self c s.self a = none) : Solmate.deposit s c a r = none := by
  simp [Solmate.deposit, h, ht]

/-- `deposit` reverts when `_mint` does. -/
theorem deposit_none_mint (h : s.previewDeposit a = some v) (hv : v ≠ 0)
    (ht : s.asset.transferFrom s.self c s.self a = some t') (hm : s.shares.mint r v = none) :
    Solmate.deposit s c a r = none := by
  simp [Solmate.deposit, h, hv, ht, hm]

/-- `deposit` reverts when the hook counter overflows. -/
theorem deposit_none_bump (h : s.previewDeposit a = some v)
    (ht : s.asset.transferFrom s.self c s.self a = some t')
    (hb : Solmate.bump s.afterDepositCount = none) : Solmate.deposit s c a r = none := by
  simp [Solmate.deposit, h, ht, hb]

/-- `deposit` succeeds when every step does. -/
theorem deposit_some {n : ℕ} (h : s.previewDeposit a = some v) (hv : v ≠ 0)
    (ht : s.asset.transferFrom s.self c s.self a = some t') (hm : s.shares.mint r v = some sh)
    (hb : Solmate.bump s.afterDepositCount = some n) :
    Solmate.deposit s c a r =
      some ({ s with asset := t', shares := sh, afterDepositCount := n }, v) := by
  simp [Solmate.deposit, h, hv, ht, hm, hb]

/-- `mint` reverts when `previewMint` does. -/
theorem mint_none_preview (h : s.previewMint a = none) : Solmate.mint s c a r = none := by
  simp [Solmate.mint, h]

/-- `mint` reverts when the asset's `transferFrom` does. -/
theorem mint_none_transfer (h : s.previewMint a = some v)
    (ht : s.asset.transferFrom s.self c s.self v = none) : Solmate.mint s c a r = none := by
  simp [Solmate.mint, h, ht]

/-- `mint` reverts when `_mint` does. -/
theorem mint_none_mint (h : s.previewMint a = some v) (hm : s.shares.mint r a = none) :
    Solmate.mint s c a r = none := by
  simp [Solmate.mint, h, hm]

/-- `mint` reverts when the hook counter overflows. -/
theorem mint_none_bump (h : s.previewMint a = some v)
    (hb : Solmate.bump s.afterDepositCount = none) : Solmate.mint s c a r = none := by
  simp [Solmate.mint, h, hb]

/-- `mint` succeeds when every step does. -/
theorem mint_some {n : ℕ} (h : s.previewMint a = some v)
    (ht : s.asset.transferFrom s.self c s.self v = some t') (hm : s.shares.mint r a = some sh)
    (hb : Solmate.bump s.afterDepositCount = some n) :
    Solmate.mint s c a r =
      some ({ s with asset := t', shares := sh, afterDepositCount := n }, v) := by
  simp [Solmate.mint, h, ht, hm, hb]

end Steps

/-- `Token.mint` fails exactly on a supply overflow. -/
theorem token_mint_none_iff {t : Token Address} {dst : Address} {v : ℕ} :
    t.mint dst v = none ↔ 2 ^ 256 ≤ t.totalSupply + v := by
  unfold Token.mint MAX; split_ifs with h <;> simp <;> omega

/-- `bump` fails exactly on a counter overflow. -/
theorem bump_none_iff {n : ℕ} : Solmate.bump n = none ↔ n + 1 = 2 ^ 256 ∨ 2 ^ 256 < n + 1 := by
  unfold Solmate.bump checkedAdd MAX; split_ifs with h <;> simp <;> omega

/-! ## The world -/

/-- The world after a successful `deposit` / `mint` from `caller` for `receiver`, pulling
`assets` and minting `shares`. -/
def depositWorld (crypto : Crypto) (w : World) (vault asset caller receiver : Address)
    (assets shares : Word) : World :=
  bumpWorld (mintWorld crypto (Erc20.transferFromWorld crypto w asset vault caller vault assets)
    vault receiver shares) vault

/-- The model state is represented by the storage, with the allowances of the shares known on
`P` and those of the asset on `Q` (the `Refines` relation weakened to `Shares.RepOn`, as after
writes). -/
structure RefinesAllow (P Q : Address → Address → Prop) (crypto : Crypto) (w : World)
    (vault asset : Address) (s : Solmate.State Address) : Prop where
  /-- The vault's address. -/
  self : s.self = vault
  /-- The share ledger, allowances on `P`. -/
  shares : RepOn P (Erc20.view crypto Erc20.Layout.solmate w vault) s.shares
  /-- The asset ledger, allowances on `Q`. -/
  asset : RepOn Q (Erc20.view crypto Erc20.Layout.solmate w asset) s.asset
  /-- `afterDepositHookCalledCounter` (slot 7). -/
  afterDeposit : (w.sload vault 7#256).toNat = s.afterDepositCount
  /-- `beforeWithdrawHookCalledCounter` (slot 6). -/
  beforeWithdraw : (w.sload vault 6#256).toNat = s.beforeWithdrawCount

/-- `Refines` is `RefinesAllow` with all allowances. -/
theorem RefinesAllow.of_refines {crypto : Crypto} {w : World} {vault asset : Address}
    {s : Solmate.State Address} (h : Refines crypto w vault asset s) :
    RefinesAllow (fun _ _ => True) (fun _ _ => True) crypto w vault asset s :=
  ⟨h.self, h.shares, h.asset, h.afterDeposit, h.beforeWithdraw⟩

/-- The share allowances known after `deposit` / `mint` for `receiver`: those whose slot is
none of the written slots (2, the receiver's balance slot, 7). -/
def DepositAllowances (crypto : Crypto) (receiver : Address) (o sp : Address) : Prop :=
  MintAllowances crypto receiver o sp ∧ Erc20.allowanceSlot crypto Erc20.Layout.solmate o sp ≠ 7#256

/-- The fixed-slot hypothesis, restricted. -/
theorem KeccakAvoids.sub {crypto : Crypto} {S : ByteArray → Prop} {l l' : List Word}
    (h : KeccakAvoids crypto S l) (hl : ∀ x ∈ l', x ∈ l) : KeccakAvoids crypto S l' :=
  fun x hx hm => h x hx (hl _ hm)

/-- No balance slot is one of the fixed slots `2, 6, 7`. -/
theorem balanceSlot_ne_fixed {crypto : Crypto}
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256]) (a : Address) :
    Erc20.balanceSlot crypto Erc20.Layout.solmate a ≠ 2#256 ∧
      Erc20.balanceSlot crypto Erc20.Layout.solmate a ≠ 6#256 ∧
      Erc20.balanceSlot crypto Erc20.Layout.solmate a ≠ 7#256 :=
  ⟨mappingSlot_ne_of_avoids hk ⟨a, 3#256, by simp, rfl⟩ (by simp),
    mappingSlot_ne_of_avoids hk ⟨a, 3#256, by simp, rfl⟩ (by simp),
    mappingSlot_ne_of_avoids hk ⟨a, 3#256, by simp, rfl⟩ (by simp)⟩

/-- `transferFrom` on the asset changes no slot of another account. -/
theorem sload_transferFromWorld_ne {crypto : Crypto} {w : World} {token sp src dst b : Address}
    {v : Word} (hb : b ≠ token) (k : Word) :
    (Erc20.transferFromWorld crypto w token sp src dst v).sload b k = w.sload b k := by
  simp only [Erc20.transferFromWorld, Erc20.transferWorld]
  rw [Shares.sload_transferWorld (.inl hb), Shares.sload_spendWorld (.inl hb)]

/-- `bumpWorld` writes only slot 7 of the vault. -/
theorem sload_bumpWorld {w : World} {vault b : Address} {k : Word} (h : b ≠ vault ∨ k ≠ 7#256) :
    (bumpWorld w vault).sload b k = w.sload b k :=
  sload_sstore_frame h

/-- `depositWorld` writes only the asset's `transferFrom` slots and the vault's slots 2, 7 and
`balanceOf[receiver]`. -/
theorem sload_depositWorld {crypto : Crypto} {w : World} {vault asset caller receiver b : Address}
    {assets shares k : Word} (hb : b ≠ vault) (hb' : b ≠ asset) :
    (depositWorld crypto w vault asset caller receiver assets shares).sload b k = w.sload b k := by
  simp only [depositWorld]
  rw [sload_bumpWorld (.inl hb), sload_mintWorld (.inl hb), sload_transferFromWorld_ne hb']

/-- `depositWorld` changes no code. -/
theorem code_depositWorld (crypto : Crypto) (w : World) (vault asset caller receiver : Address)
    (assets shares : Word) (b : Address) :
    (depositWorld crypto w vault asset caller receiver assets shares).code b = w.code b := by
  simp [depositWorld, bumpWorld, mintWorld, Erc20.transferFromWorld, Erc20.transferWorld,
    Examples.SolmateAssetTransfer.transferWorld, Erc20.spendWorld]
  split <;> simp

/-- **The world after `deposit` / `mint` represents the model's new state.** -/
theorem refinesAllow_depositWorld {crypto : Crypto} {w : World} {vault asset caller receiver : Address}
    (hne : vault ≠ asset)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : Erc20.BalanceSlotOk crypto Erc20.Layout.solmate caller)
    (hbv : Erc20.BalanceSlotOk crypto Erc20.Layout.solmate vault)
    (hbr : Erc20.BalanceSlotOk crypto Erc20.Layout.solmate receiver)
    (ha : Erc20.AllowanceSlotOk crypto Erc20.Layout.solmate caller vault)
    (hinv : Solmate.Inv (abs crypto w vault asset)) {assets shares : Word}
    {t' sh : Token Address} {c : ℕ}
    (ht : (abs crypto w vault asset).asset.transferFrom vault caller vault assets.toNat = some t')
    (hm : (abs crypto w vault asset).shares.mint receiver shares.toNat = some sh)
    (hc : Solmate.bump (abs crypto w vault asset).afterDepositCount = some c) :
    RefinesAllow (DepositAllowances crypto receiver) (TransferFromAllowances crypto vault caller vault)
      crypto (depositWorld crypto w vault asset caller receiver assets shares) vault asset
      { abs crypto w vault asset with asset := t', shares := sh, afterDepositCount := c } := by
  obtain ⟨h2, h6, h7⟩ := balanceSlot_ne_fixed hk receiver
  set w₁ := Erc20.transferFromWorld crypto w asset vault caller vault assets
  set w₂ := mintWorld crypto w₁ vault receiver shares
  have hv₁ : ∀ k, w₁.sload vault k = w.sload vault k := sload_transferFromWorld_ne hne
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · -- shares: the mint on the vault's view, then the counter write
    have hr₁ : Rep (Erc20.view crypto Erc20.Layout.solmate w₁ vault)
        (abs crypto w vault asset).shares := by
      have : Erc20.view crypto Erc20.Layout.solmate w₁ vault =
          Erc20.view crypto Erc20.Layout.solmate w vault := by
        simp only [Erc20.view, hv₁]
      rw [this]; exact rep_toToken _
    have hrep := repOn_mintWorld (amount := shares) (KeccakAvoids.sub hk (by simp)) hbr hr₁ hinv.2 hm
    refine ⟨?_, fun a => ?_, fun o sp hp => ?_⟩
    · show ((bumpWorld w₂ vault).sload vault 2#256).toNat = _
      rw [sload_bumpWorld (.inr (by decide))]; exact hrep.totalSupply
    · show ((bumpWorld w₂ vault).sload vault _).toNat = _
      rw [sload_bumpWorld (.inr (balanceSlot_ne_fixed hk a).2.2)]; exact hrep.balanceOf a
    · show ((bumpWorld w₂ vault).sload vault _).toNat = _
      rw [sload_bumpWorld (.inr hp.2)]; exact hrep.allowance o sp hp.1
  · -- asset: the `transferFrom` writes; the vault's writes are elsewhere
    have hr := rep_toToken (Erc20.view crypto Erc20.Layout.solmate w asset)
    obtain ⟨s', hms⟩ := Option.isSome_iff_exists.1
      ((transferFrom_isSome_iff hr vault caller vault assets).2 (by simp [abs, tokenView] at ht ⊢; simp [ht]))
    obtain ⟨e1, e2, e3, -⟩ := Erc20.view_transferFromWorld hbc hbv ha hms
    have hrep := rep_transferFrom hr hinv.1 hms ht
    have hview : Erc20.view crypto Erc20.Layout.solmate
        (depositWorld crypto w vault asset caller receiver assets shares) asset =
        Erc20.view crypto Erc20.Layout.solmate w₁ asset := by
      have hs : ∀ k, (depositWorld crypto w vault asset caller receiver assets shares).sload
          asset k = w₁.sload asset k := fun k => by
        simp only [depositWorld]
        rw [sload_bumpWorld (.inl hne.symm), sload_mintWorld (.inl hne.symm)]
      simp only [Erc20.view, hs]
    rw [hview]
    exact RepOn.of_eq e1 e2 (fun o sp hp => e3 o sp hp.1.1 hp.1.2 hp.2) hrep
  · -- the counter
    show ((bumpWorld w₂ vault).sload vault 7#256).toNat = c
    have hc' := hc
    simp only [Solmate.bump, checkedAdd] at hc'
    split at hc'
    · cases hc'
    · rename_i hle
      cases hc'
      have h7' : w₂.sload vault 7#256 = w.sload vault 7#256 := by
        rw [sload_mintWorld (.inr ⟨by decide, fun e => h7 e.symm⟩), hv₁]
      simp only [bumpWorld, World.sload_sstore_self, h7']
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt]
      · simp only [abs, BitVec.toNat_ofNat]; exact Nat.add_comm _ _
      · have hle' : (w.sload vault 7#256).toNat + 1 ≤ MAX := Nat.le_of_not_lt hle
        unfold MAX at hle'; simp only [BitVec.toNat_ofNat]; omega
  · show ((bumpWorld w₂ vault).sload vault 6#256).toNat = _
    rw [sload_bumpWorld (.inr (by decide)), sload_mintWorld (.inr ⟨by decide, fun e => h6 e.symm⟩),
      hv₁]
    rfl

end EvmLeanSpecs.Refinement

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault Shares

variable {crypto : Crypto} {w : World} {vault asset caller receiver : Address} {v : ℕ}

/-- `_mint` succeeds without supply overflow. -/
theorem shares_mint_some (h : (w.sload vault 2#256).toNat + v < 2 ^ 256) :
    ∃ sh, (abs crypto w vault asset).shares.mint receiver v = some sh :=
  ⟨_, Token.mint_eq_some.2 ⟨by simp only [abs, tokenView_totalSupply]; unfold MAX; omega, rfl⟩⟩

/-- The hook counter increments without overflow. -/
theorem bump_some (h : (w.sload vault 7#256).toNat + 1 < 2 ^ 256) :
    Solmate.bump (abs crypto w vault asset).afterDepositCount =
      some ((abs crypto w vault asset).afterDepositCount + 1) := by
  have h' : (abs crypto w vault asset).afterDepositCount + 1 < 2 ^ 256 := h
  have hM : ¬ MAX < (abs crypto w vault asset).afterDepositCount + 1 := by unfold MAX; omega
  simp only [Solmate.bump, checkedAdd, hM, ↓reduceIte]

/-- **Successful `deposit`, model side**: when every step of the bytecode succeeded, the model
succeeds with the same shares, and `depositWorld` represents its result. -/
theorem deposit_post_some {assets : Word} {t' : Token Address} (hne : vault ≠ asset)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : Erc20.BalanceSlotOk crypto Erc20.Layout.solmate caller)
    (hbv : Erc20.BalanceSlotOk crypto Erc20.Layout.solmate vault)
    (hbr : Erc20.BalanceSlotOk crypto Erc20.Layout.solmate receiver)
    (ha : Erc20.AllowanceSlotOk crypto Erc20.Layout.solmate caller vault)
    (hinv : Solmate.Inv (abs crypto w vault asset))
    (hpv : (abs crypto w vault asset).previewDeposit assets.toNat = some v) (hv0 : v ≠ 0)
    (hvlt : v < 2 ^ 256)
    (hT : (abs crypto w vault asset).asset.transferFrom vault caller vault assets.toNat = some t')
    (hov : (w.sload vault 2#256).toNat + v < 2 ^ 256)
    (hov7 : (w.sload vault 7#256).toNat + 1 < 2 ^ 256) :
    ∃ s', Solmate.deposit (abs crypto w vault asset) caller assets.toNat receiver = some (s', v) ∧
      RefinesAllow (DepositAllowances crypto receiver) (TransferFromAllowances crypto vault caller vault)
        crypto (depositWorld crypto w vault asset caller receiver assets (BitVec.ofNat 256 v))
        vault asset s' := by
  obtain ⟨sh, hm⟩ := shares_mint_some (asset := asset) (receiver := receiver) hov
  have hb := bump_some (crypto := crypto) (asset := asset) hov7
  refine ⟨_, deposit_some hpv hv0 hT hm hb, ?_⟩
  have hvn : (BitVec.ofNat 256 v).toNat = v := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  exact refinesAllow_depositWorld hne hk hbc hbv hbr ha hinv hT (by rw [hvn]; exact hm) hb

/-- **Successful `mint`, model side**: when every step of the bytecode succeeded, the model
succeeds with the same assets, and `depositWorld` represents its result. -/
theorem mint_post_some {shares : Word} {t' : Token Address} (hne : vault ≠ asset)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : Erc20.BalanceSlotOk crypto Erc20.Layout.solmate caller)
    (hbv : Erc20.BalanceSlotOk crypto Erc20.Layout.solmate vault)
    (hbr : Erc20.BalanceSlotOk crypto Erc20.Layout.solmate receiver)
    (ha : Erc20.AllowanceSlotOk crypto Erc20.Layout.solmate caller vault)
    (hinv : Solmate.Inv (abs crypto w vault asset))
    (hpv : (abs crypto w vault asset).previewMint shares.toNat = some v) (hvlt : v < 2 ^ 256)
    (hT : (abs crypto w vault asset).asset.transferFrom vault caller vault v = some t')
    (hov : (w.sload vault 2#256).toNat + shares.toNat < 2 ^ 256)
    (hov7 : (w.sload vault 7#256).toNat + 1 < 2 ^ 256) :
    ∃ s', Solmate.mint (abs crypto w vault asset) caller shares.toNat receiver = some (s', v) ∧
      RefinesAllow (DepositAllowances crypto receiver) (TransferFromAllowances crypto vault caller vault)
        crypto (depositWorld crypto w vault asset caller receiver (BitVec.ofNat 256 v) shares)
        vault asset s' := by
  obtain ⟨sh, hm⟩ := shares_mint_some (asset := asset) (receiver := receiver) hov
  have hb := bump_some (crypto := crypto) (asset := asset) hov7
  refine ⟨_, mint_some hpv hT hm hb, ?_⟩
  have hvn : (BitVec.ofNat 256 v).toNat = v := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  exact refinesAllow_depositWorld hne hk hbc hbv hbr ha hinv (by rw [hvn]; exact hT) hm hb

end EvmLeanSpecs.Refinement
