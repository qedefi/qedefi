import Examples.Solmate.ERC4626.SafeTransferFrom
import Examples.Solmate.ERC20.MintBurn
import EvmLogic.Solidity.Word
import Examples.Solmate.ERC4626.WithdrawInternal
import Examples.Solmate.ERC4626.ConvertGas
import Examples.Solmate.ERC4626.ViewsSpec
import Examples.Solmate.ERC4626.Withdraw

/-!
# The vault's `_mint` and `afterDeposit` as internal functions

After pulling the assets (`safeTransferFrom_wp`), `deposit` and `mint` jump to two internal
functions of the compiled vault (immutables `i`), summarised here once for both:

* `mintShares_wp`: Solmate `ERC20._mint(to, amount)` (entry `0x0fdc`, stack
  `amount :: to :: r :: rest`): `totalSupply += amount` (checked: on overflow `Panic(0x11)`),
  `balanceOf[to] += amount` (unchecked), `emit Transfer(0, to, amount)` (the topic is
  `CODECOPY`d); the world is `mintWorld` (shared with the asset's `mint`, `AssetMint`);
* `afterDeposit_wp`: `MockERC4626.afterDeposit` (entry `0x1033`): the checked
  `afterDepositHookCalledCounter++` (slot 7); the world is `bumpWorld`.

Both work on memory in the shape `FmpAfterTransfer` (free pointer `0x80` / `0xa0`) and keep it.
`readBytes_code_asset2014` / `readBytes_code_asset2169` read the `asset` immutable at the
`PUSH32`s of `deposit` and `mint`.
-/

section

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault Shares

/-- The `asset` immutable, as the `PUSH32` at `0x07dd` (in `deposit`) reads it. -/
theorem readBytes_code_asset2014 (i : SolmateVault.Immutables) :
    readBytes (SolmateVault.runtimeCodeWith i) 2014 32 = Bytes.ofWord (Word.ofAddress i.asset) := by
  have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
      (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset)] ++
      (2014, Word.ofAddress i.asset) :: [(2169, Word.ofAddress i.asset),
      (2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
  simp only [SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

/-- The `asset` immutable, as the `PUSH32` at `0x0878` (in `mint`) reads it. -/
theorem readBytes_code_asset2169 (i : SolmateVault.Immutables) :
    readBytes (SolmateVault.runtimeCodeWith i) 2169 32 = Bytes.ofWord (Word.ofAddress i.asset) := by
  have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
      (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset),
      (2014, Word.ofAddress i.asset)] ++ (2169, Word.ofAddress i.asset) ::
      [(2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
  simp only [SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

set_option maxHeartbeats 0 in
/-- **`_mint(to, amount)` (internal, entry `0x0fdc`)**: without supply overflow it returns to
`r` with the world `mintWorld` (at most 55000 gas); on overflow it reverts. -/
theorem mintShares_wp {i : SolmateVault.Immutables} (m : Machine) {amount r : Word}
    {dst : Address} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hstatic : m.frame.msg.isStatic = false)
    (hpc : m.frame.pc = 0xfdc)
    (hs : m.frame.stack = amount :: Word.ofAddress dst :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpAfterTransfer m.frame.memory)
    (hg : 60000 ≤ m.frame.gasLeft) :
    WP m (fun m' => (m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat < 2 ^ 256 ∧
        ∃ mem g rd sub,
          m' = { m.resumeWith r.toNat rest mem g rd sub with
            world := mintWorld m.ctx.crypto m.world m.frame.msg.currentTarget dst amount } ∧
          FmpAfterTransfer mem ∧ m.frame.gasLeft ≤ g + 55000)
      (fun _ o => 2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat ∧
        ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩ <;>
  · pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress]
    by_cases hov : (m_world.sload m_msg.currentTarget 2#256).toNat + amount.toNat < 2 ^ 256
    · simp only [gt_add_self_of_lt hov, iszero_zero]
      pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      pwp_codecopy
      pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      refine WP.ret ⟨hov, _, _, _, _, rfl, ?_, ?_⟩
      · unfold FmpAfterTransfer
        simp (disch := decide) only [Memory.loadWord_storeWord_of_disjoint,
          Memory.loadWord_expand, hfmp, Memory.size_storeWord, Memory.size_expand, hsize,
          Memory.wordsAfter, Memory.words, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
          Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def, ↓reduceIte]
        decide
      · evm_gas
    · simp only [gt_add_self_of_le (Nat.le_of_not_lt hov), iszero_one]
      pwp_steps [hfmp, hsize]
      exact ⟨Nat.le_of_not_lt hov, _, rfl⟩

/-- The world after `afterDepositHookCalledCounter++` (slot 7 of the vault). -/
def bumpWorld (w : World) (vault : Address) : World :=
  w.sstore vault 7#256 (1#256 + w.sload vault 7#256)

set_option maxHeartbeats 0 in
/-- **`afterDeposit(assets, shares)` (internal, entry `0x1033`)**: without counter overflow it
returns to `r` with the world `bumpWorld` (at most 30000 gas); at `type(uint256).max` it
reverts. -/
theorem afterDeposit_wp {i : SolmateVault.Immutables} (m : Machine) {x y r : Word}
    {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hstatic : m.frame.msg.isStatic = false)
    (hpc : m.frame.pc = 0x1033)
    (hs : m.frame.stack = x :: y :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpAfterTransfer m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) :
    WP m (fun m' => (m.world.sload m.frame.msg.currentTarget 7#256).toNat + 1 < 2 ^ 256 ∧
        ∃ g sub,
          m' = { m.resumeWith r.toNat rest m.frame.memory g m.frame.returnData sub with
            world := bumpWorld m.world m.frame.msg.currentTarget } ∧
          m.frame.gasLeft ≤ g + 30000)
      (fun _ o => (m.world.sload m.frame.msg.currentTarget 7#256).toNat + 1 = 2 ^ 256 ∧
        ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  pwp_steps
  by_cases hov : (m_world.sload m_msg.currentTarget 7#256).toNat + 1 < 2 ^ 256
  · have hne := add_one_ne_zero_of_lt hov
    pwp_steps
    exact WP.ret ⟨hov, _, _, rfl, by evm_gas⟩
  · have he : (m_world.sload m_msg.currentTarget 7#256).toNat + 1 = 2 ^ 256 := by
      have := (m_world.sload m_msg.currentTarget 7#256).isLt; omega
    simp only [add_one_eq_zero_of_eq he]
    rcases hmem with ⟨-, hsize⟩ | ⟨-, hsize⟩ <;>
    · pwp_steps [hsize]
      exact ⟨he, _, rfl⟩

end EvmLeanSpecs.Refinement

end

section

/-!
## `deposit` / `mint`: the world they produce, seen through the abstraction

Both entry points do the same three writes, in this order (Solmate `ERC4626` with
`MockERC4626`'s hook):

1. the asset's `transferFrom(caller, vault, assets)` with the vault as spender
   (`Erc20.transferFromWorld` on the asset's storage, `safeTransferFrom_wp`);
2. `_mint(receiver, shares)` on the vault's storage (`mintWorld`, `mintShares_wp`):
   `totalSupply += shares` (checked), `balanceOf[receiver] += shares`;
3. `afterDepositHookCalledCounter++` (slot 7, checked; `bumpWorld`, `afterDeposit_wp`).

`depositWorld` is that world. `refinesOn_depositWorld` relates it to the model: when the
model's `Token.transferFrom` of the asset ledger, `Token.mint` of the share ledger and `bump`
of the counter all succeed, the world after the three writes represents the model's new state
(`Out.RefinesOn`: both ledgers as `Shares.RepOn`, the two counters exactly).

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
  simp only [Erc20.transferFromWorld]
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
    EvmLean.Solidity.Erc20.transferWorld, Erc20.spendWorld]
  split <;> simp

/-- **The world after `deposit` / `mint` represents the model's new state.** -/
theorem refinesOn_depositWorld {crypto : Crypto} {w : World} {vault asset caller receiver : Address}
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
    Out.RefinesOn (DepositAllowances crypto receiver) (TransferFromAllowances crypto vault caller vault)
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
      Out.RefinesOn (DepositAllowances crypto receiver) (TransferFromAllowances crypto vault caller vault)
        crypto (depositWorld crypto w vault asset caller receiver assets (BitVec.ofNat 256 v))
        vault asset s' := by
  obtain ⟨sh, hm⟩ := shares_mint_some (asset := asset) (receiver := receiver) hov
  have hb := bump_some (crypto := crypto) (asset := asset) hov7
  refine ⟨_, deposit_some hpv hv0 hT hm hb, ?_⟩
  have hvn : (BitVec.ofNat 256 v).toNat = v := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  exact refinesOn_depositWorld hne hk hbc hbv hbr ha hinv hT (by rw [hvn]; exact hm) hb

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
      Out.RefinesOn (DepositAllowances crypto receiver) (TransferFromAllowances crypto vault caller vault)
        crypto (depositWorld crypto w vault asset caller receiver (BitVec.ofNat 256 v) shares)
        vault asset s' := by
  obtain ⟨sh, hm⟩ := shares_mint_some (asset := asset) (receiver := receiver) hov
  have hb := bump_some (crypto := crypto) (asset := asset) hov7
  refine ⟨_, mint_some hpv hT hm hb, ?_⟩
  have hvn : (BitVec.ofNat 256 v).toNat = v := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  exact refinesOn_depositWorld hne hk hbc hbv hbr ha hinv (by rw [hvn]; exact hT) hm hb

end EvmLeanSpecs.Refinement

end

section

/-!
## `deposit(assets, receiver)` refines the model, in any frame

`deposit_refines`: the compiled vault (any immutables `i`), run in any frame satisfying
`ViewPre i` that is non-static and has at least 250000 gas (top level or called by another
contract), on calldata `deposit(assets, receiver)` (`TwoWordCall`, so also calldata assembled
by a calling contract), ends as the model's `Solmate.deposit` of `absOf i.asset m` says
(`EntryPost`): on `some (s', shares)` it returns the ABI word of `shares`, the world is
`depositWorld` and represents `s'`; on `none` it reverts (and the frame's rollback restores
the world).

The proof composes, by `WP.bind_mono`, the dispatcher and ABI decoder (symbolic execution),
`convertToShares_wp_gas` (`previewDeposit`), the `ZERO_SHARES` check, `safeTransferFrom_wp`
(the `CALL` into the asset), `mintShares_wp`, the `Deposit` event, `afterDeposit_wp` and the
return encoder; each revert point is matched with the model step that fails
(`deposit_none_*`), and the success case with `deposit_post_some`.

Hypotheses beyond `ViewPre`: the vault is not the asset; the hash hypotheses of
`DepositModel` (fresh balance slots of caller, vault, receiver; fresh `allowance[caller][vault]`
of the asset; no balance slot is 2, 6 or 7); `Solmate.Inv` of the model state.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault Shares

/-- How a call of `deposit` / `mint` ends, by cases on the model's result `r`: on `some (s', v)`
it returns the ABI word of `v`, the world is `W v`, and the world represents `s'` (allowances of
the shares on `P`, of the asset on `Q`); on `none` it reverts. -/
def EntryPost (m : Machine) (asset : Address) (P Q : Address → Address → Prop)
    (W : ℕ → World) (r : Option (Solmate.State Address × ℕ)) (mf : Machine) (o : Outcome) :
    Prop :=
  match r with
  | some (s', v) => o = .success (Bytes.ofWord (BitVec.ofNat 256 v)) ∧ mf.world = W v ∧
      Out.RefinesOn P Q m.ctx.crypto mf.world m.frame.msg.currentTarget asset s'
  | none => ∃ out, o = .revert out

set_option maxHeartbeats 0 in
/-- **`deposit(assets, receiver)` refines `Solmate.deposit`**, in any frame. -/
theorem deposit_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m)
    (hstatic : m.frame.msg.isStatic = false) (hgas : 250000 ≤ m.frame.gasLeft)
    {assets : Word} {receiver : Address}
    (hd : TwoWordCall m.frame.msg.data 0x6e553f65 assets (Word.ofAddress receiver))
    (hne : m.frame.msg.currentTarget ≠ i.asset)
    (hk : KeccakAvoids m.ctx.crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller)
    (hbv : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate m.frame.msg.currentTarget)
    (hbr : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate receiver)
    (ha : Erc20.AllowanceSlotOk m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller
      m.frame.msg.currentTarget)
    (hinv : Solmate.Inv (absOf i.asset m)) :
    Halts m (EntryPost m i.asset (DepositAllowances m.ctx.crypto receiver)
      (TransferFromAllowances m.ctx.crypto m.frame.msg.currentTarget m.frame.msg.caller
        m.frame.msg.currentTarget)
      (fun v => depositWorld m.ctx.crypto m.world m.frame.msg.currentTarget i.asset
        m.frame.msg.caller receiver assets (BitVec.ofNat 256 v))
      (Solmate.deposit (absOf i.asset m) m.frame.msg.caller assets.toNat receiver)) := by
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  have hprev : (absOf i.asset m).previewDeposit assets.toNat =
      convertToSharesN (supplyOf m).toNat (assetsOf i.asset m).toNat assets.toNat :=
    absOf_convertToShares _ _ _
  have hassets : assets.toNat < 2 ^ 256 := assets.isLt
  obtain ⟨h2, h6, h7⟩ := balanceSlot_ne_fixed hk receiver
  generalize hr : Solmate.deposit (absOf i.asset m) m.frame.msg.caller assets.toNat receiver = res
  view_intro
  simp only [absOf] at hr hprev hinv
  pwp_run_to 0xbda [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
  refine WP.bind_mono (convertToShares_wp_gas _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    rw [deposit_none_preview (hprev.trans hnone)] at hr
    subst hr
    exact ⟨_, hrev.1⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1, hg1u⟩
  have hpv := hprev.trans hv
  have hvlt := convertToSharesN_lt hassets hv
  clear hv hprev
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 hg1u ⊢
  pwp_steps
  by_cases hv0 : v = 0
  · subst hv0
    rw [deposit_none_zero hpv] at hr
    subst hr
    rcases hmem' with ⟨hfmp, hsz⟩ | ⟨hfmp, hsz⟩ <;>
    · pwp_steps [hfmp, hsz]
      exact ⟨_, rfl⟩
  · have hne0 : (0#256 - BitVec.ofNat 256 v) ≠ 0#256 := by
      intro he
      apply hv0
      have := congrArg BitVec.toNat (sub_eq_zero.1 he).symm
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt] at this
      simpa using this
    pwp_run_to 0xf38 [readBytes_code_asset2014, ofAddress_and_addressMask,
      addressMask_and_ofAddress]
    refine WP.bind_mono (safeTransferFrom_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ hstatic rfl rfl
      (by simp) (by pjumpdest_disch) hmem' (by dsimp only; omega) (by dsimp only; omega)
      hbc hbv ha hinv.1) ?_ ?_
    · rintro mf o - ⟨hT, out, ho⟩
      rw [deposit_none_transfer hpv hT] at hr
      subst hr
      exact ⟨_, ho⟩
    rintro m2 - ⟨t', hT, hrepA, mem2, g2, rd2, sub2, rfl, hmem2, hg2⟩
    simp only [Machine.resumeWith, BitVec.reduceToNat] at hg2 ⊢
    pwp_run_to 0xfdc
    have hS : (Erc20.transferFromWorld m_ctx.crypto m_world i.asset m_msg.currentTarget m_msg.caller
        m_msg.currentTarget assets).sload m_msg.currentTarget 2#256 =
        m_world.sload m_msg.currentTarget 2#256 := sload_transferFromWorld_ne hne _
    have hvn : (BitVec.ofNat 256 v).toNat = v := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
    refine WP.bind_mono (mintShares_wp _ rfl hj hstatic rfl rfl (by simp) (by pjumpdest_disch)
      hmem2 (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hov, out, ho⟩
      rw [deposit_none_mint hpv hv0 hT (token_mint_none_iff.2 ?_)] at hr
      · subst hr
        exact ⟨_, ho⟩
      · dsimp only at hov
        rw [hS, hvn] at hov
        exact hov
    rintro m3 - ⟨hov, mem3, g3, rd3, sub3, rfl, hmem3, hg3⟩
    simp only [Machine.resumeWith, BitVec.reduceToNat] at hg3 hov ⊢
    rw [hS, hvn] at hov
    rcases hmem3 with ⟨hfmp3, hsz3⟩ | ⟨hfmp3, hsz3⟩ <;>
    · pwp_run_to 0x1033 [hfmp3, hsz3]
      have h7w : (mintWorld m_ctx.crypto (Erc20.transferFromWorld m_ctx.crypto m_world i.asset
          m_msg.currentTarget m_msg.caller m_msg.currentTarget assets) m_msg.currentTarget receiver
          (BitVec.ofNat 256 v)).sload m_msg.currentTarget 7#256 =
          m_world.sload m_msg.currentTarget 7#256 := by
        rw [sload_mintWorld (.inr ⟨by decide, fun e => h7 e.symm⟩), sload_transferFromWorld_ne hne]
      refine WP.bind_mono (afterDeposit_wp _ rfl hj hstatic rfl rfl (by simp) (by pjumpdest_disch)
        ?_ (by evm_gas)) ?_ ?_
      · unfold FmpAfterTransfer
        simp (disch := decide) only [Memory.loadWord_storeWord_of_disjoint,
          Memory.loadWord_expand, hfmp3, Memory.size_storeWord, Memory.size_expand, hsz3,
          Memory.wordsAfter, Memory.words, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
          Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def, ↓reduceIte]
        decide
      · rintro mf o - ⟨hov7, out, ho⟩
        dsimp only at hov7
        rw [h7w] at hov7
        rw [deposit_none_bump hpv hT (bump_none_iff.2 (.inl hov7))] at hr
        subst hr
        exact ⟨_, ho⟩
      rintro m4 - ⟨hov7, g4, sub4, rfl, hg4⟩
      simp only [Machine.resumeWith, BitVec.reduceToNat] at hg4 hov7 ⊢
      rw [h7w] at hov7
      pwp_steps [hfmp3, hsz3]
      obtain ⟨s', hdep', hR⟩ := deposit_post_some (crypto := m_ctx.crypto) (w := m_world)
        (vault := m_msg.currentTarget) (asset := i.asset) (caller := m_msg.caller)
        (receiver := receiver) hne hk hbc hbv hbr ha hinv hpv hv0 hvlt hT hov hov7
      rw [hdep'] at hr
      subst hr
      exact ⟨rfl, rfl, hR⟩

end EvmLeanSpecs.Refinement

end

section

/-!
## `mint(shares, receiver)` refines the model, in any frame

`mint_refines`: as `deposit_refines`, for `mint(shares, receiver)`: `previewMint_wp_gas`
(rounding up; no zero check), `safeTransferFrom_wp` of the previewed assets, `mintShares_wp` of
`shares`, the `Deposit` event, `afterDeposit_wp`. On the model's `some (s', assets)` the call
returns the ABI word of `assets`, the world is `depositWorld` and represents `s'`; on `none`
it reverts. Same hypotheses as `deposit_refines`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault Shares

set_option maxHeartbeats 0 in
/-- **`mint(shares, receiver)` refines `Solmate.mint`**, in any frame. -/
theorem mint_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m)
    (hstatic : m.frame.msg.isStatic = false) (hgas : 250000 ≤ m.frame.gasLeft)
    {shares : Word} {receiver : Address}
    (hd : TwoWordCall m.frame.msg.data 0x94bf804d shares (Word.ofAddress receiver))
    (hne : m.frame.msg.currentTarget ≠ i.asset)
    (hk : KeccakAvoids m.ctx.crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller)
    (hbv : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate m.frame.msg.currentTarget)
    (hbr : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate receiver)
    (ha : Erc20.AllowanceSlotOk m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller
      m.frame.msg.currentTarget)
    (hinv : Solmate.Inv (absOf i.asset m)) :
    Halts m (EntryPost m i.asset (DepositAllowances m.ctx.crypto receiver)
      (TransferFromAllowances m.ctx.crypto m.frame.msg.currentTarget m.frame.msg.caller
        m.frame.msg.currentTarget)
      (fun v => depositWorld m.ctx.crypto m.world m.frame.msg.currentTarget i.asset
        m.frame.msg.caller receiver (BitVec.ofNat 256 v) shares)
      (Solmate.mint (absOf i.asset m) m.frame.msg.caller shares.toNat receiver)) := by
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  have hprev : (absOf i.asset m).previewMint shares.toNat =
      previewMintN (supplyOf m).toNat (assetsOf i.asset m).toNat shares.toNat :=
    absOf_previewMint _ _ _
  have hshares : shares.toNat < 2 ^ 256 := shares.isLt
  obtain ⟨h2, h6, h7⟩ := balanceSlot_ne_fixed hk receiver
  generalize hr : Solmate.mint (absOf i.asset m) m.frame.msg.caller shares.toNat receiver = res
  view_intro
  simp only [absOf] at hr hprev hinv
  pwp_run_to 0x96b [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
  refine WP.bind_mono (previewMint_wp_gas _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    rw [mint_none_preview (hprev.trans hnone)] at hr
    subst hr
    exact ⟨_, hrev.1⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1, hg1u⟩
  have hpv := hprev.trans hv
  have hvlt := previewMintN_lt hshares hv
  have hvn : (BitVec.ofNat 256 v).toNat = v := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  clear hv hprev
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 hg1u ⊢
  pwp_run_to 0xf38 [readBytes_code_asset2169, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  refine WP.bind_mono (safeTransferFrom_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ hstatic rfl rfl
    (by simp) (by pjumpdest_disch) hmem' (by dsimp only; omega) (by dsimp only; omega)
    hbc hbv ha hinv.1) ?_ ?_
  · rintro mf o - ⟨hT, out, ho⟩
    rw [hvn] at hT
    rw [mint_none_transfer hpv hT] at hr
    subst hr
    exact ⟨_, ho⟩
  rintro m2 - ⟨t', hT, hrepA, mem2, g2, rd2, sub2, rfl, hmem2, hg2⟩
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg2 ⊢
  rw [hvn] at hT
  pwp_run_to 0xfdc
  have hS : (Erc20.transferFromWorld m_ctx.crypto m_world i.asset m_msg.currentTarget m_msg.caller
      m_msg.currentTarget (BitVec.ofNat 256 v)).sload m_msg.currentTarget 2#256 =
      m_world.sload m_msg.currentTarget 2#256 := sload_transferFromWorld_ne hne _
  refine WP.bind_mono (mintShares_wp _ rfl hj hstatic rfl rfl (by simp) (by pjumpdest_disch)
    hmem2 (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hov, out, ho⟩
    rw [mint_none_mint hpv (token_mint_none_iff.2 ?_)] at hr
    · subst hr
      exact ⟨_, ho⟩
    · dsimp only at hov
      rw [hS] at hov
      exact hov
  rintro m3 - ⟨hov, mem3, g3, rd3, sub3, rfl, hmem3, hg3⟩
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg3 hov ⊢
  rw [hS] at hov
  rcases hmem3 with ⟨hfmp3, hsz3⟩ | ⟨hfmp3, hsz3⟩ <;>
  · pwp_run_to 0x1033 [hfmp3, hsz3]
    have h7w : (mintWorld m_ctx.crypto (Erc20.transferFromWorld m_ctx.crypto m_world i.asset
        m_msg.currentTarget m_msg.caller m_msg.currentTarget (BitVec.ofNat 256 v)) m_msg.currentTarget
        receiver shares).sload m_msg.currentTarget 7#256 =
        m_world.sload m_msg.currentTarget 7#256 := by
      rw [sload_mintWorld (.inr ⟨by decide, fun e => h7 e.symm⟩), sload_transferFromWorld_ne hne]
    refine WP.bind_mono (afterDeposit_wp _ rfl hj hstatic rfl rfl (by simp) (by pjumpdest_disch)
      ?_ (by evm_gas)) ?_ ?_
    · unfold FmpAfterTransfer
      simp (disch := decide) only [Memory.loadWord_storeWord_of_disjoint,
        Memory.loadWord_expand, hfmp3, Memory.size_storeWord, Memory.size_expand, hsz3,
        Memory.wordsAfter, Memory.words, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
        Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def, ↓reduceIte]
      decide
    · rintro mf o - ⟨hov7, out, ho⟩
      dsimp only at hov7
      rw [h7w] at hov7
      rw [mint_none_bump hpv (bump_none_iff.2 (.inl hov7))] at hr
      subst hr
      exact ⟨_, ho⟩
    rintro m4 - ⟨hov7, g4, sub4, rfl, hg4⟩
    simp only [Machine.resumeWith, BitVec.reduceToNat] at hg4 hov7 ⊢
    rw [h7w] at hov7
    pwp_steps [hfmp3, hsz3]
    obtain ⟨s', hdep', hR⟩ := mint_post_some (crypto := m_ctx.crypto) (w := m_world)
      (vault := m_msg.currentTarget) (asset := i.asset) (caller := m_msg.caller)
      (receiver := receiver) hne hk hbc hbv hbr ha hinv hpv hvlt hT hov hov7
    rw [hdep'] at hr
    subst hr
    exact ⟨rfl, rfl, hR⟩


end EvmLeanSpecs.Refinement

end

section

/-!
## `deposit` and `mint` as top-level transactions

`deposit_call`, `mint_call`: a top-level call (`processMessageCall`, any `Crypto`, any context
before Prague or without EIP-7702 authorizations, any transient storage and warm sets, enough
fuel) of `deposit(assets, receiver)` / `mint(shares, receiver)` on the vault `Deployed` at
`vault` (any immutables) over the asset at `asset`, with `Abi.encodeCall` calldata, refines the
model operation on `abs ctx.crypto w vault asset` (`EntryResult`):

* model `some (s', v)`: the call succeeds, returns the ABI word of `v` (shares minted /
  assets pulled), the world is `depositWorld` (exact), and it represents `s'`
  (`Out.RefinesOn`);
* model `none`: the call reverts and the world is unchanged.

They are `deposit_refines` / `mint_refines` (frame form) at the start machine, through
`entry_call` (as `view_call` and `out_call` do for the views and withdraw/redeem).
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault Shares

/-- What a top-level `deposit` / `mint` returns, against the model's result `r`: on
`some (s', v)` success with the ABI word of `v`, the world `W v`, representing `s'`; on `none`
a revert with the world unchanged. -/
def EntryResult (crypto : Crypto) (w : World) (vault asset : Address)
    (P Q : Address → Address → Prop) (W : ℕ → World) (res : MessageResult)
    (r : Option (Solmate.State Address × ℕ)) : Prop :=
  match r with
  | some (s', v) => res.success = true ∧ res.output = Bytes.ofWord (BitVec.ofNat 256 v) ∧
      res.world = W v ∧ Out.RefinesOn P Q crypto res.world vault asset s'
  | none => res.success = false ∧ res.reverted = true ∧ res.world = w

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

set_option maxHeartbeats 1000000 in
/-- A frame summary of a top-level call to the vault, in the form `EntryPost`, gives the
result of `processMessageCall`. -/
theorem entry_call {i : SolmateVault.Immutables} {P Q : Address → Address → Prop}
    {W : ℕ → World} {r : Option (Solmate.State Address × ℕ)}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false)
    (h : Halts (startMachine ctx w tr
        (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk))
      (EntryPost (startMachine ctx w tr
        (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk)) asset P Q W r)) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk) = .ok res ∧
      EntryResult ctx.crypto w vault asset P Q W res r := by
  have hdel : delegatedAddress?
      (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk).code = none :=
    Shares.delegatedAddress?_code i
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := vault) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, hH, hs, hrun⟩ := hn fuel hle
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  refine ⟨_, hrun, ?_⟩
  unfold EntryPost at hH
  unfold EntryResult
  split at hH
  · obtain ⟨ho, hW, hR⟩ := hH
    subst ho
    obtain ⟨h1, h2, h3, -⟩ := topLevelResult_success_call (t := (callMsg
      (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk).target)
      (out := Bytes.ofWord _) hk
    exact ⟨h1, h2, h3.trans hW, h3 ▸ hR⟩
  · obtain ⟨out, ho⟩ := hH
    subst ho
    have hsnap : mf.frame.snapshot.1 = w := by rw [hs.snapshot]; rfl
    simp only [frameResult_revert, topLevelResult_world, topLevelResult_success,
      topLevelResult_reverted, ChildResult.success, hsnap]
    decide

/-- `Abi.encodeCall sel [x, y]` is a `TwoWordCall`. -/
theorem twoWordCall_encodeCall' {sel : Nat} (hsel : sel < 2 ^ 32) (x y : Word) :
    TwoWordCall (Abi.encodeCall sel [x, y]) sel x y :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _,
   Abi.calldataload_encodeCall_1 _ _ _ _⟩

/-- **`deposit(assets, receiver)` as a top-level transaction** on the deployed vault: refines
`Solmate.deposit` of the model state read from the world. -/
theorem deposit_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 250000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver : Address}
    (hk : KeccakAvoids ctx.crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate caller)
    (hbv : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate vault)
    (hbr : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate receiver)
    (ha : Erc20.AllowanceSlotOk ctx.crypto Erc20.Layout.solmate caller vault)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (assets : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0x6e553f65 [assets, Word.ofAddress receiver]) gas wa wk) = .ok res ∧
      EntryResult ctx.crypto w vault asset (DepositAllowances ctx.crypto receiver)
        (TransferFromAllowances ctx.crypto vault caller vault)
        (fun v => depositWorld ctx.crypto w vault asset caller receiver assets
          (BitVec.ofNat 256 v)) res
        (Solmate.deposit (abs ctx.crypto w vault asset) caller assets.toNat receiver) := by
  have hne := hdep.asset_ne
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := deposit_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile (by omega) hgas' (by rw [Abi.size_encodeCall]; simp))
    rfl hgas (twoWordCall_encodeCall' (by decide) assets _) hne.symm hk hbc hbv hbr ha hinv
  exact entry_call hdeleg (hdep.vaultNotPrecompile _) hm

/-- **`mint(shares, receiver)` as a top-level transaction** on the deployed vault: refines
`Solmate.mint` of the model state read from the world. -/
theorem mint_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 250000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver : Address}
    (hk : KeccakAvoids ctx.crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate caller)
    (hbv : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate vault)
    (hbr : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate receiver)
    (ha : Erc20.AllowanceSlotOk ctx.crypto Erc20.Layout.solmate caller vault)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (shares : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0x94bf804d [shares, Word.ofAddress receiver]) gas wa wk) = .ok res ∧
      EntryResult ctx.crypto w vault asset (DepositAllowances ctx.crypto receiver)
        (TransferFromAllowances ctx.crypto vault caller vault)
        (fun v => depositWorld ctx.crypto w vault asset caller receiver (BitVec.ofNat 256 v)
          shares) res
        (Solmate.mint (abs ctx.crypto w vault asset) caller shares.toNat receiver) := by
  have hne := hdep.asset_ne
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := mint_refines _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile (by omega) hgas' (by rw [Abi.size_encodeCall]; simp))
    rfl hgas (twoWordCall_encodeCall' (by decide) shares _) hne.symm hk hbc hbv hbr ha hinv
  exact entry_call hdeleg (hdep.vaultNotPrecompile _) hm

end EvmLeanSpecs.Refinement

end
