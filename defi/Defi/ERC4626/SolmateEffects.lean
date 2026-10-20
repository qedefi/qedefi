module

public import Defi.ERC4626.Solmate

/-!
# Effects of the Solmate vault operations

Characterisation lemmas: when an entry point succeeds, what it returned and how the two
ledgers changed. Everything downstream (invariants, rounding, round trips, inflation
attack) is proved from these.
-/

@[expose] public section

namespace EvmLeanSpecs.Vault.Solmate

open Token Finsupp

variable {A : Type} [DecidableEq A]

/-! ## Views -/

theorem convertToShares_eq_some {s : State A} {a n : ℕ} :
    s.convertToShares a = some n ↔
      (s.totalSupply = 0 ∧ n = a) ∨
      (s.totalSupply ≠ 0 ∧ s.totalAssets ≠ 0 ∧ a * s.totalSupply ≤ MAX ∧
        n = a * s.totalSupply / s.totalAssets) := by
  unfold State.convertToShares
  split_ifs with h
  · simp [h, eq_comm]
  · rw [mulDivDown_eq_some]; simp [h]

theorem convertToAssets_eq_some {s : State A} {n a : ℕ} :
    s.convertToAssets n = some a ↔
      (s.totalSupply = 0 ∧ a = n) ∨
      (s.totalSupply ≠ 0 ∧ n * s.totalAssets ≤ MAX ∧ a = n * s.totalAssets / s.totalSupply) := by
  unfold State.convertToAssets
  split_ifs with h
  · simp [h, eq_comm]
  · rw [mulDivDown_eq_some]; simp [h]

theorem previewMint_eq_some {s : State A} {n a : ℕ} :
    s.previewMint n = some a ↔
      (s.totalSupply = 0 ∧ a = n) ∨
      (s.totalSupply ≠ 0 ∧ n * s.totalAssets ≤ MAX ∧
        a = ceilDiv (n * s.totalAssets) s.totalSupply) := by
  unfold State.previewMint
  split_ifs with h
  · simp [h, eq_comm]
  · rw [mulDivUp_eq_some]; simp [h]

theorem previewWithdraw_eq_some {s : State A} {a n : ℕ} :
    s.previewWithdraw a = some n ↔
      (s.totalSupply = 0 ∧ n = a) ∨
      (s.totalSupply ≠ 0 ∧ s.totalAssets ≠ 0 ∧ a * s.totalSupply ≤ MAX ∧
        n = ceilDiv (a * s.totalSupply) s.totalAssets) := by
  unfold State.previewWithdraw
  split_ifs with h
  · simp [h, eq_comm]
  · rw [mulDivUp_eq_some]; simp [h]

/-! ## Entry points -/

theorem spendIfNotOwner_eq_some {t t' : Token A} {c o : A} {n : ℕ}
    (h : spendIfNotOwner t c o n = some t') :
    t'.balanceOf = t.balanceOf ∧ t'.totalSupply = t.totalSupply := by
  unfold spendIfNotOwner at h
  split_ifs at h
  · exact spend_eq_some h
  · cases h; exact ⟨rfl, rfl⟩

/-- What a successful `deposit` did. -/
theorem deposit_eq_some {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) :
    s.previewDeposit a = some n ∧ n ≠ 0 ∧ a ≤ s.asset.balanceOf c ∧
      s.totalSupply + n ≤ MAX ∧ s'.self = s.self ∧
      s'.asset.balanceOf = s.asset.balanceOf - single c a + single s.self a ∧
      s'.asset.totalSupply = s.asset.totalSupply ∧
      s'.shares.balanceOf = s.shares.balanceOf + single r n ∧
      s'.totalSupply = s.totalSupply + n := by
  unfold deposit at h
  obtain ⟨n', hp, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h with hz
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  obtain ⟨hv, hb, hs⟩ := transferFrom_eq_some ha
  obtain ⟨hmx, rfl⟩ := mint_eq_some.1 hm
  exact ⟨hp, hz, hv, hmx, rfl, hb, hs, rfl, rfl⟩

/-- What a successful `mint` did. -/
theorem mint_eq_some' {s s' : State A} {c r : A} {n a : ℕ}
    (h : mint s c n r = some (s', a)) :
    s.previewMint n = some a ∧ a ≤ s.asset.balanceOf c ∧
      s.totalSupply + n ≤ MAX ∧ s'.self = s.self ∧
      s'.asset.balanceOf = s.asset.balanceOf - single c a + single s.self a ∧
      s'.asset.totalSupply = s.asset.totalSupply ∧
      s'.shares.balanceOf = s.shares.balanceOf + single r n ∧
      s'.totalSupply = s.totalSupply + n := by
  unfold mint at h
  obtain ⟨a', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  obtain ⟨hv, hb, hs⟩ := transferFrom_eq_some ha
  obtain ⟨hmx, rfl⟩ := mint_eq_some.1 hm
  exact ⟨hp, hv, hmx, rfl, hb, hs, rfl, rfl⟩

/-- What a successful `withdraw` did. -/
theorem withdraw_eq_some {s s' : State A} {c r o : A} {a n : ℕ}
    (h : withdraw s c a r o = some (s', n)) :
    s.previewWithdraw a = some n ∧ n ≤ s.shares.balanceOf o ∧ a ≤ s.totalAssets ∧
      s'.self = s.self ∧
      s'.asset.balanceOf = s.asset.balanceOf - single s.self a + single r a ∧
      s'.asset.totalSupply = s.asset.totalSupply ∧
      s'.shares.balanceOf = s.shares.balanceOf - single o n ∧
      s'.totalSupply = s.totalSupply - n := by
  unfold withdraw at h
  obtain ⟨n', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  obtain ⟨e1, e2⟩ := spendIfNotOwner_eq_some hs1
  obtain ⟨hn, rfl⟩ := burn_eq_some.1 hb2
  obtain ⟨ha, rfl⟩ := transfer_eq_some.1 ht
  exact ⟨hp, e1 ▸ hn, ha, rfl, rfl, rfl, by simp [e1], by simp [State.totalSupply, e2]⟩

/-- What a successful `redeem` did. -/
theorem redeem_eq_some {s s' : State A} {c r o : A} {n a : ℕ}
    (h : redeem s c n r o = some (s', a)) :
    s.previewRedeem n = some a ∧ a ≠ 0 ∧ n ≤ s.shares.balanceOf o ∧ a ≤ s.totalAssets ∧
      s'.self = s.self ∧
      s'.asset.balanceOf = s.asset.balanceOf - single s.self a + single r a ∧
      s'.asset.totalSupply = s.asset.totalSupply ∧
      s'.shares.balanceOf = s.shares.balanceOf - single o n ∧
      s'.totalSupply = s.totalSupply - n := by
  unfold redeem at h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a', hp, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h with hz
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  obtain ⟨e1, e2⟩ := spendIfNotOwner_eq_some hs1
  obtain ⟨hn, rfl⟩ := burn_eq_some.1 hb2
  obtain ⟨ha, rfl⟩ := transfer_eq_some.1 ht
  exact ⟨hp, hz, e1 ▸ hn, ha, rfl, rfl, rfl, by simp [e1], by simp [State.totalSupply, e2]⟩

/-! ## Total assets after the asset moves -/

/-- Assets flowing in from a caller other than the vault raise `totalAssets` by the amount. -/
theorem totalAssets_in {s s' : State A} {c : A} {a : ℕ} (hc : c ≠ s.self)
    (hself : s'.self = s.self)
    (hb : s'.asset.balanceOf = s.asset.balanceOf - single c a + single s.self a) :
    s'.totalAssets = s.totalAssets + a := by
  simp only [State.totalAssets, hself, hb, move_apply_dst _ _ hc]

/-- Assets flowing out to a receiver other than the vault lower `totalAssets` by the amount. -/
theorem totalAssets_out {s s' : State A} {r : A} {a : ℕ} (hr : r ≠ s.self)
    (hself : s'.self = s.self)
    (hb : s'.asset.balanceOf = s.asset.balanceOf - single s.self a + single r a) :
    s'.totalAssets = s.totalAssets - a := by
  simp only [State.totalAssets, hself, hb, move_apply_src _ _ (Ne.symm hr)]

/-- Paying the vault itself (`receiver = self`) leaves `totalAssets` unchanged. -/
theorem totalAssets_out_self {s s' : State A} {a : ℕ} (ha : a ≤ s.totalAssets)
    (hself : s'.self = s.self)
    (hb : s'.asset.balanceOf = s.asset.balanceOf - single s.self a + single s.self a) :
    s'.totalAssets = s.totalAssets := by
  simp only [State.totalAssets, hself, hb, move_self ha]

/-! ## The invariant -/

theorem Inv_deposit {s s' : State A} {c r : A} {a n : ℕ} (hi : Inv s)
    (h : deposit s c a r = some (s', n)) : Inv s' := by
  unfold deposit at h
  obtain ⟨n', -, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨WF_transferFrom hi.1 ha, WF_mint hi.2 hm⟩

theorem Inv_mint {s s' : State A} {c r : A} {n a : ℕ} (hi : Inv s)
    (h : mint s c n r = some (s', a)) : Inv s' := by
  unfold mint at h
  obtain ⟨a', -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨WF_transferFrom hi.1 ha, WF_mint hi.2 hm⟩

theorem WF_spendIfNotOwner {t t' : Token A} {c o : A} {n : ℕ} (hw : t.WF)
    (h : spendIfNotOwner t c o n = some t') : t'.WF := by
  unfold spendIfNotOwner at h
  split_ifs at h
  · exact WF_spend hw h
  · cases h; exact hw

theorem Inv_withdraw {s s' : State A} {c r o : A} {a n : ℕ} (hi : Inv s)
    (h : withdraw s c a r o = some (s', n)) : Inv s' := by
  unfold withdraw at h
  obtain ⟨n', -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨WF_transfer hi.1 ht, WF_burn (WF_spendIfNotOwner hi.2 hs1) hb2⟩

theorem Inv_redeem {s s' : State A} {c r o : A} {n a : ℕ} (hi : Inv s)
    (h : redeem s c n r o = some (s', a)) : Inv s' := by
  unfold redeem at h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a', -, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨WF_transfer hi.1 ht, WF_burn (WF_spendIfNotOwner hi.2 hs1) hb2⟩

/-- Every external call preserves the invariant. -/
theorem Inv_step {s s' : State A} {op : Op A} (hi : Inv s) (h : step s op = some s') :
    Inv s' := by
  cases op with
  | deposit c a r =>
    obtain ⟨⟨s1, n⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact Inv_deposit hi h1
  | mint c n r =>
    obtain ⟨⟨s1, a⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact Inv_mint hi h1
  | withdraw c a r o =>
    obtain ⟨⟨s1, n⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact Inv_withdraw hi h1
  | redeem c n r o =>
    obtain ⟨⟨s1, a⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact Inv_redeem hi h1
  | transfer c d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨hi.1, WF_transfer hi.2 h1⟩
  | transferFrom c src d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨hi.1, WF_transferFrom hi.2 h1⟩
  | approve c sp v =>
    cases h; exact ⟨hi.1, WF_approve hi.2 _ _ _⟩
  | assetTransfer c d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨WF_transfer hi.1 h1, hi.2⟩
  | assetTransferFrom c src d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨WF_transferFrom hi.1 h1, hi.2⟩
  | assetApprove c sp v =>
    cases h; exact ⟨WF_approve hi.1 _ _ _, hi.2⟩
  | assetMint d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨WF_mint hi.1 h1, hi.2⟩
  | assetBurn src v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨WF_burn hi.1 h1, hi.2⟩

/-- **Multi-transaction invariant.** Any sequence of calls, by arbitrary callers with
arbitrary arguments, reverting or not, preserves `Inv`. -/
theorem Inv_exec {s : State A} (hi : Inv s) (ops : List (Op A)) : Inv (exec s ops) := by
  induction ops generalizing s with
  | nil => exact hi
  | cons op ops ih =>
    apply ih
    cases h : step s op with
    | none => exact hi
    | some s' => exact Inv_step hi h

/-- **INV-SUPPLY.** In every reachable state `totalSupply = Σ balanceOf` (shares) and the
asset ledger is consistent too. -/
theorem totalSupply_eq_sum_exec {s : State A} (hi : Inv s) (ops : List (Op A)) :
    (exec s ops).totalSupply = total (exec s ops).shares.balanceOf ∧
      (exec s ops).asset.totalSupply = total (exec s ops).asset.balanceOf :=
  ⟨((Inv_exec hi ops).2.1).symm, ((Inv_exec hi ops).1.1).symm⟩

/-- `self` never changes. -/
theorem self_step {s s' : State A} {op : Op A} (h : step s op = some s') : s'.self = s.self := by
  cases op with
  | deposit c a r =>
    obtain ⟨⟨s1, n⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact (deposit_eq_some h1).2.2.2.2.1
  | mint c n r =>
    obtain ⟨⟨s1, a⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact (mint_eq_some' h1).2.2.2.1
  | withdraw c a r o =>
    obtain ⟨⟨s1, n⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact (withdraw_eq_some h1).2.2.2.1
  | redeem c n r o =>
    obtain ⟨⟨s1, a⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    exact (redeem_eq_some h1).2.2.2.2.1
  | transfer | transferFrom | assetTransfer | assetTransferFrom | assetMint | assetBurn =>
    obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.1 h; rfl
  | approve | assetApprove => cases h; rfl

end EvmLeanSpecs.Vault.Solmate
