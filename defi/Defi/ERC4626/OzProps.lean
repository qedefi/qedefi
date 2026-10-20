module

public import Defi.ERC4626.Oz
public import Defi.Math.RoundTripAlgebra

/-!
# Properties of the OpenZeppelin vault

The same catalogue as `SolmateProps.lean`, for the OpenZeppelin model with decimals offset
`δ` and `k = 10^δ` virtual shares. Write `T̂ = totalAssets + 1` and `Ŝ = totalSupply + k`
for the *virtual* totals; all conversions are `mulDiv`s by `Ŝ/T̂` or `T̂/Ŝ`.

Because `Ŝ, T̂ > 0` always, every property that needed `totalSupply > 0` for Solmate holds
here unconditionally: the price `T̂/Ŝ` is monotone through every vault operation, and all
eight a16z round trips hold in every state (including an empty or drained vault).
-/

@[expose] public section

namespace EvmLeanSpecs.Vault.Oz

open Token Finsupp

variable {A : Type} [DecidableEq A] [Zero A] {δ : ℕ}

namespace State

/-- Virtual supply `Ŝ = totalSupply + 10^δ`. -/
def vS (δ : ℕ) (s : State A) : ℕ := s.totalSupply + 10 ^ δ

/-- Virtual assets `T̂ = totalAssets + 1`. -/
def vT (s : State A) : ℕ := s.totalAssets + 1

/-- The virtual exchange rate `T̂ / Ŝ` (assets per share). -/
def price (δ : ℕ) (s : State A) : ℚ := (s.vT : ℚ) / s.vS δ

theorem vS_pos (s : State A) : 0 < s.vS δ := by unfold vS; positivity

theorem vT_pos (s : State A) : 0 < s.vT := by unfold vT; omega

end State

/-! ## Views -/

theorem toShares_eq_some {s : State A} {a n : ℕ} {up : Bool} :
    s.toShares δ a up = some n ↔
      s.vS δ ≤ MAX ∧ s.vT ≤ MAX ∧ n ≤ MAX ∧
        n = (if up then ceilDiv (a * s.vS δ) s.vT else a * s.vS δ / s.vT) := by
  unfold State.toShares State.vS State.vT checkedAdd
  by_cases h1 : MAX < s.totalSupply + 10 ^ δ
  · simp only [h1, ↓reduceIte, Option.bind_none, reduceCtorEq, false_iff, not_and]
    omega
  by_cases h2 : MAX < s.totalAssets + 1
  · simp only [h1, h2, ↓reduceIte, Option.bind_some, Option.bind_none, reduceCtorEq,
      false_iff, not_and]
    omega
  simp only [h1, h2, ↓reduceIte, Option.bind_some, ozMulDiv_eq_some]
  constructor
  · rintro ⟨-, h3, h4⟩; exact ⟨by omega, by omega, h3, h4⟩
  · rintro ⟨-, -, h3, h4⟩; exact ⟨by omega, h3, h4⟩

theorem toAssets_eq_some {s : State A} {n a : ℕ} {up : Bool} :
    s.toAssets δ n up = some a ↔
      s.vT ≤ MAX ∧ s.vS δ ≤ MAX ∧ a ≤ MAX ∧
        a = (if up then ceilDiv (n * s.vT) (s.vS δ) else n * s.vT / s.vS δ) := by
  unfold State.toAssets State.vS State.vT checkedAdd
  by_cases h1 : MAX < s.totalAssets + 1
  · simp only [h1, ↓reduceIte, Option.bind_none, reduceCtorEq, false_iff, not_and]
    omega
  by_cases h2 : MAX < s.totalSupply + 10 ^ δ
  · simp only [h1, h2, ↓reduceIte, Option.bind_some, Option.bind_none, reduceCtorEq,
      false_iff, not_and]
    omega
  simp only [h1, h2, ↓reduceIte, Option.bind_some, ozMulDiv_eq_some]
  constructor
  · rintro ⟨-, h3, h4⟩; exact ⟨by omega, by omega, h3, h4⟩
  · rintro ⟨-, -, h3, h4⟩; exact ⟨by positivity, h3, h4⟩

/-! ## Entry points -/

theorem spendIfNotOwner_eq_some {t t' : Token A} {c o : A} {n : ℕ}
    (h : spendIfNotOwner t c o n = some t') :
    t'.balanceOf = t.balanceOf ∧ t'.totalSupply = t.totalSupply := by
  unfold spendIfNotOwner at h
  split_ifs at h
  · exact ozSpend_eq_some h
  · cases h; exact ⟨rfl, rfl⟩

theorem deposit_eq_some {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit δ s c a r = some (s', n)) :
    s.previewDeposit δ a = some n ∧ a ≤ s.asset.balanceOf c ∧ s'.self = s.self ∧
      s'.asset.balanceOf = s.asset.balanceOf - single c a + single s.self a ∧
      s'.totalSupply = s.totalSupply + n := by
  unfold deposit at h
  split_ifs at h
  obtain ⟨n', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  obtain ⟨hv, hb, -⟩ := ozTransferFrom_eq_some ha
  obtain ⟨-, -, -, hs⟩ := ozMint_eq_some hm
  exact ⟨hp, hv, rfl, hb, hs⟩

theorem mint_eq_some {s s' : State A} {c r : A} {n a : ℕ}
    (h : mint δ s c n r = some (s', a)) :
    s.previewMint δ n = some a ∧ a ≤ s.asset.balanceOf c ∧ s'.self = s.self ∧
      s'.asset.balanceOf = s.asset.balanceOf - single c a + single s.self a ∧
      s'.totalSupply = s.totalSupply + n := by
  unfold mint at h
  split_ifs at h
  obtain ⟨a', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  obtain ⟨hv, hb, -⟩ := ozTransferFrom_eq_some ha
  obtain ⟨-, -, -, hs⟩ := ozMint_eq_some hm
  exact ⟨hp, hv, rfl, hb, hs⟩

theorem withdraw_eq_some {s s' : State A} {c r o : A} {a n : ℕ}
    (h : withdraw δ s c a r o = some (s', n)) :
    s.previewWithdraw δ a = some n ∧ n ≤ s.shares.balanceOf o ∧ a ≤ s.totalAssets ∧
      s'.self = s.self ∧
      s'.asset.balanceOf = s.asset.balanceOf - single s.self a + single r a ∧
      s'.totalSupply = s.totalSupply - n := by
  unfold withdraw at h
  obtain ⟨m, -, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h
  obtain ⟨n', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  obtain ⟨e1, e2⟩ := spendIfNotOwner_eq_some hs1
  obtain ⟨-, hn, -, hs⟩ := ozBurn_eq_some hb2
  obtain ⟨-, -, ha, hb, -⟩ := ozTransfer_eq_some ht
  exact ⟨hp, e1 ▸ hn, ha, rfl, hb, by simp only [State.totalSupply, hs, e2]⟩

theorem redeem_eq_some {s s' : State A} {c r o : A} {n a : ℕ}
    (h : redeem δ s c n r o = some (s', a)) :
    s.previewRedeem δ n = some a ∧ n ≤ s.shares.balanceOf o ∧ a ≤ s.totalAssets ∧
      s'.self = s.self ∧
      s'.asset.balanceOf = s.asset.balanceOf - single s.self a + single r a ∧
      s'.totalSupply = s.totalSupply - n := by
  unfold redeem at h
  split_ifs at h
  obtain ⟨a', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  obtain ⟨e1, e2⟩ := spendIfNotOwner_eq_some hs1
  obtain ⟨-, hn, -, hs⟩ := ozBurn_eq_some hb2
  obtain ⟨-, -, ha, hb, -⟩ := ozTransfer_eq_some ht
  exact ⟨hp, e1 ▸ hn, ha, rfl, hb, by simp only [State.totalSupply, hs, e2]⟩

/-! ## The invariant over arbitrary call sequences -/

theorem WF_spendIfNotOwner {t t' : Token A} {c o : A} {n : ℕ} (hw : t.WF)
    (h : spendIfNotOwner t c o n = some t') : t'.WF := by
  unfold spendIfNotOwner at h
  split_ifs at h
  · exact WF_ozSpend hw h
  · cases h; exact hw

theorem Inv_step {s s' : State A} {op : Op A} (hi : Inv s) (h : step δ s op = some s') :
    Inv s' := by
  cases op with
  | deposit c a r =>
    obtain ⟨⟨s1, n⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold deposit at h1; split_ifs at h1
    obtain ⟨_, -, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨asset, ha, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨sh, hm, h1⟩ := Option.map_eq_some_iff.1 h1
    cases h1; exact ⟨WF_ozTransferFrom hi.1 ha, WF_ozMint hi.2 hm⟩
  | mint c n r =>
    obtain ⟨⟨s1, a⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold mint at h1; split_ifs at h1
    obtain ⟨_, -, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨asset, ha, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨sh, hm, h1⟩ := Option.map_eq_some_iff.1 h1
    cases h1; exact ⟨WF_ozTransferFrom hi.1 ha, WF_ozMint hi.2 hm⟩
  | withdraw c a r o =>
    obtain ⟨⟨s1, n⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold withdraw at h1
    obtain ⟨_, -, h1⟩ := Option.bind_eq_some_iff.1 h1
    split_ifs at h1
    obtain ⟨_, -, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨sh1, hs1, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨sh2, hb2, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨asset, ht, h1⟩ := Option.map_eq_some_iff.1 h1
    cases h1; exact ⟨WF_ozTransfer hi.1 ht, WF_ozBurn (WF_spendIfNotOwner hi.2 hs1) hb2⟩
  | redeem c n r o =>
    obtain ⟨⟨s1, a⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold redeem at h1; split_ifs at h1
    obtain ⟨_, -, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨sh1, hs1, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨sh2, hb2, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨asset, ht, h1⟩ := Option.map_eq_some_iff.1 h1
    cases h1; exact ⟨WF_ozTransfer hi.1 ht, WF_ozBurn (WF_spendIfNotOwner hi.2 hs1) hb2⟩
  | transfer c d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨hi.1, WF_ozTransfer hi.2 h1⟩
  | transferFrom c src d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨hi.1, WF_ozTransferFrom hi.2 h1⟩
  | approve c sp v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨hi.1, WF_ozApprove hi.2 h1⟩
  | assetTransfer c d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨WF_ozTransfer hi.1 h1, hi.2⟩
  | assetTransferFrom c src d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨WF_ozTransferFrom hi.1 h1, hi.2⟩
  | assetApprove c sp v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨WF_ozApprove hi.1 h1, hi.2⟩
  | assetMint d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨WF_ozMint hi.1 h1, hi.2⟩
  | assetBurn src v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨WF_ozBurn hi.1 h1, hi.2⟩

/-- **Multi-transaction invariant** for the OpenZeppelin vault. -/
theorem Inv_exec {s : State A} (hi : Inv s) (ops : List (Op A)) : Inv (exec δ s ops) := by
  induction ops generalizing s with
  | nil => exact hi
  | cons op ops ih =>
    apply ih
    cases h : step δ s op with
    | none => exact hi
    | some s' => exact Inv_step hi h

/-- [INV-SUPPLY] `totalSupply = Σ balanceOf` in every reachable state. -/
theorem totalSupply_eq_sum_exec {s : State A} (hi : Inv s) (ops : List (Op A)) :
    (exec δ s ops).totalSupply = total (exec δ s ops).shares.balanceOf :=
  ((Inv_exec hi ops).2.1).symm

/-! ## Previews and rounding -/

/-- [P-PREVIEW-*] Each entry point returns exactly its preview. -/
theorem previews_exact {s s' : State A} {c r o : A} {x y : ℕ} :
    (deposit δ s c x r = some (s', y) → s.previewDeposit δ x = some y) ∧
    (mint δ s c x r = some (s', y) → s.previewMint δ x = some y) ∧
    (withdraw δ s c x r o = some (s', y) → s.previewWithdraw δ x = some y) ∧
    (redeem δ s c x r o = some (s', y) → s.previewRedeem δ x = some y) :=
  ⟨fun h => (deposit_eq_some h).1, fun h => (mint_eq_some h).1,
    fun h => (withdraw_eq_some h).1, fun h => (redeem_eq_some h).1⟩

/-- [R-DEPOSIT] `n = ⌊a·Ŝ/T̂⌋`. -/
theorem deposit_rounding {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit δ s c a r = some (s', n)) :
    n * s.vT ≤ a * s.vS δ ∧ a * s.vS δ < (n + 1) * s.vT := by
  obtain ⟨-, -, -, rfl⟩ := toShares_eq_some.1 (deposit_eq_some h).1
  exact ⟨Nat.div_mul_le_self _ _, lt_div_add_one_mul _ _ (State.vT_pos s)⟩

/-- [R-MINT] `a = ⌈n·T̂/Ŝ⌉`. -/
theorem mint_rounding {s s' : State A} {c r : A} {n a : ℕ}
    (h : mint δ s c n r = some (s', a)) :
    n * s.vT ≤ a * s.vS δ ∧ a * s.vS δ < n * s.vT + s.vS δ := by
  obtain ⟨-, -, -, rfl⟩ := toAssets_eq_some.1 (mint_eq_some h).1
  exact ⟨le_ceilDiv_mul _ _ (State.vS_pos s), ceilDiv_mul_lt _ _ (State.vS_pos s)⟩

/-- [R-WITHDRAW] `n = ⌈a·Ŝ/T̂⌉`. -/
theorem withdraw_rounding {s s' : State A} {c r o : A} {a n : ℕ}
    (h : withdraw δ s c a r o = some (s', n)) :
    a * s.vS δ ≤ n * s.vT ∧ n * s.vT < a * s.vS δ + s.vT := by
  obtain ⟨-, -, -, rfl⟩ := toShares_eq_some.1 (withdraw_eq_some h).1
  exact ⟨le_ceilDiv_mul _ _ (State.vT_pos s), ceilDiv_mul_lt _ _ (State.vT_pos s)⟩

/-- [R-REDEEM] `a = ⌊n·T̂/Ŝ⌋`. -/
theorem redeem_rounding {s s' : State A} {c r o : A} {n a : ℕ}
    (h : redeem δ s c n r o = some (s', a)) :
    a * s.vS δ ≤ n * s.vT ∧ n * s.vT < (a + 1) * s.vS δ := by
  obtain ⟨-, -, -, rfl⟩ := toAssets_eq_some.1 (redeem_eq_some h).1
  exact ⟨Nat.div_mul_le_self _ _, lt_div_add_one_mul _ _ (State.vS_pos s)⟩

/-! ## State changes -/

theorem totalAssets_in {s s' : State A} {c : A} {a : ℕ} (hc : c ≠ s.self)
    (hself : s'.self = s.self)
    (hb : s'.asset.balanceOf = s.asset.balanceOf - single c a + single s.self a) :
    s'.totalAssets = s.totalAssets + a := by
  simp only [State.totalAssets, hself, hb, move_apply_dst _ _ hc]

theorem totalAssets_out {s s' : State A} {r : A} {a : ℕ} (hr : r ≠ s.self)
    (hself : s'.self = s.self)
    (hb : s'.asset.balanceOf = s.asset.balanceOf - single s.self a + single r a) :
    s'.totalAssets = s.totalAssets - a := by
  simp only [State.totalAssets, hself, hb, move_apply_src _ _ (Ne.symm hr)]

theorem deposit_vTS {s s' : State A} {c r : A} {a n : ℕ} (h : deposit δ s c a r = some (s', n))
    (hc : c ≠ s.self) : s'.vT = s.vT + a ∧ s'.vS δ = s.vS δ + n := by
  obtain ⟨-, -, hself, hb, hS⟩ := deposit_eq_some h
  have := totalAssets_in hc hself hb
  unfold State.vT State.vS; omega

theorem mint_vTS {s s' : State A} {c r : A} {n a : ℕ} (h : mint δ s c n r = some (s', a))
    (hc : c ≠ s.self) : s'.vT = s.vT + a ∧ s'.vS δ = s.vS δ + n := by
  obtain ⟨-, -, hself, hb, hS⟩ := mint_eq_some h
  have := totalAssets_in hc hself hb
  unfold State.vT State.vS; omega

/-- After `withdraw` to a receiver other than the vault: `T̂ = a + T̂'`, `Ŝ = n + Ŝ'`. -/
theorem withdraw_vTS {s s' : State A} {c r o : A} {a n : ℕ} (hi : Inv s)
    (h : withdraw δ s c a r o = some (s', n)) (hr : r ≠ s.self) :
    s.vT = a + s'.vT ∧ s.vS δ = n + s'.vS δ := by
  obtain ⟨-, hn, ha, hself, hb, hS⟩ := withdraw_eq_some h
  have := totalAssets_out hr hself hb
  have := hn.trans (balanceOf_le_totalSupply hi.2 o)
  unfold State.vT State.vS State.totalSupply at *; omega

/-- After `redeem` to a receiver other than the vault: `T̂ = a + T̂'`, `Ŝ = n + Ŝ'`. -/
theorem redeem_vTS {s s' : State A} {c r o : A} {n a : ℕ} (hi : Inv s)
    (h : redeem δ s c n r o = some (s', a)) (hr : r ≠ s.self) :
    s.vT = a + s'.vT ∧ s.vS δ = n + s'.vS δ := by
  obtain ⟨-, hn, ha, hself, hb, hS⟩ := redeem_eq_some h
  have := totalAssets_out hr hself hb
  have := hn.trans (balanceOf_le_totalSupply hi.2 o)
  unfold State.vT State.vS State.totalSupply at *; omega

/-! ## No dilution, unconditionally -/

/-- [E-PRICE-DEPOSIT] `T̂·Ŝ' ≤ T̂'·Ŝ`, in every state (no `totalSupply > 0` needed). -/
theorem deposit_price_mono {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit δ s c a r = some (s', n)) (hc : c ≠ s.self) :
    s.vT * s'.vS δ ≤ s'.vT * s.vS δ := by
  obtain ⟨e1, e2⟩ := deposit_vTS h hc
  have := (deposit_rounding h).1
  rw [e1, e2]; nlinarith

/-- [E-PRICE-MINT] -/
theorem mint_price_mono {s s' : State A} {c r : A} {n a : ℕ}
    (h : mint δ s c n r = some (s', a)) (hc : c ≠ s.self) :
    s.vT * s'.vS δ ≤ s'.vT * s.vS δ := by
  obtain ⟨e1, e2⟩ := mint_vTS h hc
  have := (mint_rounding h).1
  rw [e1, e2]; nlinarith

/-- [E-PRICE-WITHDRAW] -/
theorem withdraw_price_mono {s s' : State A} {c r o : A} {a n : ℕ} (hi : Inv s)
    (h : withdraw δ s c a r o = some (s', n)) (hr : r ≠ s.self) :
    s.vT * s'.vS δ ≤ s'.vT * s.vS δ := by
  obtain ⟨e1, e2⟩ := withdraw_vTS hi h hr
  have := (withdraw_rounding h).1
  rw [e1, e2] at this ⊢; nlinarith

/-- [E-PRICE-REDEEM] -/
theorem redeem_price_mono {s s' : State A} {c r o : A} {n a : ℕ} (hi : Inv s)
    (h : redeem δ s c n r o = some (s', a)) (hr : r ≠ s.self) :
    s.vT * s'.vS δ ≤ s'.vT * s.vS δ := by
  obtain ⟨e1, e2⟩ := redeem_vTS hi h hr
  have := (redeem_rounding h).1
  rw [e1, e2] at this ⊢; nlinarith

/-- Cross-multiplied monotonicity is monotonicity of `price` over `ℚ`. -/
theorem price_le_of_cross {s s' : State A} (h : s.vT * s'.vS δ ≤ s'.vT * s.vS δ) :
    s.price δ ≤ s'.price δ := by
  unfold State.price
  rw [div_le_div_iff₀ (by exact_mod_cast State.vS_pos s) (by exact_mod_cast State.vS_pos s')]
  exact_mod_cast h

/-! ## Solvency -/

/-- [I-SOLVENT] `Σₓ ⌊balanceOf[x]·T̂/Ŝ⌋ ≤ totalAssets` in every well-formed state. -/
theorem solvent (s : State A) (hi : Inv s) :
    (s.shares.balanceOf.sum fun _ b => b * s.vT / s.vS δ) ≤ s.totalAssets := by
  have hsum : total s.shares.balanceOf = s.totalSupply := hi.2.1
  have hpos := State.vS_pos (δ := δ) s
  have hk : 0 < 10 ^ δ := by positivity
  unfold Finsupp.sum
  have key : (∑ x ∈ s.shares.balanceOf.support, s.shares.balanceOf x * s.vT / s.vS δ) * s.vS δ
      ≤ s.totalSupply * s.vT := by
    calc (∑ x ∈ s.shares.balanceOf.support, s.shares.balanceOf x * s.vT / s.vS δ) * s.vS δ
        = ∑ x ∈ s.shares.balanceOf.support, s.shares.balanceOf x * s.vT / s.vS δ * s.vS δ :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ x ∈ s.shares.balanceOf.support, s.shares.balanceOf x * s.vT :=
          Finset.sum_le_sum fun _ _ => Nat.div_mul_le_self _ _
      _ = total s.shares.balanceOf * s.vT := by unfold total Finsupp.sum; rw [Finset.sum_mul]
      _ = s.totalSupply * s.vT := by rw [hsum]
  have hlt : s.totalSupply * s.vT < s.vT * s.vS δ := by
    rw [Nat.mul_comm]
    exact Nat.mul_lt_mul_of_pos_left (by unfold State.vS; omega) (State.vT_pos s)
  exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt key hlt))

/-! ## Round trips: all eight hold in every state -/

/-- [RT-DEPOSIT-REDEEM] `redeem(deposit(a)) ≤ a`. -/
theorem rt_deposit_redeem {s s₁ s₂ : State A} {c r c' r' o : A} {a n a' : ℕ}
    (h₁ : deposit δ s c a r = some (s₁, n)) (h₂ : redeem δ s₁ c' n r' o = some (s₂, a'))
    (hc : c ≠ s.self) : a' ≤ a := by
  obtain ⟨eT, eS⟩ := deposit_vTS h₁ hc
  have r2 := (redeem_rounding h₂).1
  rw [eT, eS] at r2
  exact rt_in_out_assets (by have := State.vS_pos (δ := δ) s; omega) (deposit_rounding h₁).1
    r2

/-- [RT-MINT-REDEEM] `redeem(n) ≤ mint(n)`. -/
theorem rt_mint_redeem {s s₁ s₂ : State A} {c r c' r' o : A} {n a a' : ℕ}
    (h₁ : mint δ s c n r = some (s₁, a)) (h₂ : redeem δ s₁ c' n r' o = some (s₂, a'))
    (hc : c ≠ s.self) : a' ≤ a := by
  obtain ⟨eT, eS⟩ := mint_vTS h₁ hc
  have r2 := (redeem_rounding h₂).1
  rw [eT, eS] at r2
  exact rt_in_out_assets (by have := State.vS_pos (δ := δ) s; omega) (mint_rounding h₁).1
    r2

/-- [RT-DEPOSIT-WITHDRAW] `withdraw(a)` burns at least the `deposit(a)` shares. -/
theorem rt_deposit_withdraw {s s₁ s₂ : State A} {c r c' r' o : A} {a n n' : ℕ}
    (h₁ : deposit δ s c a r = some (s₁, n)) (h₂ : withdraw δ s₁ c' a r' o = some (s₂, n'))
    (hc : c ≠ s.self) : n ≤ n' := by
  obtain ⟨eT, eS⟩ := deposit_vTS h₁ hc
  have r2 := (withdraw_rounding h₂).1
  rw [eT, eS] at r2
  exact rt_in_out_shares (by have := State.vT_pos s; omega) (deposit_rounding h₁).1
    r2

/-- [RT-MINT-WITHDRAW] `withdraw(mint(n))` burns at least `n` shares. -/
theorem rt_mint_withdraw {s s₁ s₂ : State A} {c r c' r' o : A} {n a n' : ℕ}
    (h₁ : mint δ s c n r = some (s₁, a)) (h₂ : withdraw δ s₁ c' a r' o = some (s₂, n'))
    (hc : c ≠ s.self) : n ≤ n' := by
  obtain ⟨eT, eS⟩ := mint_vTS h₁ hc
  have r2 := (withdraw_rounding h₂).1
  rw [eT, eS] at r2
  exact rt_in_out_shares (by have := State.vT_pos s; omega) (mint_rounding h₁).1
    r2

/-- [RT-REDEEM-DEPOSIT] `deposit(redeem(n)) ≤ n`, even when the redemption drains the vault. -/
theorem rt_redeem_deposit {s s₁ s₂ : State A} {c r o c' r' : A} {n a n' : ℕ} (hi : Inv s)
    (h₁ : redeem δ s c n r o = some (s₁, a)) (h₂ : deposit δ s₁ c' a r' = some (s₂, n'))
    (hr : r ≠ s.self) : n' ≤ n := by
  obtain ⟨eT, eS⟩ := redeem_vTS hi h₁ hr
  have r1 := (redeem_rounding h₁).1
  rw [eT, eS] at r1
  exact rt_out_in_shares (State.vT_pos s₁) r1 (deposit_rounding h₂).1

/-- [RT-WITHDRAW-DEPOSIT] `deposit(a) ≤ withdraw(a)` (shares). -/
theorem rt_withdraw_deposit {s s₁ s₂ : State A} {c r o c' r' : A} {a n n' : ℕ} (hi : Inv s)
    (h₁ : withdraw δ s c a r o = some (s₁, n)) (h₂ : deposit δ s₁ c' a r' = some (s₂, n'))
    (hr : r ≠ s.self) : n' ≤ n := by
  obtain ⟨eT, eS⟩ := withdraw_vTS hi h₁ hr
  have r1 := (withdraw_rounding h₁).1
  rw [eT, eS] at r1
  exact rt_out_in_shares (State.vT_pos s₁) r1 (deposit_rounding h₂).1

/-- [RT-REDEEM-MINT] `mint(n)` after `redeem(n)` costs at least what it paid. -/
theorem rt_redeem_mint {s s₁ s₂ : State A} {c r o c' r' : A} {n a a' : ℕ} (hi : Inv s)
    (h₁ : redeem δ s c n r o = some (s₁, a)) (h₂ : mint δ s₁ c' n r' = some (s₂, a'))
    (hr : r ≠ s.self) : a ≤ a' := by
  obtain ⟨eT, eS⟩ := redeem_vTS hi h₁ hr
  have r1 := (redeem_rounding h₁).1
  rw [eT, eS] at r1
  exact rt_out_in_assets (State.vS_pos s₁) r1 (mint_rounding h₂).1

/-- [RT-WITHDRAW-MINT] `mint(withdraw(a))` costs at least `a`. -/
theorem rt_withdraw_mint {s s₁ s₂ : State A} {c r o c' r' : A} {a n a' : ℕ} (hi : Inv s)
    (h₁ : withdraw δ s c a r o = some (s₁, n)) (h₂ : mint δ s₁ c' n r' = some (s₂, a'))
    (hr : r ≠ s.self) : a ≤ a' := by
  obtain ⟨eT, eS⟩ := withdraw_vTS hi h₁ hr
  have r1 := (withdraw_rounding h₁).1
  rw [eT, eS] at r1
  exact rt_out_in_assets (State.vS_pos s₁) r1 (mint_rounding h₂).1

/-! ## A deposit can mint zero shares -/

/-- [EIP-DEPOSIT-ZERO] Unlike Solmate, OpenZeppelin has no `ZERO_SHARES` check: when
`a·Ŝ < T̂` a successful `deposit` takes `a` assets and mints `0` shares. -/
theorem deposit_zero_shares {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit δ s c a r = some (s', n)) (hlt : a * s.vS δ < s.vT) : n = 0 := by
  have := (deposit_rounding h).1
  by_contra hn
  have : 1 * s.vT ≤ n * s.vT := Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.2 hn)
  omega

end EvmLeanSpecs.Vault.Oz
