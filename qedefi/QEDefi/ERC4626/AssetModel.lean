module

public import QEDefi.ERC4626.AssetVariants
public import QEDefi.ERC20.Spec.Laws

/-!
# The vaults over any token model

`AssetVariants.lean` states the Solmate and OpenZeppelin vaults over any `Asset σ A` and proves
their accounting theorems for an asset that is `Asset.ExactOn` the vault. Here any token model
(`QEDefi.ERC20.TokenModel`, what a token's bytecode is proved to be by `ERC20Spec`) is such an
asset:

* `TokenModel.asset`: the model called through `SafeTransferLib`/`SafeERC20` (`Result.safe`),
  exactly as `Asset.variant` calls a `Variant`; `Asset.variant_eq_asset`: the two agree on the
  variants;
* `Asset.exactOn_of_exactMoves`: a model whose transfers are exact (`ExactMoves P`) is exact at
  the vault, once a transfer from the vault to itself is too (`TokenModel.AssetSelfExact`:
  `ExactMoves` is about distinct accounts only, and a vault's `withdraw` may name itself as the
  receiver); `Asset.variant_assetSelfExact` shows the variants satisfy it.

So `GSolmate.deposit_price_mono`, `GOz.deposit_price_mono`, … apply to the asset of every token
model with these two laws (`GSolmate.deposit_price_mono_model` is the first, as an example).
-/

@[expose] public noncomputable section

namespace QEDefi.ERC20.TokenModel

variable {σ A E : Type} (M : TokenModel σ A E)

/-- **A token model as a vault's asset**: its `balanceOf` view, and its `transfer` and
`transferFrom` called through `SafeTransferLib`/`SafeERC20` (the call must succeed and return
nothing or `true`). -/
def asset : QEDefi.ERC4626.Asset σ A :=
  ⟨M.balanceOf, fun s c d v => (M.call s c (.transfer d v)).safe,
    fun s c src d v => (M.call s c (.transferFrom src d v)).safe⟩

/-- **A transfer from `a` to itself is exact** in states satisfying `P`: when it succeeds (not
reporting failure by `false`), the amount was available and the balance is unchanged. Not part
of `ExactMoves`, which is about distinct accounts. -/
def AssetSelfExact (P : σ → Prop) (a : A) : Prop :=
  ∀ s v s' r, P s → M.call s a (.transfer a v) = .ok s' r → r ≠ .word false →
    v ≤ M.balanceOf s a ∧ M.balanceOf s' a = M.balanceOf s a

theorem asset_balanceOf : M.asset.balanceOf = M.balanceOf := rfl

theorem asset_transfer (s : σ) (c d : A) (v : ℕ) :
    M.asset.transfer s c d v = (M.call s c (.transfer d v)).safe := rfl

theorem asset_transferFrom (s : σ) (c src d : A) (v : ℕ) :
    M.asset.transferFrom s c src d v = (M.call s c (.transferFrom src d v)).safe := rfl

/-- `Result.safe` succeeds exactly on a success not reporting `false`. -/
theorem assetSafe_eq_some {r : Result σ} {s' : σ} :
    r.safe = some s' ↔ ∃ ret, r = .ok s' ret ∧ ret ≠ .word false := by
  constructor
  · intro h
    match r, h with
    | .ok _ .empty, h => exact ⟨.empty, by cases h; rfl, by simp⟩
    | .ok _ (.word true), h => exact ⟨.word true, by cases h; rfl, by simp⟩
  · rintro ⟨ret, rfl, hr⟩
    match ret, hr with
    | .empty, _ => rfl
    | .word true, _ => rfl
    | .word false, hr => exact absurd rfl hr

end QEDefi.ERC20.TokenModel

namespace QEDefi.ERC4626.Asset

open QEDefi.ERC20

variable {σ A E : Type}

/-- **`Asset.variant` is the asset of the variant's model**, whatever its event policy. -/
theorem variant_eq_asset [DecidableEq A] [Zero A] (V : Variant A)
    (ev : VState A → A → Call A → List (Event A)) : variant V = (V.model ev).asset := rfl

/-- **An exact model is an exact asset.** A token model whose transfers between distinct
accounts are exact (`ExactMoves P`) and whose transfers from the vault to itself are exact
(`AssetSelfExact P vault`) is, called through `SafeTransferLib`, exact at the vault: so the
vault theorems of `AssetVariants.lean` hold over it. -/
theorem exactOn_of_exactMoves [DecidableEq A] {M : TokenModel σ A E} {P : σ → Prop} {vault : A}
    (hM : M.ExactMoves P) (hself : M.AssetSelfExact P vault) : M.asset.ExactOn P vault where
  pull := by
    intro s s' c v hP hc h
    obtain ⟨ret, hr, hne⟩ := TokenModel.assetSafe_eq_some.1 h
    exact (hM.2 s vault c vault v s' ret hP hc hr hne).2.1
  push := by
    intro s s' r v hP h
    obtain ⟨ret, hr, hne⟩ := TokenModel.assetSafe_eq_some.1 h
    simp only [TokenModel.asset_balanceOf]
    split_ifs with hrv
    · subst hrv
      exact hself s v s' ret hP hr hne
    · obtain ⟨h1, -, -⟩ := hM.1 s vault r v s' ret hP (Ne.symm hrv) hr hne
      exact ⟨by omega, by omega⟩

/-- **The variants transfer to themselves exactly** in fee-free states (`NoFee`), so
`exactOn_of_exactMoves` applies to them as soon as `ExactMoves (NoFee V)` holds. -/
theorem variant_assetSelfExact [DecidableEq A] [Zero A] (V : Variant A)
    (ev : VState A → A → Call A → List (Event A)) (a : A) :
    (V.model ev).AssetSelfExact (NoFee V) a := by
  intro s v s' r hP h hne
  have hs : (variant V).transfer s a a v = some s' := by
    rw [variant_eq_asset V ev, TokenModel.asset_transfer, TokenModel.assetSafe_eq_some]
    exact ⟨r, h, hne⟩
  have := (variant_exactOn V a).push hP hs
  simp only [ite_true] at this
  exact this

end QEDefi.ERC4626.Asset

namespace QEDefi.ERC4626.GSolmate

open QEDefi.ERC20

/-- **No dilution over any exact token model** (`GSolmate.deposit_price_mono` over
`TokenModel.asset`): a deposit never lowers the Solmate vault's assets per share. -/
theorem deposit_price_mono_model {σ A E : Type} [DecidableEq A] {M : TokenModel σ A E}
    {P : σ → Prop} {s s' : State σ A} {c r : A} {a n : ℕ} (hM : M.ExactMoves P)
    (hself : M.AssetSelfExact P s.self) (hP : P s.asset)
    (h : deposit M.asset s c a r = some (s', n)) (hc : c ≠ s.self) (hS : totalSupply s ≠ 0) :
    totalAssets M.asset s * totalSupply s' ≤ totalAssets M.asset s' * totalSupply s :=
  deposit_price_mono (Asset.exactOn_of_exactMoves hM hself) hP h hc hS

end QEDefi.ERC4626.GSolmate
