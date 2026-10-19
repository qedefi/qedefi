import EvmLeanSpecs.Refinement.VaultTotalAssets

/-!
# The vault's conversions as internal functions

Solmate's `ERC4626` computes every conversion and preview through one of four `internal view`
functions, each compiled once (the external functions jump to them):

| internal function | entry | non-empty vault (`supply ≠ 0`) | summary |
|---|---|---|---|
| `convertToShares(assets)` | `0x0bda` | `assets.mulDivDown(supply, totalAssets())` | `convertToShares_wp` |
| `convertToAssets(shares)` | `0x0593` | `shares.mulDivDown(totalAssets(), supply)` | `convertToAssets_wp` |
| `previewMint(shares)` | `0x096b` | `shares.mulDivUp(totalAssets(), supply)` | `previewMint_wp` |
| `previewWithdraw(assets)` | `0x062b` | `assets.mulDivUp(supply, totalAssets())` | `previewWithdraw_wp` |

(`previewDeposit` and `previewRedeem` are `convertToShares` and `convertToAssets`.) With
`supply == 0` each returns its argument without calling the asset.

Each summary is proved by symbolic execution of the function's own code, with the internal
calls replaced by their summaries (`totalAssets_wp`, `mulDivDown_wp`, `mulDivUp_wp`) through
`WP.bind_mono`. The result is the `Nat`-level specification (`convertToSharesN` …, which are
the specification's `Vault.Solmate.State` views with `S = totalSupply`, `T = totalAssets`)
evaluated at the vault's storage (`supplyOf`, `assetsOf`): on `some v` the function returns
`v`; on `none` (a `mulDiv` revert) the frame ends with `revert(0, 0)`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-- `convertToShares(x)`: `supply == 0 ? x : x.mulDivDown(supply, totalAssets())`. -/
def convertToSharesN (S T x : Nat) : Option Nat := if S = 0 then some x else mulDivDownN x S T

/-- `convertToAssets(x)`: `supply == 0 ? x : x.mulDivDown(totalAssets(), supply)`. -/
def convertToAssetsN (S T x : Nat) : Option Nat := if S = 0 then some x else mulDivDownN x T S

/-- `previewMint(x)`: `supply == 0 ? x : x.mulDivUp(totalAssets(), supply)`. -/
def previewMintN (S T x : Nat) : Option Nat := if S = 0 then some x else mulDivUpN x T S

/-- `previewWithdraw(x)`: `supply == 0 ? x : x.mulDivUp(supply, totalAssets())`. -/
def previewWithdrawN (S T x : Nat) : Option Nat := if S = 0 then some x else mulDivUpN x S T

/-- Memory facts at the end of a conversion: unchanged-shape (`FmpInit`, no call made) or
after the `totalAssets()` call (`FmpAfterCall`). -/
def FmpOk (mem : Memory) : Prop := FmpInit mem ∨ FmpAfterCall mem

/-- `ISZERO 0 = 1`. -/
theorem iszero_zero : Word.iszero 0#256 = 1#256 := by decide

/-- `ISZERO x = 0` for `x ≠ 0`. -/
theorem iszero_of_ne {x : Word} (h : x ≠ 0#256) : Word.iszero x = 0#256 := by
  have hb : (x == 0) = false := by simpa using h
  simp only [Word.iszero, Word.ofBool, hb]
  rfl

/-- A word is the `ofNat` of its value. -/
theorem ofNat_toNat_word (x : Word) : BitVec.ofNat 256 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

set_option maxHeartbeats 0 in
/-- **`convertToShares(x)` (internal, entry `0xbda`, stack `x :: r :: rest`)**: returns to `r` with the
specification's value, or reverts as `mulDiv` does. -/
theorem convertToShares_wp (m : Machine) {x r : Word} {rest : List Word} (hv : VaultFrame m)
    (hpc : m.frame.pc = 0xbda) (hs : m.frame.stack = x :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpInit m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ v mem g rd sub,
        convertToSharesN (supplyOf m).toNat (assetsOf m).toNat x.toNat = some v ∧
        m' = m.resumeWith r.toNat (BitVec.ofNat 256 v :: rest) mem g rd sub ∧
        FmpOk mem ∧ m.frame.gasLeft ≤ g + 12000)
      (fun mf o => convertToSharesN (supplyOf m).toNat (assetsOf m).toNat x.toNat = none ∧
        MulDivRevert m mf o) := by
  obtain ⟨hc, hj, hcode, hpre, hdepth⟩ := hv
  obtain ⟨hfmp, hsize⟩ := hmem
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [supplyOf, assetsOf]
  wp_steps
  by_cases hS : m_world.sload m_msg.currentTarget 2#256 = 0#256
  · simp only [hS, iszero_zero]
    wp_steps
    refine WP.ret ⟨x.toNat, m_memory, _, m_returnData, _,
      by simp only [convertToSharesN, hS, BitVec.toNat_ofNat]; rfl,
      by rw [Machine.resumeWith, ofNat_toNat_word], .inl ⟨hfmp, hsize⟩, ?_⟩
    evm_gas
  · have hS' : (m_world.sload m_msg.currentTarget 2#256).toNat ≠ 0 :=
      fun h => hS (BitVec.eq_of_toNat_eq (by simpa using h))
    simp only [iszero_of_ne hS]
    wp_run_to 0x47b
    wp_generalize_gas g0 hg0
    have hg0' : m_gasLeft ≤ g0 + 2300 := by subst hg0; evm_gas
    have hg0'' : g0 ≤ m_gasLeft := by subst hg0; omega
    clear hg0
    refine WP.bind_mono (totalAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl
      (by simp only [List.length_cons]; omega) (by jumpdest_disch) hfmp hsize (by dsimp only; omega)
      (by dsimp only; omega)) (fun _ _ _ h => h.elim) ?_
    rintro m1 - ⟨mem, g, rd, sub, rfl, ⟨hfmp1, hsize1⟩, hg1⟩
    simp only [Machine.resumeWith, assetsOf, BitVec.reduceToNat] at hg1 ⊢
    wp_run_to 0xe62
    refine WP.bind_mono (mulDivDown_wp _ rfl hj rfl rfl (by simp only [List.length_cons]; omega)
      (by jumpdest_disch) (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      exact ⟨by simp only [convertToSharesN, hS', ↓reduceIte]; exact hnone, hrev⟩
    rintro m2 - ⟨v, hv, rfl⟩
    simp only [Machine.resumeAt, BitVec.reduceToNat]
    wp_steps
    exact WP.ret ⟨v, mem, _, rd, sub, by simp only [convertToSharesN, hS', ↓reduceIte, hv], rfl,
      .inr ⟨hfmp1, hsize1⟩, by omega⟩

set_option maxHeartbeats 0 in
/-- **`convertToAssets(x)` (internal, entry `0x593`, stack `x :: r :: rest`)**: returns to `r` with the
specification's value, or reverts as `mulDiv` does. -/
theorem convertToAssets_wp (m : Machine) {x r : Word} {rest : List Word} (hv : VaultFrame m)
    (hpc : m.frame.pc = 0x593) (hs : m.frame.stack = x :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpInit m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ v mem g rd sub,
        convertToAssetsN (supplyOf m).toNat (assetsOf m).toNat x.toNat = some v ∧
        m' = m.resumeWith r.toNat (BitVec.ofNat 256 v :: rest) mem g rd sub ∧
        FmpOk mem ∧ m.frame.gasLeft ≤ g + 12000)
      (fun mf o => convertToAssetsN (supplyOf m).toNat (assetsOf m).toNat x.toNat = none ∧
        MulDivRevert m mf o) := by
  obtain ⟨hc, hj, hcode, hpre, hdepth⟩ := hv
  obtain ⟨hfmp, hsize⟩ := hmem
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [supplyOf, assetsOf]
  wp_steps
  by_cases hS : m_world.sload m_msg.currentTarget 2#256 = 0#256
  · simp only [hS, iszero_zero]
    wp_steps
    refine WP.ret ⟨x.toNat, m_memory, _, m_returnData, _,
      by simp only [convertToAssetsN, hS, BitVec.toNat_ofNat]; rfl,
      by rw [Machine.resumeWith, ofNat_toNat_word], .inl ⟨hfmp, hsize⟩, ?_⟩
    evm_gas
  · have hS' : (m_world.sload m_msg.currentTarget 2#256).toNat ≠ 0 :=
      fun h => hS (BitVec.eq_of_toNat_eq (by simpa using h))
    simp only [iszero_of_ne hS]
    wp_run_to 0x47b
    wp_generalize_gas g0 hg0
    have hg0' : m_gasLeft ≤ g0 + 2300 := by subst hg0; evm_gas
    have hg0'' : g0 ≤ m_gasLeft := by subst hg0; omega
    clear hg0
    refine WP.bind_mono (totalAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl
      (by simp only [List.length_cons]; omega) (by jumpdest_disch) hfmp hsize (by dsimp only; omega)
      (by dsimp only; omega)) (fun _ _ _ h => h.elim) ?_
    rintro m1 - ⟨mem, g, rd, sub, rfl, ⟨hfmp1, hsize1⟩, hg1⟩
    simp only [Machine.resumeWith, assetsOf, BitVec.reduceToNat] at hg1 ⊢
    wp_run_to 0xe62
    refine WP.bind_mono (mulDivDown_wp _ rfl hj rfl rfl (by simp only [List.length_cons]; omega)
      (by jumpdest_disch) (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      exact ⟨by simp only [convertToAssetsN, hS', ↓reduceIte]; exact hnone, hrev⟩
    rintro m2 - ⟨v, hv, rfl⟩
    simp only [Machine.resumeAt, BitVec.reduceToNat]
    wp_steps
    exact WP.ret ⟨v, mem, _, rd, sub, by simp only [convertToAssetsN, hS', ↓reduceIte, hv], rfl,
      .inr ⟨hfmp1, hsize1⟩, by omega⟩

set_option maxHeartbeats 0 in
/-- **`previewMint(x)` (internal, entry `0x96b`, stack `x :: r :: rest`)**: returns to `r` with the
specification's value, or reverts as `mulDiv` does. -/
theorem previewMint_wp (m : Machine) {x r : Word} {rest : List Word} (hv : VaultFrame m)
    (hpc : m.frame.pc = 0x96b) (hs : m.frame.stack = x :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpInit m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ v mem g rd sub,
        previewMintN (supplyOf m).toNat (assetsOf m).toNat x.toNat = some v ∧
        m' = m.resumeWith r.toNat (BitVec.ofNat 256 v :: rest) mem g rd sub ∧
        FmpOk mem ∧ m.frame.gasLeft ≤ g + 12000)
      (fun mf o => previewMintN (supplyOf m).toNat (assetsOf m).toNat x.toNat = none ∧
        MulDivRevert m mf o) := by
  obtain ⟨hc, hj, hcode, hpre, hdepth⟩ := hv
  obtain ⟨hfmp, hsize⟩ := hmem
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [supplyOf, assetsOf]
  wp_steps
  by_cases hS : m_world.sload m_msg.currentTarget 2#256 = 0#256
  · simp only [hS, iszero_zero]
    wp_steps
    refine WP.ret ⟨x.toNat, m_memory, _, m_returnData, _,
      by simp only [previewMintN, hS, BitVec.toNat_ofNat]; rfl,
      by rw [Machine.resumeWith, ofNat_toNat_word], .inl ⟨hfmp, hsize⟩, ?_⟩
    evm_gas
  · have hS' : (m_world.sload m_msg.currentTarget 2#256).toNat ≠ 0 :=
      fun h => hS (BitVec.eq_of_toNat_eq (by simpa using h))
    simp only [iszero_of_ne hS]
    wp_run_to 0x47b
    wp_generalize_gas g0 hg0
    have hg0' : m_gasLeft ≤ g0 + 2300 := by subst hg0; evm_gas
    have hg0'' : g0 ≤ m_gasLeft := by subst hg0; omega
    clear hg0
    refine WP.bind_mono (totalAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl
      (by simp only [List.length_cons]; omega) (by jumpdest_disch) hfmp hsize (by dsimp only; omega)
      (by dsimp only; omega)) (fun _ _ _ h => h.elim) ?_
    rintro m1 - ⟨mem, g, rd, sub, rfl, ⟨hfmp1, hsize1⟩, hg1⟩
    simp only [Machine.resumeWith, assetsOf, BitVec.reduceToNat] at hg1 ⊢
    wp_run_to 0xe7d
    refine WP.bind_mono (mulDivUp_wp _ rfl hj rfl rfl (by simp only [List.length_cons]; omega)
      (by jumpdest_disch) (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      exact ⟨by simp only [previewMintN, hS', ↓reduceIte]; exact hnone, hrev⟩
    rintro m2 - ⟨v, hv, rfl⟩
    simp only [Machine.resumeAt, BitVec.reduceToNat]
    wp_steps
    exact WP.ret ⟨v, mem, _, rd, sub, by simp only [previewMintN, hS', ↓reduceIte, hv], rfl,
      .inr ⟨hfmp1, hsize1⟩, by omega⟩

set_option maxHeartbeats 0 in
/-- **`previewWithdraw(x)` (internal, entry `0x62b`, stack `x :: r :: rest`)**: returns to `r` with the
specification's value, or reverts as `mulDiv` does. -/
theorem previewWithdraw_wp (m : Machine) {x r : Word} {rest : List Word} (hv : VaultFrame m)
    (hpc : m.frame.pc = 0x62b) (hs : m.frame.stack = x :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpInit m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ v mem g rd sub,
        previewWithdrawN (supplyOf m).toNat (assetsOf m).toNat x.toNat = some v ∧
        m' = m.resumeWith r.toNat (BitVec.ofNat 256 v :: rest) mem g rd sub ∧
        FmpOk mem ∧ m.frame.gasLeft ≤ g + 12000)
      (fun mf o => previewWithdrawN (supplyOf m).toNat (assetsOf m).toNat x.toNat = none ∧
        MulDivRevert m mf o) := by
  obtain ⟨hc, hj, hcode, hpre, hdepth⟩ := hv
  obtain ⟨hfmp, hsize⟩ := hmem
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [supplyOf, assetsOf]
  wp_steps
  by_cases hS : m_world.sload m_msg.currentTarget 2#256 = 0#256
  · simp only [hS, iszero_zero]
    wp_steps
    refine WP.ret ⟨x.toNat, m_memory, _, m_returnData, _,
      by simp only [previewWithdrawN, hS, BitVec.toNat_ofNat]; rfl,
      by rw [Machine.resumeWith, ofNat_toNat_word], .inl ⟨hfmp, hsize⟩, ?_⟩
    evm_gas
  · have hS' : (m_world.sload m_msg.currentTarget 2#256).toNat ≠ 0 :=
      fun h => hS (BitVec.eq_of_toNat_eq (by simpa using h))
    simp only [iszero_of_ne hS]
    wp_run_to 0x47b
    wp_generalize_gas g0 hg0
    have hg0' : m_gasLeft ≤ g0 + 2300 := by subst hg0; evm_gas
    have hg0'' : g0 ≤ m_gasLeft := by subst hg0; omega
    clear hg0
    refine WP.bind_mono (totalAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl
      (by simp only [List.length_cons]; omega) (by jumpdest_disch) hfmp hsize (by dsimp only; omega)
      (by dsimp only; omega)) (fun _ _ _ h => h.elim) ?_
    rintro m1 - ⟨mem, g, rd, sub, rfl, ⟨hfmp1, hsize1⟩, hg1⟩
    simp only [Machine.resumeWith, assetsOf, BitVec.reduceToNat] at hg1 ⊢
    wp_run_to 0xe7d
    refine WP.bind_mono (mulDivUp_wp _ rfl hj rfl rfl (by simp only [List.length_cons]; omega)
      (by jumpdest_disch) (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      exact ⟨by simp only [previewWithdrawN, hS', ↓reduceIte]; exact hnone, hrev⟩
    rintro m2 - ⟨v, hv, rfl⟩
    simp only [Machine.resumeAt, BitVec.reduceToNat]
    wp_steps
    exact WP.ret ⟨v, mem, _, rd, sub, by simp only [previewWithdrawN, hS', ↓reduceIte, hv], rfl,
      .inr ⟨hfmp1, hsize1⟩, by omega⟩

end EvmLeanSpecs.Refinement
