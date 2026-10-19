import EvmLeanSpecs.Refinement.VaultConvert

/-!
# The vault's conversion and preview views, at the bytecode level

`*_halts`: `convertToShares`, `convertToAssets`, `previewDeposit`, `previewMint`,
`previewWithdraw`, `previewRedeem` of the vault deployed with any immutables `i`, run in **any**
fresh frame satisfying `ViewPre i` (top level or called by another contract), end the frame with
`ViewPost`: the world unchanged, and the ABI word of the `Nat`-level specification
(`convertToSharesN` … at `supplyOf m`, `assetsOf i.asset m`) or `revert(0, 0)` when it is
`none`. Each proof runs the dispatcher and ABI decoder symbolically (`pwp_run_to`), then
composes the summaries of the internal conversion (`VaultConvert`) and of the return encoder
(`returnWord_wp`) with `WP.bind_mono`. `VaultViewsSpec` restates them against the model.

`WordCall data sel x` describes calldata through what the decoder reads (selector, length,
argument word), so the theorems apply both to `Abi.encodeCall sel [x]` and to calldata that a
calling contract assembled in memory.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-- What a view call ends with: the world is unchanged, and the call returns the ABI word of
`v` when the specification gives `some v`, or reverts with empty data when it gives `none`. -/
def ViewPost (m : Machine) (r : Option Nat) (mf : Machine) (o : Outcome) : Prop :=
  mf.world = m.world ∧
    match r with
    | some v => o = .success (Bytes.ofWord (BitVec.ofNat 256 v))
    | none => o = .revert .empty

/-- The start of a call frame of the vault deployed with immutables `i` that can run its views:
fresh frame of the vault's code, no value, the asset deployed at `i.asset` (any immutables, not
a precompile), room for the asset call, enough gas (`60000 ≤ gas < 2⁶⁴`), and calldata
shorter than `2⁶⁴` bytes. -/
structure ViewPre (i : SolmateVault.Immutables) (m : Machine) : Prop where
  /-- A fresh frame of the vault's code. -/
  fresh : Fresh (SolmateVault.runtimeCodeWith i) m
  /-- No value is sent (the views are not payable). -/
  value : m.frame.msg.value = 0
  /-- The asset is deployed. -/
  assetCode : ∃ ia, m.world.code i.asset = SolmateAsset.runtimeCodeWith ia
  /-- The asset is not a precompile. -/
  assetNotPrecompile : m.precompiles.isPrecompile i.asset = false
  /-- A call from this frame does not exceed the depth limit. -/
  depth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit
  /-- Enough gas. -/
  gas : 60000 ≤ m.frame.gasLeft
  /-- Gas fits 64 bits (as it does in every transaction). -/
  gasLt : m.frame.gasLeft < 2 ^ 64
  /-- Calldata length fits 64 bits. -/
  sizeLt : m.frame.msg.data.size < 2 ^ 64

/-- Calldata of a function taking one static word argument `x`, with selector `sel`. -/
structure WordCall (data : ByteArray) (sel : Nat) (x : Word) : Prop where
  /-- The selector. -/
  selector : Abi.selectorOf data = sel
  /-- One argument word. -/
  size : 36 ≤ data.size
  /-- The argument. -/
  arg : Bytes.toWord (readBytes data 4 32) = x

/-- solc's initial memory satisfies `FmpInit`. -/
theorem initMemory_fmpInit : FmpInit ((({} : Memory).expand 64 32).storeWord 64 128#256) :=
  ⟨Memory.loadWord_storeWord _ _ _, by
    simp [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words]⟩

set_option hygiene false in
/-- The common start of a view proof: turn the `Halts` goal into a `WP`, unpack `ViewPre` (into
`hval`, `hcode`, `hpre`, `hdepth`, `hg`, `hg'`, `hsz'`) and the fresh frame, destructure the
machine into `m_ctx`, `m_world`, `m_msg`, … and substitute the frame's start values. Expects
`h : ViewPre i m` and `hsz4 : 4 ≤ m.frame.msg.data.size` in context. -/
macro "view_intro" : tactic => `(tactic| (
  apply WP.halts_of_false
  obtain ⟨hf, hval, hcode, hpre, hdepth, hg, hg', hsz'⟩ := h
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  have hagree := Shares.jumpDestsAgree i
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsz4 (by omega)
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  wp_hide_jump_tables
  subst hs hpc hc hmem
  try simp only [supplyOf, assetsOf]))

set_option maxHeartbeats 0 in
/-- The return encoder of the vault's word-returning functions (`0x01dd`): `mstore(fmp, v)`,
`return(fmp, 32)`. -/
theorem returnWord_wp {i : SolmateVault.Immutables} (m : Machine) {v : Word} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i) (hpc : m.frame.pc = 0x1dd)
    (hs : m.frame.stack = v :: rest) (hlen : rest.length ≤ 1000) (hmem : FmpOk m.frame.memory)
    (hg : 100 ≤ m.frame.gasLeft) :
    WP m (fun _ => False) (fun mf o => o = .success (Bytes.ofWord v) ∧ mf.world = m.world) := by
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
  all_goals
    pwp_steps [hfmp, hsize]
    exact ⟨trivial, rfl⟩

set_option maxHeartbeats 0 in
/-- **`convertToShares(uint256)`** of the vault, in any frame: the specification's `convertToSharesN` at the vault's
total supply and total assets. -/
theorem convertToShares_halts {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {x : Word}
    (hd : WordCall m.frame.msg.data 0xc6e6f592 x) :
    Halts m (ViewPost m (convertToSharesN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  pwp_run_to 0xbda [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg]
  refine WP.bind_mono (convertToShares_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    dsimp only [supplyOf, assetsOf] at hnone
    exact ⟨hrev.2, by rw [hnone]; exact hrev.1⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1⟩
  dsimp only [supplyOf, assetsOf] at hv
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 ⊢
  refine WP.bind_mono (returnWord_wp _ rfl rfl rfl (by simp) hmem' (by dsimp only; omega)) ?_
    (fun _ _ h => h.elim)
  rintro mf o - ⟨ho, hw⟩
  exact ⟨hw, by rw [hv]; exact ho⟩

set_option maxHeartbeats 0 in
/-- **`convertToAssets(uint256)`** of the vault, in any frame: the specification's `convertToAssetsN` at the vault's
total supply and total assets. -/
theorem convertToAssets_halts {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {x : Word}
    (hd : WordCall m.frame.msg.data 0x07a2d13a x) :
    Halts m (ViewPost m (convertToAssetsN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  pwp_run_to 0x593 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg]
  refine WP.bind_mono (convertToAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    dsimp only [supplyOf, assetsOf] at hnone
    exact ⟨hrev.2, by rw [hnone]; exact hrev.1⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1⟩
  dsimp only [supplyOf, assetsOf] at hv
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 ⊢
  refine WP.bind_mono (returnWord_wp _ rfl rfl rfl (by simp) hmem' (by dsimp only; omega)) ?_
    (fun _ _ h => h.elim)
  rintro mf o - ⟨ho, hw⟩
  exact ⟨hw, by rw [hv]; exact ho⟩

set_option maxHeartbeats 0 in
/-- **`previewDeposit(uint256)`** of the vault, in any frame: the specification's `convertToSharesN` at the vault's
total supply and total assets. -/
theorem previewDeposit_halts {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {x : Word}
    (hd : WordCall m.frame.msg.data 0xef8b30f7 x) :
    Halts m (ViewPost m (convertToSharesN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  pwp_run_to 0xbda [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg]
  refine WP.bind_mono (convertToShares_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    dsimp only [supplyOf, assetsOf] at hnone
    exact ⟨hrev.2, by rw [hnone]; exact hrev.1⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1⟩
  dsimp only [supplyOf, assetsOf] at hv
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 ⊢
  pwp_run_to 0x1dd
  refine WP.bind_mono (returnWord_wp _ rfl rfl rfl (by simp) hmem' (by dsimp only; omega)) ?_
    (fun _ _ h => h.elim)
  rintro mf o - ⟨ho, hw⟩
  exact ⟨hw, by rw [hv]; exact ho⟩

set_option maxHeartbeats 0 in
/-- **`previewMint(uint256)`** of the vault, in any frame: the specification's `previewMintN` at the vault's
total supply and total assets. -/
theorem previewMint_halts {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {x : Word}
    (hd : WordCall m.frame.msg.data 0xb3d7f6b9 x) :
    Halts m (ViewPost m (previewMintN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  pwp_run_to 0x96b [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg]
  refine WP.bind_mono (previewMint_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    dsimp only [supplyOf, assetsOf] at hnone
    exact ⟨hrev.2, by rw [hnone]; exact hrev.1⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1⟩
  dsimp only [supplyOf, assetsOf] at hv
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 ⊢
  refine WP.bind_mono (returnWord_wp _ rfl rfl rfl (by simp) hmem' (by dsimp only; omega)) ?_
    (fun _ _ h => h.elim)
  rintro mf o - ⟨ho, hw⟩
  exact ⟨hw, by rw [hv]; exact ho⟩

set_option maxHeartbeats 0 in
/-- **`previewWithdraw(uint256)`** of the vault, in any frame: the specification's `previewWithdrawN` at the vault's
total supply and total assets. -/
theorem previewWithdraw_halts {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {x : Word}
    (hd : WordCall m.frame.msg.data 0x0a28a477 x) :
    Halts m (ViewPost m (previewWithdrawN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  pwp_run_to 0x62b [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg]
  refine WP.bind_mono (previewWithdraw_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    dsimp only [supplyOf, assetsOf] at hnone
    exact ⟨hrev.2, by rw [hnone]; exact hrev.1⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1⟩
  dsimp only [supplyOf, assetsOf] at hv
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 ⊢
  refine WP.bind_mono (returnWord_wp _ rfl rfl rfl (by simp) hmem' (by dsimp only; omega)) ?_
    (fun _ _ h => h.elim)
  rintro mf o - ⟨ho, hw⟩
  exact ⟨hw, by rw [hv]; exact ho⟩

set_option maxHeartbeats 0 in
/-- **`previewRedeem(uint256)`** of the vault, in any frame: the specification's `convertToAssetsN` at the vault's
total supply and total assets. -/
theorem previewRedeem_halts {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {x : Word}
    (hd : WordCall m.frame.msg.data 0x4cdad506 x) :
    Halts m (ViewPost m (convertToAssetsN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  pwp_run_to 0x593 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg]
  refine WP.bind_mono (convertToAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    dsimp only [supplyOf, assetsOf] at hnone
    exact ⟨hrev.2, by rw [hnone]; exact hrev.1⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1⟩
  dsimp only [supplyOf, assetsOf] at hv
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 ⊢
  pwp_run_to 0x1dd
  refine WP.bind_mono (returnWord_wp _ rfl rfl rfl (by simp) hmem' (by dsimp only; omega)) ?_
    (fun _ _ h => h.elim)
  rintro mf o - ⟨ho, hw⟩
  exact ⟨hw, by rw [hv]; exact ho⟩

end EvmLeanSpecs.Refinement
