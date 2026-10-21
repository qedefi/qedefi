import Examples.Solmate.ERC4626.Convert

/-!
# The vault's views, at the bytecode level

`*_halts`: each view of the vault (any immutables), run in any frame satisfying `ViewPre` (top
level or called by another contract), ends with `ViewPost`: world unchanged, and the ABI word of
the `Nat`-level specification at `supplyOf m`, `assetsOf i.asset m`, or `revert(0, 0)` on
`none`. `ViewsSpec.lean` restates them against the model.
-/

section

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

/-- What a view call ends with: world unchanged; returns the ABI word of `v` when the
specification gives `some v`, reverts with empty data on `none`. -/
def ViewPost (m : Machine) (r : Option Nat) (mf : Machine) (o : Outcome) : Prop :=
  mf.world = m.world ∧
    match r with
    | some v => o = .success (Bytes.ofWord (BitVec.ofNat 256 v))
    | none => o = .revert .empty

/-- A fresh frame of the vault (immutables `i`) that can run its views: no value, the asset
deployed at `i.asset` (not a precompile), room for the asset call, `60000 ≤ gas < 2⁶⁴`, and
calldata shorter than `2⁶⁴` bytes. -/
structure ViewPre (i : SolmateVault.Immutables) (m : Machine) : Prop where
  fresh : Fresh (SolmateVault.runtimeCodeWith i) m
  value : m.frame.msg.value = 0
  assetCode : ∃ ia, m.world.code i.asset = SolmateAsset.runtimeCodeWith ia
  assetNotPrecompile : m.precompiles.isPrecompile i.asset = false
  depth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit
  gas : 60000 ≤ m.frame.gasLeft
  gasLt : m.frame.gasLeft < 2 ^ 64
  sizeLt : m.frame.msg.data.size < 2 ^ 64

/-- Calldata with selector `sel` and one word argument `x`, described through what the decoder
reads (so it covers calldata a calling contract assembled in memory). -/
structure WordCall (data : ByteArray) (sel : Nat) (x : Word) : Prop where
  selector : Abi.selectorOf data = sel
  size : 36 ≤ data.size
  arg : Bytes.toWord (readBytes data 4 32) = x

/-- Calldata of a function without arguments, with selector `sel`. -/
structure NoArgCall (data : ByteArray) (sel : Nat) : Prop where
  selector : Abi.selectorOf data = sel
  size : 4 ≤ data.size

/-- Calldata with selector `sel` and one ABI-clean `address` argument `a`. -/
structure AddrCall (data : ByteArray) (sel : Nat) (a : Address) : Prop where
  selector : Abi.selectorOf data = sel
  size : 36 ≤ data.size
  arg : Bytes.toWord (readBytes data 4 32) = Word.ofAddress a

theorem initMemory_fmpInit : FmpInit ((({} : Memory).expand 64 32).storeWord 64 128#256) :=
  ⟨Memory.loadWord_storeWord _ _ _, by
    simp [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words]⟩

set_option hygiene false in
/-- Common start of a view proof: `Halts` to `WP`, unpack `ViewPre` and the fresh frame,
destructure the machine. Expects `h : ViewPre i m` and `hsz4 : 4 ≤ m.frame.msg.data.size`. -/
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
/-- The return encoder of word-returning functions (`0x01dd`): `return(fmp, 32)` of `v`. -/
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
/-- **`convertToShares(uint256)`**: `convertToSharesN` at the vault's supply and total assets. -/
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
/-- **`convertToAssets(uint256)`**: `convertToAssetsN` at the vault's supply and total assets. -/
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
/-- **`previewDeposit(uint256)`**: `convertToSharesN` at the vault's supply and total assets. -/
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
/-- **`previewMint(uint256)`**: `previewMintN` at the vault's supply and total assets. -/
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
/-- **`previewWithdraw(uint256)`**: `previewWithdrawN` at the vault's supply and total assets. -/
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
/-- **`previewRedeem(uint256)`**: `convertToAssetsN` at the vault's supply and total assets. -/
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

end Examples.Solmate.ERC4626

end

section

/-! ## `totalAssets`, `asset`, `max*` -/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

theorem ofNat_toNat_address (a : Address) : BitVec.ofNat 256 a.toNat = Word.ofAddress a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Word.ofAddress, BitVec.toNat_setWidth]

set_option maxHeartbeats 0 in
/-- **`totalAssets()`**: the vault's asset balance. -/
theorem totalAssets_halts {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m)
    (hd : NoArgCall m.frame.msg.data 0x01e1d114) :
    Halts m (ViewPost m (some (assetsOf i.asset m).toNat)) := by
  obtain ⟨hsel, hsz4⟩ := hd
  have hsel' := Dispatch.selector_eq hsel
  view_intro
  pwp_run_to 0x47b [hval, hsel', hlt, Abi.shr_calldataload_zero]
  refine WP.bind_mono (totalAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit.1 initMemory_fmpInit.2 (by dsimp only; omega)
    (by dsimp only; omega)) (fun _ _ _ h => h.elim) ?_
  rintro m' - ⟨mem, g, rd, sub, rfl, hmem', hg1⟩
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 ⊢
  refine WP.bind_mono (returnWord_wp _ rfl rfl rfl (by simp) (.inr hmem')
    (by dsimp only; omega)) ?_ (fun _ _ h => h.elim)
  rintro mf o - ⟨ho, hw⟩
  exact ⟨hw, by simp only [ho, assetsOf, ofNat_toNat_word]⟩

set_option maxHeartbeats 0 in
/-- **`asset()`**: the immutable `i.asset`. -/
theorem asset_halts {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) (hd : NoArgCall m.frame.msg.data 0x38d52e0f) :
    Halts m (ViewPost m (some i.asset.toNat)) := by
  obtain ⟨hsel, hsz4⟩ := hd
  have hsel' := Dispatch.selector_eq hsel
  view_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, readBytes_code_asset688,
    ofAddress_and_addressMask, addressMask_and_ofAddress]
  exact ⟨rfl, by dsimp only; rw [ofNat_toNat_address]⟩

set_option maxHeartbeats 0 in
/-- **`maxDeposit(address)`**: `type(uint256).max`. -/
theorem maxDeposit_halts {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {a : Address}
    (hd : AddrCall m.frame.msg.data 0x402d267d a) :
    Halts m (ViewPost m (some MAXN)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg, ofAddress_and_addressMask,
    Solidity.eq_self]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`maxMint(address)`**: `type(uint256).max`. -/
theorem maxMint_halts {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {a : Address}
    (hd : AddrCall m.frame.msg.data 0xc63d75b6 a) :
    Halts m (ViewPost m (some MAXN)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg, ofAddress_and_addressMask,
    Solidity.eq_self]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`maxRedeem(address)`**: the owner's share balance. -/
theorem maxRedeem_halts {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {a : Address}
    (hd : AddrCall m.frame.msg.data 0xd905777e a) :
    Halts m (ViewPost m (some (sharesOf m a).toNat)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, by simp only [sharesOf, balanceSlot_solmate, ofNat_toNat_word]⟩

set_option maxHeartbeats 0 in
/-- **`maxWithdraw(address)`**: `convertToAssets(balanceOf[owner])` (reverts on `mulDivDown`
overflow). -/
theorem maxWithdraw_halts {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m) {a : Address}
    (hd : AddrCall m.frame.msg.data 0xce96cb77 a) :
    Halts m (ViewPost m
      (convertToAssetsN (supplyOf m).toNat (assetsOf i.asset m).toNat (sharesOf m a).toNat)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  simp only [sharesOf, balanceSlot_solmate]
  pwp_run_to 0x593 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64]
  wp_generalize_gas g0 hg0
  have hg0' : m_gasLeft ≤ g0 + 3000 := by subst hg0; evm_gas
  have hg0'' : g0 ≤ m_gasLeft := by subst hg0; omega
  clear hg0
  refine WP.bind_mono (convertToAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) ⟨?_, ?_⟩ (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · simp only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide),
      Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide), Memory.loadWord_storeWord]
  · evm_gas_norm
  · rintro mf o - ⟨hnone, hrev⟩
    simp only [supplyOf, assetsOf, balanceSlot_solmate] at hnone
    exact ⟨hrev.2, by rw [hnone]; exact hrev.1⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1⟩
  simp only [supplyOf, assetsOf, balanceSlot_solmate] at hv
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 ⊢
  pwp_run_to 0x1dd
  refine WP.bind_mono (returnWord_wp _ rfl rfl rfl (by simp) hmem' (by dsimp only; omega)) ?_
    (fun _ _ h => h.elim)
  rintro mf o - ⟨ho, hw⟩
  exact ⟨hw, by rw [hv]; exact ho⟩

end Examples.Solmate.ERC4626

end
