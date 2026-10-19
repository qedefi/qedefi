import EvmLeanSpecs.Refinement.VaultViews

/-!
# The vault's remaining views: `totalAssets`, `asset`, `max*`
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-- The vault-share balance word of `a` (`balanceOf[a]`, slot `keccak(a ‖ 3)` of the executing
account). -/
def sharesOf (m : Machine) (a : Address) : Word :=
  m.world.sload m.frame.msg.currentTarget (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate a)

/-- Calldata of a function without arguments, with selector `sel`. -/
structure NoArgCall (data : ByteArray) (sel : Nat) : Prop where
  /-- The selector. -/
  selector : Abi.selectorOf data = sel
  /-- At least the selector. -/
  size : 4 ≤ data.size

/-- Calldata of a function taking one `address` argument `a` (ABI-clean: high bytes zero),
with selector `sel`. -/
structure AddrCall (data : ByteArray) (sel : Nat) (a : Address) : Prop where
  /-- The selector. -/
  selector : Abi.selectorOf data = sel
  /-- One argument word. -/
  size : 36 ≤ data.size
  /-- The argument. -/
  arg : Bytes.toWord (readBytes data 4 32) = Word.ofAddress a

set_option maxHeartbeats 0 in
/-- **`totalAssets()`** of the vault, in any frame: the asset balance of the vault. -/
theorem totalAssets_halts (m : Machine) (h : ViewPre m)
    (hd : NoArgCall m.frame.msg.data 0x01e1d114) :
    Halts m (ViewPost m (some (assetsOf m).toNat)) := by
  obtain ⟨hsel, hsz4⟩ := hd
  have hsel' := Dispatch.selector_eq hsel
  view_intro
  wp_run_to 0x47b [hval, hsel', hlt, Abi.shr_calldataload_zero]
  refine WP.bind_mono (totalAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by jumpdest_disch) initMemory_fmpInit.1 initMemory_fmpInit.2 (by dsimp only; omega)
    (by dsimp only; omega)) (fun _ _ _ h => h.elim) ?_
  rintro m' - ⟨mem, g, rd, sub, rfl, hmem', hg1⟩
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 ⊢
  refine WP.bind_mono (returnWord_wp _ rfl rfl rfl (by simp) (.inr hmem')
    (by dsimp only; omega)) ?_ (fun _ _ h => h.elim)
  rintro mf o - ⟨ho, hw⟩
  exact ⟨hw, by simp only [ho, assetsOf, ofNat_toNat_word]⟩

set_option maxHeartbeats 0 in
/-- **`asset()`** of the vault, in any frame: the immutable `assetAddr`. -/
theorem asset_halts (m : Machine) (h : ViewPre m) (hd : NoArgCall m.frame.msg.data 0x38d52e0f) :
    Halts m (ViewPost m (some assetAddr.toNat)) := by
  obtain ⟨hsel, hsz4⟩ := hd
  have hsel' := Dispatch.selector_eq hsel
  view_intro
  wp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`maxDeposit(address)`** of the vault, in any frame: `type(uint256).max`. -/
theorem maxDeposit_halts (m : Machine) (h : ViewPre m) {a : Address}
    (hd : AddrCall m.frame.msg.data 0x402d267d a) :
    Halts m (ViewPost m (some MAXN)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  wp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg, ofAddress_and_addressMask,
    Solidity.eq_self]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`maxMint(address)`** of the vault, in any frame: `type(uint256).max`. -/
theorem maxMint_halts (m : Machine) (h : ViewPre m) {a : Address}
    (hd : AddrCall m.frame.msg.data 0xc63d75b6 a) :
    Halts m (ViewPost m (some MAXN)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  wp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg, ofAddress_and_addressMask,
    Solidity.eq_self]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`maxRedeem(address)`** of the vault, in any frame: the share balance of the owner. -/
theorem maxRedeem_halts (m : Machine) (h : ViewPre m) {a : Address}
    (hd : AddrCall m.frame.msg.data 0xd905777e a) :
    Halts m (ViewPost m (some (sharesOf m a).toNat)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  wp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, by simp only [sharesOf, balanceSlot_solmate, ofNat_toNat_word]⟩

set_option maxHeartbeats 0 in
/-- **`maxWithdraw(address)`** of the vault, in any frame: `convertToAssets(balanceOf[owner])`
(which reverts on `mulDivDown` overflow, see `Vault.Solmate.maxWithdraw_reverts_of_overflow`). -/
theorem maxWithdraw_halts (m : Machine) (h : ViewPre m) {a : Address}
    (hd : AddrCall m.frame.msg.data 0xce96cb77 a) :
    Halts m (ViewPost m
      (convertToAssetsN (supplyOf m).toNat (assetsOf m).toNat (sharesOf m a).toNat)) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  view_intro
  simp only [sharesOf, balanceSlot_solmate]
  wp_run_to 0x593 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64]
  wp_generalize_gas g0 hg0
  have hg0' : m_gasLeft ≤ g0 + 3000 := by subst hg0; evm_gas
  have hg0'' : g0 ≤ m_gasLeft := by subst hg0; omega
  clear hg0
  refine WP.bind_mono (convertToAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by jumpdest_disch) ⟨?_, ?_⟩ (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · simp only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide),
      Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide), Memory.loadWord_storeWord]
  · evm_gas_norm
  · rintro mf o - ⟨hnone, hrev⟩
    simp only [supplyOf, assetsOf, balanceSlot_solmate] at hnone
    exact ⟨hrev.2, by rw [hnone]; exact hrev.1⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1⟩
  simp only [supplyOf, assetsOf, balanceSlot_solmate] at hv
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 ⊢
  wp_run_to 0x1dd
  refine WP.bind_mono (returnWord_wp _ rfl rfl rfl (by simp) hmem' (by dsimp only; omega)) ?_
    (fun _ _ h => h.elim)
  rintro mf o - ⟨ho, hw⟩
  exact ⟨hw, by rw [hv]; exact ho⟩

end EvmLeanSpecs.Refinement
