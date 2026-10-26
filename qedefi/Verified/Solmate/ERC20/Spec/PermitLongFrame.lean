import Verified.Solmate.ERC20.Spec.PermitLongFail
import Verified.Solmate.ERC20.Spec.PermitLongLimit
import Verified.Solmate.ERC20.BalanceOf

/-!
# Solmate's `permit` frames off the deployment chain, outside `Permit.DomainCase`

The frame-level theorems for a `name` slot word that is not a short string, off the deployment
chain, from a fresh frame with no value and gas from `100000` (plus `Str.getterGas` of a long
name) below `2²⁵⁶`:

* `pl_permit_long_halts`: a long name, not static, below the call-depth limit: success with
  `permitWorld` and one `Approval` log exactly when `PermitValid` holds for the separator
  `dsOfName` of the stored name, a revert otherwise (`Permit.asset_permit_halts` for a long
  name);
* `pl_permit_long_limit`, `pl_permit_long_static`: at the call-depth limit it reverts, in a
  static frame it fails;
* `pl_permit_panic`: an inconsistent slot word: it reverts (`Panic(0x22)` or an earlier check);
* `pl_permit_huge`: a long name of more words than the frame has gas: it fails.
-/

namespace Verified.Solmate.ERC20.Spec
open QEDefi.ERC4626 Verified.Solmate.ERC20.Permit
open Verified.Solmate.ERC20.Spec.PermitLongGas

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts Verified.Solmate.ERC20

/-- What `permit` does for the domain separator `ds`, gas aside (`Permit.PermitPost` without
its gas bound). -/
def PlPost (ds : Word) (owner spender : Address) (value deadline v r s : Word) (m mf : Machine)
    (o : Outcome) : Prop :=
  (PermitValid m.ctx.crypto ds m.ctx.block.timestamp owner spender value deadline v r s
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto owner)) →
    o = .success .empty ∧
    mf.world = permitWorld m.ctx.crypto m.world m.frame.msg.currentTarget owner spender value ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog m.frame.msg.currentTarget owner spender value)) ∧
  (¬ PermitValid m.ctx.crypto ds m.ctx.block.timestamp owner spender value deadline v r s
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto owner)) →
    ∃ out, o = .revert out)

/-- The separator `DOMAIN_SEPARATOR()` returns for the long name of the frame `m`. -/
noncomputable def plDs (m : Machine) : Word :=
  dsOfName m.ctx.crypto (Str.longData (m.world.sload m.frame.msg.currentTarget)
    (arrayDataSlot m.ctx.crypto 0#256)
    (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat)
    (ofNat m.ctx.block.chainId) m.frame.msg.currentTarget

set_option maxHeartbeats 0 in
/-- **`permit` with a long `name` off the deployment chain**, not static, below the depth
limit. -/
theorem pl_permit_long_halts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    {owner spender : Address} {value deadline v r s : Word}
    (hd : PermitCall m.frame.msg.data owner spender value deadline v r s)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hne : ofNat m.ctx.block.chainId ≠ ia.initialChainId)
    (hodd : m.world.sload m.frame.msg.currentTarget 0#256 &&& 1#256 = 1#256)
    (hL : 32 ≤ (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat)
    (hg : 100000 + Str.getterGas
      (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat ≤ m.frame.gasLeft)
    (hg' : m.frame.gasLeft < 2 ^ 256)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit) :
    Halts m (PlPost (plDs m) owner spender value deadline v r s m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2, harg3, harg4, harg5, harg6⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  subst hstd
  unfold PlPost PermitValid plDs
  by_cases hv : v.toNat < 256
  swap
  · have hne := eq_of_ne (Ne.symm (and_255_ne (x := v) (by omega)))
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hne, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    exact ⟨fun h => absurd h.1 hv, fun _ => ⟨_, rfl⟩⟩
  have hv' := and_255_of_lt hv
  by_cases hdl : (ofNat m_ctx.block.timestamp).toNat ≤ deadline.toNat
  swap
  · have hlt' : Word.lt deadline (ofNat m_ctx.block.timestamp) = 1 :=
      (Word.lt_eq_one_iff _ _).2 (by omega)
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hv', hlt', ofAddress_and_addressMask, addressMask_and_ofAddress,
      Solidity.eq_self, iszero_one]
    exact ⟨fun h => absurd h.2.1 hdl, fun _ => ⟨_, rfl⟩⟩
  have hge : Word.lt deadline (ofNat m_ctx.block.timestamp) = 0 := (Word.lt_eq_zero_iff _ _).2 hdl
  pwp_run_to 1060 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3,
    harg4, harg5, harg6, hv', hge, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Solidity.eq_self, iszero_zero]
  refine WP.bind_mono (pl_ds_long _ rfl hj rfl rfl (by simp) (by pjumpdest_disch)
    (Memory.loadWord_storeWord _ _ _) (by simp [Memory.size_storeWord, Memory.size_expand,
      Memory.wordsAfter, Memory.words]) hne hodd hL (by dsimp only; omega))
    (fun _ _ _ h => h.elim) ?_
  rintro _ - ⟨mem, g, sub, rfl, h64, hs, hgb, hgu, hlog⟩
  dsimp only [Machine.resumeWith] at hgb hgu hlog ⊢
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  have hm := Gas.memoryCost_mono (show 128 + 32 * (((Word.shr 1#256 (m_world.sload
    m_msg.currentTarget 0#256)).toNat + 31) / 32) ≤ 256 + 64 * (((Word.shr 1#256 (m_world.sload
    m_msg.currentTarget 0#256)).toNat + 31) / 32) by omega)
  simp only [Str.getterGas] at hg
  refine WP.mono (pl_body _ (le_max_left _ _) (by omega) rfl hj rfl rfl rfl h64 hs hv'
    (by dsimp only; omega) (by dsimp only; omega) rfl hdel1 hdepth hstatic) (fun _ _ h => h) ?_
  intro mf o _ ⟨h1, h2, h3⟩
  refine ⟨fun h => ?_, fun h => h2 fun h' => h ⟨hv, hdl, h'⟩⟩
  obtain ⟨ho, hw, ht, hc, hl⟩ := h1 h.2.2
  exact ⟨ho, hw, ht, hc, hl.trans (by rw [hlog])⟩

set_option maxHeartbeats 0 in
/-- **`permit` with a long `name` off the deployment chain at the call-depth limit**: it
reverts. -/
theorem pl_permit_long_limit {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    {owner spender : Address} {value deadline v r s : Word}
    (hd : PermitCall m.frame.msg.data owner spender value deadline v r s)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hne : ofNat m.ctx.block.chainId ≠ ia.initialChainId)
    (hodd : m.world.sload m.frame.msg.currentTarget 0#256 &&& 1#256 = 1#256)
    (hL : 32 ≤ (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat)
    (hg : 100000 + Str.getterGas
      (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat ≤ m.frame.gasLeft)
    (hg' : m.frame.gasLeft < 2 ^ 256)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : Gas.stackDepthLimit < m.frame.msg.depth + 1) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2, harg3, harg4, harg5, harg6⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  subst hstd
  by_cases hv : v.toNat < 256
  swap
  · have hne := eq_of_ne (Ne.symm (and_255_ne (x := v) (by omega)))
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hne, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    exact ⟨_, rfl⟩
  have hv' := and_255_of_lt hv
  by_cases hdl : (ofNat m_ctx.block.timestamp).toNat ≤ deadline.toNat
  swap
  · have hlt' : Word.lt deadline (ofNat m_ctx.block.timestamp) = 1 :=
      (Word.lt_eq_one_iff _ _).2 (by omega)
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hv', hlt', ofAddress_and_addressMask, addressMask_and_ofAddress,
      Solidity.eq_self, iszero_one]
    exact ⟨_, rfl⟩
  have hge : Word.lt deadline (ofNat m_ctx.block.timestamp) = 0 := (Word.lt_eq_zero_iff _ _).2 hdl
  pwp_run_to 1060 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3,
    harg4, harg5, harg6, hv', hge, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Solidity.eq_self, iszero_zero]
  refine WP.bind_mono (pl_ds_long _ rfl hj rfl rfl (by simp) (by pjumpdest_disch)
    (Memory.loadWord_storeWord _ _ _) (by simp [Memory.size_storeWord, Memory.size_expand,
      Memory.wordsAfter, Memory.words]) hne hodd hL (by dsimp only; omega))
    (fun _ _ _ h => h.elim) ?_
  rintro _ - ⟨mem, g, sub, rfl, h64, hs, hgb, hgu, hlog⟩
  dsimp only [Machine.resumeWith] at hgb hgu hlog ⊢
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  have hm := Gas.memoryCost_mono (show 128 + 32 * (((Word.shr 1#256 (m_world.sload
    m_msg.currentTarget 0#256)).toNat + 31) / 32) ≤ 256 + 64 * (((Word.shr 1#256 (m_world.sload
    m_msg.currentTarget 0#256)).toNat + 31) / 32) by omega)
  simp only [Str.getterGas] at hg
  exact pl_body_limit _ (le_max_left _ _) (by omega) rfl hj rfl rfl rfl h64 hs hv'
    (by dsimp only; omega) (by dsimp only; omega) rfl hdel1 hdepth hstatic

set_option maxHeartbeats 0 in
/-- **`permit` with a long `name` off the deployment chain in a static frame**: it fails. -/
theorem pl_permit_long_static {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = true)
    {owner spender : Address} {value deadline v r s : Word}
    (hd : PermitCall m.frame.msg.data owner spender value deadline v r s)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hne : ofNat m.ctx.block.chainId ≠ ia.initialChainId)
    (hodd : m.world.sload m.frame.msg.currentTarget 0#256 &&& 1#256 = 1#256)
    (hL : 32 ≤ (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat)
    (hg : 100000 + Str.getterGas
      (Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat ≤ m.frame.gasLeft)
    (hg' : m.frame.gasLeft < 2 ^ 256)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx) :
    Halts m (fun _ o => QEDefi.ERC20.Spec.Fails o) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2, harg3, harg4, harg5, harg6⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  subst hstd
  by_cases hv : v.toNat < 256
  swap
  · have hne := eq_of_ne (Ne.symm (and_255_ne (x := v) (by omega)))
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hne, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    trivial
  have hv' := and_255_of_lt hv
  by_cases hdl : (ofNat m_ctx.block.timestamp).toNat ≤ deadline.toNat
  swap
  · have hlt' : Word.lt deadline (ofNat m_ctx.block.timestamp) = 1 :=
      (Word.lt_eq_one_iff _ _).2 (by omega)
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hv', hlt', ofAddress_and_addressMask, addressMask_and_ofAddress,
      Solidity.eq_self, iszero_one]
    trivial
  have hge : Word.lt deadline (ofNat m_ctx.block.timestamp) = 0 := (Word.lt_eq_zero_iff _ _).2 hdl
  pwp_run_to 1060 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3,
    harg4, harg5, harg6, hv', hge, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Solidity.eq_self, iszero_zero]
  refine WP.bind_mono (pl_ds_long _ rfl hj rfl rfl (by simp) (by pjumpdest_disch)
    (Memory.loadWord_storeWord _ _ _) (by simp [Memory.size_storeWord, Memory.size_expand,
      Memory.wordsAfter, Memory.words]) hne hodd hL (by dsimp only; omega))
    (fun _ _ _ h => h.elim) ?_
  rintro _ - ⟨mem, g, sub, rfl, h64, hs, hgb, hgu, hlog⟩
  dsimp only [Machine.resumeWith] at hgb hgu hlog ⊢
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  have hm := Gas.memoryCost_mono (show 128 + 32 * (((Word.shr 1#256 (m_world.sload
    m_msg.currentTarget 0#256)).toNat + 31) / 32) ≤ 256 + 64 * (((Word.shr 1#256 (m_world.sload
    m_msg.currentTarget 0#256)).toNat + 31) / 32) by omega)
  simp only [Str.getterGas] at hg
  exact pl_body_static _ (le_max_left _ _) (by omega) rfl hj rfl rfl rfl h64 hs
    (by dsimp only; omega) hstatic

set_option maxHeartbeats 0 in
/-- **`permit` off the deployment chain with an inconsistent `name` slot word**, in any frame
with no value: it reverts. -/
theorem pl_permit_panic {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) 
    {owner spender : Address} {value deadline v r s : Word}
    (hd : PermitCall m.frame.msg.data owner spender value deadline v r s)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hne : ofNat m.ctx.block.chainId ≠ ia.initialChainId)
    (hnone : nameBytes m.ctx.crypto (m.world.sload m.frame.msg.currentTarget) = none)
    (hg : 100000 ≤ m.frame.gasLeft)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2, harg3, harg4, harg5, harg6⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  subst hstd
  by_cases hv : v.toNat < 256
  swap
  · have hne := eq_of_ne (Ne.symm (and_255_ne (x := v) (by omega)))
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hne, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    exact ⟨_, rfl⟩
  have hv' := and_255_of_lt hv
  by_cases hdl : (ofNat m_ctx.block.timestamp).toNat ≤ deadline.toNat
  swap
  · have hlt' : Word.lt deadline (ofNat m_ctx.block.timestamp) = 1 :=
      (Word.lt_eq_one_iff _ _).2 (by omega)
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hv', hlt', ofAddress_and_addressMask, addressMask_and_ofAddress,
      Solidity.eq_self, iszero_one]
    exact ⟨_, rfl⟩
  have hge : Word.lt deadline (ofNat m_ctx.block.timestamp) = 0 := (Word.lt_eq_zero_iff _ _).2 hdl
  pwp_run_to 1060 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3,
    harg4, harg5, harg6, hv', hge, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Solidity.eq_self, iszero_zero]
  exact pl_ds_panic _ rfl hj rfl rfl (by simp) (Memory.loadWord_storeWord _ _ _)
    (by simp [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words]) hne
    hnone (by dsimp only; omega)

set_option maxHeartbeats 0 in
/-- **`permit` off the deployment chain with a long `name` of more words than the frame has
gas**, in any frame with no value: it fails. -/
theorem pl_permit_huge {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) 
    {owner spender : Address} {value deadline v r s : Word}
    (hd : PermitCall m.frame.msg.data owner spender value deadline v r s)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hne : ofNat m.ctx.block.chainId ≠ ia.initialChainId)
    (hodd : m.world.sload m.frame.msg.currentTarget 0#256 &&& 1#256 = 1#256)
    (hg : 100000 ≤ m.frame.gasLeft)
    (hbig : m.frame.gasLeft + 1 <
      ((Word.shr 1#256 (m.world.sload m.frame.msg.currentTarget 0#256)).toNat + 31) / 32)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx) :
    Halts m (fun _ o => QEDefi.ERC20.Spec.Fails o) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2, harg3, harg4, harg5, harg6⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  subst hstd
  by_cases hv : v.toNat < 256
  swap
  · have hne := eq_of_ne (Ne.symm (and_255_ne (x := v) (by omega)))
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hne, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    trivial
  have hv' := and_255_of_lt hv
  by_cases hdl : (ofNat m_ctx.block.timestamp).toNat ≤ deadline.toNat
  swap
  · have hlt' : Word.lt deadline (ofNat m_ctx.block.timestamp) = 1 :=
      (Word.lt_eq_one_iff _ _).2 (by omega)
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hv', hlt', ofAddress_and_addressMask, addressMask_and_ofAddress,
      Solidity.eq_self, iszero_one]
    trivial
  have hge : Word.lt deadline (ofNat m_ctx.block.timestamp) = 0 := (Word.lt_eq_zero_iff _ _).2 hdl
  pwp_run_to 1060 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3,
    harg4, harg5, harg6, hv', hge, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Solidity.eq_self, iszero_zero]
  exact pl_ds_huge (H := fun _ o => QEDefi.ERC20.Spec.Fails o) ⟨fun _ _ => trivial, fun _ _ => trivial⟩
    _ rfl hj rfl rfl (by simp) (Memory.loadWord_storeWord _ _ _)
    (by simp [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words]) hne
    hodd (by dsimp only; omega) (by dsimp only; omega)

end Verified.Solmate.ERC20.Spec
