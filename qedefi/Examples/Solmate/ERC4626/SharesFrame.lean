import Examples.Solmate.ERC20.TransferFrom
import Examples.Solmate.ERC20.Approve
import Examples.Solmate.ERC4626.SharesBase
import Examples.Solmate.ERC4626.Views
import Examples.Solmate.ERC20.Spec

/-!
# The vault's share-token functions in any frame

`Halts` summaries and `*_refines` theorems for the vault's share `transfer`, `transferFrom`,
`approve` and views from a fresh frame with **any** parents (top level or called by another
contract), in the shape of the asset's callee summaries (`ERC20/Transfer.lean` etc.). Calldata is
described by what the ABI decoder reads (`TwoWordCall`, `ThreeWordCall`).
-/

section

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open EvmLogic.Solidity.ERC20 (transferWorld)

set_option maxHeartbeats 0 in
/-- **`transfer(to, amount)` of the vault's shares, success**, in any non-static frame. -/
theorem sharesTransfer_halts_ok {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {dst : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)).toNat) :
    Halts m (TransferOk dst amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [balanceSlot_solmate] at hbal
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_sub_self_of_le hbal, iszero_zero]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  pwp_codecopy
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨rfl, by simp only [outputMachine, transferWorld, balanceSlot_solmate], rfl, rfl, ?_⟩
  dsimp only [outputMachine]
  evm_gas

set_option maxHeartbeats 0 in
/-- **`transfer(to, amount)` of the vault's shares, insufficient balance**: `Panic(0x11)`. -/
theorem sharesTransfer_halts_revert {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m)
    (hval : m.frame.msg.value = 0) {dst : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 10000 ≤ m.frame.gasLeft)
    (hbal : (m.world.sload m.frame.msg.currentTarget
      (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)).toNat <
        amount.toNat) :
    Halts m (Reverts 10000 m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [balanceSlot_solmate] at hbal
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_sub_self_of_lt hbal, iszero_one]
  pwp_steps
  refine ⟨⟨_, rfl⟩, ?_⟩
  dsimp only [outputMachine]
  evm_gas

set_option maxHeartbeats 0 in
/-- **`approve(spender, amount)` of the vault's shares**: always succeeds. -/
theorem sharesApprove_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {spender : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x095ea7b3 (Word.ofAddress spender) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 40000 ≤ m.frame.gasLeft) :
    Halts m (ApproveOk spender amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  refine ⟨rfl, ?_, rfl, rfl, ?_⟩
  · simp only [outputMachine, ERC20.approveWorld, allowanceSlot_solmate]
  · dsimp only [outputMachine]
    evm_gas

set_option maxHeartbeats 0 in
/-- **`transferFrom(src, dst, amount)` of the vault's shares, success**: the allowance is
infinite or covers `amount`, and the source balance covers `amount`. -/
theorem sharesTransferFrom_halts_ok {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src dst : Address}
    {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (hspend : m.world.sload m.frame.msg.currentTarget
        (ERC20.allowanceSlot m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller) =
        ERC20.maxWord ∨
      amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
        (ERC20.allowanceSlot m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller)).toNat)
    (hbal : amount.toNat ≤ ((ERC20.spendWorld m.ctx.crypto m.world m.frame.msg.currentTarget src
      m.frame.msg.caller amount).sload m.frame.msg.currentTarget
        (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat) :
    Halts m (TransferFromOk src dst amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate, allowanceSlot_solmate] at hbal hspend
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  by_cases hmax : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 4#256)))) = MAXW
  · simp only [hmax, Solidity.eq_self, ↓reduceIte] at hbal ⊢
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [gt_sub_self_of_le hbal, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    pwp_codecopy
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine ⟨rfl, ?_, rfl, rfl, ?_⟩
    · simp only [outputMachine, ERC20.transferFromWorld, ERC20.transferWorld, transferWorld,
        ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate,
        allowanceSlot_solmate, hmax, ↓reduceIte]
    · dsimp only [outputMachine]
      evm_gas
  · simp only [eq_of_ne hmax, hmax, ↓reduceIte] at hbal ⊢
    have hle := hspend.resolve_left hmax
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [gt_sub_self_of_le hle, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [gt_sub_self_of_le hbal, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    pwp_codecopy
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine ⟨rfl, ?_, rfl, rfl, ?_⟩
    · simp only [outputMachine, ERC20.transferFromWorld, ERC20.transferWorld, transferWorld,
        ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate,
        allowanceSlot_solmate, hmax, ↓reduceIte]
    · dsimp only [outputMachine]
      evm_gas

set_option maxHeartbeats 0 in
/-- **`transferFrom(src, dst, amount)` of the vault's shares, revert**: the allowance (unless
infinite) or the source balance does not cover `amount`. -/
theorem sharesTransferFrom_halts_revert {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src dst : Address}
    {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (hfail : ¬ ((m.world.sload m.frame.msg.currentTarget
        (ERC20.allowanceSlot m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller) =
        ERC20.maxWord ∨
      amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
        (ERC20.allowanceSlot m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller)).toNat) ∧
      amount.toNat ≤ ((ERC20.spendWorld m.ctx.crypto m.world m.frame.msg.currentTarget src
        m.frame.msg.caller amount).sload m.frame.msg.currentTarget
          (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat)) :
    Halts m (Reverts 80000 m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate, allowanceSlot_solmate] at hfail
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  by_cases hmax : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 4#256)))) = MAXW
  · simp only [hmax, Solidity.eq_self, ↓reduceIte, true_or, true_and,
      Nat.not_le] at hfail ⊢
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [gt_sub_self_of_lt hfail, iszero_one]
    pwp_steps
    refine ⟨⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]
    evm_gas
  · simp only [eq_of_ne hmax, hmax, ↓reduceIte, false_or] at hfail ⊢
    by_cases hle : amount.toNat ≤ (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
          (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 4#256))))).toNat
    · simp only [hle, true_and, Nat.not_le] at hfail
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      simp only [gt_sub_self_of_le hle, iszero_zero]
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      simp only [gt_sub_self_of_lt hfail, iszero_one]
      pwp_steps
      refine ⟨⟨_, rfl⟩, ?_⟩
      dsimp only [outputMachine]
      evm_gas
    · rw [Nat.not_le] at hle
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      simp only [gt_sub_self_of_lt hle, iszero_one]
      pwp_steps
      refine ⟨⟨_, rfl⟩, ?_⟩
      dsimp only [outputMachine]
      evm_gas

end Examples.Solmate.ERC4626

end

section

/-! ## Share-token functions refine `Token` (hash hypotheses as for the asset) -/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open EvmLogic.Solidity.ERC20 (transferWorld view_transferWorld)
open QEDefi.Math QEDefi.ERC20 Examples.Solmate.ERC4626.Shares

/-- **`transfer(dst, amount)` of the vault's shares refines `Token.transfer`**, any frame. -/
theorem sharesTransfer_refines {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {dst : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hs : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)
    (hdst : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate dst)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    match t.transfer m.frame.msg.caller dst amount.toNat with
    | some t' => Halts m (fun mf o => TransferOk dst amount m mf o ∧
        RepOn (TransferAllowances m.ctx.crypto m.frame.msg.caller dst)
          (ERC20.view m.ctx.crypto ERC20.Layout.solmate mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 10000 m) := by
  split
  · rename_i t' hT
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1
      ((transfer_isSome_iff hr m.frame.msg.caller dst amount).2 (by simp [hT]))
    have hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
        (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)).toNat := by
      unfold ERC20.Model.transfer at hm
      split at hm
      · assumption
      · cases hm
    obtain ⟨h1, h2, h3, -⟩ := view_transferWorld (token := m.frame.msg.currentTarget) hs hdst hm
    have hrep := rep_transfer hr hw hm hT
    refine (sharesTransfer_halts_ok m hf hval hstatic hd hsz hg hbal).mono
      fun mf o _ hok => ⟨hok, ?_⟩
    rw [hok.2.1]
    exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1 hp.2) hrep
  · rename_i hT
    have hbal : (m.world.sload m.frame.msg.currentTarget
        (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)).toNat <
          amount.toNat := by
      have := hr.balanceOf m.frame.msg.caller
      simp only [ERC20.view] at this
      rw [this]
      unfold Token.transfer at hT
      split at hT
      · assumption
      · cases hT
    exact sharesTransfer_halts_revert m hf hval hd hsz (by omega) hbal

/-- **`transferFrom(src, dst, amount)` of the vault's shares refines `Token.transferFrom`**,
any frame. -/
theorem sharesTransferFrom_refines {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {src dst : Address} {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (hs : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate src)
    (hdst : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate dst)
    (ha : ERC20.AllowanceSlotOk m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    match t.transferFrom m.frame.msg.caller src dst amount.toNat with
    | some t' => Halts m (fun mf o => TransferFromOk src dst amount m mf o ∧
        RepOn (TransferFromAllowances m.ctx.crypto m.frame.msg.caller src dst)
          (ERC20.view m.ctx.crypto ERC20.Layout.solmate mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 80000 m) := by
  split
  · rename_i t' hT
    obtain ⟨t₁, hsp, htr⟩ := Option.bind_eq_some_iff.1 hT
    obtain ⟨s₁, hm₁⟩ := Option.isSome_iff_exists.1
      ((spend_isSome_iff hr src m.frame.msg.caller amount).2 (by simp [hsp]))
    have hal := allowance_cond_of_spend hr hsp
    have hbal : amount.toNat ≤ ((ERC20.spendWorld m.ctx.crypto m.world m.frame.msg.currentTarget
        src m.frame.msg.caller amount).sload m.frame.msg.currentTarget
          (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat := by
      rw [balance_spendWorld ha hm₁, hr.balanceOf src, ← (Token.spend_eq_some hsp).1]
      exact (Token.transfer_eq_some.1 htr).1
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1
      ((transferFrom_isSome_iff hr m.frame.msg.caller src dst amount).2 (by simp [hT]))
    obtain ⟨h1, h2, h3, -⟩ := ERC20.view_transferFromWorld hs hdst ha hm
    have hrep := rep_transferFrom hr hw hm hT
    refine (sharesTransferFrom_halts_ok m hf hval hstatic hd hsz hg hal hbal).mono
      fun mf o _ hok => ⟨hok, ?_⟩
    rw [hok.2.1]
    exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1.1 hp.1.2 hp.2) hrep
  · rename_i hT
    refine sharesTransferFrom_halts_revert m hf hval hstatic hd hsz hg ?_
    rintro ⟨hal, hbal⟩
    cases hsp : t.spend src m.frame.msg.caller amount.toNat with
    | none =>
      have ha' := hr.allowance src m.frame.msg.caller trivial
      unfold Token.spend at hsp
      split at hsp
      · cases hsp
      · rename_i hmax
        split at hsp
        · rename_i hlt
          rcases hal with h | h
          · exact hmax (by rw [← ha']; exact (eq_maxWord_iff _).1 h)
          · simp only [ERC20.view] at ha'; omega
        · cases hsp
    | some t₁ =>
      have htr : t₁.transfer src dst amount.toNat = none := by
        unfold Token.transferFrom at hT
        rw [hsp] at hT
        simpa using hT
      obtain ⟨s₁, hm₁⟩ := Option.isSome_iff_exists.1
        ((spend_isSome_iff hr src m.frame.msg.caller amount).2 (by simp [hsp]))
      rw [balance_spendWorld ha hm₁, hr.balanceOf src, ← (Token.spend_eq_some hsp).1] at hbal
      unfold Token.transfer at htr
      split at htr
      · omega
      · cases htr

/-- **`approve(spender, amount)` of the vault's shares refines `Token.approve`**, any frame. -/
theorem sharesApprove_refines {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {spender : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x095ea7b3 (Word.ofAddress spender) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 40000 ≤ m.frame.gasLeft)
    (ha : ERC20.AllowanceSlotOk m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller spender)
    {t : Token Address} (hr : Rep (assetView m) t) :
    Halts m (fun mf o => ApproveOk spender amount m mf o ∧
      RepOn (ApproveAllowances m.ctx.crypto m.frame.msg.caller spender)
        (ERC20.view m.ctx.crypto ERC20.Layout.solmate mf.world m.frame.msg.currentTarget)
        (t.approve m.frame.msg.caller spender amount.toNat)) := by
  obtain ⟨h1, h2, h3, -⟩ := ERC20.view_approveWorld (w := m.world)
    (token := m.frame.msg.currentTarget) (amount := amount) ha
  refine (sharesApprove_halts m hf hval hstatic hd hsz hg).mono fun mf o _ hok => ⟨hok, ?_⟩
  rw [hok.2.1]
  exact RepOn.of_eq h1 h2 h3 (rep_approve hr m.frame.msg.caller spender amount)

end Examples.Solmate.ERC4626

end

section

/-! ## Share-token views: return the stored word, world unchanged -/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

set_option maxHeartbeats 0 in
/-- **`totalSupply()` of the vault's shares**, in any frame. -/
theorem sharesTotalSupply_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hd : NoArgCall m.frame.msg.data 0x18160ddd) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget 2#256) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`balanceOf(a)` of the vault's shares**, in any frame. -/
theorem sharesBalanceOf_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0) {a : Address}
    (hd : AddrCall m.frame.msg.data 0x70a08231 a) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget
      (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate a)) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`allowance(owner, spender)` of the vault's shares**, in any frame. -/
theorem sharesAllowance_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    {owner spender : Address}
    (hd : TwoWordCall m.frame.msg.data 0xdd62ed3e (Word.ofAddress owner) (Word.ofAddress spender))
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget
      (ERC20.allowanceSlot m.ctx.crypto ERC20.Layout.solmate owner spender)) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`decimals()` of the vault**, in any frame: the immutable as a `uint8`. -/
theorem sharesDecimals_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hd : NoArgCall m.frame.msg.data 0x313ce567) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (i.decimals &&& 255#256) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64,
    Shares.readBytes_code_decimals]
  exact ⟨rfl, rfl⟩

end Examples.Solmate.ERC4626

end
