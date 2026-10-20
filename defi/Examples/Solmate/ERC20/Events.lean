import Examples.Solmate.ERC20.Approve
import Defi.ERC4626.Logs
import Examples.Solmate.ERC20.TransferFrom
import Examples.Solmate.ERC20.MintBurn
import Examples.Solmate.ERC4626.Invariants.System
import Examples.Solmate.ERC4626.Events

/-!
# Events of the asset's `transfer` and `approve`: bytecode

Companions of `transfer_halts_ok` (`AssetTransfer.lean`) and `approve_halts`
(`AssetApprove.lean`) that also determine the frame's logs: the same symbolic execution, with
the postcondition strengthened by the log the `LOG3` appends.

* `transfer_halts_ok_events`: `TransferOk` and the frame's logs gain exactly
  `Transfer(caller, dst, amount)` emitted by the asset;
* `approve_halts_events`: `ApproveOk` and the logs gain exactly `Approval(caller, spender,
  amount)`.

The topic is the `PUSH32` / code-copied constant of the bytecode; the indexed addresses are the
masked calldata words; the data is the amount, stored at the free pointer.
-/

section

namespace Examples.Solmate.ERC20
open Examples.Solmate.ERC4626 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts
open EvmLogic.Solidity.ERC20 (transferWorld)

set_option maxHeartbeats 0 in
/-- **`transfer(dst, amount)` of the asset, success, with its log**: as `transfer_halts_ok`,
and the frame's logs gain `Transfer(caller, dst, amount)`. -/
theorem transfer_halts_ok_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {dst : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)).toNat) :
    Halts m (fun mf o => TransferOk dst amount m mf o ∧
      mf.frame.sub.logs = m.frame.sub.logs.push
        (transferLog m.frame.msg.currentTarget m.frame.msg.caller dst amount)) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [balanceSlot_solmate] at hbal
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_sub_self_of_le hbal, iszero_zero]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  pwp_codecopy
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨⟨rfl, by simp only [outputMachine, transferWorld, balanceSlot_solmate], rfl, rfl, ?_⟩,
    ?_⟩
  · dsimp only [outputMachine]
    evm_gas
  · dsimp only [outputMachine]
    event_log [amount]

set_option maxHeartbeats 0 in
/-- **`approve(spender, amount)` of the asset, with its log**: as `approve_halts`, and the
frame's logs gain `Approval(caller, spender, amount)`. -/
theorem approve_halts_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {spender : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x095ea7b3 (Word.ofAddress spender) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 40000 ≤ m.frame.gasLeft) :
    Halts m (fun mf o => ApproveOk spender amount m mf o ∧
      mf.frame.sub.logs = m.frame.sub.logs.push
        (approvalLog m.frame.msg.currentTarget m.frame.msg.caller spender amount)) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  refine ⟨⟨rfl, ?_, rfl, rfl, ?_⟩, ?_⟩
  · simp only [outputMachine, ERC20.approveWorld, allowanceSlot_solmate]
  · dsimp only [outputMachine]
    evm_gas
  · dsimp only [outputMachine]
    event_log [amount]

end Examples.Solmate.ERC20

end

section

/-!
## Events of the asset's `transferFrom`: bytecode

`transferFrom_halts_ok_events`: the companion of `transferFrom_halts_ok`
(`AssetTransferFrom.lean`) that also determines the frame's logs — on both success paths
(infinite and finite allowance) the frame's logs gain exactly `Transfer(src, dst, amount)`
emitted by the asset. Solmate emits **no** `Approval` when it spends the allowance.
-/

namespace Examples.Solmate.ERC20
open Examples.Solmate.ERC4626 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts
open EvmLogic.Solidity.ERC20 (transferWorld)

set_option maxHeartbeats 0 in
/-- **`transferFrom(src, dst, amount)` of the asset, success, with its log**: as
`transferFrom_halts_ok`, and the frame's logs gain `Transfer(src, dst, amount)` (and nothing
else: no `Approval`). -/
theorem transferFrom_halts_ok_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
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
    Halts m (fun mf o => TransferFromOk src dst amount m mf o ∧
      mf.frame.sub.logs = m.frame.sub.logs.push
        (transferLog m.frame.msg.currentTarget src dst amount)) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate, allowanceSlot_solmate] at hbal hspend
  have hagree := assetJumpDestsAgree ia
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
    refine ⟨⟨rfl, ?_, rfl, rfl, ?_⟩, ?_⟩
    · simp only [outputMachine, ERC20.transferFromWorld, ERC20.transferWorld, transferWorld,
        ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate,
        allowanceSlot_solmate, hmax, ↓reduceIte]
    · dsimp only [outputMachine]
      evm_gas
    · dsimp only [outputMachine]
      event_log [amount]
  · simp only [eq_of_ne hmax, hmax, ↓reduceIte] at hbal ⊢
    have hle := hspend.resolve_left hmax
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [gt_sub_self_of_le hle, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [gt_sub_self_of_le hbal, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    pwp_codecopy
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine ⟨⟨rfl, ?_, rfl, rfl, ?_⟩, ?_⟩
    · simp only [outputMachine, ERC20.transferFromWorld, ERC20.transferWorld, transferWorld,
        ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate,
        allowanceSlot_solmate, hmax, ↓reduceIte]
    · dsimp only [outputMachine]
      evm_gas
    · dsimp only [outputMachine]
      event_log [amount]

end Examples.Solmate.ERC20

end

section

/-!
## Events of the asset's `mint` and `burn`: bytecode

Companions of `mint_halts_ok` (`AssetMint.lean`) and `burn_halts_ok` (`AssetBurn.lean`) that
also determine the frame's logs: `MockERC20.mint(dst, amount)` emits `Transfer(0, dst, amount)`
and `burn(src, amount)` emits `Transfer(src, 0, amount)` (Solmate's `_mint` / `_burn`).
-/

namespace Examples.Solmate.ERC20
open Examples.Solmate.ERC4626 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts

set_option maxHeartbeats 0 in
/-- **`mint(dst, amount)` of the asset, success, with its log**: as `mint_halts_ok`, and the
frame's logs gain `Transfer(0, dst, amount)`. -/
theorem mint_halts_ok_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {dst : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x40c10f19 (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hov : (m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat < 2 ^ 256) :
    Halts m (fun mf o => MintOk dst amount m mf o ∧
      mf.frame.sub.logs = m.frame.sub.logs.push
        (transferLog m.frame.msg.currentTarget 0 dst amount)) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_add_self_of_lt hov, iszero_zero]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  pwp_codecopy
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine WP.halt_of_step (step_stop ?_) (by same_frame) ⟨⟨rfl, ?_, rfl, rfl, ?_⟩, ?_⟩
  · pcode_fact
  · simp only [mintWorld, balanceSlot_solmate]
  · evm_gas
  · event_log [amount]

set_option maxHeartbeats 0 in
/-- **`burn(src, amount)` of the asset, success, with its log**: as `burn_halts_ok`, and the
frame's logs gain `Transfer(src, 0, amount)`. -/
theorem burn_halts_ok_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat) :
    Halts m (fun mf o => BurnOk src amount m mf o ∧
      mf.frame.sub.logs = m.frame.sub.logs.push
        (transferLog m.frame.msg.currentTarget src 0 amount)) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [balanceSlot_solmate] at hbal
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_sub_self_of_le hbal, iszero_zero]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  pwp_codecopy
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine WP.halt_of_step (step_stop ?_) (by same_frame) ⟨⟨rfl, ?_, rfl, rfl, ?_⟩, ?_⟩
  · pcode_fact
  · simp only [burnWorld, balanceSlot_solmate]
  · evm_gas
  · event_log [amount]

end Examples.Solmate.ERC20

end

section

/-!
## Events of the asset's functions against the model

For the deployed asset (Solmate `MockERC20`, any immutables), the logs of `transfer`,
`transferFrom`, `approve`, `mint` and `burn` are the encoding of the model's events
(`Solmate.Events`):

* **Frame form** (`assetTransfer_events`, …): in any non-static fresh frame (top level, or the
  vault's `safeTransfer` / `safeTransferFrom`), with the hypotheses of the refinement theorems
  `assetTransfer_refines`, … (fewer: no hash or well-formedness hypothesis is needed to know
  the events, except `AllowanceSlotOk` for `transferFrom`), the frame ends as `EventsPost`
  with `L = encode vault asset (Events.transfer .asset t caller dst amount)` (… for the other
  functions), `t` the ledger the asset's storage represents: on success it appended exactly
  these logs, on revert the model emits nothing. The success cases are the bytecode
  companions `*_halts_ok_events`, the reverts the existing `*_halts_revert` theorems.
* **Top-level form** (`assetTransfer_events_call`, …): a top-level call to the deployed asset
  returns a result whose `logs` are `encode vault asset (events (abs ctx.crypto w vault asset)
  op)` for the model operation `op` (also when it reverts: then both are empty).
-/

namespace Examples.Solmate.ERC20
open Examples.Solmate.ERC4626 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.ERC4626 Defi.Math Defi.ERC20 Defi.ERC4626.Solmate Examples.Solmate.ERC4626.Shares

/-! ## Frame form -/

/-- **`transfer(dst, amount)` of the asset emits the model's events**, in any non-static
frame. -/
theorem assetTransfer_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {dst : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    {t : Token Address} (hr : Rep (assetView m) t) (vault : Address) :
    Halts m (EventsPost m (encode vault m.frame.msg.currentTarget
      (Events.transfer .asset t m.frame.msg.caller dst amount.toNat))) := by
  have hb := hr.balanceOf m.frame.msg.caller
  simp only [ERC20.view] at hb
  cases hT : t.transfer m.frame.msg.caller dst amount.toNat with
  | some t' =>
    have hbal := (Token.transfer_eq_some.1 hT).1
    rw [← hb] at hbal
    refine (transfer_halts_ok_events m hf hval hstatic hd hsz hg hbal).mono
      fun mf o _ ⟨hok, hl⟩ => ?_
    rw [hok.1]
    simp only [Events.transfer, hT, Option.isSome_some, ↓reduceIte]
    exact eventsPost_success (by rw [hl]; exact push_eq_encode (toLog_transfer ..))
  | none =>
    have hbal : (m.world.sload m.frame.msg.currentTarget
        (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)).toNat <
          amount.toNat := by
      rw [hb]
      unfold Token.transfer at hT
      split at hT
      · assumption
      · cases hT
    refine (transfer_halts_revert m hf hval hd hsz (by omega) hbal).mono fun mf o _ hrev => ?_
    simp only [Events.transfer, hT, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      encode_nil]
    exact eventsPost_revert hrev.1

/-- **`transferFrom(src, dst, amount)` of the asset emits the model's events** (`Transfer`
only, no `Approval`), in any non-static frame. -/
theorem assetTransferFrom_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {src dst : Address} {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (ha : ERC20.AllowanceSlotOk m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller)
    {t : Token Address} (hr : Rep (assetView m) t) (vault : Address) :
    Halts m (EventsPost m (encode vault m.frame.msg.currentTarget
      (Events.transferFrom .asset t m.frame.msg.caller src dst amount.toNat))) := by
  cases hT : t.transferFrom m.frame.msg.caller src dst amount.toNat with
  | some t' =>
    obtain ⟨t₁, hsp, htr⟩ := Option.bind_eq_some_iff.1 hT
    obtain ⟨s₁, hm₁⟩ := Option.isSome_iff_exists.1
      ((spend_isSome_iff hr src m.frame.msg.caller amount).2 (by simp [hsp]))
    have hal := allowance_cond_of_spend hr hsp
    have hbal : amount.toNat ≤ ((ERC20.spendWorld m.ctx.crypto m.world m.frame.msg.currentTarget
        src m.frame.msg.caller amount).sload m.frame.msg.currentTarget
          (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat := by
      rw [balance_spendWorld ha hm₁, hr.balanceOf src, ← (Token.spend_eq_some hsp).1]
      exact (Token.transfer_eq_some.1 htr).1
    refine (transferFrom_halts_ok_events m hf hval hstatic hd hsz hg hal hbal).mono
      fun mf o _ ⟨hok, hl⟩ => ?_
    rw [hok.1]
    simp only [Events.transferFrom, hT, Option.isSome_some, ↓reduceIte]
    exact eventsPost_success (by rw [hl]; exact push_eq_encode (toLog_transfer ..))
  | none =>
    refine (transferFrom_halts_revert m hf hval hstatic hd hsz hg ?_).mono fun mf o _ hrev => ?_
    · rintro ⟨hal, hbal⟩
      cases hsp : t.spend src m.frame.msg.caller amount.toNat with
      | none =>
        have ha' := hr.allowance src m.frame.msg.caller trivial
        unfold Token.spend at hsp
        split at hsp
        · cases hsp
        · rename_i hmax
          split at hsp
          · rcases hal with h | h
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
    · simp only [Events.transferFrom, hT, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        encode_nil]
      exact eventsPost_revert hrev.1

/-- **`approve(spender, amount)` of the asset emits the model's event**, in any non-static
frame. -/
theorem assetApprove_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {spender : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x095ea7b3 (Word.ofAddress spender) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 40000 ≤ m.frame.gasLeft) (vault : Address) :
    Halts m (EventsPost m (encode vault m.frame.msg.currentTarget
      (Events.approve .asset m.frame.msg.caller spender amount.toNat))) :=
  (approve_halts_events m hf hval hstatic hd hsz hg).mono fun mf o _ ⟨hok, hl⟩ => by
    rw [hok.1]
    exact eventsPost_success (by rw [hl]; exact push_eq_encode (toLog_approval ..))

/-- **`mint(dst, amount)` of the asset emits the model's events**, in any non-static frame. -/
theorem assetMint_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {dst : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x40c10f19 (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    {t : Token Address} (hr : Rep (assetView m) t) (vault : Address) :
    Halts m (EventsPost m (encode vault m.frame.msg.currentTarget
      (Events.mint .asset t dst amount.toNat))) := by
  have hts : (m.world.sload m.frame.msg.currentTarget 2#256).toNat = t.totalSupply :=
    hr.totalSupply
  cases hT : t.mint dst amount.toNat with
  | some t' =>
    have hov := (Token.mint_eq_some.1 hT).1
    refine (mint_halts_ok_events m hf hval hstatic hd hsz hg
      (by rw [hts]; unfold MAX at hov; omega)).mono fun mf o _ ⟨hok, hl⟩ => ?_
    rw [hok.1]
    simp only [Events.mint, hT, Option.isSome_some, ↓reduceIte]
    exact eventsPost_success (by rw [hl]; exact push_eq_encode (toLog_transfer ..))
  | none =>
    have hov : MAX < t.totalSupply + amount.toNat := by
      unfold Token.mint at hT
      split at hT
      · assumption
      · cases hT
    refine (mint_halts_revert m hf hval hd hsz (by omega)
      (by rw [hts]; unfold MAX at hov; omega)).mono fun mf o _ hrev => ?_
    simp only [Events.mint, hT, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, encode_nil]
    exact eventsPost_revert hrev.1

/-- **`burn(src, amount)` of the asset emits the model's events**, in any non-static frame. -/
theorem assetBurn_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {src : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    {t : Token Address} (hr : Rep (assetView m) t) (vault : Address) :
    Halts m (EventsPost m (encode vault m.frame.msg.currentTarget
      (Events.burn .asset t src amount.toNat))) := by
  have hbal : (m.world.sload m.frame.msg.currentTarget
      (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat = t.balanceOf src :=
    hr.balanceOf src
  cases hT : t.burn src amount.toNat with
  | some t' =>
    have hv := (Token.burn_eq_some.1 hT).1
    refine (burn_halts_ok_events m hf hval hstatic hd hsz hg (by rw [hbal]; exact hv)).mono
      fun mf o _ ⟨hok, hl⟩ => ?_
    rw [hok.1]
    simp only [Events.burn, hT, Option.isSome_some, ↓reduceIte]
    exact eventsPost_success (by rw [hl]; exact push_eq_encode (toLog_transfer ..))
  | none =>
    have hlt : t.balanceOf src < amount.toNat := by
      unfold Token.burn at hT
      split at hT
      · assumption
      · cases hT
    refine (burn_halts_revert m hf hval hd hsz (by omega) (by rw [hbal]; exact hlt)).mono
      fun mf o _ hrev => ?_
    simp only [Events.burn, hT, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, encode_nil]
    exact eventsPost_revert hrev.1

/-! ## Top-level form -/

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

/-- Short calldata fits the frame theorems' size bound. -/
theorem encodeCall_size_lt (sel : Nat) (args : List Word) (h : args.length ≤ 3) :
    (Abi.encodeCall sel args).size < 2 ^ 64 := by
  rw [Abi.size_encodeCall]; omega

/-- Lift a frame theorem `EventsPost` about the start of a top-level call to the deployed asset
to the result of `processMessageCall`. -/
theorem asset_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) {data : ByteArray}
    {L : Array Log}
    (h : ∀ ia : SolmateAsset.Immutables,
      let m := startMachine ctx w tr
        (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller data gas wa wk)
      Fresh (SolmateAsset.runtimeCodeWith ia) m → Halts m (EventsPost m L)) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code asset) asset caller data gas wa wk) = .ok res ∧ res.logs = L := by
  obtain ⟨ia, hcode⟩ := hdep.assetCode
  rw [hcode]
  exact events_call hdeleg (delegatedAddress?_assetCode ia) (hdep.assetNotPrecompile _)
    (h ia (fresh_startMachine ctx w tr
      (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller data gas wa wk)))

/-- **`asset.transfer(dst, amount)` at the top level**: the result's logs are the model's
events, encoded. -/
theorem assetTransfer_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (dst : Address) (amount : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code asset) asset caller
          (Abi.encodeCall 0xa9059cbb [Word.ofAddress dst, amount]) gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.assetTransfer caller dst amount.toNat)) := by
  exact asset_events_call hdep hdeleg fun _ hf => assetTransfer_events _ hf rfl rfl
    (Invariants.twoWordCall_encodeCall (by decide) _ _)
    (encodeCall_size_lt _ _ (by simp)) hgas (rep_toToken _) vault

/-- **`asset.transferFrom(src, dst, amount)` at the top level**: the result's logs are the
model's events, encoded. -/
theorem assetTransferFrom_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 90000 ≤ gas)
    {src : Address} (ha : ERC20.AllowanceSlotOk ctx.crypto ERC20.Layout.solmate src caller)
    (dst : Address) (amount : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code asset) asset caller
          (Abi.encodeCall 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, amount])
          gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset)
          (.assetTransferFrom caller src dst amount.toNat)) := by
  exact asset_events_call hdep hdeleg fun _ hf => assetTransferFrom_events _ hf rfl rfl
    (Invariants.threeWordCall_encodeCall (by decide) _ _ _)
    (encodeCall_size_lt _ _ (by simp)) hgas ha (rep_toToken _) vault

/-- **`asset.approve(spender, amount)` at the top level**: the result's logs are the model's
event, encoded. -/
theorem assetApprove_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 40000 ≤ gas)
    (spender : Address) (amount : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code asset) asset caller
          (Abi.encodeCall 0x095ea7b3 [Word.ofAddress spender, amount]) gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.assetApprove caller spender amount.toNat)) := by
  exact asset_events_call hdep hdeleg fun _ hf => assetApprove_events _ hf rfl rfl
    (Invariants.twoWordCall_encodeCall (by decide) _ _)
    (encodeCall_size_lt _ _ (by simp)) hgas vault

/-- **`asset.mint(dst, amount)` at the top level** (any caller): the result's logs are the
model's events, encoded. -/
theorem assetMint_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (dst : Address) (amount : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code asset) asset caller
          (Abi.encodeCall 0x40c10f19 [Word.ofAddress dst, amount]) gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.assetMint dst amount.toNat)) := by
  exact asset_events_call hdep hdeleg fun _ hf => assetMint_events _ hf rfl rfl
    (Invariants.twoWordCall_encodeCall (by decide) _ _)
    (encodeCall_size_lt _ _ (by simp)) hgas (rep_toToken _) vault

/-- **`asset.burn(src, amount)` at the top level** (any caller): the result's logs are the
model's events, encoded. -/
theorem assetBurn_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 60000 ≤ gas)
    (src : Address) (amount : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code asset) asset caller
          (Abi.encodeCall 0x9dc29fac [Word.ofAddress src, amount]) gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.assetBurn src amount.toNat)) := by
  exact asset_events_call hdep hdeleg fun _ hf => assetBurn_events _ hf rfl rfl
    (Invariants.twoWordCall_encodeCall (by decide) _ _)
    (encodeCall_size_lt _ _ (by simp)) hgas (rep_toToken _) vault

end Examples.Solmate.ERC20

end
