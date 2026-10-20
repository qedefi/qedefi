import Examples.Solmate.ERC4626.SharesCode
import Defi.ERC4626.Logs

/-!
# Events of the vault's share-token functions: bytecode

Companions of `transfer_ok`, `approve_ok`, `transferFrom_ok` (`SharesTransfer.lean`, …): the
same top-level symbolic executions, whose conclusions also give the result's logs —
`Transfer(caller, dst, amount)`, `Approval(caller, spender, amount)`, and
`Transfer(src, dst, amount)` (Solmate's `transferFrom` emits no `Approval`), each emitted by the
vault. The reverting runs need no companion: a failed top-level call has no logs
(`run_logs_of_fail`).
-/

namespace Examples.Solmate.ERC4626.Shares
open Defi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts EvmLogic.Solidity.Dispatch EvmLogic.Solidity.ERC20 EvmLean.Bytes

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller src dst spender : Address} {amount : Word} {gas : Nat} {warmAddrs : AddressSet}
  {warmKeys : StorageKeySet}

/-- The logs of a successful top-level result are the frame's. -/
theorem topLevelResult_logs_of_success {t : Option Address} {w : World} {tr : TransientStorage}
    {r : ChildResult} (h : r.success = true) : (topLevelResult t w tr r).logs = r.sub.logs := by
  unfold topLevelResult
  simp [h]

set_option maxHeartbeats 10000000 in
/-- **`transfer`, success, with its log**: `transfer_ok`, and the result's logs are
`Transfer(caller, dst, amount)` of the vault. -/
theorem transfer_ok_events (hgas : 100000 ≤ gas)
    (hbal : amount.toNat ≤ ((view ctx.crypto Layout.solmate w vault).balanceOf caller).toNat)
    (k : Nat) :
    ∃ r, run (k + 400) (start ctx w tr
        (vaultCall i vault caller (transferData dst amount) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = transferWorld ctx.crypto w vault caller dst amount ∧
      r.logs = #[transferLog vault caller dst amount] := by
  have hjd := jumpDestsAgree i
  have hbal' : amount.toNat ≤
      (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (BitVec.ofNat 256 3)))).toNat := hbal
  rw [show k + 400 = (k + 349) + 51 by omega, run_start_transfer (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [transferData]
  simp only [gt_sub_self_of_le hbal']
  psol_steps [transferData]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [ChildResult.success]
  · simp only [topLevelResult_output]
    decide +kernel
  · simp only [topLevelResult_world]
    rfl
  · rw [topLevelResult_logs_of_success]
    rotate_left
    · simp [ChildResult.success]
    event_log [amount]

set_option maxHeartbeats 10000000 in
/-- **`approve`, with its log**: `approve_ok`, and the result's logs are `Approval(caller,
spender, amount)` of the vault. -/
theorem approve_ok_events (hgas : 100000 ≤ gas) (k : Nat) :
    ∃ r, run (k + 300) (start ctx w tr
        (vaultCall i vault caller (approveData spender amount) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = approveWorld ctx.crypto w vault caller spender amount ∧
      r.logs = #[approvalLog vault caller spender amount] := by
  have hjd := jumpDestsAgree i
  rw [show k + 300 = (k + 259) + 41 by omega, run_start_approve (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [approveData]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [ChildResult.success]
  · simp only [topLevelResult_output]
    decide +kernel
  · simp only [topLevelResult_world]
    rfl
  · rw [topLevelResult_logs_of_success]
    rotate_left
    · simp [ChildResult.success]
    event_log [amount]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
/-- **`transferFrom`, success, with its log**: `transferFrom_ok`, and the result's logs are
`Transfer(src, dst, amount)` of the vault (no `Approval`). -/
theorem transferFrom_ok_events (hgas : 100000 ≤ gas)
    (hal : (view ctx.crypto Layout.solmate w vault).allowance src caller = maxWord ∨
      amount.toNat ≤ ((view ctx.crypto Layout.solmate w vault).allowance src caller).toNat)
    (hbal : amount.toNat ≤ ((spendWorld ctx.crypto w vault src caller amount).sload vault
      (balanceSlot ctx.crypto Layout.solmate src)).toNat) (k : Nat) :
    ∃ r, run (k + 500) (start ctx w tr
        (vaultCall i vault caller (transferFromData src dst amount) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = transferFromWorld ctx.crypto w vault caller src dst amount ∧
      r.logs = #[transferLog vault src dst amount] := by
  have hjd := jumpDestsAgree i
  rw [show k + 500 = (k + 444) + 56 by omega, run_start_transferFrom (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [transferFromData]
  by_cases hmax : (view ctx.crypto Layout.solmate w vault).allowance src caller = maxWord
  · have hmax' : w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4))))) =
        maxWord := hmax
    simp only [eq_maxWord_of_eq hmax']
    psol_steps [transferFromData]
    have hbal' : amount.toNat ≤ (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
        ofWord (BitVec.ofNat 256 3)))).toNat := by
      simp only [spendWorld, show w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) =
        maxWord from hmax, ↓reduceIte] at hbal
      exact hbal
    simp only [gt_sub_self_of_le hbal']
    psol_steps [transferFromData]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [topLevelResult_success]; rfl
    · simp only [topLevelResult_output]
      decide +kernel
    · simp only [topLevelResult_world, transferFromWorld, spendWorld,
        show w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) = maxWord from hmax,
        ↓reduceIte]
      rfl
    · rw [topLevelResult_logs_of_success]
      rotate_left
      · rfl
      event_log [amount]
  · have hmax' : w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4))))) ≠
        maxWord := hmax
    have hal' : amount.toNat ≤ (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
          ofWord (BitVec.ofNat 256 4)))))).toNat := hal.resolve_left hmax
    simp only [eq_maxWord_of_ne hmax']
    psol_steps [transferFromData]
    simp only [gt_sub_self_of_le hal']
    psol_steps [transferFromData]
    have hbal' : amount.toNat ≤ ((w.sstore vault (ctx.crypto.keccak256
        (ofWord (Word.ofAddress caller) ++ ofWord (ctx.crypto.keccak256
          (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4)))))
        (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
          ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
            ofWord (BitVec.ofNat 256 4))))) - amount)).sload vault
        (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 3)))).toNat := by
      simp only [spendWorld, show ¬ w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) =
        maxWord from hmax, ↓reduceIte] at hbal
      exact hbal
    simp only [gt_sub_self_of_le hbal']
    psol_steps [transferFromData]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [topLevelResult_success]; rfl
    · simp only [topLevelResult_output]
      decide +kernel
    · simp only [topLevelResult_world, transferFromWorld, spendWorld,
        show ¬ w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) = maxWord from hmax,
        ↓reduceIte]
      rfl
    · rw [topLevelResult_logs_of_success]
      rotate_left
      · rfl
      event_log [amount]

end Examples.Solmate.ERC4626.Shares
