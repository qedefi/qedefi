import EvmLogic.Tactic.Patched
import EvmLogic.Solidity.Dispatch
import EvmLogic.Program.Call
import EvmLogic.Tactic.KernelRfl
import Verified.OpenZeppelin.VestingWallet.Arith
import QEDefi.Vesting.Model
import Verified.OpenZeppelin.Contracts.VestingWallet

/-!
# `VestingWallet`: the code for arbitrary immutables

`code i` is the runtime code of OpenZeppelin's `VestingWallet` deployed with immutables `i`
(`_start`, `_duration`). Its jump table is the canonical one for all immutables
(`jumpDestsAgree`), and the `PUSH32`s of the immutables read `i.start`, `i.duration`. The
contract masks both to 64 bits (`uint64`), as it does `block.timestamp`: `start i`,
`duration i` and `clock` are these masked values, the parameters of the model schedule.
-/

namespace Verified.OpenZeppelin.VestingWallet
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Verified.OpenZeppelin.Contracts

/-- The runtime code of the wallet deployed with immutables `i`. -/
abbrev code (i : VestingWallet.Immutables) : ByteArray := VestingWallet.runtimeCodeWith i

/-- The patches only touch `PUSH32` immediates, so the jump table is the canonical one. -/
theorem jumpDestsAgree (i : VestingWallet.Immutables) :
    JumpDestsAgree (code i) VestingWallet.runtimeCode := by
  unfold JumpDestsAgree; kernel_decide

theorem size_code (i : VestingWallet.Immutables) : (code i).size = 2264 :=
  (size_patchWords _ _).trans VestingWallet.size_runtimeCode

theorem delegatedAddress?_code (i : VestingWallet.Immutables) :
    delegatedAddress? (code i) = none :=
  delegatedAddress?_of_size (by rw [size_code]; decide)

theorem patches_eq (i : VestingWallet.Immutables) :
    i.patches = [(295, i.duration), (1236, i.duration), (1458, i.duration), (1198, i.start)] :=
  rfl

/-- The `duration` immutable as the `PUSH32` at 294 reads it. -/
theorem readBytes_code_295 (i : VestingWallet.Immutables) :
    readBytes (code i) 295 32 = Bytes.ofWord i.duration := by
  simp only [code, VestingWallet.runtimeCodeWith, patches_eq]
  exact readBytes_patchWords_last _ [] _ _ _ (by rw [VestingWallet.size_runtimeCode]; decide)
    (by simp)

/-- The `duration` immutable as the `PUSH32` at 1235 reads it. -/
theorem readBytes_code_1236 (i : VestingWallet.Immutables) :
    readBytes (code i) 1236 32 = Bytes.ofWord i.duration := by
  simp only [code, VestingWallet.runtimeCodeWith, patches_eq]
  exact readBytes_patchWords_last _ [(295, i.duration)] _ _ _
    (by rw [VestingWallet.size_runtimeCode]; decide) (by simp)

/-- The `duration` immutable as the `PUSH32` at 1457 reads it. -/
theorem readBytes_code_1458 (i : VestingWallet.Immutables) :
    readBytes (code i) 1458 32 = Bytes.ofWord i.duration := by
  simp only [code, VestingWallet.runtimeCodeWith, patches_eq]
  exact readBytes_patchWords_last _ [(295, i.duration), (1236, i.duration)] _ _ _
    (by rw [VestingWallet.size_runtimeCode]; decide) (by simp)

/-- The `start` immutable as the `PUSH32` at 1197 reads it. -/
theorem readBytes_code_1198 (i : VestingWallet.Immutables) :
    readBytes (code i) 1198 32 = Bytes.ofWord i.start := by
  simp only [code, VestingWallet.runtimeCodeWith, patches_eq]
  exact readBytes_patchWords_last _ [(295, i.duration), (1236, i.duration), (1458, i.duration)]
    _ _ _ (by rw [VestingWallet.size_runtimeCode]; decide) (by simp)

/-- The 64-bit mask `uint64` casts compile to. -/
def mask64 : Word := 0xffffffffffffffff#256

/-- The schedule's start as the contract reads it: `uint64(_start)`. -/
def start (i : VestingWallet.Immutables) : Nat := i.start.toNat % 2 ^ 64

/-- The schedule's duration as the contract reads it: `uint64(_duration)`. -/
def duration (i : VestingWallet.Immutables) : Nat := i.duration.toNat % 2 ^ 64

/-- The model schedule of the deployment with immutables `i`. -/
def sched (i : VestingWallet.Immutables) : QEDefi.Vesting.Schedule := ⟨start i, duration i⟩

/-- The model state of the wallet at `self` in world `w`: its ETH balance and `_released`
(slot 1). -/
def state (w : World) (self : Address) : QEDefi.Vesting.State :=
  ⟨(w.balance self).toNat, (w.sload self 1#256).toNat⟩

/-- The time as the contract reads it: `uint64(block.timestamp)`. -/
def clock (b : BlockEnv) : Nat := b.timestamp % 2 ^ 64

theorem toNat_and_mask64 (x : Word) : (mask64 &&& x).toNat = x.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_and, mask64, BitVec.toNat_ofNat, Nat.and_comm]
  rw [show (0xffffffffffffffff : Nat) % 2 ^ 256 = 2 ^ 64 - 1 by decide]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem toNat_and_mask64' (x : Word) : (x &&& mask64).toNat = x.toNat % 2 ^ 64 := by
  rw [BitVec.and_comm]; exact toNat_and_mask64 x

/-- The wallet's frame: its code, its jump table. -/
structure WalletFrame (i : VestingWallet.Immutables) (m : Machine) : Prop where
  /-- The frame runs the wallet's code. -/
  hcode : m.frame.code = code i
  /-- The frame's jump table is that code's. -/
  jumps : JumpTable m.frame.jumpDests (code i)

end Verified.OpenZeppelin.VestingWallet
