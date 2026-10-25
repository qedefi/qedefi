import Verified.AaveV3.AToken.Havoc.Good

/-!
# Reading back what the AToken wrote

Rewrite rules for reads after writes at the executing account, under the Keccak hypotheses
`SlotsOk`: a `_userState`, `_allowances` or `_nonces` write leaves the fixed slots (`0`, `1`,
`54`, the EIP-1967 slot) and the slots of the other families as they were. Given to the prefix
executor as simp lemmas (`sload_sstore_user_fixed hK`, …), they keep the symbolic worlds small.
-/

namespace Verified.AaveV3.AToken.Havoc
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity
  Verified.AaveV3.Contracts

variable {crypto : Crypto}

theorem user_ne_fixed (hK : SlotsOk crypto) (a : Address) {k : Word} (hk : k ∈ fixedSlots) :
    k ≠ mappingSlot crypto (Word.ofAddress a) 52#256 := fun h =>
  Finset.disjoint_left.1 hK.userFixed (mem_userSlots crypto a) (by rw [userSlot, ← h]; exact hk)

theorem allow_ne_fixed (hK : SlotsOk crypto) (o s : Address) {k : Word} (hk : k ∈ fixedSlots) :
    k ≠ mappingSlot crypto (Word.ofAddress s) (mappingSlot crypto (Word.ofAddress o) 53#256) :=
  fun h => Finset.disjoint_left.1 hK.allowFixed (mem_allowanceSlots crypto o s) (by rw [← h]; exact hk)

theorem nonce_ne_fixed (hK : SlotsOk crypto) (a : Address) {k : Word} (hk : k ∈ fixedSlots) :
    k ≠ mappingSlot crypto (Word.ofAddress a) 58#256 := fun h =>
  Finset.disjoint_left.1 hK.nonceFixed (mem_nonceSlots crypto a) (by rw [← h]; exact hk)

theorem user_ne_allow (hK : SlotsOk crypto) (a o s : Address) :
    mappingSlot crypto (Word.ofAddress a) 52#256 ≠
      mappingSlot crypto (Word.ofAddress s) (mappingSlot crypto (Word.ofAddress o) 53#256) :=
  fun h => Finset.disjoint_left.1 hK.allow (mem_allowanceSlots crypto o s)
    (by rw [← h]; exact mem_userSlots crypto a)

theorem user_ne_nonce (hK : SlotsOk crypto) (a b : Address) :
    mappingSlot crypto (Word.ofAddress a) 52#256 ≠ mappingSlot crypto (Word.ofAddress b) 58#256 :=
  fun h => Finset.disjoint_left.1 hK.nonce (mem_nonceSlots crypto b)
    (by rw [← h]; exact mem_userSlots crypto a)

theorem mem_fixed_54 : (54#256 : Word) ∈ fixedSlots := by simp [fixedSlots]
theorem mem_fixed_0 : (0#256 : Word) ∈ fixedSlots := by simp [fixedSlots]
theorem mem_fixed_1 : (1#256 : Word) ∈ fixedSlots := by simp [fixedSlots]
theorem mem_fixed_impl : ATokenProxy.implSlot ∈ fixedSlots := by simp [fixedSlots]

/-- Slot 54 after a `_userState` write. -/
theorem sload54_sstore_user (hK : SlotsOk crypto) (w : World) (t a : Address) (v : Word) :
    (w.sstore t (mappingSlot crypto (Word.ofAddress a) 52#256) v).sload t 54#256 =
      w.sload t 54#256 :=
  World.sload_sstore_ne_key _ _ _ (user_ne_fixed hK a mem_fixed_54)

/-- Slot 54 after an `_allowances` write. -/
theorem sload54_sstore_allow (hK : SlotsOk crypto) (w : World) (t o s : Address) (v : Word) :
    (w.sstore t (mappingSlot crypto (Word.ofAddress s) (mappingSlot crypto (Word.ofAddress o)
      53#256)) v).sload t 54#256 = w.sload t 54#256 :=
  World.sload_sstore_ne_key _ _ _ (allow_ne_fixed hK o s mem_fixed_54)

/-- A `_userState` slot after an `_allowances` write. -/
theorem sloadUser_sstore_allow (hK : SlotsOk crypto) (w : World) (t a o s : Address) (v : Word) :
    (w.sstore t (mappingSlot crypto (Word.ofAddress s) (mappingSlot crypto (Word.ofAddress o)
      53#256)) v).sload t (mappingSlot crypto (Word.ofAddress a) 52#256) =
      w.sload t (mappingSlot crypto (Word.ofAddress a) 52#256) :=
  World.sload_sstore_ne_key _ _ _ (user_ne_allow hK a o s)

/-- A `_userState` slot after the `_totalSupply` write. -/
theorem sloadUser_sstore54 (hK : SlotsOk crypto) (w : World) (t a : Address) (v : Word) :
    (w.sstore t 54#256 v).sload t (mappingSlot crypto (Word.ofAddress a) 52#256) =
      w.sload t (mappingSlot crypto (Word.ofAddress a) 52#256) :=
  World.sload_sstore_ne_key _ _ _ (user_ne_fixed hK a mem_fixed_54).symm

end Verified.AaveV3.AToken.Havoc
