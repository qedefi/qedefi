import Verified.AaveV3.AToken.Mint.Basic

/-!
# `AToken.burn`: assumptions on the two external calls, the postcondition

`burn(from, receiverOfUnderlying, amount, scaledAmount, index)` (`_burnScaled`, `_burn`, then
`IERC20(_underlyingAsset).safeTransfer(receiver, amount)`) makes two external calls the token
does not control. Their effect is assumed, explicitly:

* `HandleActionOkCode`: the rewards controller's `handleAction` succeeds, leaves the token's
  storage unchanged and every account's code unchanged (the code of the underlying must still
  be there for the second call);
* `TransferOk`: the underlying's `transfer(receiver, amount)` from the token returns `true`
  (one ABI word) and leaves the token's storage unchanged. This includes that the token holds
  enough underlying: the theorem says nothing about the underlying's own ledger.

`burnWorld` is the token storage after the three writes (the user's word with the new index,
`_totalSupply - amount`, the user's word with `balance - amount`); `BurnOk` the postcondition.
-/

namespace Verified.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter

/-- **Modelling assumption on the rewards controller** (for `burn`): as `HandleActionOk`, and
the call leaves every account's code unchanged. -/
def HandleActionOkCode (rc : ByteArray) (token : Address) : Prop :=
  ∀ (mc : Machine) (user : Address) (supply userBalance : Word), Fresh rc mc →
    mc.frame.msg.caller = token → mc.frame.msg.value = 0 →
    Abi.selectorOf mc.frame.msg.data = 0x31873e2e → mc.frame.msg.data.size = 100 →
    Bytes.toWord (readBytes mc.frame.msg.data 4 32) = Word.ofAddress user →
    Bytes.toWord (readBytes mc.frame.msg.data 36 32) = supply →
    Bytes.toWord (readBytes mc.frame.msg.data 68 32) = userBalance →
    Halts mc (fun mf o => (∃ out, o = .success out) ∧
      (∀ slot, mf.world.sload token slot = mc.world.sload token slot) ∧
      ∀ a, mf.world.code a = mc.world.code a)

/-- **Modelling assumption on the underlying token at `ua`**: `transfer(dst, amount)` called by
`token` without value, in any frame running the code installed at `ua`, returns `true` (the
32-byte word 1) and leaves `token`'s storage unchanged. -/
def TransferOk (ua token : Address) : Prop :=
  ∀ (mc : Machine) (dst : Address) (amount : Word), Fresh (mc.world.code ua) mc →
    mc.frame.msg.caller = token → mc.frame.msg.value = 0 →
    Abi.selectorOf mc.frame.msg.data = 0xa9059cbb → mc.frame.msg.data.size = 68 →
    Bytes.toWord (readBytes mc.frame.msg.data 4 32) = Word.ofAddress dst →
    Bytes.toWord (readBytes mc.frame.msg.data 36 32) = amount →
    Halts mc (fun mf o => o = .success (Bytes.ofWord 1) ∧
      ∀ slot, mf.world.sload token slot = mc.world.sload token slot)

/-- The address of the underlying asset of `t`: `_underlyingAsset` (slot 61). -/
def underlyingAddress (w : World) (t : Address) : Address := Word.toAddress (w.sload t 61#256)

theorem toAddress_mask160_and (x : Word) :
    Word.toAddress (1461501637330902918203684832716283019655932542975#256 &&& x) =
      Word.toAddress x := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.toAddress, BitVec.toNat_setWidth, BitVec.toNat_and,
    show (1461501637330902918203684832716283019655932542975#256).toNat = 2 ^ 160 - 1 from rfl,
    Nat.and_comm (2 ^ 160 - 1), Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]

/-- The storage of `t` after `burn(u, _, _, amt, idx)`'s three writes: `_userState[u]` with the
new index, `_totalSupply - amt`, `_userState[u]` with the new balance `scaledBalance - amt`. -/
def burnWorld (crypto : Crypto) (w : World) (t u : Address) (amt idx : Word) : World :=
  ((w.sstore t (userStateSlot crypto u) (userWordIndexed (w.sload t (userStateSlot crypto u)) idx)
    ).sstore t 54#256 (w.sload t 54#256 - amt)).sstore t (userStateSlot crypto u)
    (userWordMinted (scaledBalance crypto w t u - amt) (w.sload t (userStateSlot crypto u)) idx)

/-- A successful `burn(u, _, _, amt, idx)` in frame `m`: returns whether `u`'s scaled balance
becomes zero, and the executing account's storage is `burnWorld`. -/
def BurnOk (u : Address) (amt idx : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord (Word.iszero
    (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u - amt))) ∧
  ∀ slot, mf.world.sload m.frame.msg.currentTarget slot =
    (burnWorld m.ctx.crypto m.world m.frame.msg.currentTarget u amt idx).sload
      m.frame.msg.currentTarget slot

end Verified.AaveV3.AToken
