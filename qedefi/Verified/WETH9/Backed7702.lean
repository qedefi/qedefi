import Verified.WETH9.Backed
import EvmLogic.Program.Reentrancy.Deleg

/-!
# WETH9's ether backs its tokens after any transaction, EIP-7702 included

`weth9_solvent` and `weth9_backed` (`Verified.WETH9.Backed`) assume the transaction is before
Prague or carries no EIP-7702 authorization. Mainnet runs Prague: a type-4 transaction may carry
authorizations, which `processMessageCall` applies before the top-level message runs. They can
only rewrite the code and nonce of accounts holding empty code or a delegation designator, never
WETH9's, and keep every balance (`EvmLogic.Program.Delegation`). So the same conclusions hold for
every transaction, with the same remaining hypotheses (`processMessageCall_good_v_7702`).
-/

namespace Verified.WETH9
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open QEDefi.Solvency EvmLogic.Program.Reentrancy

/-- **WETH9 stays solvent after any transaction**, EIP-7702 authorizations included: from a world
in which it is solvent, any top-level message call (any fork, any authorizations; any target,
code, value, calldata; an unprotected sender; any callees, including ones that call WETH9 at any
depth) that moves its value, hashing with the world's `crypto`, ends in a world in which it is
solvent — provided no `allowance` entry shares its slot with a `balanceOf` entry. `weth9_solvent`
without its fork/authorization hypothesis. -/
theorem weth9_solvent_7702 {crypto : Crypto} {weth : Address}
    (hK : Disjoint (allowanceSlots crypto) (balanceSlots crypto 3#256)) {fuel : Nat}
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (hw : Good crypto weth w) (hctx : ctx.crypto = crypto)
    (hmsg : TopOk (· = weth) w msg) (hv : msg.shouldTransferValue = true)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) : Good crypto weth r.world :=
  processMessageCall_good_v_7702 (goodOps_solvent size_code deleg_code) hw hmsg hv hctx
    (weth_covers hK _) hr

/-- **WETH9's ether backs its tokens, after any transaction**, EIP-7702 authorizations included:
when the slots of `balanceOf[a]` do not collide, `Σₐ balanceOf[a] ≤ address(weth).balance` and
the sum is below `2²⁵⁶`, over all addresses. `weth9_backed` without its fork/authorization
hypothesis; the other hypotheses are those of `weth9_backed`. -/
theorem weth9_backed_7702 {crypto : Crypto} {weth : Address}
    (hK : Disjoint (allowanceSlots crypto) (balanceSlots crypto 3#256))
    (hinj : Function.Injective (balSlot crypto)) {fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (hw : Good crypto weth w) (hctx : ctx.crypto = crypto)
    (hmsg : TopOk (· = weth) w msg) (hv : msg.shouldTransferValue = true)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    ∑ a : Address, (r.world.sload weth (balSlot crypto a)).toNat ≤
        (r.world.balance weth).toNat ∧
      ∑ a : Address, (r.world.sload weth (balSlot crypto a)).toNat < 2 ^ 256 := by
  have h := weth9_solvent_7702 hK hw hctx hmsg hv hr
  have he := owed_eq_sum_addresses (crypto := crypto) (base := 3#256) (bank := weth) r.world hinj
  exact ⟨he ▸ h.backed, he ▸ h.bounded⟩

end Verified.WETH9
