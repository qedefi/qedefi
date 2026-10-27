import Verified.WeirdERC20.YAMV2.Spec.Transfer

/-!
# YAMv2 under the spec: `transferFrom`, the code-level postcondition

`transferFrom(src, dst, v)` of YAMv2 (OpenZeppelin-3, solc 0.6.12): first `_transfer(src, dst,
v)` (zero sender or recipient, amount above the balance, overflowing credit revert), then
`allowance[src][caller].sub(v, reason)` (an amount above the allowance reverts) written back by
`_approve(src, caller, ·)` (a zero caller reverts), `Transfer` then `Approval`, `true`.
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626
open Verified.WeirdERC20.AMPL.Spec (iszero_lt_size ampl_addr_ne')

/-- The allowance `transferFrom` reads, after the move. -/
def allowAfter (m : Machine) (src dst : Address) (v : Word) : Word :=
  (moveWorld m.ctx.crypto m.world m.frame.msg.currentTarget src dst v).sload
    m.frame.msg.currentTarget (allowSlot m.ctx.crypto src m.frame.msg.caller)

/-- `transferFrom(src, dst, v)`'s code-level end: a value, a zero sender, recipient or caller,
an amount above the balance or the allowance revert; otherwise (when the credit fits) the move,
the allowance lowered, `true`, `Transfer` and `Approval`. -/
def TransferFromPost (m : Machine) (src dst : Address) (v : Word) (mf : Machine) (o : Outcome) :
    Prop :=
  (m.frame.msg.value ≠ 0 → ∃ out, o = .revert out) ∧
  (src = 0 ∨ dst = 0 ∨ m.frame.msg.caller = 0 ∨
    (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat < v.toNat →
    ∃ out, o = .revert out) ∧
  (src ≠ 0 → dst ≠ 0 → m.frame.msg.caller ≠ 0 →
    v.toNat ≤ (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat →
    ((debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget src v).sload
      m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + v.toNat < 2 ^ 256 →
    ((allowAfter m src dst v).toNat < v.toNat → ∃ out, o = .revert out) ∧
    (v.toNat ≤ (allowAfter m src dst v).toNat →
      m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
      mf.world = (moveWorld m.ctx.crypto m.world m.frame.msg.currentTarget src dst v).sstore
        m.frame.msg.currentTarget (allowSlot m.ctx.crypto src m.frame.msg.caller)
        (allowAfter m src dst v - v) ∧
      mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
      mf.frame.sub.logs = (m.frame.sub.logs.push
        (transferLog m.frame.msg.currentTarget src dst v)).push
        (approvalLog m.frame.msg.currentTarget src m.frame.msg.caller
          (allowAfter m src dst v - v))))

end Verified.WeirdERC20.YAMV2.Spec
