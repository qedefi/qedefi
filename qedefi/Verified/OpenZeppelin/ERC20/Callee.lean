import Verified.OpenZeppelin.ERC20.Basic
import Verified.Solmate.ERC20.BalanceOf
import QEDefi.ERC4626.Logs

/-!
# `OzAsset` as a callee: vocabulary

The postconditions of the callee summaries of OpenZeppelin's `ERC20Mock` in any fresh frame
(`Fresh OzAsset.runtimeCode m`: top level or a callee at any depth). A success fixes the
output, the world (the `ERC20Oz` `*World` with `Layout.oz`), the transient storage, the created
accounts, the logs (the event appended to the frame's logs) and a gas bound. A revert is the
Solmate `Reverts`. The calldata is described by what the ABI decoder reads (`TwoWordCall`), so
it also covers calldata a caller assembled in memory.
-/

namespace Verified.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Solidity.ERC20
open EvmLean.Interpreter QEDefi.ERC4626

/-- The token's storage view in the frame `m` (the token is the executing account). -/
abbrev assetView (m : Machine) : ERC20.State :=
  view m.ctx.crypto Layout.oz m.world m.frame.msg.currentTarget

/-- `balanceOf(a)` returns the word in `a`'s balance slot, changes nothing, uses ≤ 3000 gas. -/
def BalanceOfPost (a : Address) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord (m.world.sload m.frame.msg.currentTarget
    (balanceSlot m.ctx.crypto Layout.oz a))) ∧
  mf.world = m.world ∧ mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  mf.frame.sub.logs = m.frame.sub.logs ∧ m.frame.gasLeft ≤ mf.frame.gasLeft + 3000

/-- A successful `transfer(dst, amount)`: ABI `true`, world `moveWorld` from the caller, log
`Transfer(caller, dst, amount)`, ≤ 55000 gas. -/
def TransferOk (dst : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord 1) ∧
  mf.world = moveWorld m.ctx.crypto Layout.oz m.world m.frame.msg.currentTarget
    m.frame.msg.caller dst amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  mf.frame.sub.logs = m.frame.sub.logs.push
    (transferLog m.frame.msg.currentTarget m.frame.msg.caller dst amount) ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 55000

/-- A successful `approve(spender, amount)`: ABI `true`, world `allowanceWorld`, log
`Approval(caller, spender, amount)`, ≤ 40000 gas. -/
def ApproveOk (spender : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord 1) ∧
  mf.world = allowanceWorld m.ctx.crypto Layout.oz m.world m.frame.msg.currentTarget
    m.frame.msg.caller spender amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  mf.frame.sub.logs = m.frame.sub.logs.push
    (approvalLog m.frame.msg.currentTarget m.frame.msg.caller spender amount) ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 40000

/-- A successful `transferFrom(src, dst, amount)` from the spender `caller`: ABI `true`, world
`ozTransferFromWorld`, the single log `Transfer(src, dst, amount)` (OpenZeppelin v5 emits no
`Approval` when spending an allowance), ≤ 80000 gas. -/
def TransferFromOk (src dst : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord 1) ∧
  mf.world = ozTransferFromWorld m.ctx.crypto Layout.oz m.world m.frame.msg.currentTarget
    m.frame.msg.caller src dst amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  mf.frame.sub.logs = m.frame.sub.logs.push
    (transferLog m.frame.msg.currentTarget src dst amount) ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 80000

/-- A successful `mint(dst, amount)`: empty output, world `mintWorld`, log
`Transfer(0, dst, amount)`, ≤ 55000 gas. -/
def MintOk (dst : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success .empty ∧
  mf.world = mintWorld m.ctx.crypto Layout.oz m.world m.frame.msg.currentTarget dst amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  mf.frame.sub.logs = m.frame.sub.logs.push
    (transferLog m.frame.msg.currentTarget 0 dst amount) ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 55000

/-- A successful `burn(src, amount)`: empty output, world `burnWorld`, log
`Transfer(src, 0, amount)`, ≤ 55000 gas. -/
def BurnOk (src : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success .empty ∧
  mf.world = burnWorld m.ctx.crypto Layout.oz m.world m.frame.msg.currentTarget src amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  mf.frame.sub.logs = m.frame.sub.logs.push
    (transferLog m.frame.msg.currentTarget src 0 amount) ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 55000

theorem balanceSlot_oz (crypto : Crypto) (a : Address) :
    balanceSlot crypto Layout.oz a =
      crypto.keccak256 (Bytes.ofWord (Word.ofAddress a) ++ Bytes.ofWord 0#256) := rfl

theorem allowanceSlot_oz (crypto : Crypto) (owner spender : Address) :
    allowanceSlot crypto Layout.oz owner spender =
      crypto.keccak256 (Bytes.ofWord (Word.ofAddress spender) ++
        Bytes.ofWord (crypto.keccak256 (Bytes.ofWord (Word.ofAddress owner) ++
          Bytes.ofWord 1#256))) := rfl

end Verified.OpenZeppelin.ERC20
