import Examples.Solmate.ERC20.BalanceOf
import QEDefi.ERC20.Rep
import EvmLogic.Program.Call
import Examples.Solmate.ERC4626.SharesRep
import QEDefi.ERC4626.Solmate

/-!
# The asset's storage view and `balanceOf` against the model

`assetView` (the asset's ERC-20 storage view in a frame), `ApproveOk` and
`assetBalanceOf_refines`, split off `Spec` so that `MintBurn` does not wait for the
`transfer`/`transferFrom` proofs, and `Approve`/`EventsTransfer` do not wait for the vault.
-/

namespace Examples.Solmate.ERC20
open Examples.Solmate.ERC4626 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open EvmLogic.Solidity.ERC20 (transferWorld view_transferWorld)
open QEDefi.Math QEDefi.ERC20 Examples.Solmate.ERC4626.Shares

/-- The asset's storage view in the frame `m` (the asset is the executing account). -/
abbrev assetView (m : Machine) : ERC20.State :=
  ERC20.view m.ctx.crypto ERC20.Layout.solmate m.world m.frame.msg.currentTarget

/-- A successful asset `approve`: returns ABI `true`, the world is `ERC20.approveWorld`, at most
40000 gas used. -/
def ApproveOk (spender : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord 1) ∧
  mf.world = ERC20.approveWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller
    spender amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 40000

/-- **`balanceOf(a)` of the asset** returns the represented balance, in any frame. -/
theorem assetBalanceOf_refines {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (a : Address)
    (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = balanceOfSelector)
    (hsize : 36 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress a)
    (hg : 3000 ≤ m.frame.gasLeft) {P : Address → Address → Prop} {t : Token Address}
    (hr : RepOn P (assetView m) t) :
    Halts m (fun mf o => o = .success (Bytes.ofWord (BitVec.ofNat 256 (t.balanceOf a))) ∧
      mf.world = m.world) :=
  (balanceOf_halts m hf a hval hsel hsize hsize' harg hg).mono fun _ _ _ ⟨ho, hw, _⟩ =>
    ⟨by rw [ho, ← hr.balanceOf a, ofNat_toNat_word]; rfl, hw⟩

end Examples.Solmate.ERC20
