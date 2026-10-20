import Examples.Solmate.ERC20.Spec

/-!
# The asset's `approve`

`approve(spender, amount)` of the deployed asset (Solmate `MockERC20`, any immutables):

* `approve_halts`: in any non-static fresh frame (a top-level call or a callee frame) the call
  always succeeds, returns ABI `true`, and the world is `Erc20.approveWorld` (one `SSTORE` to
  `allowance[msg.sender][spender]`; the definition is shared with the vault's share token);
* `assetApprove_refines`: the same, against the model: the asset's storage view represents
  `Token.approve` of the represented ledger, for every allowance entry that is the written one
  or has another slot (`ApproveAllowances`). Needs `AllowanceSlotOk` for the written entry.
-/

namespace Examples.Solmate.ERC20
open Examples.Solmate.ERC4626 Defi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.ERC4626 Defi.Math Defi.ERC20 Examples.Solmate.ERC4626.Shares

/-- What a successful `approve(spender, amount)` of the asset ends with: it returns ABI `true`,
the world is `Erc20.approveWorld`, transient storage and created accounts are unchanged, and at
most 40000 gas is used. -/
def ApproveOk (spender : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord 1) ∧
  mf.world = ERC20.approveWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller
    spender amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 40000

set_option maxHeartbeats 0 in
/-- **`approve(spender, amount)` of the asset**, in any non-static frame: always succeeds. -/
theorem approve_halts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
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
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  refine ⟨rfl, ?_, rfl, rfl, ?_⟩
  · simp only [outputMachine, ERC20.approveWorld, allowanceSlot_solmate]
  · dsimp only [outputMachine]
    evm_gas

/-- The allowance predicate of an `approve`'s result: the written entry, and every entry whose
slot is not the written slot. -/
def ApproveAllowances (crypto : Crypto) (owner spender : Address) (o sp : Address) : Prop :=
  (o = owner ∧ sp = spender) ∨ ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp ≠
    ERC20.allowanceSlot crypto ERC20.Layout.solmate owner spender

/-- **`approve(spender, amount)` of the asset refines `Token.approve`**, in any non-static
frame: success with the model's ledger. -/
theorem assetApprove_refines {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
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
  refine (approve_halts m hf hval hstatic hd hsz hg).mono fun mf o _ hok => ⟨hok, ?_⟩
  rw [hok.2.1]
  exact RepOn.of_eq h1 h2 h3 (rep_approve hr m.frame.msg.caller spender amount)

end Examples.Solmate.ERC20
