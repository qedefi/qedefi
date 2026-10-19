import EvmLeanSpecs.Refinement.SharesFrame
import EvmLeanSpecs.Refinement.VaultViewsMax

/-!
# The vault's share-token views in any frame

Frame forms of `totalSupply()`, `balanceOf(a)`, `allowance(owner, spender)` and `decimals()`
of the vault (any immutables), from a fresh frame with any parents: each returns the ABI word
of the value read from storage (`decimals`: the immutable masked to `uint8`) and leaves the
world unchanged (`SharesViewPost`). These are the share-token counterparts of the asset's
`balanceOf_halts` and complete the frame-level coverage of the vault's view functions
(`VaultViewsSpec.lean` covers the ERC-4626 views).
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-- A view returning the word `v` and changing nothing. -/
def SharesViewPost (v : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord v) ∧ mf.world = m.world

set_option maxHeartbeats 0 in
/-- **`totalSupply()` of the vault's shares**, in any frame. -/
theorem sharesTotalSupply_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hd : NoArgCall m.frame.msg.data 0x18160ddd) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget 2#256) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`balanceOf(a)` of the vault's shares**, in any frame. -/
theorem sharesBalanceOf_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0) {a : Address}
    (hd : AddrCall m.frame.msg.data 0x70a08231 a) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget
      (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate a)) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`allowance(owner, spender)` of the vault's shares**, in any frame. -/
theorem sharesAllowance_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    {owner spender : Address}
    (hd : TwoWordCall m.frame.msg.data 0xdd62ed3e (Word.ofAddress owner) (Word.ofAddress spender))
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (m.world.sload m.frame.msg.currentTarget
      (Erc20.allowanceSlot m.ctx.crypto Erc20.Layout.solmate owner spender)) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 0 in
/-- **`decimals()` of the vault**, in any frame: the immutable as a `uint8`. -/
theorem sharesDecimals_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hd : NoArgCall m.frame.msg.data 0x313ce567) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (SharesViewPost (i.decimals &&& 255#256) m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64,
    Shares.readBytes_code_decimals]
  exact ⟨rfl, rfl⟩

end EvmLeanSpecs.Refinement
