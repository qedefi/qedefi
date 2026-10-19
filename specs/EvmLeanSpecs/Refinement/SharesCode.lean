import EvmLeanProofs.Solidity.SharesExtraTactic
import EvmLeanProofs.Solidity.SharesExtraCall
import EvmLeanProofs.Solidity.SharesExtraErc20
import EvmLeanProofs.Contracts.SolmateVault
import EvmLeanProofs.KernelRfl

/-!
# The vault's share token: code, calldata, dispatch

Shared definitions for the refinement proofs of the share-token functions of the compiled
Solmate vault (`Contracts.SolmateVault`, Solmate `MockERC4626`, 5248 bytes), **for arbitrary
immutables** `i : SolmateVault.Immutables` (asset address, chain id, domain separator,
decimals): the code is `SolmateVault.runtimeCodeWith i` (the canonical code patched by
position; `runtimeCodeFor … asset self` is an instance, and so is the canonical deployment,
`runtimeCodeWith_deployment`). Symbolic execution runs on it with `psol_steps`
(`EvmLeanProofs.Solidity.SharesExtraTactic`), using `jumpDestsAgree`.

* calldata (`transferData`, …) and the top-level call message `vaultCall`;
* `reaches_*`: the dispatcher reaches each function's ABI decoder (entry pc, number of steps,
  gas), for every machine (`Dispatch.Reaches`).

The share token's storage is Solmate's `ERC20` layout (`Erc20.Layout.solmate`: `totalSupply`
2, `balanceOf` 3, `allowance` 4), read with `Erc20.view`.
-/

namespace EvmLeanSpecs.Refinement.Shares

open EvmLean Interpreter Solidity Contracts Dispatch

/-! ## Code -/

/-- The runtime code of the vault deployed with immutables `i`. -/
abbrev code (i : SolmateVault.Immutables) : ByteArray := SolmateVault.runtimeCodeWith i

/-- The patches only touch `PUSH32` immediates: the jump table is the canonical one, for all
immutables (kernel evaluation of the `JUMPDEST` scan, which skips the patched bytes). -/
theorem jumpDestsAgree (i : SolmateVault.Immutables) :
    JumpDestsAgree (code i) SolmateVault.runtimeCode := by
  unfold JumpDestsAgree; kernel_decide

/-- The vault code has 5248 bytes. -/
theorem size_code (i : SolmateVault.Immutables) : (code i).size = 5248 := by
  exact (size_patchWords _ _).trans SolmateVault.size_runtimeCode

/-- The vault code is not an EIP-7702 delegation designator. -/
theorem delegatedAddress?_code (i : SolmateVault.Immutables) : delegatedAddress? (code i) = none :=
  delegatedAddress?_of_size (by rw [size_code]; decide)

/-- The `decimals` immutable, as `PUSH32` at 622 reads it. -/
theorem readBytes_code_decimals (i : SolmateVault.Immutables) :
    readBytes (code i) 623 32 = Bytes.ofWord i.decimals := by
  have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
      (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset),
      (2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset),
      (2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset)] ++ (623, i.decimals) :: [] :=
    rfl
  simp only [code, SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

/-! ## Calldata -/

/-- Calldata of `transfer(dst, amount)`. -/
def transferData (dst : Address) (amount : Word) : ByteArray :=
  Abi.encodeCall 0xa9059cbb [Word.ofAddress dst, amount]

/-- Calldata of `approve(spender, amount)`. -/
def approveData (spender : Address) (amount : Word) : ByteArray :=
  Abi.encodeCall 0x095ea7b3 [Word.ofAddress spender, amount]

/-- Calldata of `transferFrom(src, dst, amount)`. -/
def transferFromData (src dst : Address) (amount : Word) : ByteArray :=
  Abi.encodeCall 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, amount]

/-- Calldata of `balanceOf(a)`. -/
def balanceOfData (a : Address) : ByteArray := Abi.encodeCall 0x70a08231 [Word.ofAddress a]

/-- Calldata of `allowance(owner, spender)`. -/
def allowanceData (owner spender : Address) : ByteArray :=
  Abi.encodeCall 0xdd62ed3e [Word.ofAddress owner, Word.ofAddress spender]

/-- Calldata of `totalSupply()`. -/
def totalSupplyData : ByteArray := Abi.encodeCall 0x18160ddd []

/-- Calldata of `decimals()`. -/
def decimalsData : ByteArray := Abi.encodeCall 0x313ce567 []

/-- The selectors are the artifact's method identifiers. -/
theorem selectors_mem :
    ("transfer(address,uint256)", (0xa9059cbb : UInt32)) ∈ SolmateVault.selectors ∧
    ("approve(address,uint256)", (0x095ea7b3 : UInt32)) ∈ SolmateVault.selectors ∧
    ("transferFrom(address,address,uint256)", (0x23b872dd : UInt32)) ∈ SolmateVault.selectors ∧
    ("balanceOf(address)", (0x70a08231 : UInt32)) ∈ SolmateVault.selectors ∧
    ("allowance(address,address)", (0xdd62ed3e : UInt32)) ∈ SolmateVault.selectors ∧
    ("totalSupply()", (0x18160ddd : UInt32)) ∈ SolmateVault.selectors ∧
    ("decimals()", (0x313ce567 : UInt32)) ∈ SolmateVault.selectors := by
  decide

/-- A top-level, zero-value call of the vault (immutables `i`) deployed at `vault`. -/
abbrev vaultCall (i : SolmateVault.Immutables) (vault caller : Address) (data : ByteArray)
    (gas : Nat) (warmAddrs : AddressSet) (warmKeys : StorageKeySet) : Message :=
  callMsg (code i) vault caller data gas warmAddrs warmKeys

/-- `processMessageCall` of a vault call starts the interpreter on the vault code. -/
theorem processMessageCall_vaultCall {i : SolmateVault.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {vault caller : Address} {data : ByteArray} {gas : Nat}
    {warmAddrs : AddressSet} {warmKeys : StorageKeySet}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false) (fuel : Nat) :
    processMessageCall fuel ctx w tr (vaultCall i vault caller data gas warmAddrs warmKeys) =
      run fuel (start ctx w tr (vaultCall i vault caller data gas warmAddrs warmKeys)) :=
  processMessageCall_callMsg hdeleg (delegatedAddress?_code i) hpre fuel

/-! ## Dispatch -/

set_option maxHeartbeats 1000000 in
/-- Dispatch of `transfer`: entry 893, 51 steps, 208 gas. -/
theorem reaches_transfer (i : SolmateVault.Immutables) : Reaches (code i) 0xa9059cbb 893 51 208 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

set_option maxHeartbeats 1000000 in
/-- Dispatch of `approve`: entry 536, 41 steps, 164 gas. -/
theorem reaches_approve (i : SolmateVault.Immutables) : Reaches (code i) 0x095ea7b3 536 41 164 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

set_option maxHeartbeats 1000000 in
/-- Dispatch of `transferFrom`: entry 599, 56 steps, 230 gas. -/
theorem reaches_transferFrom (i : SolmateVault.Immutables) :
    Reaches (code i) 0x23b872dd 599 56 230 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

set_option maxHeartbeats 1000000 in
/-- Dispatch of `totalSupply`: entry 590, 51 steps, 208 gas. -/
theorem reaches_totalSupply (i : SolmateVault.Immutables) :
    Reaches (code i) 0x18160ddd 590 51 208 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

set_option maxHeartbeats 1000000 in
/-- Dispatch of `balanceOf`: entry 804, 50 steps, 207 gas. -/
theorem reaches_balanceOf (i : SolmateVault.Immutables) : Reaches (code i) 0x70a08231 804 50 207 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

set_option maxHeartbeats 1000000 in
/-- Dispatch of `allowance`: entry 1077, 44 steps, 184 gas. -/
theorem reaches_allowance (i : SolmateVault.Immutables) :
    Reaches (code i) 0xdd62ed3e 1077 44 184 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

set_option maxHeartbeats 1000000 in
/-- Dispatch of `decimals`: entry 618, 41 steps, 164 gas. -/
theorem reaches_decimals (i : SolmateVault.Immutables) : Reaches (code i) 0x313ce567 618 41 164 := by
  have hjd := jumpDestsAgree i
  psol_dispatch

/-! ## Calldata facts -/

/-- Selector and size of calldata with `n` word arguments. -/
theorem encodeCall_facts (sel : Nat) (args : List Word) (hsel : sel < 2 ^ 32)
    (hn : 4 + 32 * args.length < 2 ^ 256) :
    Abi.selectorOf (Abi.encodeCall sel args) = sel ∧ 4 ≤ (Abi.encodeCall sel args).size ∧
      (Abi.encodeCall sel args).size < 2 ^ 256 := by
  rw [Abi.selectorOf_encodeCall, Abi.size_encodeCall]
  exact ⟨Nat.mod_eq_of_lt hsel, by omega, hn⟩

end EvmLeanSpecs.Refinement.Shares
