import EvmLeanProofs.Solidity.Dispatch
import EvmLeanProofs.Solidity.Erc20
import EvmLeanProofs.Solidity.Examples.Erc20Code
import EvmLeanProofs.Call

/-!
# Compiled ERC-20: calls and dispatch

Calls into the compiled ERC-20 of `Erc20Code` (Solmate layout, `Erc20.Layout.solmate`) and
the dispatcher lemma for `transfer(address,uint256)`.

* `transferCalldata to amount`: `a9059cbb ‖ pad(to) ‖ amount`.
* `call token caller data gas …`: a top-level, zero-value message call of the token.
* `reaches_transfer`: for every machine at the start of a call with selector `a9059cbb`, the
  dispatcher reaches the ABI decoder of `transfer` (pc 413) in 49 steps, charging 206 gas
  (`Dispatch.Reaches`, proved by `sol_dispatch` in a few seconds); `Reaches.run_eq` applies
  it to `start`.
-/

namespace EvmLean.Solidity.Examples.SolmateErc20

open Interpreter Dispatch

/-- The selector of `transfer(address,uint256)` (from `--hashes`). -/
def transferSelector : Nat := 0xa9059cbb

/-- Calldata of `transfer(to, amount)`. -/
def transferCalldata (to : Address) (amount : Word) : ByteArray :=
  Abi.encodeCall transferSelector [Word.ofAddress to, amount]

/-- A top-level, zero-value message call of the token at `token` from `caller` with calldata
`data`, `gas` gas and the given warm sets. -/
def call (token caller : Address) (data : ByteArray) (gas : Nat) (warmAddrs : AddressSet)
    (warmKeys : StorageKeySet) : Message where
  caller := caller
  target := some token
  currentTarget := token
  gas := gas
  value := 0
  data := data
  codeAddress := some token
  code := code
  depth := 0
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := warmAddrs
  accessedStorageKeys := warmKeys

/-- The machine at the start of a top-level message call `msg` (`initMachine`'s result). -/
def start (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) : Machine where
  ctx := ctx
  precompiles := PrecompileImpl.standard ctx
  world := w
  transient := tr
  originalWorld := w
  createdAccounts := ∅
  frame := Frame.init msg (.call 0 0) (w, tr)
  parents := []

/-- The size of the token code. -/
theorem size_code : code.size = 1639 := by decide +kernel

/-- The token code is not an EIP-7702 delegation designator. -/
theorem delegatedAddress?_code : delegatedAddress? code = none := by
  simp only [delegatedAddress?, isValidDelegation, size_code, eoaDelegatedCodeLength]
  rfl

/-- `processMessageCall` of a call to the token starts the interpreter on the token code. -/
theorem processMessageCall_call {ctx : Context} {w : World} {tr : TransientStorage}
    {token caller : Address} {data : ByteArray} {gas : Nat} {warmAddrs : AddressSet}
    {warmKeys : StorageKeySet} (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (fuel : Nat) :
    processMessageCall fuel ctx w tr (call token caller data gas warmAddrs warmKeys) =
      run fuel (start ctx w tr (call token caller data gas warmAddrs warmKeys)) := by
  have hd : delegatedAddress? (call token caller data gas warmAddrs warmKeys).code = none :=
    delegatedAddress?_code
  have hi := initMachine_call (pre := PrecompileImpl.standard ctx) (ctx := ctx) (w := w) (tr := tr)
    (msg := call token caller data gas warmAddrs warmKeys) (a := token) rfl rfl hpre rfl rfl
  exact processMessageCall_eq_run hdeleg hd hi fuel

/-- The selector of `transferCalldata`. -/
theorem selectorOf_transferCalldata (to : Address) (amount : Word) :
    Abi.selectorOf (transferCalldata to amount) = transferSelector := by
  rw [transferCalldata, Abi.selectorOf_encodeCall]; rfl

/-- `CALLDATASIZE` of `transferCalldata`. -/
theorem size_transferCalldata (to : Address) (amount : Word) :
    (transferCalldata to amount).size = 68 := by
  rw [transferCalldata, Abi.size_encodeCall]; rfl

/-- **Dispatch of `transfer`**: selector `a9059cbb` reaches pc 413 in 49 steps for 206 gas. -/
theorem reaches_transfer : Reaches code transferSelector 413 49 206 := by
  sol_dispatch

end EvmLean.Solidity.Examples.SolmateErc20
