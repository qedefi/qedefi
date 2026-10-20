import EvmLogic.Step.Basic
import EvmLogic.Solidity.Abi

/-!
# Top-level calls into a compiled contract

`processMessageCall_callMsg` reduces a top-level zero-value call (`callMsg`) to `run` from
the machine `start`, assuming no EIP-7702 delegation and a non-precompile target.
-/

namespace EvmLogic.Solidity
open EvmLean EvmLean.Interpreter

/-- A top-level, zero-value message call of the contract at `token` (running `code`) from
`caller` with calldata `data`, `gas` gas and the given warm sets. -/
def callMsg (code : ByteArray) (token caller : Address) (data : ByteArray) (gas : Nat)
    (warmAddrs : AddressSet) (warmKeys : StorageKeySet) : Message where
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

theorem delegatedAddress?_of_size {code : ByteArray} (h : code.size ≠ 23) :
    delegatedAddress? code = none := by
  simp only [delegatedAddress?, isValidDelegation, eoaDelegatedCodeLength]
  simp [h]

/-- `processMessageCall` of `callMsg` starts the interpreter on the contract code. -/
theorem processMessageCall_callMsg {code : ByteArray} {ctx : Context} {w : World}
    {tr : TransientStorage} {token caller : Address} {data : ByteArray} {gas : Nat}
    {warmAddrs : AddressSet} {warmKeys : StorageKeySet}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hcode : delegatedAddress? code = none)
    (hpre : Precompile.isPrecompile ctx.fork token = false) (fuel : Nat) :
    processMessageCall fuel ctx w tr (callMsg code token caller data gas warmAddrs warmKeys) =
      run fuel (start ctx w tr (callMsg code token caller data gas warmAddrs warmKeys)) := by
  have hi := initMachine_call (pre := PrecompileImpl.standard ctx) (ctx := ctx) (w := w)
    (tr := tr) (msg := callMsg code token caller data gas warmAddrs warmKeys) (a := token)
    rfl rfl hpre rfl rfl
  exact processMessageCall_eq_run (msg := callMsg code token caller data gas warmAddrs warmKeys)
    hdeleg hcode hi fuel

end EvmLogic.Solidity
