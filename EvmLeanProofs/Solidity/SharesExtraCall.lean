import EvmLeanProofs.Solidity.Dispatch
import EvmLeanProofs.Solidity.Call

/-!
# Dispatch from the start of a top-level call

`Dispatch.Reaches.run_start` instantiates a dispatch lemma (`Dispatch.Reaches`) at the machine
`start ctx w tr (callMsg code …)` of a top-level call (`EvmLeanProofs.Solidity.Call`), for any
calldata with the right selector: the hypotheses are about the calldata only. Every
per-function theorem about a compiled contract starts with it.
-/

namespace EvmLean.Solidity.Dispatch

open Interpreter

/-- **Dispatch of a top-level call.** -/
theorem Reaches.run_start {code : ByteArray} {sel entry n cost : Nat}
    (h : Reaches code sel entry n cost) {ctx : Context} {w : World} {tr : TransientStorage}
    {token caller : Address} {data : ByteArray} {gas : Nat} {warmAddrs : AddressSet}
    {warmKeys : StorageKeySet} (hsel : Abi.selectorOf data = sel) (hsz : 4 ≤ data.size)
    (hsz' : data.size < 2 ^ 256) (hgas : cost ≤ gas) (k : Nat) :
    run (k + n) (start ctx w tr (callMsg code token caller data gas warmAddrs warmKeys)) =
      run k { start ctx w tr (callMsg code token caller data gas warmAddrs warmKeys) with
        frame := { (start ctx w tr (callMsg code token caller data gas warmAddrs warmKeys)).frame with
          pc := entry, stack := [BitVec.ofNat 256 sel], memory := initMemory,
          gasLeft := gas - cost } } :=
  h.run_eq (msg := callMsg code token caller data gas warmAddrs warmKeys) rfl rfl rfl hsel hsz
    hsz' hgas k

end EvmLean.Solidity.Dispatch
