import QEDefiTest.Contracts
import QEDefiTest.Solidity
import QEDefiTest.Strings

/-!
# QEDefiTest

Evaluation tests of the `qedefi` package (`#guard`): the compiled-contract constants
(selectors, event topics, sizes, addresses, immutables, storage layouts), the Solidity layer
on concrete calldata, and the compiled `string` getters run in the interpreter. Not a default
target and not part of the proof libraries; `lake test` builds it.
-/
