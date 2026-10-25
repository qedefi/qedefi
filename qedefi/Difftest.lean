import Difftest.Family
import Difftest.Gen
import Difftest.Local
import Difftest.Main
import Difftest.Rpc
import Difftest.Session
import Difftest.Time
import Difftest.Token

/-!
# Differential testing

`lake exe difftest`: the compiled contracts run on `evm-lean` and on Foundry's anvil, compared on
status, return data, logs, gas, touched storage and ether balances.
-/
