import EvmLean

/-!
# The evm-lean side of the differential tester

Transactions are executed as `EvmLean.Tx.process` does, except that the top-level message
is run directly with `Interpreter.processMessageCall` so its return data is visible. Gas
price is zero, so only the transaction's value moves ether.
-/

namespace Examples.Differential

open EvmLean

/-- The outcome of a transaction, in the form both sides are compared in. -/
structure Outcome where
  /-- Receipt status. -/
  success : Bool
  /-- Return data or revert data. -/
  output : ByteArray
  /-- Logs (empty unless successful). -/
  logs : Array Log
  /-- Gas used after the refund. -/
  gasUsed : Nat

/-- Interpreter steps allowed per transaction (far more than 10M gas can pay for). -/
def fuel : Nat := 50_000_000

/-- Execute a transaction (a creation if `to = none`) sending `value` wei in the block
environment `env`; fails if the interpreter runs out of fuel, `gas` is below the intrinsic
cost or the sender cannot pay `value`. -/
def execTx (crypto : Crypto) (env : BlockEnv) (world : World) (sender : Address)
    (to : Option Address) (data : ByteArray) (gas : Nat) (value : Nat := 0) :
    Except String (Outcome × World) := do
  if (world.balance sender).toNat < value then throw s!"sender cannot pay value {value}"
  let tx : Transaction := .legacy
    { nonce := (world.account sender).nonce, gasPrice := 0, gas, to, value, data,
      v := 27, r := 0, s := 0 }
  let intrinsic := (Tx.intrinsicGas tx).regular
  if gas < intrinsic then throw s!"gas limit {gas} below intrinsic cost {intrinsic}"
  let nonce := (world.account sender).nonce
  let w := Interpreter.incrementNonce world sender
  let msg := Tx.prepareMessage crypto .cancun env w tx sender nonce (gas - intrinsic)
  let ctx : Context := { crypto, fork := .cancun, block := env,
                         tx := { origin := sender, gasPrice := 0 } }
  let res ← match Interpreter.processMessageCall fuel ctx w ∅ msg with
    | .ok r => pure r
    | .error _ => throw "interpreter out of fuel"
  let gasUsedBeforeRefund := gas - res.gasLeft
  let refund := min (gasUsedBeforeRefund / 5) res.refundCounter.toNat
  let w := res.accountsToDelete.foldl (fun w a => w.erase a) res.world
  let w := Tx.destroyTouchedEmpty w res.touchedAccounts
  return ({ success := res.success, output := res.output, logs := res.logs,
            gasUsed := gasUsedBeforeRefund - refund }, w)

/-- The intrinsic gas of a legacy transaction to `to` (a creation if `none`) with `data`: the
least gas limit a transaction may carry. -/
def intrinsicGasOf (to : Option Address) (data : ByteArray) : Nat :=
  (Tx.intrinsicGas (.legacy { nonce := 0, gasPrice := 0, gas := 0, to, value := 0, data,
                              v := 27, r := 0, s := 0 })).regular

/-- The non-zero storage slots of `a` (storage never holds zeros). -/
def storageSlots (w : World) (a : Address) : List Word := (w.account a).storage.keys

end Examples.Differential
