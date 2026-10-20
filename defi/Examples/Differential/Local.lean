import EvmLean

/-!
# The evm-lean side of the differential tester

A transaction is executed the way `EvmLean.Tx.process` does it, except that the top-level
message is run directly with `Interpreter.processMessageCall` so that its return data is
visible: the sender's nonce is incremented, `Tx.prepareMessage` builds the message (warm
precompiles, origin, target and coinbase), the interpreter runs it, and the receipt's
`gasUsed` is computed with the EIP-3529 refund cap. Gas price and value are zero, so no
ether moves. Contract creations (`to = none`) run the creation code as a creation message.
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

/-- Execute a transaction from `sender` to `to` (or a creation) with calldata `data` and gas
limit `gas` in a block with environment `env` (the tester uses the block anvil mined the
same transaction in). Returns the outcome and the new world, or an error if the interpreter ran out
of fuel or the gas limit does not cover the intrinsic cost. -/
def execTx (crypto : Crypto) (env : BlockEnv) (world : World) (sender : Address)
    (to : Option Address) (data : ByteArray) (gas : Nat) : Except String (Outcome × World) := do
  let tx : Transaction := .legacy
    { nonce := (world.account sender).nonce, gasPrice := 0, gas, to, value := 0, data,
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

/-- The non-zero storage slots of `a` (storage never holds zeros). -/
def storageSlots (w : World) (a : Address) : List Word := (w.account a).storage.keys

end Examples.Differential
