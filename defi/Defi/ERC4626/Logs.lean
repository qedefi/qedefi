import EvmLogic.Solidity.Events
import EvmLean.Crypto.Keccak

/-!
# The logs of the Solmate contracts' events

* **Topics.** `transferTopic`, `approvalTopic`, `depositTopic`, `withdrawTopic` are the
  Keccak-256 hashes of the event signatures (checked against the executable Keccak below and
  against `contracts/artifacts/*/events.json`). In the bytecode they are `PUSH32` constants (or
  copied from the code), so no hash hypothesis is involved: the theorems hold for every
  `Crypto`.
* **Logs.** `transferLog token src dst v` = `Transfer(src, dst, v)` emitted by `token`: topics
  `[transferTopic, pad(src), pad(dst)]` (indexed addresses left-padded), data the ABI word of
  `v`; `approvalLog`; `depositLog vault caller owner assets shares` (data: two words);
  `withdrawLog vault caller receiver owner assets shares` (three indexed addresses).
* **Tactics** for the companion proofs: `event_log d` closes the equation between the entry a
  `LOGn` appended during symbolic execution (`logEntry`, a memory read) and the expected log
  with data words `d`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Interpreter EvmLean.Solidity

/-! ## Topics and logs -/

/-- `keccak256("Transfer(address,address,uint256)")`. -/
def transferTopic : Word :=
  0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef#256

/-- `keccak256("Approval(address,address,uint256)")`. -/
def approvalTopic : Word :=
  0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925#256

/-- `keccak256("Deposit(address,address,uint256,uint256)")`. -/
def depositTopic : Word :=
  0xdcbc1c05240f31ff3ad067ef1ee35ce4997762752e3a095284754544f4c709d7#256

/-- `keccak256("Withdraw(address,address,address,uint256,uint256)")`. -/
def withdrawTopic : Word :=
  0xfbde797d201c681b91056529119e0b02407c7bb96a4a2c75c01fc9667232c8db#256

#guard Keccak.hash256 "Transfer(address,address,uint256)".toUTF8 = transferTopic
#guard Keccak.hash256 "Approval(address,address,uint256)".toUTF8 = approvalTopic
#guard Keccak.hash256 "Deposit(address,address,uint256,uint256)".toUTF8 = depositTopic
#guard Keccak.hash256 "Withdraw(address,address,address,uint256,uint256)".toUTF8 =
  withdrawTopic

/-- `Transfer(src, dst, amount)` emitted by `token`. -/
def transferLog (token src dst : Address) (amount : Word) : Log :=
  eventLog token [transferTopic, Word.ofAddress src, Word.ofAddress dst] [amount]

/-- `Approval(owner, spender, amount)` emitted by `token`. -/
def approvalLog (token owner spender : Address) (amount : Word) : Log :=
  eventLog token [approvalTopic, Word.ofAddress owner, Word.ofAddress spender] [amount]

/-- `Deposit(caller, owner, assets, shares)` emitted by `vault`. -/
def depositLog (vault caller owner : Address) (assets shares : Word) : Log :=
  eventLog vault [depositTopic, Word.ofAddress caller, Word.ofAddress owner] [assets, shares]

/-- `Withdraw(caller, receiver, owner, assets, shares)` emitted by `vault`. -/
def withdrawLog (vault caller receiver owner : Address) (assets shares : Word) : Log :=
  eventLog vault [withdrawTopic, Word.ofAddress caller, Word.ofAddress receiver,
    Word.ofAddress owner] [assets, shares]

/-! ## Tactics -/

/-- Close the memory goal `mem.read off len = Abi.encodeArgs [..]` of an event's data after
symbolic execution: read-over-write through the `MSTORE`s and expansions. -/
macro "event_data" : tactic => `(tactic| (
  dsimp only
  simp (disch := decide) only [BitVec.reduceToNat, Memory.read_expand, Memory.read_storeWord,
    Memory.read_storeWord_of_disjoint, Memory.read_64, encodeArgs_one, encodeArgs_two]))

/-- Turn the entry a `LOGn` appended (`logEntry`) into the `eventLog` with data `d` and close
the log equation: the data by `event_data`, the rest (address, topics, earlier logs) by
`rfl`. -/
macro "event_log " d:term : tactic => `(tactic| (
  rw [logEntry_eq_eventLog (data := $d)]
  rotate_left
  event_data
  try rfl))

end EvmLeanSpecs.Refinement
