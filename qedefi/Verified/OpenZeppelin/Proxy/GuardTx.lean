import Verified.OpenZeppelin.Proxy.Guard7702
import EvmLogic.Tx.Guard

/-!
# Only the owner can upgrade: whole transactions, and any sequence of them

`Guard.lean` and `Guard7702.lean` prove the upgrade guard for one top-level message call, and
`GuardTrace.lean` for traces of message calls interleaved with assumed environment steps. Here
the guard is a theorem about `EvmLean.Tx.process` (`deployed_tx`, `impl_kept_tx`), and about any
sequence of real transactions (`txs_impl_kept`), with nothing assumed between them:

* "not sent by the owner" is about the transaction's **recovered sender** (`out.sender`), and the
  EIP-7702 hypothesis is that the owner signed none of the transaction's authorizations — any
  type, recipient, calldata, value, gas, fees and authorizations otherwise, any fork and block;
* the message-level hypotheses are derived: the message's sender is the recovered sender, it is
  not one of the contracts (EIP-3607: they hold code), a call runs the recipient's own code from
  the world after the fee debit (`EvmLogic.Tx.process_split_guard`);
* the prefix (the sender's nonce and fee) and the suffix (refund, coinbase reward,
  self-destructed and touched-empty accounts erased) keep the deployment: the contracts hold real
  code, so they are not deleted; the owner is never created in the transaction (its nonce is not
  zero), so it is not deleted and keeps its nonce (`EvmLogic.Tx.guardWorld_suffixWorld`).

So the environment steps of `GuardTrace.lean` (a transaction's nonce and fee, the owner not
acting) are no longer assumed: `txs_impl_kept` is stated over `EvmLogic.Tx.TxSteps`, sequences of
successful transactions and nothing else.
-/

namespace Verified.OpenZeppelin.Proxy

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLean.Tx EvmLogic.Program.Nested
open EvmLogic.Tx Verified.OpenZeppelin.Contracts

namespace Dep

variable (D : Dep)

/-- **The owner does not act in the transaction**: it is not the transaction's recovered sender,
and it signed none of its EIP-7702 authorizations. -/
def OwnerIdle (i : Input) (_ : World) (out : TxOutput) : Prop :=
  out.sender ≠ D.o ∧ ∀ auth ∈ i.tx.authorizations, recoverAuthority i.crypto auth ≠ some D.o

theorem txIdle {crypto : Crypto} {tx : Transaction} {out : TxOutput} (hsender : out.sender ≠ D.o)
    (hauth : ∀ auth ∈ tx.authorizations, recoverAuthority crypto auth ≠ some D.o) :
    TxIdle D.X crypto tx out :=
  ⟨hsender, fun auth ha a hra hx => hauth auth ha (by rw [hra, show a = D.o from hx])⟩

/-- **A transaction not sent by the owner keeps the deployment.** From a deployed world (the
three contracts hold their code, the implementation slot holds `ia`, ProxyAdmin is owned by `o`,
an externally owned account that has sent a transaction), every successful transaction whose
recovered sender is not `o` and none of whose EIP-7702 authorizations `o` signed (any other
sender, type, recipient, calldata, value, gas, fees and authorizations; any fork, block, hashing)
ends in a deployed world. -/
theorem deployed_tx {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {w : World} {tx : Transaction} {hint : Option Address}
    {out : TxOutput} (hw : D.Deployed w) (hsender : out.sender ≠ D.o)
    (hauth : ∀ auth ∈ tx.authorizations, recoverAuthority crypto auth ≠ some D.o)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    D.Deployed out.world :=
  (D.deployed_iff _).2 (process_guard_world_7702 (codeOk D) D.G_keep D.inv
    ((D.deployed_iff w).1 hw) (D.txIdle hsender hauth) h)

/-- **Only the owner can upgrade, for every transaction**: a successful transaction from a
deployed world, not sent by the owner and carrying no authorization the owner signed, leaves the
implementation slot and ProxyAdmin's owner unchanged (and the world deployed). -/
theorem impl_kept_tx {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {w : World} {tx : Transaction} {hint : Option Address}
    {out : TxOutput} (hw : D.Deployed w) (hsender : out.sender ≠ D.o)
    (hauth : ∀ auth ∈ tx.authorizations, recoverAuthority crypto auth ≠ some D.o)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    out.world.sload D.px implSlot = Word.ofAddress D.ia ∧
      out.world.sload D.pa 0 = Word.ofAddress D.o ∧ D.Deployed out.world :=
  have hd := D.deployed_tx hw hsender hauth h
  ⟨hd.impl, hd.owner, hd⟩

/-- **Only the owner can upgrade, along any sequence of transactions.** From a deployed world,
after any number of successful transactions in none of which the owner acts (it sends none and
signs none of their authorizations), the implementation slot still holds `ia`, ProxyAdmin is
still owned by `o`, and the world is still deployed. Nothing is assumed between transactions. -/
theorem txs_impl_kept {w₀ w : World} (h₀ : D.Deployed w₀) (h : TxSteps D.OwnerIdle w₀ w) :
    w.sload D.px implSlot = Word.ofAddress D.ia ∧ w.sload D.pa 0 = Word.ofAddress D.o ∧
      D.Deployed w := by
  have hd : D.Deployed w :=
    h.keeps (fun _ _ _ hw hr hok => D.deployed_tx hw hok.1 hok.2 hr) h₀
  exact ⟨hd.impl, hd.owner, hd⟩

/-- **Until the owner acts.** Along any sequence of transactions from a deployed world, the first
transaction in which the owner acts (`i`, after `pre`, in none of which it acts) starts from a
world where the implementation slot still holds `ia` and ProxyAdmin is still owned by `o`: every
upgrade is caused by a transaction of the owner. -/
theorem txs_impl_until_owner {w₀ v : World} {i : Input} {out : TxOutput}
    (h₀ : D.Deployed w₀) (hpre : TxSteps D.OwnerIdle w₀ v) (hr : i.run v = .ok out)
    (hchg : out.world.sload D.px implSlot ≠ v.sload D.px implSlot ∨
      out.world.sload D.pa 0 ≠ v.sload D.pa 0) :
    ¬ D.OwnerIdle i v out ∧ v.sload D.px implSlot = Word.ofAddress D.ia ∧
      v.sload D.pa 0 = Word.ofAddress D.o := by
  obtain ⟨hi, ho, hv⟩ := D.txs_impl_kept h₀ hpre
  refine ⟨fun hok => ?_, hi, ho⟩
  obtain ⟨hi', ho', -⟩ := D.impl_kept_tx hv hok.1 hok.2 hr
  rcases hchg with hc | hc
  · exact hc (hi'.trans hi.symm)
  · exact hc (ho'.trans ho.symm)

end Dep

/-! ## The hypotheses are satisfiable -/

namespace Example

/-- **On the example deployment**: no sequence of transactions in which the owner does not act
upgrades. -/
theorem world_txs_impl_kept {w : World} (h : TxSteps dep.OwnerIdle world w) :
    w.sload dep.px implSlot = Word.ofAddress dep.ia :=
  (dep.txs_impl_kept world_deployed h).1

end Example

end Verified.OpenZeppelin.Proxy
