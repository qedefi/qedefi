import Verified.OpenZeppelin.Proxy.GuardTrace
import EvmLogic.Program.Nested.GuardDelegWorld
import EvmLogic.Tx.IdleDel

/-!
# Only the owner can upgrade, EIP-7702 authorizations included

`Dep.impl_kept` (`Guard.lean`) assumes `ctx.fork < .prague ∨ ctx.tx.authorizations = []`. Here
that hypothesis is replaced by what it was protecting against:

* the owner signed none of the transaction's authorizations (`hauth`). Signing one is acting: it
  installs a delegation designator at the owner's account, and code then runs as the owner. The
  other authorities may delegate their accounts to anything; the three contracts hold real code,
  which no authorization rewrites;
* a call to the owner runs the code at the owner's account (`hca`: `codeAddress` is the owner),
  true of the message of every transaction (`EvmLogic.Tx.prepareMessage_codeAddress`).

`impl_kept_7702` is `impl_kept` with these two hypotheses (`EvmLogic.Program.Nested.
processMessageCall_guard_7702`). `deployed_7702` keeps the whole deployment (`Deployed`: code,
slots, the owner idle) and adds that the owner is not scheduled for deletion, which a transaction
needs to keep the owner idle after its suffix (`Verified.OpenZeppelin.Proxy.GuardTx`).
-/

namespace Verified.OpenZeppelin.Proxy

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open EvmLogic.AbsInt Verified.OpenZeppelin.Contracts

namespace Dep

variable (D : Dep)

/-- The owner signed none of the authorizations: the idle principal of the guard does not act. -/
theorem idleNoAuth {ctx : Context}
    (hauth : ∀ auth ∈ ctx.tx.authorizations, recoverAuthority ctx.crypto auth ≠ some D.o) :
    IdleNoAuth D.X ctx := fun auth ha a hra hx => hauth auth ha (by rw [hra, show a = D.o from hx])

/-- **Only the owner can upgrade, for any transaction.** From a world where the proxy, its
ProxyAdmin and the implementation are deployed, the implementation slot holds `ia` and ProxyAdmin
is owned by an externally owned account `o` that has sent a transaction (no code, nonce `≠ 0`):
every top-level message call whose sender is neither `o` nor one of the three contracts, among
whose EIP-7702 authorizations `o` signed none, and which runs the owner's own code if it calls
the owner, leaves the implementation slot and ProxyAdmin's owner unchanged. `impl_kept` without
`ctx.fork < .prague ∨ ctx.tx.authorizations = []`. -/
theorem impl_kept_7702 {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    (hpx : w.code D.px = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩)
    (hpa : w.code D.pa = OzProxyAdmin.runtimeCode) (hia : w.code D.ia = ActorImpl.runtimeCode)
    (himpl : w.sload D.px implSlot = Word.ofAddress D.ia)
    (howner : w.sload D.pa 0 = Word.ofAddress D.o)
    (ho : (w.code D.o).size = 0 ∧ (w.account D.o).nonce ≠ 0)
    (hauth : ∀ auth ∈ ctx.tx.authorizations, recoverAuthority ctx.crypto auth ≠ some D.o)
    (htop : TopOk D.Rl w msg) (hsender : msg.caller ≠ D.o)
    (hto : msg.currentTarget = D.o → msg.target = some D.o → msg.code.size = 0)
    (hca : msg.currentTarget = D.o → msg.target = some D.o → msg.codeAddress = some D.o)
    {fuel : Nat} {r : MessageResult} (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    r.world.sload D.px implSlot = Word.ofAddress D.ia ∧
      r.world.sload D.pa 0 = Word.ofAddress D.o := by
  have hw : RelayCode D.Rl D.code w := by
    rintro r (rfl | rfl | rfl)
    · rw [hpx, code_px]
    · rw [hpa, code_pa]
    · rw [hia, code_ia]
  exact processMessageCall_guard_7702 (codeOk D) D.G_keep D.inv hw ⟨himpl, howner⟩
    (fun x hx => hx ▸ ho) (D.idleNoAuth hauth) (fun hx ht => by
      have hx' : msg.currentTarget = D.o := hx
      rw [hx'] at ht ⊢; exact hca hx' ht)
    ⟨htop, hsender, fun hx ht => hto hx (hx ▸ ht)⟩ hr

/-- **A message call not sent by the owner keeps the deployment, for any transaction**, and does
not schedule the owner for deletion: `Deployed` holds after it (code, implementation, owner, the
owner idle), and `o ∉ r.accountsToDelete`. The hypotheses are those of `impl_kept_7702`. -/
theorem deployed_7702 {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    (hw : D.Deployed w)
    (hauth : ∀ auth ∈ ctx.tx.authorizations, recoverAuthority ctx.crypto auth ≠ some D.o)
    (htop : TopOk D.Rl w msg) (hsender : msg.caller ≠ D.o)
    (hto : msg.currentTarget = D.o → msg.target = some D.o → msg.code.size = 0)
    (hca : msg.currentTarget = D.o → msg.target = some D.o → msg.codeAddress = some D.o)
    {fuel : Nat} {r : MessageResult} (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    D.Deployed r.world ∧ D.o ∉ r.accountsToDelete := by
  have hg := (D.deployed_iff w).1 hw
  have hca' : D.X msg.currentTarget → msg.target = some msg.currentTarget →
      msg.codeAddress = some msg.currentTarget := fun hx ht => by
    have hx' : msg.currentTarget = D.o := hx
    rw [hx'] at ht ⊢; exact hca hx' ht
  have htop' : GuardTop D.Rl D.X w msg := ⟨htop, hsender, fun hx ht => hto hx (hx ▸ ht)⟩
  refine ⟨(D.deployed_iff _).2 (processMessageCall_guard_world_7702 (codeOk D) D.G_keep D.inv
    hg (D.idleNoAuth hauth) hca' htop' hr), ?_⟩
  exact EvmLogic.Tx.processMessageCall_not_deleted (X := D.X)
    (fun _ hm => reaches_createIdle_7702 (codeOk D) D.G_keep D.inv hg.2.1 hg.1 hg.2.2
      (D.idleNoAuth hauth) hca' htop' trivial hm) hr D.o rfl

end Dep

end Verified.OpenZeppelin.Proxy
