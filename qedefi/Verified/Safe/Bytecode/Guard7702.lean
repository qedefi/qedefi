import Verified.Safe.Bytecode.Guard
import EvmLogic.Program.Nested.GuardDelegWorld
import EvmLogic.Tx.IdleDel

/-!
# Only a quorum of Safe owners can upgrade, EIP-7702 authorizations included

`Verified.Safe.Guard.Dep.impl_kept` assumes `ctx.fork < .prague ∨ ctx.tx.authorizations = []`.
Here that hypothesis is replaced by what it was protecting against:

* no idle principal (an owner outside the signers `T`, and from Prague the address `1`) signed
  one of the transaction's authorizations (`hauth`). Signing one is acting: it installs a
  delegation designator at the signer's account, and code then runs as that account. Other
  authorities may delegate their accounts to anything; the five relays hold real code, which no
  authorization rewrites;
* a call to an idle account runs the code at that account (`hca`), true of the message of every
  transaction (`EvmLogic.Tx.prepareMessage_codeAddress`).

`impl_kept_7702` is `impl_kept` with these two hypotheses
(`EvmLogic.Program.Nested.processMessageCall_guardD_7702`). `guard_world_7702` keeps the whole
deployment (`GuardWorld`: the protected state, the relays' code, the idle principals idle) and
adds that no idle principal is scheduled for deletion, which a transaction needs to keep them
idle after its suffix (`Verified.Safe.Guard.GuardTx`).
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open EvmLogic.AbsInt Verified.OpenZeppelin.Contracts Verified.OpenZeppelin.Proxy
open Verified.Safe.Contracts

namespace Dep

variable (D : Dep)

/-- **Only a quorum of the Safe's owners can upgrade, for any transaction.** `impl_kept` with,
instead of `ctx.fork < .prague ∨ ctx.tx.authorizations = []`: no idle principal signed one of the
transaction's EIP-7702 authorizations (`hauth`), and a call to an idle account runs the code at
that account (`hca`, true of every transaction's message). The other hypotheses are those of
`impl_kept`. -/
theorem impl_kept_7702 {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    {O T : Finset Address} {thr : Nat} {h₀ : Word}
    (hpx : w.code D.px = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩)
    (hpa : w.code D.pa = OzProxyAdmin.runtimeCode) (hia : w.code D.ia = ActorImpl.runtimeCode)
    (hsf : w.code D.sf = SafeProxy.runtimeCode) (hsg : w.code D.sg = SafeSingleton.runtimeCode)
    (himpl : w.sload D.px implSlot = Word.ofAddress D.ia)
    (howner : w.sload D.pa 0 = Word.ofAddress D.sf)
    (hsafe : D.SafeOk ctx.crypto ctx.block.chainId O T thr h₀ (w.sload D.sf))
    (hthr : thr < 2 ^ 256) (hcard : (O ∩ T).card < thr)
    (hsig : Signers ctx.crypto ctx.block.chainId D.sf O T)
    (hh : h₀ = 0 ∨ ¬ D.Rl (Word.toAddress h₀))
    (hidle : ∀ x, X ctx.fork O T x → (w.code x).size = 0 ∧ (w.account x).nonce ≠ 0)
    (hcaller : ¬ X ctx.fork O T msg.caller)
    (hcode : X ctx.fork O T msg.currentTarget → msg.target = some msg.currentTarget →
      msg.code.size = 0)
    (hauth : ∀ auth ∈ ctx.tx.authorizations, ∀ a, recoverAuthority ctx.crypto auth = some a →
      ¬ X ctx.fork O T a)
    (hca : X ctx.fork O T msg.currentTarget → msg.target = some msg.currentTarget →
      msg.codeAddress = some msg.currentTarget)
    (htop : TopOk D.Rl w msg)
    (hR : ∀ m, Reaches ctx w tr msg m → D.Rw ctx.crypto ctx.block.chainId O T m)
    {fuel : Nat} {r : MessageResult} (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    D.G ctx.crypto ctx.block.chainId O T thr h₀ r.world := by
  have hw : RelayCode D.Rl D.code w := by
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · rw [hpx, code_px]
    · rw [hpa, code_pa]
    · rw [hia, code_ia]
    · rw [hsf, code_sf]
    · rw [hsg, code_sg]
  exact processMessageCall_guardD_7702 (K := Kc ctx) (codeOk D) D.G_keep
    (D.inv ctx hthr hcard hsig hh) hw ⟨himpl, howner, hsafe⟩ hidle hauth hca
    ⟨htop, hcaller, hcode⟩ hR hr rfl

/-- **A message call signed by fewer than `thr` owners keeps the deployment, for any
transaction**, and schedules no idle principal for deletion. Hashing, chain id and fork are
those of the context (`hcr`, `hch`, `hfk`); the world hypotheses are bundled as `GuardWorld`
(the protected state `G`, the five relays' code, the idle principals idle); the others are those
of `impl_kept_7702`. -/
theorem guard_world_7702 {crypto : Crypto} {chainId : Nat} {fork : Fork} {ctx : Context}
    {w : World} {tr : TransientStorage} {msg : Message} {O T : Finset Address} {thr : Nat}
    {h₀ : Word} (hcr : ctx.crypto = crypto) (hch : ctx.block.chainId = chainId)
    (hfk : ctx.fork = fork)
    (hw : GuardWorld D.Rl D.code (X fork O T) (D.G crypto chainId O T thr h₀) w)
    (hthr : thr < 2 ^ 256) (hcard : (O ∩ T).card < thr)
    (hsig : Signers crypto chainId D.sf O T) (hh : h₀ = 0 ∨ ¬ D.Rl (Word.toAddress h₀))
    (hauth : IdleNoAuth (X fork O T) ctx)
    (hca : X fork O T msg.currentTarget → msg.target = some msg.currentTarget →
      msg.codeAddress = some msg.currentTarget)
    (hmsg : GuardTop D.Rl (X fork O T) w msg)
    (hR : ∀ m, Reaches ctx w tr msg m → D.Rw crypto chainId O T m)
    {fuel : Nat} {r : MessageResult} (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    GuardWorld D.Rl D.code (X fork O T) (D.G crypto chainId O T thr h₀) r.world ∧
      ∀ x, X fork O T x → x ∉ r.accountsToDelete := by
  subst hcr hch hfk
  refine ⟨processMessageCall_guardD_world_7702 (K := Kc ctx) (codeOk D) D.G_keep
    (D.inv ctx hthr hcard hsig hh) hw hauth hca hmsg hR hr rfl, ?_⟩
  exact EvmLogic.Tx.processMessageCall_not_deleted
    (fun _ hm => reaches_createIdleD_7702 (K := Kc ctx) (codeOk D) D.G_keep
      (D.inv ctx hthr hcard hsig hh) hw.2.1 hw.1 hw.2.2 hauth hca hmsg hR rfl hm) hr

end Dep

end Verified.Safe.Guard
