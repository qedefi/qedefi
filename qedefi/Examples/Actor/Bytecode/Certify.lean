import Examples.OpenZeppelin.Contracts.OzProxyAdmin
import Examples.OpenZeppelin.Contracts.OzTransparentProxy
import Examples.OpenZeppelin.Contracts.ActorImpl
import EvmLogic.AbsInt.Guard.Frame
import EvmLogic.Tactic.KernelRfl

/-!
# Guarded certificates of the proxy, its ProxyAdmin and the implementation

The guarded abstract interpreter (`EvmLogic/AbsInt/Guard`) explores, in the kernel:

- **`OzProxyAdmin` when the sender is not the owner** (`cfgPA`: `CALLER` is atom `0`, slot `0`
  holds atom `1`, the two differ). `_checkOwner` compares them, so every owner-only function
  reverts: no call, no creation and no `SSTORE` is reachable.
- **`OzTransparentProxy` when the sender is not the admin** (`cfgPX`: `CALLER` is atom `0`, the
  admin immutable is `sym 0`, they differ; the implementation slot holds atom `1`). The admin
  branch is never taken: no `SSTORE`, and the only call goes to atom `1` (the `DELEGATECALL` to
  the implementation).
- **`ActorImpl`** (`cfgIA`): no call, no creation, `SSTORE` only at key `0`.

The trees do not depend on the valuation, so `pa_cert`, `px_cert` and `ia_cert` hold for every
sender, owner, admin and implementation.
-/

namespace Examples.Actor.ProxyGuard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.AbsInt EvmLogic.AbsInt.Guard Examples.OpenZeppelin.Contracts

/-! ## Configurations -/

/-- ProxyAdmin, sender (atom `0`) not the owner (atom `1`, in slot `0`). -/
def cfgPA : Cfg where
  callerAtom := some 0
  slots := [(0, 1)]
  distinct := [(.atom 0, .atom 1)]
  callAllowed := fun _ => false
  sstoreAllowed := fun _ => false

/-- The proxy, sender (atom `0`) not the admin (`sym 0`); the implementation slot holds atom `1`,
the only allowed call target. -/
def cfgPX : Cfg where
  callerAtom := some 0
  slots := [(OzTransparentProxy.implementationSlot.toNat, 1)]
  distinct := [(.atom 0, .sym 0)]
  callAllowed := fun a => a == .atom 1
  sstoreAllowed := fun _ => false

/-- The implementation: no call, `SSTORE` at key `0` only. -/
def cfgIA : Cfg where
  callAllowed := fun _ => false
  sstoreAllowed := fun a => a == .const 0

/-- The admin `PUSH32` of the proxy (instruction at pc `15`, immediate at offset `16`). -/
def proxySyms : List (Nat × Nat) := [(15, 0)]

def certFuel : Nat := 100000

/-! ## Explorations (kernel) -/

theorem pa_certify : (gcertify cfgPA OzProxyAdmin.runtimeCode [] [] certFuel).isSome = true := by
  kernel_decide

theorem px_certify :
    (gcertify cfgPX OzTransparentProxy.runtimeCode proxySyms [] certFuel).isSome = true := by
  kernel_decide

theorem ia_certify : (gcertify cfgIA ActorImpl.runtimeCode [] [] certFuel).isSome = true := by
  kernel_decide

theorem gscan_proxy (i : OzTransparentProxy.Immutables) :
    gscan (OzTransparentProxy.runtimeCodeWith i) proxySyms =
      gscan OzTransparentProxy.runtimeCode proxySyms := by
  kernel_decide

/-! ## Certificates -/

/-- The recorded states of ProxyAdmin. -/
def tPA : GTree := (gcertify cfgPA OzProxyAdmin.runtimeCode [] [] certFuel).get pa_certify

/-- The recorded states of the proxy. -/
def tPX : GTree :=
  (gcertify cfgPX OzTransparentProxy.runtimeCode proxySyms [] certFuel).get px_certify

/-- The recorded states of the implementation. -/
def tIA : GTree := (gcertify cfgIA ActorImpl.runtimeCode [] [] certFuel).get ia_certify

theorem pa_cert (ν : Env) : GCert ν cfgPA OzProxyAdmin.runtimeCode [] tPA :=
  gcertify_sound (fuel := certFuel) (syms := []) (Option.some_get pa_certify).symm
    (fun _ _ h => by cases h)

theorem ia_cert (ν : Env) : GCert ν cfgIA ActorImpl.runtimeCode [] tIA :=
  gcertify_sound (fuel := certFuel) (syms := []) (Option.some_get ia_certify).symm
    (fun _ _ h => by cases h)

theorem proxy_readBytes_admin (i : OzTransparentProxy.Immutables) :
    readBytes (OzTransparentProxy.runtimeCodeWith i) 16 32 =
      Bytes.ofWord (Word.ofAddress i.admin) := by
  have hp : i.patches = [] ++ (16, Word.ofAddress i.admin) :: [] := rfl
  simp only [OzTransparentProxy.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [OzTransparentProxy.size_runtimeCode]; decide)
    (by simp)

theorem proxy_symOk (i : OzTransparentProxy.Immutables) {ν : Env} (hν : ν.ρ 0 = i.admin) :
    SymOk ν.ρ (OzTransparentProxy.runtimeCodeWith i) proxySyms := by
  intro q k h
  simp only [proxySyms, symAt] at h
  split at h
  · rename_i hq
    cases h
    have : q = 15 := by simpa using hq
    subst this
    rw [proxy_readBytes_admin, Bytes.toWord_ofWord, hν]
  · cases h

theorem px_cert (i : OzTransparentProxy.Immutables) {ν : Env} (hν : ν.ρ 0 = i.admin) :
    GCert ν cfgPX (OzTransparentProxy.runtimeCodeWith i) [] tPX := by
  refine gcertify_sound (fuel := certFuel) (syms := proxySyms) ?_ (proxy_symOk i hν)
  have h := (Option.some_get px_certify).symm
  unfold gcertify gtable at h ⊢
  rw [gscan_proxy]
  exact h

end Examples.Actor.ProxyGuard
