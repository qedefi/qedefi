import Verified.OpenZeppelin.Constructor.ProxyDeploy
import Verified.OpenZeppelin.Proxy.GuardTrace

/-!
# The proxy's upgrade guard, anchored at deployment

`Dep.trace_impl_kept` (`Verified.OpenZeppelin.Proxy.GuardTrace`) starts from a world assumed to
be `Dep.Deployed`. Here that world is the result of the proxy's own creation (`proxy_create`):

- `deployed_of_create`: the creation succeeds and its world is `Deployed` for the deployment
  `(px, pa, logic, o)`, `px` the created proxy and `pa = createAddress px 1` its `ProxyAdmin`,
  as soon as `o` is an externally owned account that has sent a transaction.
- `trace_impl_kept_of_create`: from that world, along any trace of transactions none of which is
  sent by `o`, the implementation slot still holds `logic` and the `ProxyAdmin` is still owned
  by `o`; nothing is assumed about the starting state beyond the creation's preconditions.

The deployment `D : Dep` is given existentially; it carries only the four addresses and proofs
that they differ, so it is unique.
-/

namespace Verified.OpenZeppelin.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program Verified.OpenZeppelin.Contracts
open Verified.OpenZeppelin.Proxy

/-- A `ProxyDeployed` world is `Deployed`, given that `logic` held `ActorImpl` and `o` was an
externally owned account with a non-zero nonce before (neither changes, being neither the proxy
nor its admin). -/
theorem deployed_of_proxyDeployed {w w' : World} {D : Dep}
    (hdep : ProxyDeployed w D.px D.ia D.o D.pa w')
    (hlogic : w.code D.ia = ActorImpl.runtimeCode) (hoCode : (w.code D.o).size = 0)
    (hoNonce : (w.account D.o).nonce ≠ 0) (hopx : D.o ≠ D.px) (hopa : D.o ≠ D.pa) :
    D.Deployed w' where
  codePx := hdep.codePx
  codePa := hdep.codePa
  codeIa := by
    show (w'.account D.ia).code = _
    rw [hdep.other _ D.px_ia.symm D.pa_ia.symm]; exact hlogic
  impl := hdep.impl
  owner := hdep.owner
  ownerCode := by
    show (w'.account D.o).code.size = 0
    rw [hdep.other _ hopx hopa]; exact hoCode
  ownerNonce := by rw [hdep.other _ hopx hopa]; exact hoNonce

/-- **Deploying the proxy gives a `Deployed` world.** Under the hypotheses of `proxy_create`,
and with `o` an externally owned account that has sent a transaction (no code, nonce `≠ 0`, as
`Dep.Deployed` requires), the creation terminates successfully in a world that is `Deployed`
for the deployment of `px = msg.currentTarget`, `pa = createAddress px 1`, `logic` and `o`. -/
theorem deployed_of_create {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    {logic o : Address}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (htarget : msg.target = none)
    (hcode : msg.code = OzTransparentProxy.creationCode ++
      OzTransparentProxy.constructorArgsFor logic o)
    (hval : msg.value = 0) (hdepth : msg.depth = 0) (hstatic : msg.isStatic = false)
    (hd : accountDeployable w msg.currentTarget = true)
    (hlogic : w.code logic = ActorImpl.runtimeCode)
    (hpre : Precompile.isPrecompile ctx.fork logic = false)
    (ho : o ≠ 0) (hoCode : (w.code o).size = 0) (hoNonce : (w.account o).nonce ≠ 0)
    (hpaDep : accountDeployable w (createAddress ctx.crypto.keccak256 msg.currentTarget 1) = true)
    (hpaSelf : createAddress ctx.crypto.keccak256 msg.currentTarget 1 ≠ msg.currentTarget)
    (hpa0 : createAddress ctx.crypto.keccak256 msg.currentTarget 1 ≠ 0)
    (hg : 1000000 ≤ msg.gas) (hg' : msg.gas < 2 ^ 64) :
    ∃ r : MessageResult, (∃ n, ∀ fuel, n ≤ fuel → processMessageCall fuel ctx w tr msg = .ok r) ∧
      r.success = true ∧ ∃ D : Dep, D.px = msg.currentTarget ∧
        D.pa = createAddress ctx.crypto.keccak256 msg.currentTarget 1 ∧ D.ia = logic ∧ D.o = o ∧
        D.Deployed r.world := by
  obtain ⟨r, hr, hs, hdep⟩ := proxy_create hdeleg htarget hcode hval hdepth hstatic hd hlogic hpre
    ho hpaDep hpaSelf hpa0 hg hg'
  simp only [accountDeployable, Bool.and_eq_true, decide_eq_true_eq] at hd hpaDep
  have hsz : (w.code logic).size ≠ 0 := by rw [hlogic, ActorImpl.size_runtimeCode]; decide
  have hpxIa : msg.currentTarget ≠ logic := fun he => hsz (by rw [← he]; exact hd.1.2)
  have hpaIa : createAddress ctx.crypto.keccak256 msg.currentTarget 1 ≠ logic := fun he =>
    hsz (by rw [← he]; exact hpaDep.1.2)
  have hopx : o ≠ msg.currentTarget := fun he => hoNonce (by rw [he]; exact hd.1.1)
  have hopa : o ≠ createAddress ctx.crypto.keccak256 msg.currentTarget 1 := fun he =>
    hoNonce (by rw [he]; exact hpaDep.1.1)
  refine ⟨r, hr, hs, ⟨msg.currentTarget, _, logic, o, hpaSelf.symm, hpxIa, hpaIa⟩,
    rfl, rfl, rfl, rfl, ?_⟩
  exact deployed_of_proxyDeployed (D := ⟨msg.currentTarget, _, logic, o, hpaSelf.symm, hpxIa,
    hpaIa⟩) hdep hlogic hoCode hoNonce hopx hopa

/-- **Only the owner can upgrade, from deployment on.** Under the hypotheses of
`deployed_of_create`, the creation of the proxy terminates successfully, and along every trace
from its world whose transactions are not sent by `o` (with any environment steps between
them, `Dep.Reach`), the implementation slot of the proxy still holds `logic` and the
`ProxyAdmin` is still owned by `o`. -/
theorem trace_impl_kept_of_create {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {logic o : Address}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (htarget : msg.target = none)
    (hcode : msg.code = OzTransparentProxy.creationCode ++
      OzTransparentProxy.constructorArgsFor logic o)
    (hval : msg.value = 0) (hdepth : msg.depth = 0) (hstatic : msg.isStatic = false)
    (hd : accountDeployable w msg.currentTarget = true)
    (hlogic : w.code logic = ActorImpl.runtimeCode)
    (hpre : Precompile.isPrecompile ctx.fork logic = false)
    (ho : o ≠ 0) (hoCode : (w.code o).size = 0) (hoNonce : (w.account o).nonce ≠ 0)
    (hpaDep : accountDeployable w (createAddress ctx.crypto.keccak256 msg.currentTarget 1) = true)
    (hpaSelf : createAddress ctx.crypto.keccak256 msg.currentTarget 1 ≠ msg.currentTarget)
    (hpa0 : createAddress ctx.crypto.keccak256 msg.currentTarget 1 ≠ 0)
    (hg : 1000000 ≤ msg.gas) (hg' : msg.gas < 2 ^ 64) :
    ∃ r : MessageResult, (∃ n, ∀ fuel, n ≤ fuel → processMessageCall fuel ctx w tr msg = .ok r) ∧
      r.success = true ∧ ∃ D : Dep, D.px = msg.currentTarget ∧
        D.pa = createAddress ctx.crypto.keccak256 msg.currentTarget 1 ∧ D.ia = logic ∧ D.o = o ∧
        ∀ (txs : List Message) (w' : World), D.Reach r.world txs w' →
          (∀ tx ∈ txs, tx.caller ≠ o) →
          w'.sload msg.currentTarget OzTransparentProxy.implementationSlot =
              Word.ofAddress logic ∧
            w'.sload (createAddress ctx.crypto.keccak256 msg.currentTarget 1) 0 =
              Word.ofAddress o := by
  obtain ⟨r, hr, hs, D, hpx, hpa, hia, hoD, hD⟩ := deployed_of_create hdeleg htarget hcode hval
    hdepth hstatic hd hlogic hpre ho hoCode hoNonce hpaDep hpaSelf hpa0 hg hg'
  refine ⟨r, hr, hs, D, hpx, hpa, hia, hoD, fun txs w' hreach hcaller => ?_⟩
  obtain ⟨h1, h2, -⟩ := D.trace_impl_kept hD hreach (by rw [hoD]; exact hcaller)
  rw [hpx, hia] at h1
  rw [hpa, hoD] at h2
  exact ⟨h1, h2⟩

end Verified.OpenZeppelin.Constructor
