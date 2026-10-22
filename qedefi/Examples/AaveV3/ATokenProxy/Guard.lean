import Examples.AaveV3.ATokenProxy.Forward
import Examples.AaveV3.ATokenProxy.Admin
import Examples.AaveV3.AToken.Guard

/-!
# The aToken proxy: the Pool-only entry points have no effect for anyone else

`proxy_poolOnly_noEffect` is `AToken.poolOnly_noEffect` for a frame running the aToken *proxy*
(`ATokenProxy.runtimeCode`, the code at every aToken address, e.g. a top-level call to the
proxy), whose EIP-1967 implementation slot points at code equal to the AToken implementation:
called by anyone but the Pool with one of the five `onlyPool` selectors, any further calldata
and any value, the frame reverts and changes nothing. The proof composes the proxy's forwarding
summary (`forward_halts`, the implementation run by `DELEGATECALL` on the proxy's storage, with
the proxy's caller and value) with the implementation's `poolOnly_noEffectOut`; the admin, who
cannot reach the implementation, gets the proxy's own revert (`admin_reverts`).
-/

namespace Examples.AaveV3.ATokenProxy
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Examples.AaveV3.Contracts Examples.AaveV3.AToken

theorem poolOnly_not_proxySelector {s : Nat} (h : s ∈ poolOnlySelectors) :
    s ∉ proxySelectors := by
  simp only [poolOnlySelectors, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The AToken implementation is not an EIP-7702 delegation designator. -/
theorem delegatedAddress_aToken : delegatedAddress? AToken.runtimeCode = none := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- **Access control through the proxy.** A frame running the aToken proxy whose implementation
slot points at the AToken implementation's code, called by anyone but the Pool with one of the
`onlyPool` selectors (any further calldata, any value, any world, any depth below 1024), reverts
and changes nothing (world, transient storage, created accounts, logs). Besides
`poolOnly_noEffect`'s hypotheses: the implementation is no precompile, and the gas covers the
proxy's calldata copy (`Gas.copyCost`, `Gas.memoryCost` of the calldata size). -/
theorem proxy_poolOnly_noEffect (m : Machine) (hf : Fresh ATokenProxy.runtimeCode m)
    (himpl : m.world.code (implementation m.world m.frame.msg.currentTarget) = AToken.runtimeCode)
    (hpre : m.precompiles.isPrecompile (implementation m.world m.frame.msg.currentTarget) = false)
    (hsel : Abi.selectorOf m.frame.msg.data ∈ poolOnlySelectors)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc : m.frame.msg.caller ≠ pool) (hdepth : m.frame.msg.depth < 1024)
    (hg : 18000 + Gas.copyCost m.frame.msg.data.size + Gas.memoryCost m.frame.msg.data.size ≤
      m.frame.gasLeft)
    (hgu : m.frame.gasLeft < 2 ^ 256) :
    Halts m (NoEffect (10000 + Gas.copyCost m.frame.msg.data.size +
      Gas.memoryCost m.frame.msg.data.size) m) := by
  have hsel' := Or.inr (a := m.frame.msg.data.size < 4) (poolOnly_not_proxySelector hsel)
  by_cases ha : m.frame.msg.caller = admin
  · exact (admin_reverts m hf hsel' ha hsize' (by omega)).mono fun _ _ _ h =>
      ⟨h.1, ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩, by have := h.2.2.2.2.2; omega⟩
  refine (forward_halts m hf (B := 4) (G := 3000) (Hc := fun mc => NoEffectOut 3000 4 mc) hsel' ha
    hsize' (.inr (by rw [himpl]; exact delegatedAddress_aToken)) hpre hdepth
    (by simp only [Gas.copyCost, Gas.copyPerWord, Gas.words, Gas.memoryCost, Gas.memoryPerWord]
        at hg ⊢; omega) hgu ?_ ?_).mono ?_
  · rintro mc mcf oc ⟨⟨out, rfl, hout⟩, -⟩
    exact hout
  · intro mc hfr hdf hG
    rw [himpl] at hfr
    exact poolOnly_noEffectOut mc hfr (by rw [hdf.data]; exact hsel)
      (by rw [hdf.data]; exact hsize') (by rw [hdf.caller]; exact hc) hG
  · rintro mf o - ⟨mc, mcf, oc, hdf, ⟨⟨out, rfl, -⟩, ⟨hw, ht, hca, hl⟩, hgc⟩, hfw⟩
    obtain ⟨ho, hw', ht', hca', hl', hg'⟩ := hfw
    refine ⟨⟨out, ho⟩, ⟨hw', ht', hca'.trans (hca.trans hdf.created), hl'⟩, ?_⟩
    simp only [Gas.copyCost, Gas.copyPerWord, Gas.words, Gas.memoryCost, Gas.memoryPerWord]
      at hg' ⊢
    omega

/-- **No storage write through the proxy by a non-Pool caller.** Under the hypotheses of
`proxy_poolOnly_noEffect`, every storage slot of the proxy account, among them the aToken's
`_totalSupply` (slot 54) and `_userState` rows (slot 52), holds its old value when the frame
ends. -/
theorem proxy_poolOnly_sload_unchanged (m : Machine) (hf : Fresh ATokenProxy.runtimeCode m)
    (himpl : m.world.code (implementation m.world m.frame.msg.currentTarget) = AToken.runtimeCode)
    (hpre : m.precompiles.isPrecompile (implementation m.world m.frame.msg.currentTarget) = false)
    (hsel : Abi.selectorOf m.frame.msg.data ∈ poolOnlySelectors)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc : m.frame.msg.caller ≠ pool) (hdepth : m.frame.msg.depth < 1024)
    (hg : 18000 + Gas.copyCost m.frame.msg.data.size + Gas.memoryCost m.frame.msg.data.size ≤
      m.frame.gasLeft)
    (hgu : m.frame.gasLeft < 2 ^ 256) :
    Halts m (fun mf o => (∃ out, o = .revert out) ∧
      ∀ slot, mf.world.sload m.frame.msg.currentTarget slot =
        m.world.sload m.frame.msg.currentTarget slot) :=
  (proxy_poolOnly_noEffect m hf himpl hpre hsel hsize' hc hdepth hg hgu).mono
    fun _ _ _ h => ⟨h.1, fun _ => by rw [h.2.1.1]⟩

end Examples.AaveV3.ATokenProxy
