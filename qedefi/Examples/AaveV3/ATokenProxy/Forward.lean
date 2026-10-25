import Examples.AaveV3.ATokenProxy.Delegate

/-!
# Aave V3 aToken proxy: EIP-1967 forwarding

`forward_halts`: a fresh frame running the proxy, called by anyone but the admin with calldata
that selects none of the proxy's functions (or is shorter than a selector), goes through the
dispatcher, `_willFallback`'s admin check and the `SLOAD` of the implementation slot to the
delegation block (`delegate_halts`), so it ends `Forwarded` after the implementation's frame.
It is the proxy half of every statement about a call to an aToken address: compose it with a
`Fresh AToken.runtimeCode` summary of the implementation (`Guard.lean`).
-/

namespace Examples.AaveV3.ATokenProxy
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Examples.AaveV3.Contracts

set_option hygiene false in
/-- From the dispatcher's end at the delegation block (pc 1129) to the postcondition of
`forward_halts`, by `delegate_halts`. -/
local macro "to_delegate" : tactic => `(tactic| (
  apply WP.halts
  refine Halts.mono (delegate_halts _ (B := B) (G := G) (Hc := Hc) (by rfl) (by exact hj)
    (by rfl) (by rfl) (by simp) (by rfl) (by exact hsize) (by exact hdel) (by exact hpre)
    (by exact hdepth) ?_ ?_ hB ?_) ?_
  · evm_gas_bounds; dsimp only; omega
  · dsimp only; omega
  · intro mc hfr hdf hG
    exact hchild mc hfr (hdf.of_eq rfl rfl rfl rfl rfl rfl rfl) hG
  · rintro mf o - ⟨mc, mcf, oc, hdf, hcc, hfw⟩
    refine ⟨mc, mcf, oc, hdf.of_eq rfl rfl rfl rfl rfl rfl rfl, hcc,
      hfw.of_le (d := 3000) rfl rfl rfl ?_ (by dsimp only; omega)⟩
    evm_gas_bounds; dsimp only; omega))

set_option maxHeartbeats 0 in
/-- **EIP-1967 forwarding.** A fresh frame running the aToken proxy, called by anyone but the
admin with calldata that selects none of the proxy's own functions, delegates to the
implementation in its EIP-1967 slot (`implementation`), passing the calldata, and ends as
`Forwarded` says: the implementation's output and effects after success, its revert data and no
effect after a revert, an empty revert after an exceptional halt. Hypotheses: the
implementation's frame `Halts` with `Hc` whenever it starts with at least `G` gas (`hchild`),
its output has at most `B` bytes (`hB`), the proxy has enough gas (`hg`), and the call can be
made (no EIP-7702 delegation, not a precompile, depth below 1024). -/
theorem forward_halts (m : Machine) (hf : Fresh ATokenProxy.runtimeCode m) {B G : Nat}
    {Hc : Machine → Machine → Outcome → Prop}
    (hsel : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ proxySelectors)
    (hc : m.frame.msg.caller ≠ admin) (hsize : m.frame.msg.data.size < 2 ^ 64)
    (hdel : m.ctx.fork < .prague ∨
      delegatedAddress? (m.world.code (implementation m.world m.frame.msg.currentTarget)) = none)
    (hpre : m.precompiles.isPrecompile (implementation m.world m.frame.msg.currentTarget) = false)
    (hdepth : m.frame.msg.depth < 1024)
    (hg : 2 * G + 64 * (Gas.copyCost B + Gas.memoryCost B) + Gas.copyCost m.frame.msg.data.size +
      Gas.memoryCost m.frame.msg.data.size + 11000 ≤ m.frame.gasLeft)
    (hgu : m.frame.gasLeft < 2 ^ 256)
    (hB : ∀ mc mcf oc, Hc mc mcf oc → (outputOf oc).size ≤ B)
    (hchild : ∀ mc, Fresh (m.world.code (implementation m.world m.frame.msg.currentTarget)) mc →
      DelegatedFrom m mc → G ≤ mc.frame.gasLeft → Halts mc (Hc mc)) :
    Halts m (fun mf o => ∃ mc mcf oc, DelegatedFrom m mc ∧ Hc mc mcf oc ∧
      Forwarded m (6000 + Gas.copyCost m.frame.msg.data.size +
        Gas.memoryCost m.frame.msg.data.size + Gas.copyCost B + Gas.memoryCost B)
        mc mcf oc mf o) := by
  have hc' := adminWord_eq_caller hc
  apply WP.halts_of_false
  by_cases h4 : m.frame.msg.data.size < 4
  · have hlt := lt_size_four_one h4
    fresh_intro
    pwp_steps [hlt, hc', iszero_zero]
    to_delegate
  · have hlt := Examples.Solmate.ERC20.lt_size_four (n := m.frame.msg.data.size) (by omega)
      (by omega)
    obtain ⟨e1, e2, e3, e4, e5⟩ := dispatch_facts (hsel.resolve_left h4)
    by_cases hgt : Abi.selectorOf m.frame.msg.data < 0x5c60da1b
    · have hg' := gt_selector_lt hgt
      fresh_intro
      pwp_steps [hlt, Abi.shr_calldataload_zero, hg', e1, e2, e3, e4, e5, hc', iszero_zero]
      to_delegate
    · have hg' := gt_selector_ge hgt
      fresh_intro
      pwp_steps [hlt, Abi.shr_calldataload_zero, hg', e1, e2, e3, e4, e5, hc', iszero_zero]
      to_delegate

end Examples.AaveV3.ATokenProxy
