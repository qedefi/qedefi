import Verified.AaveV3.AToken.Havoc.Frame

/-!
# The proxy, for any caller but its admin

The aEthWETH proxy (`InitializableImmutableAdminUpgradeabilityProxy`) for a caller that is not
the admin: its own functions (`admin()`, `implementation()`, `upgradeTo`, `upgradeToAndCall`)
fall back (`ifAdmin`), `initialize(address,bytes)` reverts (the implementation slot is set), and
everything else reaches `_delegate`: `DELEGATECALL` into the implementation, which `Good` pins to
the AToken code. `pwp_delegatecall` takes the call for any gas and any outcome, with the
implementation's frame summarised by `FrameOk` (`delegate_child_halts`); the proxy then returns
or reverts with the returned data (`RETURNDATACOPY`'s memory left unknown). No output-size bound is
needed: a copy that runs out of gas just ends the frame, which `FailOk` allows.
-/

namespace Verified.AaveV3.AToken.Havoc
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Solidity Verified.AaveV3.Contracts

theorem toAddress_implWord :
    Word.toAddress 992034533817904973746697726720069568450736519898#256 = impl := by decide

theorem implWord_eq : Word.ofAddress impl = 992034533817904973746697726720069568450736519898#256 := by
  decide

set_option hygiene false in
/-- The handler of `apwp_run` for the proxy: its `DELEGATECALL`, and the end of the frame. -/
macro "proxy_handle" : tactic => `(tactic| first
  | (refine pwp_stop (by code_fact) rfl ?_)
  | (refine pwp_return ‹_› (by code_fact) rfl rfl ?_)
  | (refine pwp_delegatecall (Gc := Good ctx.crypto) ?_ ?_ rfl rfl ?_ ?_ (wp_of_resume ?_)
     on_goal 1 => assumption
     on_goal 1 => code_fact
     on_goal 2 =>
       exact fun mc hd =>
         delegate_child_halts hF hK hcov ‹_› hd toAddress_implWord ‹_› hst
           (by rw [ht]; exact .inl rfl) rfl
     on_goal 2 => (intro _ _ _ _ _ _ _ _ _ _; apwp_cont [mask_and_eq, and_mask_eq,
       Word.toAddress_ofAddress, EvmLogic.Solidity.eq_self, addressMask_and_ofAddress])))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- **The proxy keeps `Good` for any caller but its admin**, given that the AToken code does. -/
theorem proxyOk_of (hF : FrameOk) : ProxyOk := by
  intro G ctx w tr ow created msg jd g sub snap ko ks parents hK hcov hg hsnap hw hst ht hadm
  have hadmw := ATokenProxy.adminWord_eq_caller hadm
  have himpl : w.sload msg.currentTarget
      24440054405305269366569402256811496959409073762505157381672968839269610695612#256 =
      992034533817904973746697726720069568450736519898#256 := by
    rw [ht, ← implWord_eq]; exact hw.implSlot
  apwp_run [mask_and_eq, and_mask_eq, Word.toAddress_ofAddress, EvmLogic.Solidity.eq_self,
    addressMask_and_ofAddress, himpl, hadmw] using proxy_handle
  all_goals with_reducible assumption

end Verified.AaveV3.AToken.Havoc
