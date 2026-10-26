import Verified.AaveV3.AToken.Havoc.Proxy

/-!
# Summaries of every dangerous frame, and any transaction

`atoken_covers`: every dangerous frame at a protected account, with any caller (`CoversA`), ends
in a `Good` world — by induction on gas (`coversA_of_lt`): a frame at the implementation runs the
AToken code (`FrameOk`); a frame at the proxy runs the proxy code, which for any caller but the
admin forwards to the AToken code (`proxyOk_of`); a frame at the proxy **called by the admin** (the
PoolConfigurator: `upgradeTo`, `upgradeToAndCall`, …) is the one explicit hypothesis,
`GovernanceKeeps`.

Not yet stated: the top-level theorem (any message call keeps `Good`, so after any transaction
the aEthWETH ledger balances). It needs `FrameOk`, which is proved only for some functions
(`Body/`), and `SlotsOk`'s global hash hypotheses restated per execution (see
`docs/aave-v3.md`).
-/

namespace Verified.AaveV3.AToken.Havoc
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Solidity Verified.AaveV3.Contracts

/-- **Governance keeps the invariant** (the explicit hypothesis): every dangerous frame at the
proxy whose caller is the proxy admin (the PoolConfigurator, governance's executor), with at most
`G` gas, ends in a `Good` world — whenever every dangerous frame with less gas does (its
callbacks). It holds of an admin that only upgrades to the same AToken implementation, or not at
all; it is not provable from the code, since `upgradeTo(newImpl)` may install any code. -/
def GovernanceKeeps (crypto : Crypto) : Prop :=
  ∀ G, (∀ G' < G, CoversA Prot (Good crypto) (Ctx crypto) G') →
    ∀ m, DStartA Prot (Good crypto) (Ctx crypto) G m → m.frame.msg.currentTarget = proxy →
      m.frame.msg.caller = ATokenProxy.admin → Halts m (FailOk (Good crypto))

/-- **The summaries of every dangerous frame, with any caller**, given that the AToken code keeps
`Good` (`FrameOk`) and governance does. -/
theorem atoken_covers {crypto : Crypto} (hK : SlotsOk crypto) (hF : FrameOk)
    (hGov : GovernanceKeeps crypto) (G : Nat) : CoversA Prot (Good crypto) (Ctx crypto) G := by
  refine coversA_of_lt (fun G ih m hd => ?_) G
  have hctx : m.ctx.crypto = crypto := hd.context
  obtain ⟨o, s, hfr⟩ := hd.fresh
  rcases hd.danger.1 with hp | hi
  · by_cases hadm : m.frame.msg.caller = ATokenProxy.admin
    · exact hGov G ih m hd hp hadm
    · have h := (proxyOk_of hF).halts (G := G) (by rw [hctx]; exact hK) (by rw [hctx]; exact ih)
        hfr (by rw [hd.code, hp, hd.world.proxyCode]) (hd.pre)
        hd.gas (by rw [hctx]; exact hd.snapshot) (by rw [hctx]; exact hd.world) hd.danger.2 hp hadm
      rw [hctx] at h; exact h
  · have h := hF.halts (G := G) (by rw [hctx]; exact hK) (by rw [hctx]; exact ih) hfr
      (by rw [hd.code, hi, hd.world.implCode]) hd.pre hd.gas (by rw [hctx]; exact hd.snapshot)
      (by rw [hctx]; exact hd.world) hd.danger.2 (.inr hi)
    rw [hctx] at h; exact h

end Verified.AaveV3.AToken.Havoc
