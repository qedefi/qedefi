import EvmLeanSpecs.Refinement.PermitSpec
import EvmLeanSpecs.Refinement.Events

/-!
# The events of `permit`

`permit` emits `Approval(owner, spender, value)` on success and nothing on failure. The frame
theorems of `permit` (`PermitPost`) already state the success logs, so these companions are
corollaries, in the `EventsPost` form of `Events.lean`:

* `asset_permit_events`, `vault_permit_events` (any frame): `EventsPost m (permitEvents …)`;
* top level: `PermitResult` (`PermitCall.lean`) gives `res.logs = #[approvalLog …]` on success
  and `#[]` on failure (`permit_logs`).
-/

namespace EvmLeanSpecs.Refinement.Permit

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

open Classical in
/-- The logs `permit` emits from the start machine `m`: `Approval(owner, spender, value)` by
the executing token if the permit is valid, none otherwise. -/
noncomputable def permitEvents (ds : Word) (owner spender : Address) (value deadline v r s : Word)
    (m : Machine) : Array Log :=
  if PermitValid m.ctx.crypto ds m.ctx.block.timestamp owner spender value deadline v r s
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto owner)) then
    #[approvalLog m.frame.msg.currentTarget owner spender value]
  else #[]

/-- `PermitPost` gives `EventsPost` for `permitEvents`. -/
theorem eventsPost_of_permitPost {ds : Word} {owner spender : Address}
    {value deadline v r s : Word} {m mf : Machine} {o : Outcome}
    (h : PermitPost ds owner spender value deadline v r s m mf o) :
    EventsPost m (permitEvents ds owner spender value deadline v r s m) mf o := by
  obtain ⟨h1, h2, -⟩ := h
  unfold permitEvents
  split
  · rename_i hv
    obtain ⟨rfl, -, -, -, hl⟩ := h1 hv
    exact eventsPost_success (by rw [hl]; rfl)
  · rename_i hv
    exact eventsPost_revert (h2 hv)

/-- **The events of the asset's `permit`**, in any frame. -/
theorem asset_permit_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    {owner spender : Address} {value deadline v r s : Word}
    (hd : PermitCall m.frame.msg.data owner spender value deadline v r s)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hcase : DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))
    (hg : 100000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit) :
    Halts m (EventsPost m (permitEvents (dsOf ia.initialChainId ia.initialDomainSeparator m) owner
      spender value deadline v r s m)) :=
  (asset_permit_halts m hf hval hstatic hd hsz hcase hg hg' hstd hdel1 hdepth).mono
    fun _ _ _ h => eventsPost_of_permitPost h

/-- **The events of the vault's `permit`**, in any frame. -/
theorem vault_permit_events {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    {owner spender : Address} {value deadline v r s : Word}
    (hd : PermitCall m.frame.msg.data owner spender value deadline v r s)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hcase : DomainCase i.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))
    (hg : 100000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit) :
    Halts m (EventsPost m (permitEvents (dsOf i.initialChainId i.initialDomainSeparator m) owner
      spender value deadline v r s m)) :=
  (vault_permit_halts m hf hval hstatic hd hsz hcase hg hg' hstd hdel1 hdepth).mono
    fun _ _ _ h => eventsPost_of_permitPost h

open Classical in
/-- The logs of a top-level `permit` result. -/
theorem permit_logs {crypto : Crypto} {ds : Word} {timestamp : Nat} {w : World}
    {token owner spender : Address} {value deadline v r s : Word} {res : MessageResult}
    (h : PermitResult crypto ds timestamp w token owner spender value deadline v r s res) :
    res.logs = if PermitValid crypto ds timestamp owner spender value deadline v r s
        (w.sload token (nonceSlot crypto owner)) then #[approvalLog token owner spender value]
      else #[] := by
  split
  · exact (h.1 ‹_›).2.2.2
  · exact (h.2 ‹_›).2.2.2

end EvmLeanSpecs.Refinement.Permit
