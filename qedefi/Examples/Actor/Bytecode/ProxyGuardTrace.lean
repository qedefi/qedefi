import Examples.Actor.Bytecode.ProxyGuard
import EvmLogic.Program.Nested.GuardTrace
import QEDefi.Trace.Lift

/-!
# Only the owner can upgrade, along any sequence of transactions

`ProxyGuard.lean` proves the upgrade guard for one top-level message call (`Dep.impl_kept`). Here
it is lifted to traces, the way the ERC-4626 bytecode results are stated
(`Examples.Solmate.ERC4626.Invariants.System`, `QEDefi.Trace.Lift`): top-level message calls
(`CallStep`, any sender, any calldata and value, success or revert) interleaved with environment
steps (`EnvStep`) that leave the deployment's code and storage alone and do not make the owner
active (no code for it, its nonce does not decrease). A transaction's own nonce increment and fee
payment are environment steps (`EnvStep.of_balances_nonces`).

- `trace_impl_kept`: along every trace whose transactions are not sent by the owner, the
  implementation slot and ProxyAdmin's owner never change, and the deployment stays deployed.
- `trace_impl_until_owner`: along any trace, the owner's first transaction starts from a world
  where the implementation and the owner are still the original ones.

The per-call step is `processMessageCall_guard_world`: a guarded call keeps the world invariant,
the relays' code and the owner's idleness, so the next call's hypotheses hold again. In the terms
of `QEDefi.Trace.Lift`, the trace refines the model whose state is the pair (implementation,
owner) and in which every non-owner transaction is the identity.
-/

namespace Examples.Actor.ProxyGuard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open EvmLogic.AbsInt Examples.OpenZeppelin.Contracts QEDefi.Trace.Lift

namespace Dep

variable (D : Dep)

/-! ## Deployments and transitions -/

/-- **A deployed world**: the three contracts hold their code, the implementation slot holds
`ia`, ProxyAdmin is owned by `o`, and `o` is an externally owned account that has sent a
transaction (no code, nonce `≠ 0`). -/
structure Deployed (w : World) : Prop where
  codePx : w.code D.px = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩
  codePa : w.code D.pa = OzProxyAdmin.runtimeCode
  codeIa : w.code D.ia = ActorImpl.runtimeCode
  impl : w.sload D.px implSlot = Word.ofAddress D.ia
  owner : w.sload D.pa 0 = Word.ofAddress D.o
  ownerCode : (w.code D.o).size = 0
  ownerNonce : (w.account D.o).nonce ≠ 0

/-- **A transaction**: a terminated top-level message call `msg` (any sender, calldata and value;
success or revert), before Prague or without EIP-7702 authorizations, whose sender is none of the
three contracts (EIP-3607), and which runs the code of the account it calls. -/
def CallStep (w : World) (msg : Message) (w' : World) : Prop :=
  ∃ (ctx : Context) (tr : TransientStorage) (fuel : Nat) (r : MessageResult),
    (ctx.fork < .prague ∨ ctx.tx.authorizations = []) ∧ TopOk D.Rl w msg ∧
    (msg.currentTarget = D.o → msg.target = some D.o → msg.code.size = 0) ∧
    processMessageCall fuel ctx w tr msg = .ok r ∧ r.world = w'

/-- **An environment step**: the three contracts' code and storage are unchanged; the owner
gets no code and its nonce does not decrease (it signs no EIP-7702 authorization). Anything
else may change. -/
def EnvStep (w w' : World) : Prop :=
  KeepP D.Rl w w' ∧ w'.code D.o = w.code D.o ∧ (w.account D.o).nonce ≤ (w'.account D.o).nonce

/-- A step that changes only balances and nonces, with nonces not decreasing (a transaction's
nonce increment and fee payment), is an environment step. -/
theorem EnvStep.of_balances_nonces {w w' : World}
    (hs : ∀ a, (w'.account a).storage = (w.account a).storage)
    (hc : ∀ a, (w'.account a).code = (w.account a).code) (hn : NonceLe w w') :
    D.EnvStep w w' :=
  ⟨fun p _ => ⟨hs p, hc p⟩, hc D.o, hn D.o⟩

/-- **The trace system**: worlds, transactions labelled by their message, environment steps.
Its model state is the pair (implementation slot, ProxyAdmin's owner slot), and a transaction
not sent by the owner (`Ok`) is the identity on it. -/
def system : System World (Word × Word) Message where
  step s _ := some s
  abs w := (w.sload D.px implSlot, w.sload D.pa 0)
  call := D.CallStep
  env := D.EnvStep
  Pre w := RelayCode D.Rl D.code w ∧ IdleW D.X w
  Inv s := s = (Word.ofAddress D.ia, Word.ofAddress D.o)
  Agree := Eq
  Ok msg := msg.caller ≠ D.o

/-- **Traces**: `D.Reach w txs w'` when `w'` is reached from `w` by the transactions `txs` in
order, interleaved with any number of environment steps. -/
abbrev Reach : World → List Message → World → Prop := D.system.Reach

/-! ## The refinement -/

theorem guardWorld_iff (w : World) :
    GuardWorld D.Rl D.code D.X D.G w ↔
      D.system.Pre w ∧ D.system.Inv (D.system.abs w) := by
  simp only [GuardWorld, system, G, Prod.mk.injEq]
  exact ⟨fun ⟨h, hr, hx⟩ => ⟨⟨hr, hx⟩, h⟩, fun ⟨⟨hr, hx⟩, h⟩ => ⟨h, hr, hx⟩⟩

theorem deployed_iff (w : World) : D.Deployed w ↔ GuardWorld D.Rl D.code D.X D.G w := by
  constructor
  · intro h
    refine ⟨⟨h.impl, h.owner⟩, ?_, fun x hx => hx ▸ ⟨h.ownerCode, h.ownerNonce⟩⟩
    rintro r (rfl | rfl | rfl)
    · rw [h.codePx, code_px]
    · rw [h.codePa, code_pa]
    · rw [h.codeIa, code_ia]
  · rintro ⟨⟨hi, ho⟩, hrc, hx⟩
    exact ⟨(hrc _ (.inl rfl)).trans D.code_px, (hrc _ (.inr (.inl rfl))).trans D.code_pa,
      (hrc _ (.inr (.inr rfl))).trans D.code_ia, hi, ho, (hx _ rfl).1, (hx _ rfl).2⟩

/-- **One transaction not sent by the owner** keeps the deployment and the protected state:
`processMessageCall_guard_world` with the frame invariants of `ProxyGuard.lean`. -/
theorem callStep_guard {w w' : World} {msg : Message} (hw : GuardWorld D.Rl D.code D.X D.G w)
    (hs : msg.caller ≠ D.o) (hc : D.CallStep w msg w') : GuardWorld D.Rl D.code D.X D.G w' := by
  obtain ⟨ctx, tr, fuel, r, hdeleg, htop, hto, hr, rfl⟩ := hc
  exact processMessageCall_guard_world (codeOk D) D.G_keep D.inv hw hdeleg
    ⟨htop, hs, fun hx ht => hto hx (hx ▸ ht)⟩ hr

theorem envStep_pre {w w' : World} (hp : D.system.Pre w) (he : D.EnvStep w w') :
    D.system.Pre w' ∧ D.system.abs w' = D.system.abs w := by
  obtain ⟨hk, hco, hn⟩ := he
  refine ⟨⟨fun r hr => (hk r hr).2.trans (hp.1 r hr), fun x hx => ?_⟩, ?_⟩
  · subst hx
    exact ⟨by rw [hco]; exact (hp.2 _ rfl).1, fun h0 => (hp.2 _ rfl).2 (by omega)⟩
  · show (_, _) = (_, _)
    rw [(hk _ (.inl rfl)).sload' implSlot, (hk _ (.inr (.inl rfl))).sload' 0]

/-- **The trace system refines the model**: every non-owner transaction is the identity on
(implementation, owner), and environment steps do not change them. -/
theorem refinement : D.system.Refinement where
  agree := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  inv_agree _ _ h hi := h ▸ hi
  inv_step _ _ _ hi h := Option.some.inj h ▸ hi
  step_agree _ _ _ _ _ h := h ▸ rfl
  call w msg w' hp hi hs hc := by
    have hw := D.callStep_guard ((D.guardWorld_iff w).2 ⟨hp, hi⟩) hs hc
    obtain ⟨hp', hi'⟩ := (D.guardWorld_iff w').1 hw
    exact ⟨hp', show D.system.abs w' = D.system.abs w from hi'.trans hi.symm⟩
  env _ _ hp he := D.envStep_pre hp he

/-! ## The theorems -/

theorem mem_takeWhile_imp {p : Message → Bool} :
    ∀ {l : List Message} {x : Message}, x ∈ l.takeWhile p → p x = true
  | [], _, h => by simp at h
  | a :: l, x, h => by
    simp only [List.takeWhile_cons] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · assumption
      · exact mem_takeWhile_imp h
    · simp at h

/-- **Only the owner can upgrade, along any trace.** From a deployed world, along any sequence
of transactions none of which is sent by the owner (with any environment steps between them),
the implementation slot still holds `ia`, ProxyAdmin is still owned by `o`, and the world is
still deployed. -/
theorem trace_impl_kept {w₀ w : World} {txs : List Message} (h₀ : D.Deployed w₀)
    (hr : D.Reach w₀ txs w) (hs : ∀ msg ∈ txs, msg.caller ≠ D.o) :
    w.sload D.px implSlot = Word.ofAddress D.ia ∧ w.sload D.pa 0 = Word.ofAddress D.o ∧
      D.Deployed w := by
  obtain ⟨hp, hi⟩ := (D.guardWorld_iff w₀).1 ((D.deployed_iff w₀).1 h₀)
  obtain ⟨hp', hi', -⟩ := D.refinement.lift hr hs hp hi
  have hw := (D.deployed_iff w).2 ((D.guardWorld_iff w).2 ⟨hp', hi'⟩)
  exact ⟨hw.impl, hw.owner, hw⟩

/-- **Until the owner acts.** Along any trace from a deployed world, the owner's first
transaction `tx` (every earlier one, `pre`, is sent by someone else) starts from a world `v`
where the implementation slot still holds `ia` and ProxyAdmin is still owned by `o`. -/
theorem trace_impl_until_owner {w₀ w : World} {pre post : List Message} {tx : Message}
    (h₀ : D.Deployed w₀) (hr : D.Reach w₀ (pre ++ tx :: post) w)
    (hpre : ∀ msg ∈ pre, msg.caller ≠ D.o) :
    ∃ v v', D.Reach w₀ pre v ∧ D.CallStep v tx v' ∧ D.Reach v' post w ∧
      v.sload D.px implSlot = Word.ofAddress D.ia ∧ v.sload D.pa 0 = Word.ofAddress D.o := by
  obtain ⟨u, h₁, h₂⟩ := System.Reach.split hr
  obtain ⟨u', h₃, h₄⟩ := System.Reach.split (ops₁ := [tx]) h₂
  obtain ⟨v, v', hv, hc, hv'⟩ := System.Reach.single_inv h₃
  have hpv : D.Reach w₀ pre v := by simpa using h₁.trans hv
  obtain ⟨hi, ho, -⟩ := D.trace_impl_kept h₀ hpv hpre
  exact ⟨v, v', hpv, hc, by simpa using hv'.trans h₄, hi, ho⟩

/-- The same, read off any trace: up to the first transaction sent by the owner (the longest
prefix of transactions not sent by it), the implementation and the owner are unchanged. -/
theorem trace_impl_until_first_owner {w₀ w : World} {txs : List Message}
    (h₀ : D.Deployed w₀) (hr : D.Reach w₀ txs w) :
    ∃ v, D.Reach w₀ (txs.takeWhile (·.caller ≠ D.o)) v ∧
      D.Reach v (txs.dropWhile (·.caller ≠ D.o)) w ∧
      v.sload D.px implSlot = Word.ofAddress D.ia ∧ v.sload D.pa 0 = Word.ofAddress D.o := by
  rw [← List.takeWhile_append_dropWhile (p := (·.caller ≠ D.o)) (l := txs)] at hr
  obtain ⟨v, h₁, h₂⟩ := System.Reach.split hr
  have hs : ∀ msg ∈ txs.takeWhile (·.caller ≠ D.o), msg.caller ≠ D.o := fun msg hm => by
    simpa using mem_takeWhile_imp hm
  obtain ⟨hi, ho, -⟩ := D.trace_impl_kept h₀ h₁ hs
  exact ⟨v, h₁, h₂, hi, ho⟩

end Dep

/-! ## The hypotheses are satisfiable -/

namespace Example

theorem world_deployed : dep.Deployed world := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := world_ok
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- **The theorem on this world**: no sequence of transactions from anyone but the owner
upgrades. -/
theorem world_trace_impl_kept {w : World} {txs : List Message} (hr : dep.Reach world txs w)
    (hs : ∀ msg ∈ txs, msg.caller ≠ dep.o) : w.sload dep.px implSlot = Word.ofAddress dep.ia :=
  (dep.trace_impl_kept world_deployed hr hs).1

end Example

end Examples.Actor.ProxyGuard
