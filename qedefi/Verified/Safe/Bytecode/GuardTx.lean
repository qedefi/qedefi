import Verified.Safe.Bytecode.Guard7702
import EvmLogic.Tx.Guard

/-!
# Only a quorum of Safe owners can upgrade: whole transactions, and any sequence of them

`Guard.lean` and `Guard7702.lean` prove the Safe upgrade guard for one top-level message call.
Here it is a theorem about `EvmLean.Tx.process` (`deployed_tx`), and about any sequence of real
transactions (`txs_deployed`), with nothing assumed between them:

* the signers `T` include fewer than `thr` owners, and the owners outside `T` (and from Prague
  the address `1`) are the idle principals: none of them is the transaction's **recovered
  sender**, and none signed one of its EIP-7702 authorizations (signing one is acting);
* the message-level hypotheses are derived (`EvmLogic.Tx.process_split_guard`): the message's
  sender is the recovered sender, not a relay (EIP-3607), a call runs the recipient's own code,
  and a call to an idle account runs no code (it has none);
* the prefix and the suffix keep the deployment (`EvmLogic.Tx.guardWorld_suffixWorld`): relays
  hold real code and are not deleted; idle principals are never created in the transaction (their
  nonce is not zero), so they are not deleted and keep their nonce.

The run-level hashing hypothesis of `impl_kept` (`Rw`: the Safe's nonce and approval writes hit
no protected key, which only a keccak collision can break) becomes one on the machines of the
transaction (`EvmLogic.Tx.TxReaches`). The hashing, chain id and fork are those of the deployment
(`G` reads keccak-derived slots and digests of this chain; the idle principals depend on the
fork), so a sequence of transactions shares them (`TxOk`).
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLean.Tx EvmLogic.Program.Nested
open EvmLogic.Tx Verified.OpenZeppelin.Contracts Verified.OpenZeppelin.Proxy
open Verified.Safe.Contracts

namespace Dep

variable (D : Dep)

/-- **A deployed world**, for hashing `crypto`, chain `chainId` and fork `fork`: the proxy,
ProxyAdmin, the implementation, the `SafeProxy` and the singleton hold their code, the
implementation slot holds `ia`, ProxyAdmin is owned by the Safe, the Safe is configured as
`SafeOk` (singleton `sg`, threshold `thr`, owners within `O`, only the sentinel module, no guard,
no module guard, fallback handler `h₀`, no approval of a digest of this Safe by an owner outside
`T`), and the idle principals (`X fork O T`: the owners outside `T`, from Prague the address `1`)
are externally owned accounts that have sent a transaction (no code, nonce `≠ 0`). -/
structure Deployed (crypto : Crypto) (chainId : Nat) (fork : Fork) (O T : Finset Address)
    (thr : Nat) (h₀ : Word) (w : World) : Prop where
  codePx : w.code D.px = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩
  codePa : w.code D.pa = OzProxyAdmin.runtimeCode
  codeIa : w.code D.ia = ActorImpl.runtimeCode
  codeSf : w.code D.sf = SafeProxy.runtimeCode
  codeSg : w.code D.sg = SafeSingleton.runtimeCode
  impl : w.sload D.px implSlot = Word.ofAddress D.ia
  owner : w.sload D.pa 0 = Word.ofAddress D.sf
  safe : D.SafeOk crypto chainId O T thr h₀ (w.sload D.sf)
  idle : ∀ x, X fork O T x → (w.code x).size = 0 ∧ (w.account x).nonce ≠ 0

section
variable {crypto : Crypto} {chainId : Nat} {fork : Fork} {O T : Finset Address} {thr : Nat}
  {h₀ : Word}

theorem deployed_iff (w : World) :
    D.Deployed crypto chainId fork O T thr h₀ w ↔
      GuardWorld D.Rl D.code (X fork O T) (D.G crypto chainId O T thr h₀) w := by
  constructor
  · intro h
    refine ⟨⟨h.impl, h.owner, h.safe⟩, ?_, h.idle⟩
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · rw [h.codePx, code_px]
    · rw [h.codePa, code_pa]
    · rw [h.codeIa, code_ia]
    · rw [h.codeSf, code_sf]
    · rw [h.codeSg, code_sg]
  · rintro ⟨⟨hi, ho, hs⟩, hrc, hx⟩
    exact ⟨(hrc _ (.inl rfl)).trans D.code_px, (hrc _ (.inr (.inl rfl))).trans D.code_pa,
      (hrc _ (.inr (.inr (.inl rfl)))).trans D.code_ia,
      (hrc _ (.inr (.inr (.inr (.inl rfl))))).trans D.code_sf,
      (hrc _ (.inr (.inr (.inr (.inr rfl))))).trans D.code_sg, hi, ho, hs, hx⟩

end

/-- **A transaction signed by fewer than `thr` owners keeps the deployment.** From a world
deployed for `crypto`, the chain of `env` and `fork`, where the signers `T` (`Signers`: every
owner that `ecrecover` recovers from a digest of this Safe on this chain is in `T`) include fewer
than `thr` owners and the fallback handler `h₀` is unset or not a relay: every successful
transaction (any type, recipient, calldata, value, gas, fees and authorizations) that no idle
principal sends (`hsender`) and none of whose EIP-7702 authorizations an idle principal signed
(`hauth`) ends in a deployed world — the same implementation, the same owner of ProxyAdmin, the
same Safe configuration. Assumed of hashing: the Safe's nonce and approval writes during the
transaction hit no protected key (`hR`, `Rw` on the transaction's machines). -/
theorem deployed_tx {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {w : World} {tx : Transaction} {hint : Option Address}
    {out : TxOutput} {O T : Finset Address} {thr : Nat} {h₀ : Word}
    (hw : D.Deployed crypto env.chainId fork O T thr h₀ w)
    (hthr : thr < 2 ^ 256) (hcard : (O ∩ T).card < thr)
    (hsig : Signers crypto env.chainId D.sf O T) (hh : h₀ = 0 ∨ ¬ D.Rl (Word.toAddress h₀))
    (hsender : ¬ X fork O T out.sender)
    (hauth : ∀ auth ∈ tx.authorizations, ∀ a, recoverAuthority crypto auth = some a →
      ¬ X fork O T a)
    (hR : ∀ m, TxReaches crypto fork env gasAvail blobAvail w tx hint m →
      D.Rw crypto env.chainId O T m)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    D.Deployed crypto env.chainId fork O T thr h₀ out.world :=
  (D.deployed_iff _).2 (process_guardWorld (codeOk D) D.G_keep
    (fun _ _ _ _ hw₁ htm htop hauth' hca hreach hr =>
      D.guard_world_7702 htm.ctxCrypto (by rw [htm.ctxBlock]) htm.ctxFork hw₁ hthr hcard hsig hh
        hauth' hca htop (fun m hm => hR m (hreach m hm)) hr)
    ((D.deployed_iff w).1 hw) ⟨hsender, hauth⟩ h)

/-- **Only a quorum of the Safe's owners can upgrade, for every transaction**: under the
hypotheses of `deployed_tx`, the implementation slot, ProxyAdmin's owner and the Safe's
configuration are unchanged by the transaction. -/
theorem impl_kept_tx {fuel : Nat} {crypto : Crypto} {fork : Fork} {env : BlockEnv}
    {gasAvail blobAvail : Nat} {w : World} {tx : Transaction} {hint : Option Address}
    {out : TxOutput} {O T : Finset Address} {thr : Nat} {h₀ : Word}
    (hw : D.Deployed crypto env.chainId fork O T thr h₀ w)
    (hthr : thr < 2 ^ 256) (hcard : (O ∩ T).card < thr)
    (hsig : Signers crypto env.chainId D.sf O T) (hh : h₀ = 0 ∨ ¬ D.Rl (Word.toAddress h₀))
    (hsender : ¬ X fork O T out.sender)
    (hauth : ∀ auth ∈ tx.authorizations, ∀ a, recoverAuthority crypto auth = some a →
      ¬ X fork O T a)
    (hR : ∀ m, TxReaches crypto fork env gasAvail blobAvail w tx hint m →
      D.Rw crypto env.chainId O T m)
    (h : process fuel crypto fork env gasAvail blobAvail w tx hint = .ok out) :
    D.G crypto env.chainId O T thr h₀ out.world :=
  ((D.deployed_iff _).1 (D.deployed_tx hw hthr hcard hsig hh hsender hauth hR h)).1

/-- **The transactions admitted along a sequence**: they hash with `crypto`, run on chain
`chainId` at fork `fork`, no idle principal (`X fork O T`) sends one or signed one of its
EIP-7702 authorizations, and the Safe's nonce and approval writes in them hit no protected key
(`Rw` on the transaction's machines). -/
structure TxOk (crypto : Crypto) (chainId : Nat) (fork : Fork) (O T : Finset Address)
    (i : Input) (w : World) (out : TxOutput) : Prop where
  hashing : i.crypto = crypto
  chain : i.env.chainId = chainId
  onFork : i.fork = fork
  sender : ¬ X fork O T out.sender
  auth : ∀ auth ∈ i.tx.authorizations, ∀ a, recoverAuthority crypto auth = some a →
    ¬ X fork O T a
  hash : ∀ m, TxReaches i.crypto i.fork i.env i.gasAvail i.blobAvail w i.tx i.hint m →
    D.Rw crypto chainId O T m

/-- **Only a quorum of the Safe's owners can upgrade, along any sequence of transactions.**
From a deployed world, where the signers `T` include fewer than `thr` owners, after any number of
successful transactions in which no idle principal acts (none sends one, none signed one of their
authorizations), the world is still deployed: the same implementation, the same owner of
ProxyAdmin, the same Safe configuration. Nothing is assumed between transactions. -/
theorem txs_deployed {crypto : Crypto} {chainId : Nat} {fork : Fork} {O T : Finset Address}
    {thr : Nat} {h₀ : Word} (hthr : thr < 2 ^ 256) (hcard : (O ∩ T).card < thr)
    (hsig : Signers crypto chainId D.sf O T) (hh : h₀ = 0 ∨ ¬ D.Rl (Word.toAddress h₀))
    {w₀ w : World} (h₀' : D.Deployed crypto chainId fork O T thr h₀ w₀)
    (h : TxSteps (D.TxOk crypto chainId fork O T) w₀ w) :
    D.Deployed crypto chainId fork O T thr h₀ w := by
  refine h.keeps (fun i v out hv hr hok => ?_) h₀'
  obtain ⟨fuel, cr, fk, env, ga, ba, tx, hint⟩ := i
  obtain ⟨hcr, hch, hfk, hs, ha, hR⟩ := hok
  dsimp only at hcr hch hfk hR hr ha
  subst hcr hch hfk
  exact D.deployed_tx hv hthr hcard hsig hh hs ha hR hr

/-- The protected state along any sequence of transactions in which no idle principal acts. -/
theorem txs_impl_kept {crypto : Crypto} {chainId : Nat} {fork : Fork} {O T : Finset Address}
    {thr : Nat} {h₀ : Word} (hthr : thr < 2 ^ 256) (hcard : (O ∩ T).card < thr)
    (hsig : Signers crypto chainId D.sf O T) (hh : h₀ = 0 ∨ ¬ D.Rl (Word.toAddress h₀))
    {w₀ w : World} (h₀' : D.Deployed crypto chainId fork O T thr h₀ w₀)
    (h : TxSteps (D.TxOk crypto chainId fork O T) w₀ w) :
    w.sload D.px implSlot = Word.ofAddress D.ia ∧ w.sload D.pa 0 = Word.ofAddress D.sf ∧
      D.SafeOk crypto chainId O T thr h₀ (w.sload D.sf) :=
  have hd := D.txs_deployed hthr hcard hsig hh h₀' h
  ⟨hd.impl, hd.owner, hd.safe⟩

end Dep

end Verified.Safe.Guard
