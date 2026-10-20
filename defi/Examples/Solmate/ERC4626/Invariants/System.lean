import Defi.ERC4626.Agree
import Examples.Solmate.ERC20.Spec
import Examples.Solmate.ERC4626.ViewsSpec
import Examples.Solmate.ERC20.Approve
import Examples.Solmate.ERC20.MintBurn

/-!
# The concrete system: deployed vault and asset under arbitrary call sequences

The precise statement of *which* concrete executions the invariant theorems are about.

## States

Worlds `w : World` with `Deployed w vault asset`: the compiled Solmate `MockERC4626` at
`vault` (any immutables whose `asset` is `asset`) and the compiled `MockERC20` at `asset`
(`Abstraction.lean`). The abstraction is `abs crypto w vault asset`, for one fixed `crypto`
(the hash function of the chain).

## Transitions

* **Modelled calls** (`CallStep`): a top-level message call (`processMessageCall`, i.e. the
  message part of a transaction) from an **arbitrary caller** (other than the vault and the
  asset themselves, which have code and so cannot send transactions, EIP-3607) to the vault
  or to the asset,
  with zero value, calldata `VCall.data c` encoding one of the modelled state-changing
  functions with arbitrary arguments (`VCall`, mirroring `Solmate.Op`: the four ERC-4626
  entry points, the vault's `transfer`/`transferFrom`/`approve`, and the asset's
  `transfer`/`transferFrom`/`approve`/`mint`/`burn` — `asset.transfer(vault, D)` is a
  donation), at least `minGas` and fewer than `2⁶⁴` gas, in any context of `crypto` that is
  before Prague or has no EIP-7702 authorizations, and that **terminates**: for all large
  enough fuel `processMessageCall` returns the same result (`Terminates`). Successful and
  reverting calls are both included; the next world is the result's world.
* **Environment steps** (`EnvStep`): any transition that changes neither the storage nor the
  code of the vault and the asset: transactions to other contracts that do not reach them,
  ETH transfers (also to the vault or the asset: the model has no ETH), the transaction-level
  bookkeeping around a message call (nonce, gas purchase and refund, coinbase fee), block
  rewards, and **view calls** to the vault or the asset (`envStep_of_world_eq`; the view
  refinement theorems `*_call` of `VaultViewsSpec.lean` say they return the model's values
  and keep the world).

## Hash hypotheses, once per trace

`SlotsOk crypto vault Act` for a finite list `Act` of actors containing the vault and every
address appearing in the trace's calls (`VCall.actors`): each actor's balance slot and each
actor-pair's allowance slot is fresh among the single-level address-keyed preimages
(`Erc20.BalanceSlotOk`, `Erc20.AllowanceSlotOk`: one target against `2¹⁶¹` candidates,
plausible), the allowance slots of distinct actor pairs differ, and none of these slots is one
of the hook-counter slots 6 and 7. This is a statement about finitely many hashes.

The concrete world is then related to the model up to the allowances of non-actor pairs
(`AgreeOn (ActorPairs Act)`): an allowance entry `allowance[o][sp]` with `o ∉ Act` might, by a
collision no plausible hypothesis excludes, share a slot with a written balance.

## The system

`system crypto vault asset minGas Act K : Lift.System World (State Address) VCall`, where `K`
selects the call kinds admitted (`fun _ => True` for all of them; `VCall.Proven` for those
whose bytecode refinement is on `main` today). `refinement` builds its
`Lift.System.Refinement` from one `OpRefinesAt` theorem per admitted call.
-/

section

namespace EvmLeanSpecs.Refinement.Invariants

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift

/-! ## Calls -/

/-- A modelled state-changing call, with its ABI arguments. -/
inductive VCall where
  /-- `vault.deposit(assets, receiver)` from `caller`. -/
  | deposit (caller : Address) (assets : Word) (receiver : Address)
  /-- `vault.mint(shares, receiver)` from `caller`. -/
  | mint (caller : Address) (shares : Word) (receiver : Address)
  /-- `vault.withdraw(assets, receiver, owner)` from `caller`. -/
  | withdraw (caller : Address) (assets : Word) (receiver owner : Address)
  /-- `vault.redeem(shares, receiver, owner)` from `caller`. -/
  | redeem (caller : Address) (shares : Word) (receiver owner : Address)
  /-- `vault.transfer(dst, amount)` from `caller`. -/
  | transfer (caller dst : Address) (amount : Word)
  /-- `vault.transferFrom(src, dst, amount)` from `caller`. -/
  | transferFrom (caller src dst : Address) (amount : Word)
  /-- `vault.approve(spender, amount)` from `caller`. -/
  | approve (caller spender : Address) (amount : Word)
  /-- `asset.transfer(dst, amount)` from `caller` (a donation when `dst` is the vault). -/
  | assetTransfer (caller dst : Address) (amount : Word)
  /-- `asset.transferFrom(src, dst, amount)` from `caller`. -/
  | assetTransferFrom (caller src dst : Address) (amount : Word)
  /-- `asset.approve(spender, amount)` from `caller`. -/
  | assetApprove (caller spender : Address) (amount : Word)
  /-- `asset.mint(dst, amount)` from `caller` (`MockERC20.mint` is unrestricted). -/
  | assetMint (caller dst : Address) (amount : Word)
  /-- `asset.burn(src, amount)` from `caller` (`MockERC20.burn` is unrestricted). -/
  | assetBurn (caller src : Address) (amount : Word)

namespace VCall

/-- The caller. -/
def caller : VCall → Address
  | .deposit c _ _ | .mint c _ _ | .withdraw c _ _ _ | .redeem c _ _ _ | .transfer c _ _
  | .transferFrom c _ _ _ | .approve c _ _ | .assetTransfer c _ _ | .assetTransferFrom c _ _ _
  | .assetApprove c _ _ | .assetMint c _ _ | .assetBurn c _ _ => c

/-- Whether the call goes to the asset (otherwise to the vault). -/
def onAsset : VCall → Bool
  | .deposit .. | .mint .. | .withdraw .. | .redeem .. | .transfer .. | .transferFrom ..
  | .approve .. => false
  | .assetTransfer .. | .assetTransferFrom .. | .assetApprove .. | .assetMint ..
  | .assetBurn .. => true

/-- The called account. -/
def target (c : VCall) (vault asset : Address) : Address := if c.onAsset then asset else vault

/-- The ABI calldata (selectors from `SolmateVault.selectors` / `SolmateAsset.selectors`). -/
def data : VCall → ByteArray
  | .deposit _ a r => Abi.encodeCall 0x6e553f65 [a, Word.ofAddress r]
  | .mint _ n r => Abi.encodeCall 0x94bf804d [n, Word.ofAddress r]
  | .withdraw _ a r o => Abi.encodeCall 0xb460af94 [a, Word.ofAddress r, Word.ofAddress o]
  | .redeem _ n r o => Abi.encodeCall 0xba087652 [n, Word.ofAddress r, Word.ofAddress o]
  | .transfer _ d v => Shares.transferData d v
  | .transferFrom _ s d v => Shares.transferFromData s d v
  | .approve _ sp v => Shares.approveData sp v
  | .assetTransfer _ d v => Shares.transferData d v
  | .assetTransferFrom _ s d v => Shares.transferFromData s d v
  | .assetApprove _ sp v => Shares.approveData sp v
  | .assetMint _ d v => Abi.encodeCall 0x40c10f19 [Word.ofAddress d, v]
  | .assetBurn _ s v => Abi.encodeCall 0x9dc29fac [Word.ofAddress s, v]

/-- The model operation the call implements (ABI words as naturals). -/
def op : VCall → Op Address
  | .deposit c a r => .deposit c a.toNat r
  | .mint c n r => .mint c n.toNat r
  | .withdraw c a r o => .withdraw c a.toNat r o
  | .redeem c n r o => .redeem c n.toNat r o
  | .transfer c d v => .transfer c d v.toNat
  | .transferFrom c s d v => .transferFrom c s d v.toNat
  | .approve c sp v => .approve c sp v.toNat
  | .assetTransfer c d v => .assetTransfer c d v.toNat
  | .assetTransferFrom c s d v => .assetTransferFrom c s d v.toNat
  | .assetApprove c sp v => .assetApprove c sp v.toNat
  | .assetMint _ d v => .assetMint d v.toNat
  | .assetBurn _ s v => .assetBurn s v.toNat

/-- Every address the call mentions. -/
def actors : VCall → List Address
  | .deposit c _ r | .mint c _ r => [c, r]
  | .withdraw c _ r o | .redeem c _ r o => [c, r, o]
  | .transfer c d _ | .approve c d _ | .assetTransfer c d _ | .assetApprove c d _
  | .assetMint c d _ | .assetBurn c d _ => [c, d]
  | .transferFrom c s d _ | .assetTransferFrom c s d _ => [c, s, d]

/-- The calls whose bytecode refinement is proved on `main` today (`InvariantsCalls.lean`):
the vault's share-token functions and the asset's `transfer` / `transferFrom` (so donations). -/
def Proven : VCall → Prop
  | .transfer .. | .transferFrom .. | .approve .. | .assetTransfer .. | .assetTransferFrom .. =>
      True
  | .deposit .. | .mint .. | .withdraw .. | .redeem .. | .assetApprove .. | .assetMint ..
  | .assetBurn .. => False

end VCall

/-! ## Transitions -/

/-- A top-level message call **terminates** with result `r`: for every large enough fuel the
interpreter returns `r` (fuel only bounds the number of steps; it is not gas). -/
def Terminates (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message)
    (r : MessageResult) : Prop :=
  ∃ n, ∀ fuel, n ≤ fuel → processMessageCall fuel ctx w tr msg = .ok r

/-- **A modelled call.** `w'` is the world after a terminating top-level call `c` (from any
caller other than the vault and the asset themselves — a transaction's sender has no code,
EIP-3607 — zero value, at least `minGas` and fewer than `2⁶⁴` gas, any transient storage and warm
sets, any context with hash `crypto` before Prague or without EIP-7702 authorizations), whether
it succeeded or reverted. -/
def CallStep (crypto : Crypto) (vault asset : Address) (minGas : Nat) (w : World) (c : VCall)
    (w' : World) : Prop :=
  ∃ (ctx : Context) (tr : TransientStorage) (gas : Nat) (wa : AddressSet) (wk : StorageKeySet)
    (r : MessageResult),
    ctx.crypto = crypto ∧ (ctx.fork < .prague ∨ ctx.tx.authorizations = []) ∧
    minGas ≤ gas ∧ gas < 2 ^ 64 ∧ c.caller ≠ vault ∧ c.caller ≠ asset ∧
    Terminates ctx w tr (callMsg (w.code (c.target vault asset)) (c.target vault asset) c.caller
      c.data gas wa wk) r ∧
    r.world = w'

/-- **An environment step**: storage and code of the vault and the asset are unchanged. -/
def EnvStep (vault asset : Address) (w w' : World) : Prop :=
  (∀ k, w'.sload vault k = w.sload vault k) ∧ (∀ k, w'.sload asset k = w.sload asset k) ∧
    w'.code vault = w.code vault ∧ w'.code asset = w.code asset

/-- A call that leaves the world unchanged (e.g. every view call, `VaultViewsSpec.*_call`, or a
call to an unrelated contract that does not touch the vault or the asset) is an environment
step. -/
theorem envStep_of_world_eq {vault asset : Address} {w w' : World} (h : w' = w) :
    EnvStep vault asset w w' := by
  subst h; exact ⟨fun _ => rfl, fun _ => rfl, rfl, rfl⟩

/-! ## Hash hypotheses -/

/-- The allowance pairs of actors. -/
def ActorPairs (Act : List Address) (o sp : Address) : Prop := o ∈ Act ∧ sp ∈ Act

/-- **The trace-level hash hypothesis** for the actors `Act` (finitely many slots). -/
structure SlotsOk (crypto : Crypto) (vault : Address) (Act : List Address) : Prop where
  /-- The vault is an actor (its asset balance is written by the vault's functions). -/
  vault_mem : vault ∈ Act
  /-- Every actor's balance slot is fresh (`Erc20.BalanceSlotOk`). -/
  bal : ∀ a ∈ Act, Erc20.BalanceSlotOk crypto Erc20.Layout.solmate a
  /-- Every actor pair's allowance slot is fresh (`Erc20.AllowanceSlotOk`). -/
  allow : ∀ o ∈ Act, ∀ sp ∈ Act, Erc20.AllowanceSlotOk crypto Erc20.Layout.solmate o sp
  /-- Distinct actor pairs have distinct allowance slots. -/
  allowInj : ∀ o ∈ Act, ∀ sp ∈ Act, ∀ o' ∈ Act, ∀ sp' ∈ Act,
    Erc20.allowanceSlot crypto Erc20.Layout.solmate o sp =
      Erc20.allowanceSlot crypto Erc20.Layout.solmate o' sp' → o = o' ∧ sp = sp'
  /-- No actor's balance slot is a hook-counter slot. -/
  balFixed : ∀ a ∈ Act, Erc20.balanceSlot crypto Erc20.Layout.solmate a ≠ 6#256 ∧
    Erc20.balanceSlot crypto Erc20.Layout.solmate a ≠ 7#256
  /-- No actor pair's allowance slot is a hook-counter slot. -/
  allowFixed : ∀ o ∈ Act, ∀ sp ∈ Act, Erc20.allowanceSlot crypto Erc20.Layout.solmate o sp ≠ 6#256 ∧
    Erc20.allowanceSlot crypto Erc20.Layout.solmate o sp ≠ 7#256

/-! ## The system -/

/-- The concrete system: deployed worlds, modelled calls admitted by `K` whose actors are in
`Act`, environment steps; the model is `Solmate.step` with the invariant `Solmate.Inv` (and the
vault's address), and states agree up to the allowances of non-actor pairs. -/
noncomputable def system (crypto : Crypto) (vault asset : Address) (minGas : Nat)
    (Act : List Address) (K : VCall → Prop) : System World (State Address) VCall where
  step s c := step s c.op
  abs w := abs crypto w vault asset
  call := CallStep crypto vault asset minGas
  env := EnvStep vault asset
  Pre w := Deployed w vault asset
  Inv s := Inv s ∧ s.self = vault
  Agree := AgreeOn (ActorPairs Act)
  Ok c := (∀ a ∈ c.actors, a ∈ Act) ∧ K c

/-- What a refinement theorem of call `c` says, in terms of `abs`: if the model operation
succeeds with `s'`, the world after the call agrees with `s'` (up to non-actor allowances); if
it reverts, the world is unchanged. -/
def CallRefines (crypto : Crypto) (vault asset : Address) (Act : List Address) (w : World)
    (c : VCall) (w' : World) : Prop :=
  match step (abs crypto w vault asset) c.op with
  | some s' => AgreeOn (ActorPairs Act) (abs crypto w' vault asset) s'
  | none => w' = w

/-- **The per-call refinement obligation** of call `c`: under the trace's hash hypothesis, from
every deployed world whose abstraction is well formed, every terminating call `c` keeps the
deployment and refines `c.op`. -/
def OpRefinesAt (crypto : Crypto) (vault asset : Address) (minGas : Nat) (Act : List Address)
    (c : VCall) : Prop :=
  SlotsOk crypto vault Act → (∀ a ∈ c.actors, a ∈ Act) →
    ∀ w w', Deployed w vault asset → Inv (abs crypto w vault asset) →
      CallStep crypto vault asset minGas w c w' →
      Deployed w' vault asset ∧ CallRefines crypto vault asset Act w c w'

/-! ## Deployment and abstraction frames -/

/-- `Deployed` depends only on the code of the two accounts. -/
theorem _root_.EvmLeanSpecs.Refinement.Deployed.of_code {w w' : World} {vault asset : Address} (h : Deployed w vault asset)
    (hv : w'.code vault = w.code vault) (ha : w'.code asset = w.code asset) :
    Deployed w' vault asset where
  vaultCode := by rw [hv]; exact h.vaultCode
  assetCode := by rw [ha]; exact h.assetCode
  vaultNotPrecompile := h.vaultNotPrecompile
  assetNotPrecompile := h.assetNotPrecompile

/-- The asset code (any immutables) has 2870 bytes. -/
theorem size_assetCode (ia : SolmateAsset.Immutables) :
    (SolmateAsset.runtimeCodeWith ia).size = 2870 :=
  (size_patchWords _ _).trans SolmateAsset.size_runtimeCode

/-- The vault and the asset are different accounts (their codes have different sizes). -/
theorem _root_.EvmLeanSpecs.Refinement.Deployed.vault_ne_asset {w : World} {vault asset : Address}
    (h : Deployed w vault asset) : vault ≠ asset := by
  rintro rfl
  obtain ⟨i, -, hi⟩ := h.vaultCode
  obtain ⟨ia, hia⟩ := h.assetCode
  have := congrArg ByteArray.size (hi.symm.trans hia)
  rw [size_assetCode] at this
  have h2 := Shares.size_code i
  simp only [Shares.code] at h2
  omega

/-- A token's ledger depends only on its storage. -/
theorem tokenView_congr {crypto : Crypto} {w w' : World} {token : Address}
    (h : ∀ k, w'.sload token k = w.sload token k) : tokenView crypto w' token = tokenView crypto w token := by
  simp only [tokenView, Erc20.view, h]

/-- The abstraction depends only on the storage of the vault and the asset. -/
theorem abs_congr {crypto : Crypto} {w w' : World} {vault asset : Address}
    (hv : ∀ k, w'.sload vault k = w.sload vault k) (ha : ∀ k, w'.sload asset k = w.sload asset k) :
    abs crypto w' vault asset = abs crypto w vault asset := by
  simp only [abs, tokenView_congr hv, tokenView_congr ha, hv]

/-- A storage view representing `t` on the allowances `P ⊇ G` gives a ledger agreeing with `t`
on `G`. -/
theorem tokAgree_of_repOn {crypto : Crypto} {w : World} {token : Address}
    {P G : Address → Address → Prop} {t : Token Address}
    (h : Shares.RepOn P (Erc20.view crypto Erc20.Layout.solmate w token) t)
    (hG : ∀ o sp, G o sp → P o sp) : TokAgree G (tokenView crypto w token) t where
  balanceOf := by
    ext a; rw [tokenView_balanceOf]; exact h.balanceOf a
  totalSupply := h.totalSupply
  allowance o sp hg := h.allowance o sp (hG o sp hg)

/-- **Bridge for a vault call**: the share storage represents `t'` on `P ⊇ actor pairs`, and
every slot of the asset and the hook-counter slots are unchanged. -/
theorem agree_of_shares {crypto : Crypto} {w w' : World} {vault asset : Address}
    {Act : List Address} {P : Address → Address → Prop} {t' : Token Address}
    (hrep : Shares.RepOn P (Erc20.view crypto Erc20.Layout.solmate w' vault) t')
    (hP : ∀ o sp, ActorPairs Act o sp → P o sp)
    (ha : ∀ k, w'.sload asset k = w.sload asset k)
    (h6 : w'.sload vault 6#256 = w.sload vault 6#256)
    (h7 : w'.sload vault 7#256 = w.sload vault 7#256) :
    AgreeOn (ActorPairs Act) (abs crypto w' vault asset)
      { abs crypto w vault asset with shares := t' } where
  self := rfl
  asset := by simp only [abs, tokenView_congr ha]; exact .refl _
  shares := tokAgree_of_repOn hrep hP
  afterDeposit := congrArg BitVec.toNat h7
  beforeWithdraw := congrArg BitVec.toNat h6

/-- **Bridge for an asset call**: the asset storage represents `t'` on `P ⊇ actor pairs`, and
every slot of the vault is unchanged. -/
theorem agree_of_asset {crypto : Crypto} {w w' : World} {vault asset : Address}
    {Act : List Address} {P : Address → Address → Prop} {t' : Token Address}
    (hrep : Shares.RepOn P (Erc20.view crypto Erc20.Layout.solmate w' asset) t')
    (hP : ∀ o sp, ActorPairs Act o sp → P o sp)
    (hv : ∀ k, w'.sload vault k = w.sload vault k) :
    AgreeOn (ActorPairs Act) (abs crypto w' vault asset)
      { abs crypto w vault asset with asset := t' } where
  self := rfl
  asset := tokAgree_of_repOn hrep hP
  shares := by simp only [abs, tokenView_congr hv]; exact .refl _
  afterDeposit := by simp only [abs, hv]
  beforeWithdraw := by simp only [abs, hv]

/-- **Bridge for the ERC-4626 entry points** (both ledgers and a hook counter change): the
share and asset storage represent the model's new ledgers on allowance predicates containing
the actor pairs (`Shares.RepOn`, as the deposit/mint/withdraw/redeem refinement theorems give
them), and the counter slots hold the model's counters. This is `Refines` weakened to
`RepOn`; it is all the wiring of a `Pending` obligation needs on the model side. -/
theorem agree_of_reps {crypto : Crypto} {w' : World} {vault asset : Address}
    {Act : List Address} {P₁ P₂ : Address → Address → Prop} {s' : State Address}
    (hself : s'.self = vault)
    (hsh : Shares.RepOn P₁ (Erc20.view crypto Erc20.Layout.solmate w' vault) s'.shares)
    (has : Shares.RepOn P₂ (Erc20.view crypto Erc20.Layout.solmate w' asset) s'.asset)
    (hP₁ : ∀ o sp, ActorPairs Act o sp → P₁ o sp) (hP₂ : ∀ o sp, ActorPairs Act o sp → P₂ o sp)
    (h7 : (w'.sload vault 7#256).toNat = s'.afterDepositCount)
    (h6 : (w'.sload vault 6#256).toNat = s'.beforeWithdrawCount) :
    AgreeOn (ActorPairs Act) (abs crypto w' vault asset) s' where
  self := hself.symm
  asset := tokAgree_of_repOn has hP₂
  shares := tokAgree_of_repOn hsh hP₁
  afterDeposit := h7
  beforeWithdraw := h6

/-! ## The refinement, from per-call theorems -/

/-- Admissible operations read only actor allowances. -/
theorem reads_of_actors {Act : List Address} {vault : Address} (hv : vault ∈ Act) {c : VCall}
    (hc : ∀ a ∈ c.actors, a ∈ Act) : Reads (ActorPairs Act) vault c.op := by
  cases c <;> simp_all [VCall.actors, VCall.op, Reads, ActorPairs]

/-- `CallRefines` is the system's `OpRefines`. -/
theorem opRefines_of_callRefines {crypto : Crypto} {vault asset : Address} {minGas : Nat}
    {Act : List Address} {K : VCall → Prop} {w w' : World} {c : VCall}
    (h : CallRefines crypto vault asset Act w c w') :
    (system crypto vault asset minGas Act K).OpRefines w c w' := by
  unfold CallRefines at h
  unfold System.OpRefines
  have e : (system crypto vault asset minGas Act K).step
      ((system crypto vault asset minGas Act K).abs w) c = step (abs crypto w vault asset) c.op :=
    rfl
  rw [e]
  revert h
  cases step (abs crypto w vault asset) c.op <;> exact id

/-- **The concrete system refines the model**, given a refinement theorem for every admitted
call kind and the trace's hash hypothesis. -/
theorem refinement {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}
    {K : VCall → Prop} (hs : SlotsOk crypto vault Act)
    (href : ∀ c, K c → OpRefinesAt crypto vault asset minGas Act c) :
    (system crypto vault asset minGas Act K).Refinement where
  agree := AgreeOn.equivalence
  inv_agree _ _ h hi := ⟨h.inv hi.1, h.self.symm.trans hi.2⟩
  inv_step _ _ _ hi h := ⟨Inv_step hi.1 h, (self_step h).trans hi.2⟩
  step_agree _ _ c hok hi h := by
    have := stepD_agree h (op := c.op) (by rw [hi.2]; exact reads_of_actors hs.vault_mem hok.1)
    exact this
  call w c w' hp hi hok hc := by
    obtain ⟨hp', hr⟩ := href c hok.2 hs hok.1 w w' hp hi.1 hc
    exact ⟨hp', opRefines_of_callRefines hr⟩
  env w w' hp he :=
    ⟨hp.of_code he.2.2.1 he.2.2.2, abs_congr he.1 he.2.1⟩

end EvmLeanSpecs.Refinement.Invariants

end

section

/-!
## Per-call refinement obligations proved on `main`

`OpRefinesAt` (the abs-level per-call refinement statement of `InvariantsSystem.lean`) for the
calls whose bytecode refinement exists today:

* the vault's share-token functions `transfer`, `transferFrom`, `approve`, from the top-level
  theorems `Shares.transfer_refines`, `Shares.transferFrom_refines`, `Shares.approve_refines`;
* the asset's `transfer` (in particular donations to the vault) and `transferFrom`, from the
  frame-level (callee) theorems `assetTransfer_refines`, `assetTransferFrom_refines`, lifted to
  a top-level call by `call_of_halts`.

Each proof: the terminating call's result is the one the refinement theorem describes (the
interpreter is deterministic in the fuel, `Terminates`); on success the written storage
represents the model's new ledger on the allowances whose slots are not written, which
includes every actor pair under `SlotsOk`; the other contract's storage and the hook-counter
slots are untouched; the codes are unchanged (`SSTORE` only). Reverts keep the world.

All five need only `100000 ≤ minGas`.
-/

namespace EvmLeanSpecs.Refinement.Invariants

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift

/-! ## World lemmas -/

theorem code_transferWorld (crypto : Crypto) (w : World) (token src dst : Address) (v : Word)
    (b : Address) :
    (EvmLean.Solidity.Erc20.transferWorld crypto w token src dst v).code b = w.code b := by
  simp [EvmLean.Solidity.Erc20.transferWorld]

theorem code_spendWorld (crypto : Crypto) (w : World) (token o sp : Address) (v : Word)
    (b : Address) : (Erc20.spendWorld crypto w token o sp v).code b = w.code b := by
  unfold Erc20.spendWorld; dsimp only; split <;> simp

theorem code_transferFromWorld (crypto : Crypto) (w : World) (token sp src dst : Address)
    (v : Word) (b : Address) :
    (Erc20.transferFromWorld crypto w token sp src dst v).code b = w.code b := by
  simp only [Erc20.transferFromWorld, code_transferWorld, code_spendWorld]

theorem code_approveWorld (crypto : Crypto) (w : World) (token o sp : Address) (v : Word)
    (b : Address) : (Erc20.approveWorld crypto w token o sp v).code b = w.code b := by
  simp [Erc20.approveWorld]

theorem sload_transferFromWorld_other {crypto : Crypto} {w : World} {token sp src dst b : Address}
    {v : Word} (hb : b ≠ token) (k : Word) :
    (Erc20.transferFromWorld crypto w token sp src dst v).sload b k = w.sload b k := by
  simp only [Erc20.transferFromWorld]
  rw [Shares.sload_transferWorld (.inl hb), Shares.sload_spendWorld (.inl hb)]

/-! ## Top-level glue -/

/-- A frame summary of a top-level call gives the result of `processMessageCall`: on success
the result's world is the final frame's, on revert it is the initial world. -/
theorem call_of_halts {ctx : Context} {w : World} {tr : TransientStorage} {code : ByteArray}
    {a caller : Address} {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}
    {H : Machine → Outcome → Prop} (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? code = none) (hpre : Precompile.isPrecompile ctx.fork a = false)
    (h : Halts (startMachine ctx w tr (callMsg code a caller data gas wa wk)) H) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ mf o r, H mf o ∧
      processMessageCall fuel ctx w tr (callMsg code a caller data gas wa wk) = .ok r ∧
      (∀ out, o = .success out → r.world = mf.world) ∧ (∀ out, o = .revert out → r.world = w) := by
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := a)
    (msg := callMsg code a caller data gas wa wk) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, hH, hs, hrun⟩ := hn fuel hle
  refine ⟨mf, o, _, hH, hrun, fun out ho => ?_, fun out ho => ?_⟩
  · subst ho
    have hk : mf.frame.kind = .call 0 0 := hs.kind
    exact (topLevelResult_success_call (t := (callMsg code a caller data gas wa wk).target)
      (out := out) hk).2.2.1
  · subst ho
    have hsnap : mf.frame.snapshot.1 = w := by rw [hs.snapshot]; rfl
    simp only [frameResult_revert, topLevelResult_world, hsnap]

/-- `Abi.encodeCall sel [x, y]` is a `TwoWordCall`. -/
theorem twoWordCall_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (x y : Word) :
    TwoWordCall (Abi.encodeCall sel [x, y]) sel x y :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _,
   Abi.calldataload_encodeCall_1 _ _ _ _⟩

/-- `Abi.encodeCall sel [x, y, z]` is a `ThreeWordCall`. -/
theorem threeWordCall_encodeCall {sel : Nat} (hsel : sel < 2 ^ 32) (x y z : Word) :
    ThreeWordCall (Abi.encodeCall sel [x, y, z]) sel x y z :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _,
   Abi.calldataload_encodeCall_1 _ _ _ _, Abi.calldataload_encodeCall_2 _ _ _ _ _⟩

/-- Unpacking `CallStep`: deterministic results. -/
theorem terminates_unique {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    {r r' : MessageResult} {n fuel : Nat} (hn : ∀ fuel, n ≤ fuel → processMessageCall fuel ctx w tr msg = .ok r)
    (hle : n ≤ fuel) (h : processMessageCall fuel ctx w tr msg = .ok r') : r' = r := by
  rw [hn fuel hle] at h; cases h; rfl

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

/-- `CallRefines` from a successful model step. -/
theorem callRefines_some {w w' : World} {c : VCall} {s' : State Address}
    (hop : Solmate.step (abs crypto w vault asset) c.op = some s')
    (h : AgreeOn (ActorPairs Act) (abs crypto w' vault asset) s') :
    CallRefines crypto vault asset Act w c w' := by
  unfold CallRefines; rw [hop]; exact h

/-- `CallRefines` from a reverting model step. -/
theorem callRefines_none {w w' : World} {c : VCall}
    (hop : Solmate.step (abs crypto w vault asset) c.op = none) (h : w' = w) :
    CallRefines crypto vault asset Act w c w' := by
  unfold CallRefines; rw [hop]; exact h

/-! ## The vault's share-token functions -/

set_option maxHeartbeats 1000000 in
/-- **`vault.transfer`** refines `Op.transfer`. -/
theorem opRefines_transfer (hmin : 100000 ≤ minGas) (caller dst : Address) (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.transfer caller dst amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨i, -, hcode⟩ := hdep.vaultCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false, hcode] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hd : dst ∈ Act := hact dst (by simp [VCall.actors])
  obtain ⟨r', hr', hres⟩ := Shares.transfer_refines (i := i) (tr := tr) (gas := gas) (warmAddrs := wa)
    (warmKeys := wk) (w := w) (vault := vault) (caller := caller) (dst := dst) (amount := amount)
    hdeleg (hdep.vaultNotPrecompile _) (by omega) (hs.bal caller hc) (hs.bal dst hd)
    (rep_toToken _) hinv.2 (max n 400) (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hr'
  split at hres
  · rename_i t' ht
    obtain ⟨-, -, hwld, hrep, hframe⟩ := hres
    refine ⟨hdep.of_code (by rw [hwld]; exact code_transferWorld ..)
      (by rw [hwld]; exact code_transferWorld ..), callRefines_some (s' := { abs ctx.crypto w vault asset with shares := t' }) ?_ ?_⟩
    · show Option.map _ ((abs ctx.crypto w vault asset).shares.transfer _ _ _) = _
      rw [show (abs ctx.crypto w vault asset).shares.transfer caller dst amount.toNat = some t'
        from ht]; rfl
    exact agree_of_shares hrep
      (fun o sp ⟨ho, hsp⟩ => ⟨Erc20.balanceSlot_ne_allowanceSlot (hs.allow o ho sp hsp) _ |>.symm,
        Erc20.balanceSlot_ne_allowanceSlot (hs.allow o ho sp hsp) _ |>.symm⟩)
      (fun k => hframe asset k (.inl hne.symm))
      (hframe vault 6#256 (.inr ⟨(hs.balFixed caller hc).1.symm, (hs.balFixed dst hd).1.symm⟩))
      (hframe vault 7#256 (.inr ⟨(hs.balFixed caller hc).2.symm, (hs.balFixed dst hd).2.symm⟩))
  · rename_i ht
    obtain ⟨-, -, hwld⟩ := hres
    refine ⟨hwld ▸ hdep, callRefines_none ?_ hwld⟩
    show Option.map _ ((abs ctx.crypto w vault asset).shares.transfer _ _ _) = _
    rw [show (abs ctx.crypto w vault asset).shares.transfer caller dst amount.toNat = none
      from ht]; rfl

/-- Actor pairs avoid the slot of another actor pair's allowance, unless they are that pair. -/
theorem SlotsOk.allowP {crypto : Crypto} {vault : Address} {Act : List Address}
    (hs : SlotsOk crypto vault Act) {o sp a b : Address} (ho : o ∈ Act) (hsp : sp ∈ Act)
    (ha : a ∈ Act) (hb : b ∈ Act) :
    (o = a ∧ sp = b) ∨ Erc20.allowanceSlot crypto Erc20.Layout.solmate o sp ≠
      Erc20.allowanceSlot crypto Erc20.Layout.solmate a b := by
  by_cases h : o = a ∧ sp = b
  · exact .inl h
  · exact .inr fun e => h (hs.allowInj o ho sp hsp a ha b hb e)

/-- Actor pairs avoid every actor's balance slot. -/
theorem SlotsOk.balP {crypto : Crypto} {vault : Address} {Act : List Address}
    (hs : SlotsOk crypto vault Act) {o sp : Address} (ho : o ∈ Act) (hsp : sp ∈ Act) (a : Address) :
    Erc20.allowanceSlot crypto Erc20.Layout.solmate o sp ≠
      Erc20.balanceSlot crypto Erc20.Layout.solmate a :=
  (Erc20.balanceSlot_ne_allowanceSlot (hs.allow o ho sp hsp) a).symm

set_option maxHeartbeats 1000000 in
/-- **`vault.transferFrom`** refines `Op.transferFrom`. -/
theorem opRefines_transferFrom (hmin : 100000 ≤ minGas) (caller src dst : Address)
    (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.transferFrom caller src dst amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨i, -, hcode⟩ := hdep.vaultCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false, hcode] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hsr : src ∈ Act := hact src (by simp [VCall.actors])
  have hd : dst ∈ Act := hact dst (by simp [VCall.actors])
  obtain ⟨r', hr', hres⟩ := Shares.transferFrom_refines (i := i) (tr := tr) (gas := gas)
    (warmAddrs := wa) (warmKeys := wk) (w := w) (vault := vault) (caller := caller) (src := src)
    (dst := dst) (amount := amount)
    hdeleg (hdep.vaultNotPrecompile _) (by omega) (hs.bal src hsr) (hs.bal dst hd)
    (hs.allow src hsr caller hc) (rep_toToken _) hinv.2 (max n 500) (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hr'
  split at hres
  · rename_i t' ht
    obtain ⟨-, -, hwld, hrep, hframe⟩ := hres
    refine ⟨hdep.of_code (by rw [hwld]; exact code_transferFromWorld ..)
      (by rw [hwld]; exact code_transferFromWorld ..),
      callRefines_some (s' := { abs ctx.crypto w vault asset with shares := t' }) ?_ ?_⟩
    · show Option.map _ ((abs ctx.crypto w vault asset).shares.transferFrom _ _ _ _) = _
      rw [show (abs ctx.crypto w vault asset).shares.transferFrom caller src dst amount.toNat =
        some t' from ht]; rfl
    exact agree_of_shares hrep
      (fun o sp ⟨ho, hsp⟩ => ⟨hs.balP ho hsp src, hs.balP ho hsp dst,
        hs.allowP ho hsp hsr hc⟩)
      (fun k => hframe asset k (.inl hne.symm))
      (hframe vault 6#256 (.inr ⟨(hs.balFixed src hsr).1.symm, (hs.balFixed dst hd).1.symm,
        (hs.allowFixed src hsr caller hc).1.symm⟩))
      (hframe vault 7#256 (.inr ⟨(hs.balFixed src hsr).2.symm, (hs.balFixed dst hd).2.symm,
        (hs.allowFixed src hsr caller hc).2.symm⟩))
  · rename_i ht
    obtain ⟨-, -, hwld⟩ := hres
    refine ⟨hwld ▸ hdep, callRefines_none ?_ hwld⟩
    show Option.map _ ((abs ctx.crypto w vault asset).shares.transferFrom _ _ _ _) = _
    rw [show (abs ctx.crypto w vault asset).shares.transferFrom caller src dst amount.toNat = none
      from ht]; rfl

set_option maxHeartbeats 1000000 in
/-- **`vault.approve`** refines `Op.approve`. -/
theorem opRefines_approve (hmin : 100000 ≤ minGas) (caller spender : Address) (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.approve caller spender amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨i, -, hcode⟩ := hdep.vaultCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false, hcode] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hsp : spender ∈ Act := hact spender (by simp [VCall.actors])
  obtain ⟨r', hr', -, -, hwld, hrep, hframe⟩ := Shares.approve_refines (i := i) (tr := tr)
    (gas := gas) (warmAddrs := wa) (warmKeys := wk) (w := w) (vault := vault) (caller := caller)
    (spender := spender) (amount := amount)
    hdeleg (hdep.vaultNotPrecompile _) (by omega) (hs.allow caller hc spender hsp)
    (rep_toToken _) (max n 300) (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hr'
  refine ⟨hdep.of_code (by rw [hwld]; exact code_approveWorld ..)
    (by rw [hwld]; exact code_approveWorld ..),
    callRefines_some (s' := { abs ctx.crypto w vault asset with
      shares := (abs ctx.crypto w vault asset).shares.approve caller spender amount.toNat }) rfl ?_⟩
  exact agree_of_shares hrep (fun o sp ⟨ho, hsp'⟩ => hs.allowP ho hsp' hc hsp)
    (fun k => hframe asset k (.inl hne.symm))
    (hframe vault 6#256 (.inr (hs.allowFixed caller hc spender hsp).1.symm))
    (hframe vault 7#256 (.inr (hs.allowFixed caller hc spender hsp).2.symm))

/-! ## The asset's `transfer` and `transferFrom`, top level -/

set_option maxHeartbeats 1000000 in
/-- **`asset.transfer`** (a donation when `dst` is the vault) refines `Op.assetTransfer`. -/
theorem opRefines_assetTransfer (hmin : 100000 ≤ minGas) (caller dst : Address) (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.assetTransfer caller dst amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨ia, hcode⟩ := hdep.assetCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, ite_true, hcode] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hd : dst ∈ Act := hact dst (by simp [VCall.actors])
  have hm := assetTransfer_refines (ia := ia) (dst := dst) (amount := amount)
    (startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Shares.transferData dst amount) gas wa wk))
    (fresh_startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Shares.transferData dst amount) gas wa wk)) rfl rfl
    (twoWordCall_encodeCall (by decide) _ _)
    (show (Shares.transferData dst amount).size < 2 ^ 64 by
      rw [Shares.transferData, Abi.size_encodeCall]; simp)
    (show 60000 ≤ gas by omega) (hs.bal caller hc) (hs.bal dst hd) (rep_toToken _) hinv.1
  split at hm
  · rename_i t' ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨ho, hwld, -⟩, hrep⟩, hrun, hsucc, -⟩ := hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw : r'.world = Erc20.transferWorld ctx.crypto w asset caller dst amount :=
      (hsucc _ ho).trans hwld
    rw [← hsucc _ ho] at hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_transferWorld ..)
      (by rw [hw]; exact code_transferWorld ..),
      callRefines_some (s' := { abs ctx.crypto w vault asset with asset := t' }) ?_ ?_⟩
    · show Option.map _ ((abs ctx.crypto w vault asset).asset.transfer _ _ _) = _
      rw [show (abs ctx.crypto w vault asset).asset.transfer caller dst amount.toNat = some t'
        from ht]; rfl
    exact agree_of_asset hrep (fun o sp ⟨ho, hsp⟩ => ⟨hs.balP ho hsp caller, hs.balP ho hsp dst⟩)
      (fun k => by rw [hw]; exact Shares.sload_transferWorld (.inl hne))
  · rename_i ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨out, ho⟩, -⟩, hrun, -, hrev⟩ := hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw := hrev out ho
    refine ⟨hw ▸ hdep, callRefines_none ?_ hw⟩
    show Option.map _ ((abs ctx.crypto w vault asset).asset.transfer _ _ _) = _
    rw [show (abs ctx.crypto w vault asset).asset.transfer caller dst amount.toNat = none
      from ht]; rfl

set_option maxHeartbeats 1000000 in
/-- **`asset.transferFrom`** refines `Op.assetTransferFrom`. -/
theorem opRefines_assetTransferFrom (hmin : 100000 ≤ minGas) (caller src dst : Address)
    (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.assetTransferFrom caller src dst amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨ia, hcode⟩ := hdep.assetCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, ite_true, hcode] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hsr : src ∈ Act := hact src (by simp [VCall.actors])
  have hd : dst ∈ Act := hact dst (by simp [VCall.actors])
  have hm := assetTransferFrom_refines (ia := ia) (src := src) (dst := dst) (amount := amount)
    (startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Shares.transferFromData src dst amount) gas wa wk))
    (fresh_startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Shares.transferFromData src dst amount) gas wa wk)) rfl rfl
    (threeWordCall_encodeCall (by decide) _ _ _)
    (show (Shares.transferFromData src dst amount).size < 2 ^ 64 by
      rw [Shares.transferFromData, Abi.size_encodeCall]; simp)
    (show 90000 ≤ gas by omega) (hs.bal src hsr) (hs.bal dst hd) (hs.allow src hsr caller hc)
    (rep_toToken _) hinv.1
  split at hm
  · rename_i t' ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨ho, hwld, -⟩, hrep⟩, hrun, hsucc, -⟩ := hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw : r'.world = Erc20.transferFromWorld ctx.crypto w asset caller src dst amount :=
      (hsucc _ ho).trans hwld
    rw [← hsucc _ ho] at hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_transferFromWorld ..)
      (by rw [hw]; exact code_transferFromWorld ..),
      callRefines_some (s' := { abs ctx.crypto w vault asset with asset := t' }) ?_ ?_⟩
    · show Option.map _ ((abs ctx.crypto w vault asset).asset.transferFrom _ _ _ _) = _
      rw [show (abs ctx.crypto w vault asset).asset.transferFrom caller src dst amount.toNat =
        some t' from ht]; rfl
    exact agree_of_asset hrep (fun o sp ⟨ho, hsp⟩ =>
        ⟨⟨hs.balP ho hsp src, hs.balP ho hsp dst⟩, hs.allowP ho hsp hsr hc⟩)
      (fun k => by rw [hw]; exact sload_transferFromWorld_other hne k)
  · rename_i ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨out, ho⟩, -⟩, hrun, -, hrev⟩ := hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw := hrev out ho
    refine ⟨hw ▸ hdep, callRefines_none ?_ hw⟩
    show Option.map _ ((abs ctx.crypto w vault asset).asset.transferFrom _ _ _ _) = _
    rw [show (abs ctx.crypto w vault asset).asset.transferFrom caller src dst amount.toNat = none
      from ht]; rfl

/-- **Every call on `main` today refines its operation** (`VCall.Proven`). -/
theorem opRefines_proven (hmin : 100000 ≤ minGas) (c : VCall) (hc : c.Proven) :
    OpRefinesAt crypto vault asset minGas Act c := by
  cases c with
  | transfer c d v => exact opRefines_transfer hmin c d v
  | transferFrom c s d v => exact opRefines_transferFrom hmin c s d v
  | approve c sp v => exact opRefines_approve hmin c sp v
  | assetTransfer c d v => exact opRefines_assetTransfer hmin c d v
  | assetTransferFrom c s d v => exact opRefines_assetTransferFrom hmin c s d v
  | deposit => exact hc.elim
  | mint => exact hc.elim
  | withdraw => exact hc.elim
  | redeem => exact hc.elim
  | assetApprove => exact hc.elim
  | assetMint => exact hc.elim
  | assetBurn => exact hc.elim

end EvmLeanSpecs.Refinement.Invariants

end

section

/-!
## `asset.approve` at the top level: the invariants layer's obligation

`opRefines_assetApprove`: the `OpRefinesAt` obligation of `InvariantsSystem.lean` for a
top-level call of the asset's `approve(spender, amount)` (any caller, any arguments), from the
frame-level `assetApprove_refines` lifted by `call_of_halts`, as for the asset's
`transfer` in `InvariantsCalls.lean`. The call always succeeds; the asset's storage represents
`Token.approve` on every actor pair (`SlotsOk`), the vault's storage is untouched.
-/

namespace EvmLeanSpecs.Refinement.Invariants

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

set_option maxHeartbeats 1000000 in
/-- **`asset.approve`** refines `Op.assetApprove`. -/
theorem opRefines_assetApprove (hmin : 100000 ≤ minGas) (caller spender : Address)
    (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.assetApprove caller spender amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨ia, hcode⟩ := hdep.assetCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, ite_true, hcode] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hsp : spender ∈ Act := hact spender (by simp [VCall.actors])
  have hm := assetApprove_refines (ia := ia) (spender := spender) (amount := amount)
    (startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Shares.approveData spender amount) gas wa wk))
    (fresh_startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Shares.approveData spender amount) gas wa wk)) rfl rfl
    (twoWordCall_encodeCall (by decide) _ _)
    (show (Shares.approveData spender amount).size < 2 ^ 64 by
      rw [Shares.approveData, Abi.size_encodeCall]; simp)
    (show 40000 ≤ gas by omega) (hs.allow caller hc spender hsp) (rep_toToken _)
  obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
    (hdep.assetNotPrecompile _) hm
  obtain ⟨mf, o, r', ⟨⟨ho, hwld, -⟩, hrep⟩, hrun, hsucc, -⟩ := hn' (max n n') (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hrun
  have hw : r'.world = Erc20.approveWorld ctx.crypto w asset caller spender amount :=
    (hsucc _ ho).trans hwld
  rw [← hsucc _ ho] at hrep
  refine ⟨hdep.of_code (by rw [hw]; exact code_approveWorld ..)
    (by rw [hw]; exact code_approveWorld ..),
    callRefines_some (s' := { abs ctx.crypto w vault asset with
      asset := (abs ctx.crypto w vault asset).asset.approve caller spender amount.toNat }) rfl ?_⟩
  exact agree_of_asset hrep (fun o sp ⟨ho, hsp'⟩ => hs.allowP ho hsp' hc hsp)
    (fun k => by rw [hw]; exact World.sload_sstore_ne_addr _ _ _ _ hne)

end EvmLeanSpecs.Refinement.Invariants

end

section

/-!
## `asset.mint` at the top level: the invariants layer's obligation

`opRefines_assetMint`: the `OpRefinesAt` obligation of `InvariantsSystem.lean` for a top-level
call of the asset's unrestricted `mint(dst, amount)` (any caller, any arguments), from the
frame-level `assetMint_refines` lifted by `call_of_halts`. On success the asset's storage
represents `Token.mint` (balances and supply exactly, allowances on every actor pair under
`SlotsOk`), the vault's storage is untouched; on overflow the call reverts.

Besides `SlotsOk` it needs the hash hypothesis `KeccakAvoids crypto (AddressKeyed [3]) [2]`
(no balance slot is the `totalSupply` slot; see `AssetMint.lean` for why it is necessary).
-/

namespace EvmLeanSpecs.Refinement.Invariants

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

/-- Actor pairs avoid both slots a `mint` / `burn` of `a` writes. -/
theorem SlotsOk.mintP (hs : SlotsOk crypto vault Act) {o sp : Address} (ho : o ∈ Act)
    (hsp : sp ∈ Act) (a : Address) : MintAllowances crypto a o sp :=
  ⟨(hs.allow o ho sp hsp).2.2, hs.balP ho hsp a⟩

set_option maxHeartbeats 1000000 in
/-- **`asset.mint`** refines `Op.assetMint`. -/
theorem opRefines_assetMint (hmin : 100000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256]) (caller dst : Address)
    (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.assetMint caller dst amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨ia, hcode⟩ := hdep.assetCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, ite_true, hcode] at hn
  have hd : dst ∈ Act := hact dst (by simp [VCall.actors])
  have hm := assetMint_refines (ia := ia) (dst := dst) (amount := amount)
    (startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Abi.encodeCall 0x40c10f19 [Word.ofAddress dst, amount]) gas wa wk))
    (fresh_startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Abi.encodeCall 0x40c10f19 [Word.ofAddress dst, amount]) gas wa wk)) rfl rfl
    (twoWordCall_encodeCall (by decide) _ _)
    (show (Abi.encodeCall 0x40c10f19 [Word.ofAddress dst, amount]).size < 2 ^ 64 by
      rw [Abi.size_encodeCall]; simp)
    (show 60000 ≤ gas by omega) hk (hs.bal dst hd) (rep_toToken _) hinv.1
  split at hm
  · rename_i t' ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨ho, hwld, -⟩, hrep⟩, hrun, hsucc, -⟩ :=
      hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw : r'.world = mintWorld ctx.crypto w asset dst amount := (hsucc _ ho).trans hwld
    rw [← hsucc _ ho] at hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_mintWorld ..)
      (by rw [hw]; exact code_mintWorld ..),
      callRefines_some (s' := { abs ctx.crypto w vault asset with asset := t' }) ?_ ?_⟩
    · show Option.map _ ((abs ctx.crypto w vault asset).asset.mint _ _) = _
      rw [show (abs ctx.crypto w vault asset).asset.mint dst amount.toNat = some t' from ht]; rfl
    exact agree_of_asset hrep (fun o sp ⟨ho, hsp⟩ => hs.mintP ho hsp dst)
      (fun k => by rw [hw]; exact sload_mintWorld (.inl hne))
  · rename_i ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨out, ho⟩, -⟩, hrun, -, hrev⟩ := hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw := hrev out ho
    refine ⟨hw ▸ hdep, callRefines_none ?_ hw⟩
    show Option.map _ ((abs ctx.crypto w vault asset).asset.mint _ _) = _
    rw [show (abs ctx.crypto w vault asset).asset.mint dst amount.toNat = none from ht]; rfl

end EvmLeanSpecs.Refinement.Invariants

end

section

/-!
## `asset.burn` at the top level: the invariants layer's obligation

`opRefines_assetBurn`: the `OpRefinesAt` obligation of `InvariantsSystem.lean` for a top-level
call of the asset's unrestricted `burn(src, amount)` (any caller, any arguments; with
`src = vault` this is the model's "loss"), from the frame-level `assetBurn_refines` lifted by
`call_of_halts`. Same hypotheses as `opRefines_assetMint`.
-/

namespace EvmLeanSpecs.Refinement.Invariants

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

set_option maxHeartbeats 1000000 in
/-- **`asset.burn`** refines `Op.assetBurn`. -/
theorem opRefines_assetBurn (hmin : 100000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256]) (caller src : Address)
    (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.assetBurn caller src amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨ia, hcode⟩ := hdep.assetCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, ite_true, hcode] at hn
  have hsr : src ∈ Act := hact src (by simp [VCall.actors])
  have hm := assetBurn_refines (ia := ia) (src := src) (amount := amount)
    (startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Abi.encodeCall 0x9dc29fac [Word.ofAddress src, amount]) gas wa wk))
    (fresh_startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Abi.encodeCall 0x9dc29fac [Word.ofAddress src, amount]) gas wa wk)) rfl rfl
    (twoWordCall_encodeCall (by decide) _ _)
    (show (Abi.encodeCall 0x9dc29fac [Word.ofAddress src, amount]).size < 2 ^ 64 by
      rw [Abi.size_encodeCall]; simp)
    (show 60000 ≤ gas by omega) hk (hs.bal src hsr) (rep_toToken _) hinv.1
  split at hm
  · rename_i t' ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨ho, hwld, -⟩, hrep⟩, hrun, hsucc, -⟩ :=
      hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw : r'.world = burnWorld ctx.crypto w asset src amount := (hsucc _ ho).trans hwld
    rw [← hsucc _ ho] at hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_burnWorld ..)
      (by rw [hw]; exact code_burnWorld ..),
      callRefines_some (s' := { abs ctx.crypto w vault asset with asset := t' }) ?_ ?_⟩
    · show Option.map _ ((abs ctx.crypto w vault asset).asset.burn _ _) = _
      rw [show (abs ctx.crypto w vault asset).asset.burn src amount.toNat = some t' from ht]; rfl
    exact agree_of_asset hrep (fun o sp ⟨ho, hsp⟩ => hs.mintP ho hsp src)
      (fun k => by rw [hw]; exact sload_burnWorld (.inl hne))
  · rename_i ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨out, ho⟩, -⟩, hrun, -, hrev⟩ := hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw := hrev out ho
    refine ⟨hw ▸ hdep, callRefines_none ?_ hw⟩
    show Option.map _ ((abs ctx.crypto w vault asset).asset.burn _ _) = _
    rw [show (abs ctx.crypto w vault asset).asset.burn src amount.toNat = none from ht]; rfl

end EvmLeanSpecs.Refinement.Invariants

end
