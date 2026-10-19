import EvmLeanSpecs.Refinement.InvariantsAgree
import EvmLeanSpecs.Refinement.AssetSpec
import EvmLeanSpecs.Refinement.VaultViewsSpec

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
  message part of a transaction) from an **arbitrary caller** to the vault or to the asset,
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
caller, zero value, at least `minGas` and fewer than `2⁶⁴` gas, any transient storage and warm
sets, any context with hash `crypto` before Prague or without EIP-7702 authorizations), whether
it succeeded or reverted. -/
def CallStep (crypto : Crypto) (vault asset : Address) (minGas : Nat) (w : World) (c : VCall)
    (w' : World) : Prop :=
  ∃ (ctx : Context) (tr : TransientStorage) (gas : Nat) (wa : AddressSet) (wk : StorageKeySet)
    (r : MessageResult),
    ctx.crypto = crypto ∧ (ctx.fork < .prague ∨ ctx.tx.authorizations = []) ∧
    minGas ≤ gas ∧ gas < 2 ^ 64 ∧
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
