import Verified.Solmate.ERC4626.Permit
import Verified.Solmate.ERC4626.Abstraction
import Verified.Solmate.ERC4626.Events
import QEDefi.ERC20.Permit

/-!
# `permit`, `DOMAIN_SEPARATOR()`, `nonces(owner)`: top level, refinement, events

Top-level (`processMessageCall`) forms of the `permit`, `DOMAIN_SEPARATOR()` and `nonces` frame
theorems; the refinement of `permit` against `PermitToken.permit` (frame, top-level and
`opRefines` forms); and its events. See `docs/erc4626/details.md` §7.
-/

section

namespace Verified.Solmate.ERC4626.Permit
open Verified.Solmate.ERC20 QEDefi.ERC4626 Verified.Solmate.ERC20.Permit

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

/-- The result of a top-level `permit` call: success with `permitWorld` and one `Approval` log
iff `PermitValid` at the owner's stored nonce, else a revert with world `w` and no logs. -/
def PermitResult (crypto : Crypto) (ds : Word) (timestamp : Nat) (w : World) (token : Address)
    (owner spender : Address) (value deadline v r s : Word) (res : MessageResult) : Prop :=
  (PermitValid crypto ds timestamp owner spender value deadline v r s
      (w.sload token (nonceSlot crypto owner)) →
    res.success = true ∧ res.output = .empty ∧
    res.world = permitWorld crypto w token owner spender value ∧
    res.logs = #[approvalLog token owner spender value]) ∧
  (¬ PermitValid crypto ds timestamp owner spender value deadline v r s
      (w.sload token (nonceSlot crypto owner)) →
    res.success = false ∧ res.reverted = true ∧ res.world = w ∧ res.logs = #[])

theorem topLevelResult_revert {t : Option Address} {mf : Machine} {out : ByteArray} :
    let r := topLevelResult t (frameResult mf (.revert out)).2.1 (frameResult mf (.revert out)).2.2
      (frameResult mf (.revert out)).1
    r.success = false ∧ r.reverted = true ∧ r.world = mf.frame.snapshot.1 ∧ r.logs = #[] := by
  simp [frameResult_revert, topLevelResult, ChildResult.success, MessageResult.success]

theorem permit_call_of_halts {ctx : Context} {w : World} {tr : TransientStorage}
    {code : ByteArray} {token caller : Address} {data : ByteArray} {gas : Nat}
    {wa : AddressSet} {wk : StorageKeySet} {ds : Word} {owner spender : Address}
    {value deadline v r s : Word}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? code = none) (hpre : Precompile.isPrecompile ctx.fork token = false)
    (h : Halts (startMachine ctx w tr (callMsg code token caller data gas wa wk))
      (PermitPost ds owner spender value deadline v r s
        (startMachine ctx w tr (callMsg code token caller data gas wa wk)))) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res,
      processMessageCall fuel ctx w tr (callMsg code token caller data gas wa wk) = .ok res ∧
      PermitResult ctx.crypto ds ctx.block.timestamp w token owner spender value deadline v r s
        res := by
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := token)
    (msg := callMsg code token caller data gas wa wk) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, ⟨h1, h2, -⟩, hs, hrun⟩ := hn fuel hle
  refine ⟨_, hrun, fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨rfl, hw, -, -, hl⟩ := h1 hv
    have hk : mf.frame.kind = .call 0 0 := hs.kind
    obtain ⟨hsu, ho, hwr, -, hlr⟩ := topLevelResult_success_call
      (t := (callMsg code token caller data gas wa wk).target) (out := .empty) hk
    refine ⟨hsu, ho, hwr.trans hw, hlr.trans (hl.trans ?_)⟩
    rfl
  · obtain ⟨out, rfl⟩ := h2 hv
    obtain ⟨hsu, hrv, hwr, hlr⟩ := topLevelResult_revert
      (t := (callMsg code token caller data gas wa wk).target) (mf := mf) (out := out)
    refine ⟨hsu, hrv, hwr.trans ?_, hlr⟩
    rw [hs.snapshot]; rfl

theorem delegatedAddress?_asset (ia : SolmateAsset.Immutables) :
    delegatedAddress? (SolmateAsset.runtimeCodeWith ia) = none :=
  delegatedAddress?_of_size (by
    rw [SolmateAsset.runtimeCodeWith, size_patchWords, SolmateAsset.size_runtimeCode]; decide)

set_option maxHeartbeats 1000000 in
/-- **`permit` of the asset, top level.** The domain separator is the one
`DOMAIN_SEPARATOR()` returns (`domainSeparator …`). -/
theorem asset_permit_call {ia : SolmateAsset.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {asset caller : Address} {gas : Nat} {wa : AddressSet}
    {wk : StorageKeySet} {owner spender : Address} {value deadline v r s : Word}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork asset = false)
    (hcase : DomainCase ia.initialChainId (ofNat ctx.block.chainId) (w.sload asset 0#256))
    (hdel1 : ctx.fork < .prague ∨ delegatedAddress? (w.code 1) = none)
    (hg : 100000 ≤ gas) (hg' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res,
      processMessageCall fuel ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
        (permitData owner spender value deadline v r s) gas wa wk) = .ok res ∧
      PermitResult ctx.crypto (domainSeparator ctx.crypto ia.initialChainId
          ia.initialDomainSeparator (ofNat ctx.block.chainId) (w.sload asset 0#256) asset)
        ctx.block.timestamp w asset owner spender value deadline v r s res := by
  refine permit_call_of_halts hdeleg (delegatedAddress?_asset ia) hpre ?_
  have hf := fresh_startMachine ctx w tr
    (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller (permitData owner spender value deadline v r s) gas wa wk)
  exact asset_permit_halts _ hf rfl rfl (permitCall_encodeCall owner spender value deadline v r s)
    (show (permitData owner spender value deadline v r s).size < 2 ^ 64 by
      rw [permitData, Abi.size_encodeCall]; simp) hcase hg hg' rfl hdel1
    (by simp [startMachine, Frame.init, callMsg, Gas.stackDepthLimit])

set_option maxHeartbeats 1000000 in
/-- **`permit` of the vault's share token, top level.** -/
theorem vault_permit_call {i : SolmateVault.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {vault caller : Address} {gas : Nat} {wa : AddressSet}
    {wk : StorageKeySet} {owner spender : Address} {value deadline v r s : Word}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false)
    (hcase : DomainCase i.initialChainId (ofNat ctx.block.chainId) (w.sload vault 0#256))
    (hdel1 : ctx.fork < .prague ∨ delegatedAddress? (w.code 1) = none)
    (hg : 100000 ≤ gas) (hg' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res,
      processMessageCall fuel ctx w tr (callMsg (SolmateVault.runtimeCodeWith i) vault caller
        (permitData owner spender value deadline v r s) gas wa wk) = .ok res ∧
      PermitResult ctx.crypto (domainSeparator ctx.crypto i.initialChainId
          i.initialDomainSeparator (ofNat ctx.block.chainId) (w.sload vault 0#256) vault)
        ctx.block.timestamp w vault owner spender value deadline v r s res := by
  refine permit_call_of_halts hdeleg (Shares.delegatedAddress?_code i) hpre ?_
  have hf := fresh_startMachine ctx w tr
    (callMsg (SolmateVault.runtimeCodeWith i) vault caller (permitData owner spender value deadline v r s) gas wa wk)
  exact vault_permit_halts _ hf rfl rfl (permitCall_encodeCall owner spender value deadline v r s)
    (show (permitData owner spender value deadline v r s).size < 2 ^ 64 by
      rw [permitData, Abi.size_encodeCall]; simp) hcase hg hg' rfl hdel1
    (by simp [startMachine, Frame.init, callMsg, Gas.stackDepthLimit])

/-! ## Views -/

theorem view_call_of_halts {ctx : Context} {w : World} {tr : TransientStorage}
    {code : ByteArray} {token caller : Address} {data : ByteArray} {gas : Nat}
    {wa : AddressSet} {wk : StorageKeySet} {out : ByteArray} {H : Machine → Outcome → Prop}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? code = none) (hpre : Precompile.isPrecompile ctx.fork token = false)
    (h : Halts (startMachine ctx w tr (callMsg code token caller data gas wa wk)) H)
    (hH : ∀ mf o, H mf o → o = .success out ∧ mf.world = w) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res,
      processMessageCall fuel ctx w tr (callMsg code token caller data gas wa wk) = .ok res ∧
      res.success = true ∧ res.output = out ∧ res.world = w := by
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := token)
    (msg := callMsg code token caller data gas wa wk) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, hHo, hs, hrun⟩ := hn fuel hle
  obtain ⟨rfl, hw⟩ := hH mf o hHo
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  obtain ⟨hsu, ho, hwr, -, -⟩ := topLevelResult_success_call
    (t := (callMsg code token caller data gas wa wk).target) (out := out) hk
  exact ⟨_, hrun, hsu, ho, hwr.trans hw⟩

/-- Calldata of `DOMAIN_SEPARATOR()`. -/
def domainSeparatorData : ByteArray := Abi.encodeCall 0x3644e515 []

/-- Calldata of `nonces(owner)`. -/
def noncesData (owner : Address) : ByteArray := Abi.encodeCall 0x7ecebe00 [Word.ofAddress owner]

set_option maxHeartbeats 1000000 in
/-- **`DOMAIN_SEPARATOR()` of the asset, top level**: the immutable on the deployment chain, else
recomputed from the short name; world unchanged. -/
theorem asset_domainSeparator_call {ia : SolmateAsset.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {asset caller : Address} {gas : Nat} {wa : AddressSet}
    {wk : StorageKeySet}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork asset = false)
    (hcase : DomainCase ia.initialChainId (ofNat ctx.block.chainId) (w.sload asset 0#256))
    (hg : 20000 ≤ gas) (hg' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res,
      processMessageCall fuel ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
        domainSeparatorData gas wa wk) = .ok res ∧
      res.success = true ∧
      res.output = Bytes.ofWord (domainSeparator ctx.crypto ia.initialChainId
        ia.initialDomainSeparator (ofNat ctx.block.chainId) (w.sload asset 0#256) asset) ∧
      res.world = w := by
  have hf := fresh_startMachine ctx w tr
    (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller domainSeparatorData gas wa wk)
  have hh := asset_domainSeparator_halts _ hf rfl
    (by simp [startMachine, Frame.init, callMsg, domainSeparatorData, Abi.selectorOf_encodeCall])
    (by simp [startMachine, Frame.init, callMsg, domainSeparatorData, Abi.size_encodeCall])
    (by simp [startMachine, Frame.init, callMsg, domainSeparatorData, Abi.size_encodeCall])
    hcase hg hg'
  exact view_call_of_halts hdeleg (delegatedAddress?_asset ia) hpre hh (fun _ _ h => ⟨h.1, h.2.1⟩)

set_option maxHeartbeats 1000000 in
/-- **`DOMAIN_SEPARATOR()` of the vault, top level.** -/
theorem vault_domainSeparator_call {i : SolmateVault.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {vault caller : Address} {gas : Nat} {wa : AddressSet}
    {wk : StorageKeySet}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false)
    (hcase : DomainCase i.initialChainId (ofNat ctx.block.chainId) (w.sload vault 0#256))
    (hg : 20000 ≤ gas) (hg' : gas < 2 ^ 64) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res,
      processMessageCall fuel ctx w tr (callMsg (SolmateVault.runtimeCodeWith i) vault caller
        domainSeparatorData gas wa wk) = .ok res ∧
      res.success = true ∧
      res.output = Bytes.ofWord (domainSeparator ctx.crypto i.initialChainId
        i.initialDomainSeparator (ofNat ctx.block.chainId) (w.sload vault 0#256) vault) ∧
      res.world = w := by
  have hf := fresh_startMachine ctx w tr
    (callMsg (SolmateVault.runtimeCodeWith i) vault caller domainSeparatorData gas wa wk)
  have hh := vault_domainSeparator_halts _ hf rfl
    (by simp [startMachine, Frame.init, callMsg, domainSeparatorData, Abi.selectorOf_encodeCall])
    (by simp [startMachine, Frame.init, callMsg, domainSeparatorData, Abi.size_encodeCall])
    (by simp [startMachine, Frame.init, callMsg, domainSeparatorData, Abi.size_encodeCall])
    hcase hg hg'
  exact view_call_of_halts hdeleg (Shares.delegatedAddress?_code i) hpre hh (fun _ _ h => ⟨h.1, h.2.1⟩)

set_option maxHeartbeats 1000000 in
/-- **`nonces(owner)` of the asset, top level**: returns the word in `nonces[owner]`. -/
theorem asset_nonces_call {ia : SolmateAsset.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {asset caller : Address} {gas : Nat} {wa : AddressSet}
    {wk : StorageKeySet} (owner : Address)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork asset = false) (hg : 3000 ≤ gas) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res,
      processMessageCall fuel ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
        (noncesData owner) gas wa wk) = .ok res ∧
      res.success = true ∧
      res.output = Bytes.ofWord (w.sload asset (nonceSlot ctx.crypto owner)) ∧ res.world = w := by
  have hf := fresh_startMachine ctx w tr
    (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller (noncesData owner) gas wa wk)
  have hh := asset_nonces_halts _ hf owner rfl
    (by simp [startMachine, Frame.init, callMsg, noncesData, Abi.selectorOf_encodeCall])
    (by simp [startMachine, Frame.init, callMsg, noncesData, Abi.size_encodeCall])
    (by simp [startMachine, Frame.init, callMsg, noncesData, Abi.size_encodeCall])
    (Abi.calldataload_encodeCall_0 _ _ _) hg
  exact view_call_of_halts hdeleg (delegatedAddress?_asset ia) hpre hh (fun _ _ h => ⟨h.1, h.2.1⟩)

set_option maxHeartbeats 1000000 in
/-- **`nonces(owner)` of the vault, top level.** -/
theorem vault_nonces_call {i : SolmateVault.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {vault caller : Address} {gas : Nat} {wa : AddressSet}
    {wk : StorageKeySet} (owner : Address)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false) (hg : 3000 ≤ gas) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res,
      processMessageCall fuel ctx w tr (callMsg (SolmateVault.runtimeCodeWith i) vault caller
        (noncesData owner) gas wa wk) = .ok res ∧
      res.success = true ∧
      res.output = Bytes.ofWord (w.sload vault (nonceSlot ctx.crypto owner)) ∧ res.world = w := by
  have hf := fresh_startMachine ctx w tr
    (callMsg (SolmateVault.runtimeCodeWith i) vault caller (noncesData owner) gas wa wk)
  have hh := vault_nonces_halts _ hf owner rfl
    (by simp [startMachine, Frame.init, callMsg, noncesData, Abi.selectorOf_encodeCall])
    (by simp [startMachine, Frame.init, callMsg, noncesData, Abi.size_encodeCall])
    (by simp [startMachine, Frame.init, callMsg, noncesData, Abi.size_encodeCall])
    (Abi.calldataload_encodeCall_0 _ _ _) hg
  exact view_call_of_halts hdeleg (Shares.delegatedAddress?_code i) hpre hh (fun _ _ h => ⟨h.1, h.2.1⟩)

end Verified.Solmate.ERC4626.Permit

end

section

/-!
## `permit` refines the model

`permitView` reads the extended ledger `PermitToken` (nonces at `keccak(a ‖ 5)`) from storage,
with no hash hypothesis; `PermitSlotsOk` covers the two written slots.
-/

namespace Verified.Solmate.ERC4626.Permit
open Verified.Solmate.ERC20 QEDefi.ERC4626 Verified.Solmate.ERC20.Permit

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts
open QEDefi.Math QEDefi.ERC20

/-! ## The abstraction -/

/-- The nonces of the Solmate token at `token`, read from storage. -/
noncomputable def noncesView (crypto : Crypto) (w : World) (token : Address) : Address →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun a => (w.sload token (nonceSlot crypto a)).toNat

/-- The extended ledger (balances, allowances, total supply, nonces) of the token at `token`. -/
noncomputable def permitView (crypto : Crypto) (w : World) (token : Address) :
    PermitToken Address :=
  ⟨tokenView crypto w token, noncesView crypto w token⟩

@[simp] theorem noncesView_apply (crypto : Crypto) (w : World) (token a : Address) :
    noncesView crypto w token a = (w.sload token (nonceSlot crypto a)).toNat := by
  simp [noncesView]

/-- The model's validity predicate of a `permit` call: `PermitValid` at the nonce `n`. -/
def validAt (crypto : Crypto) (ds : Word) (timestamp : Nat) (owner spender : Address)
    (value deadline v r s : Word) (n : ℕ) : Prop :=
  PermitValid crypto ds timestamp owner spender value deadline v r s (BitVec.ofNat 256 n)

noncomputable instance (crypto : Crypto) (ds : Word) (timestamp : Nat) (owner spender : Address)
    (value deadline v r s : Word) :
    DecidablePred (validAt crypto ds timestamp owner spender value deadline v r s) :=
  Classical.decPred _

/-- The model's `permit` at the view, for the bytecode's validity check. -/
noncomputable def modelPermit (crypto : Crypto) (ds : Word) (timestamp : Nat) (w : World)
    (token owner spender : Address) (value deadline v r s : Word) : Option (PermitToken Address) :=
  (permitView crypto w token).permit owner spender value.toNat
    (validAt crypto ds timestamp owner spender value deadline v r s)

theorem validAt_view {crypto : Crypto} {ds : Word} {timestamp : Nat} {w : World}
    {token owner spender : Address} {value deadline v r s : Word} :
    validAt crypto ds timestamp owner spender value deadline v r s
        ((permitView crypto w token).nonces owner) ↔
      PermitValid crypto ds timestamp owner spender value deadline v r s
        (w.sload token (nonceSlot crypto owner)) := by
  simp only [validAt, permitView, noncesView_apply, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## Hash hypotheses and representation -/

/-- The hash hypotheses for the slots a `permit(owner, spender, …)` writes. -/
structure PermitSlotsOk (crypto : Crypto) (owner spender : Address) : Prop where
  allow : ERC20.AllowanceSlotOk crypto ERC20.Layout.solmate owner spender
  /-- `nonces[owner]` is the hash of no other address-keyed row of `balanceOf`, `allowance`,
  `nonces` (one target against `3 · 2¹⁶⁰` candidates). -/
  nonceFresh : KeccakFresh crypto (AddressKeyed [3#256, 4#256, 5#256])
    (slotPreimage (Word.ofAddress owner) 5#256)
  nonceTotal : nonceSlot crypto owner ≠ 2#256
  sep : ERC20.allowanceSlot crypto ERC20.Layout.solmate owner spender ≠ nonceSlot crypto owner

/-- The storage of `token` in `w` represents the extended ledger `l`: the ledger in the sense
of `Shares.RepOn P`, the nonces of the owners in `Pn`. -/
structure PermitRepOn (P : Address → Address → Prop) (Pn : Address → Prop) (crypto : Crypto)
    (w : World) (token : Address) (l : PermitToken Address) : Prop where
  ledger : QEDefi.ERC20.RepOn P (ERC20.view crypto ERC20.Layout.solmate w token) l.token
  nonce : ∀ a, Pn a → (w.sload token (nonceSlot crypto a)).toNat = l.nonces a

/-- The allowance entries known after `permit(owner, spender, …)`: the written entry, and every
entry whose slot is neither written slot. -/
def PermitAllowances (crypto : Crypto) (owner spender : Address) (o sp : Address) : Prop :=
  ((o = owner ∧ sp = spender) ∨
    ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp ≠
      ERC20.allowanceSlot crypto ERC20.Layout.solmate owner spender) ∧
  ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp ≠ nonceSlot crypto owner

/-- The nonces known after `permit(owner, spender, …)`: the owner's, and every nonce whose slot
is not the written allowance slot. -/
def PermitNonces (crypto : Crypto) (owner spender : Address) (a : Address) : Prop :=
  a = owner ∨ nonceSlot crypto a ≠ ERC20.allowanceSlot crypto ERC20.Layout.solmate owner spender

theorem permitRep_view (crypto : Crypto) (w : World) (token : Address) :
    PermitRepOn (fun _ _ => True) (fun _ => True) crypto w token (permitView crypto w token) :=
  ⟨rep_toToken _, fun a _ => (noncesView_apply crypto w token a).symm⟩

/-- **`permitWorld` represents the model's `permit`.** -/
theorem rep_permitWorld {crypto : Crypto} {w : World} {token owner spender : Address}
    {value : Word} {valid : ℕ → Prop} [DecidablePred valid] {l' : PermitToken Address}
    (hs : PermitSlotsOk crypto owner spender)
    (h : (permitView crypto w token).permit owner spender value.toNat valid = some l') :
    PermitRepOn (PermitAllowances crypto owner spender) (PermitNonces crypto owner spender) crypto
      (permitWorld crypto w token owner spender value) token l' := by
  obtain ⟨-, ht, hn⟩ := PermitToken.permit_eq_some h
  have hfresh := hs.nonceFresh
  have hns : ∀ (a : Address) (p : Word), p ∈ [3#256, 4#256, 5#256] → (a ≠ owner ∨ p ≠ 5#256) →
      mappingSlot crypto (Word.ofAddress a) p ≠ nonceSlot crypto owner :=
    fun a p hp hne => mappingSlot_ne_of_fresh_addr hfresh hp hne
  have hbal : ∀ a, ERC20.balanceSlot crypto ERC20.Layout.solmate a ≠ nonceSlot crypto owner :=
    fun a => hns a 3#256 (by simp) (.inr (by decide))
  have hbal' := ERC20.balanceSlot_ne_allowanceSlot hs.allow
  have hat : ERC20.allowanceSlot crypto ERC20.Layout.solmate owner spender ≠ 2#256 :=
    hs.allow.2.2
  have hread : ∀ k, (permitWorld crypto w token owner spender value).sload token k =
      if k = ERC20.allowanceSlot crypto ERC20.Layout.solmate owner spender then value
      else if k = nonceSlot crypto owner then w.sload token (nonceSlot crypto owner) + 1#256
      else w.sload token k := by
    intro k
    simp only [permitWorld, World.sload_sstore, true_and]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- total supply
    show ((permitWorld crypto w token owner spender value).sload token 2#256).toNat = _
    rw [hread, ht]
    simp only [Ne.symm hat, Ne.symm hs.nonceTotal, ↓reduceIte]
    rfl
  · -- balances
    intro a
    show ((permitWorld crypto w token owner spender value).sload token
      (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat = _
    rw [hread, ht]
    simp [hbal' a, hbal a, Token.approve, Token.setAllowance, tokenView, toToken, ERC20.view, permitView]
  · -- allowances
    intro o sp ⟨h1, h2⟩
    show ((permitWorld crypto w token owner spender value).sload token
      (ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp)).toNat = _
    rw [hread, ht]
    rcases h1 with ⟨rfl, rfl⟩ | h1
    · simp [Token.approve, Token.setAllowance]
    · simp only [h1, h2, ↓reduceIte]
      have hne : ¬ (o = owner ∧ sp = spender) := by rintro ⟨rfl, rfl⟩; exact h1 rfl
      by_cases ho : o = owner
      · subst ho
        have hsp : sp ≠ spender := fun e => hne ⟨rfl, e⟩
        simp [Token.approve, Token.setAllowance, hsp, tokenView, toToken, ERC20.view,
          permitView]
      · simp [Token.approve, Token.setAllowance, ho, tokenView, toToken, ERC20.view,
          permitView]
  · -- nonces
    intro a ha
    rw [hread, hn]
    by_cases hao : a = owner
    · subst hao
      simp only [Ne.symm hs.sep, ↓reduceIte, BitVec.toNat_add]
      simp [permitView, U256]
    · have ha' : nonceSlot crypto a ≠ ERC20.allowanceSlot crypto ERC20.Layout.solmate owner spender :=
        ha.resolve_left hao
      have hna : nonceSlot crypto a ≠ nonceSlot crypto owner := hns a 5#256 (by simp) (.inl hao)
      simp only [ha', hna, ↓reduceIte]
      simp [Finsupp.update_apply, hao, permitView]

theorem sload_permitWorld {crypto : Crypto} {w : World} {token owner spender b : Address}
    {value k : Word}
    (h : b ≠ token ∨ (k ≠ nonceSlot crypto owner ∧
      k ≠ ERC20.allowanceSlot crypto ERC20.Layout.solmate owner spender)) :
    (permitWorld crypto w token owner spender value).sload b k = w.sload b k := by
  simp only [permitWorld, World.sload_sstore]
  rcases h with h | ⟨h1, h2⟩
  · simp [h]
  · simp [h1, h2]

theorem code_permitWorld (crypto : Crypto) (w : World) (token owner spender : Address)
    (value : Word) (a : Address) :
    (permitWorld crypto w token owner spender value).code a = w.code a := by
  simp only [permitWorld, World.code_sstore]

/-! ## Refinement, frame form -/

/-- The model-level post of `permit` from the start machine `m`: the model's `permit` succeeds
iff the frame does, and then the storage represents its result and the frame logged `Approval`. -/
def PermitRefinesPost (ds : Word) (owner spender : Address) (value deadline v r s : Word)
    (m mf : Machine) (o : Outcome) : Prop :=
  match modelPermit m.ctx.crypto ds m.ctx.block.timestamp m.world m.frame.msg.currentTarget owner
      spender value deadline v r s with
  | some l' => o = .success .empty ∧
    PermitRepOn (PermitAllowances m.ctx.crypto owner spender)
      (PermitNonces m.ctx.crypto owner spender) m.ctx.crypto mf.world m.frame.msg.currentTarget l' ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog m.frame.msg.currentTarget owner spender value)
  | none => ∃ out, o = .revert out

theorem refinesPost_of_permitPost {ds : Word} {owner spender : Address}
    {value deadline v r s : Word} {m mf : Machine} {o : Outcome}
    (hs : PermitSlotsOk m.ctx.crypto owner spender)
    (h : PermitPost ds owner spender value deadline v r s m mf o) :
    PermitRefinesPost ds owner spender value deadline v r s m mf o := by
  obtain ⟨h1, h2, -⟩ := h
  unfold PermitRefinesPost
  split
  · rename_i l' hl
    have hv := (validAt_view).1 (PermitToken.permit_eq_some hl).1
    obtain ⟨ho, hw, -, -, hlog⟩ := h1 hv
    refine ⟨ho, ?_, hlog⟩
    rw [hw]
    exact rep_permitWorld hs hl
  · rename_i hl
    apply h2
    intro hv
    have := (PermitToken.permit_isSome (s := permitView m.ctx.crypto m.world
      m.frame.msg.currentTarget) (owner := owner) (spender := spender) (value := value.toNat)
      (valid := validAt m.ctx.crypto ds m.ctx.block.timestamp owner spender value deadline v r s)).2
      ((validAt_view).2 hv)
    unfold modelPermit at hl
    rw [hl] at this
    exact absurd this (by simp)

/-- **`permit` of the asset refines `PermitToken.permit`**, in any frame. -/
theorem asset_permit_refines {ia : SolmateAsset.Immutables} (m : Machine)
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
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hs : PermitSlotsOk m.ctx.crypto owner spender) :
    Halts m (fun mf o =>
      PermitPost (dsOf ia.initialChainId ia.initialDomainSeparator m) owner spender value deadline
        v r s m mf o ∧
      PermitRefinesPost (dsOf ia.initialChainId ia.initialDomainSeparator m) owner spender value
        deadline v r s m mf o) :=
  (asset_permit_halts m hf hval hstatic hd hsz hcase hg hg' hstd hdel1 hdepth).mono
    fun _ _ _ h => ⟨h, refinesPost_of_permitPost hs h⟩

/-- **`permit` of the vault's share token refines `PermitToken.permit`**, in any frame. -/
theorem vault_permit_refines {i : SolmateVault.Immutables} (m : Machine)
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
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hs : PermitSlotsOk m.ctx.crypto owner spender) :
    Halts m (fun mf o =>
      PermitPost (dsOf i.initialChainId i.initialDomainSeparator m) owner spender value deadline
        v r s m mf o ∧
      PermitRefinesPost (dsOf i.initialChainId i.initialDomainSeparator m) owner spender value
        deadline v r s m mf o) :=
  (vault_permit_halts m hf hval hstatic hd hsz hcase hg hg' hstd hdel1 hdepth).mono
    fun _ _ _ h => ⟨h, refinesPost_of_permitPost hs h⟩

/-! ## Refinement, top level and `opRefines` form -/

/-- **The per-call refinement statement of `permit`** (shape of `Invariants.CallRefines`): on
`some l'` the new world represents `l'` and only the two written slots of `token` changed; on
`none`, `w' = w`. -/
def PermitCallRefines (crypto : Crypto) (ds : Word) (timestamp : Nat) (token : Address)
    (owner spender : Address) (value deadline v r s : Word) (w w' : World) : Prop :=
  match modelPermit crypto ds timestamp w token owner spender value deadline v r s with
  | some l' => PermitRepOn (PermitAllowances crypto owner spender)
      (PermitNonces crypto owner spender) crypto w' token l' ∧
    (∀ b k, b ≠ token ∨ (k ≠ nonceSlot crypto owner ∧
      k ≠ ERC20.allowanceSlot crypto ERC20.Layout.solmate owner spender) →
      w'.sload b k = w.sload b k) ∧
    (∀ a, w'.code a = w.code a)
  | none => w' = w

theorem callRefines_of_result {crypto : Crypto} {ds : Word} {timestamp : Nat} {w : World}
    {token owner spender : Address} {value deadline v r s : Word} {res : MessageResult}
    (hs : PermitSlotsOk crypto owner spender)
    (h : PermitResult crypto ds timestamp w token owner spender value deadline v r s res) :
    PermitCallRefines crypto ds timestamp token owner spender value deadline v r s w res.world := by
  obtain ⟨h1, h2⟩ := h
  unfold PermitCallRefines
  split
  · rename_i l' hl
    have hv := (validAt_view).1 (PermitToken.permit_eq_some hl).1
    obtain ⟨-, -, hw, -⟩ := h1 hv
    rw [hw]
    exact ⟨rep_permitWorld hs hl, fun b k hk => sload_permitWorld hk,
      code_permitWorld crypto w token owner spender value⟩
  · rename_i hl
    apply (h2 ?_).2.2.1
    intro hv
    have := (PermitToken.permit_isSome (s := permitView crypto w token) (owner := owner)
      (spender := spender) (value := value.toNat)
      (valid := validAt crypto ds timestamp owner spender value deadline v r s)).2
      ((validAt_view).2 hv)
    unfold modelPermit at hl
    rw [hl] at this
    exact absurd this (by simp)

/-- **`permit` of the asset, top level, against the model**: `PermitResult` and
`PermitCallRefines`. -/
theorem asset_permit_call_refines {ia : SolmateAsset.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {asset caller : Address} {gas : Nat} {wa : AddressSet}
    {wk : StorageKeySet} {owner spender : Address} {value deadline v r s : Word}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork asset = false)
    (hcase : DomainCase ia.initialChainId (ofNat ctx.block.chainId) (w.sload asset 0#256))
    (hdel1 : ctx.fork < .prague ∨ delegatedAddress? (w.code 1) = none)
    (hg : 100000 ≤ gas) (hg' : gas < 2 ^ 64) (hs : PermitSlotsOk ctx.crypto owner spender) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res,
      processMessageCall fuel ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
        (permitData owner spender value deadline v r s) gas wa wk) = .ok res ∧
      PermitResult ctx.crypto (domainSeparator ctx.crypto ia.initialChainId
          ia.initialDomainSeparator (ofNat ctx.block.chainId) (w.sload asset 0#256) asset)
        ctx.block.timestamp w asset owner spender value deadline v r s res ∧
      PermitCallRefines ctx.crypto (domainSeparator ctx.crypto ia.initialChainId
          ia.initialDomainSeparator (ofNat ctx.block.chainId) (w.sload asset 0#256) asset)
        ctx.block.timestamp asset owner spender value deadline v r s w res.world := by
  obtain ⟨n, hn⟩ := asset_permit_call (ia := ia) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (owner := owner) (spender := spender) (value := value) (deadline := deadline)
    (v := v) (r := r) (s := s) hdeleg hpre hcase hdel1 hg hg'
  exact ⟨n, fun fuel hle => let ⟨res, h1, h2⟩ := hn fuel hle;
    ⟨res, h1, h2, callRefines_of_result hs h2⟩⟩

/-- **`permit` of the vault's share token, top level, against the model.** -/
theorem vault_permit_call_refines {i : SolmateVault.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {vault caller : Address} {gas : Nat} {wa : AddressSet}
    {wk : StorageKeySet} {owner spender : Address} {value deadline v r s : Word}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false)
    (hcase : DomainCase i.initialChainId (ofNat ctx.block.chainId) (w.sload vault 0#256))
    (hdel1 : ctx.fork < .prague ∨ delegatedAddress? (w.code 1) = none)
    (hg : 100000 ≤ gas) (hg' : gas < 2 ^ 64) (hs : PermitSlotsOk ctx.crypto owner spender) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res,
      processMessageCall fuel ctx w tr (callMsg (SolmateVault.runtimeCodeWith i) vault caller
        (permitData owner spender value deadline v r s) gas wa wk) = .ok res ∧
      PermitResult ctx.crypto (domainSeparator ctx.crypto i.initialChainId
          i.initialDomainSeparator (ofNat ctx.block.chainId) (w.sload vault 0#256) vault)
        ctx.block.timestamp w vault owner spender value deadline v r s res ∧
      PermitCallRefines ctx.crypto (domainSeparator ctx.crypto i.initialChainId
          i.initialDomainSeparator (ofNat ctx.block.chainId) (w.sload vault 0#256) vault)
        ctx.block.timestamp vault owner spender value deadline v r s w res.world := by
  obtain ⟨n, hn⟩ := vault_permit_call (i := i) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (owner := owner) (spender := spender) (value := value) (deadline := deadline)
    (v := v) (r := r) (s := s) hdeleg hpre hcase hdel1 hg hg'
  exact ⟨n, fun fuel hle => let ⟨res, h1, h2⟩ := hn fuel hle;
    ⟨res, h1, h2, callRefines_of_result hs h2⟩⟩

/-- **`opRefines` form (asset)**: every terminating top-level `permit` call gives
`PermitCallRefines` and `PermitResult`. -/
theorem asset_permit_opRefines {ia : SolmateAsset.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {asset caller : Address} {gas : Nat} {wa : AddressSet}
    {wk : StorageKeySet} {owner spender : Address} {value deadline v r s : Word}
    {res : MessageResult} {n : Nat}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork asset = false)
    (hcase : DomainCase ia.initialChainId (ofNat ctx.block.chainId) (w.sload asset 0#256))
    (hdel1 : ctx.fork < .prague ∨ delegatedAddress? (w.code 1) = none)
    (hg : 100000 ≤ gas) (hg' : gas < 2 ^ 64) (hs : PermitSlotsOk ctx.crypto owner spender)
    (hterm : ∀ fuel, n ≤ fuel → processMessageCall fuel ctx w tr
      (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
        (permitData owner spender value deadline v r s) gas wa wk) = .ok res) :
    PermitCallRefines ctx.crypto (domainSeparator ctx.crypto ia.initialChainId
        ia.initialDomainSeparator (ofNat ctx.block.chainId) (w.sload asset 0#256) asset)
      ctx.block.timestamp asset owner spender value deadline v r s w res.world ∧
    PermitResult ctx.crypto (domainSeparator ctx.crypto ia.initialChainId
        ia.initialDomainSeparator (ofNat ctx.block.chainId) (w.sload asset 0#256) asset)
      ctx.block.timestamp w asset owner spender value deadline v r s res := by
  obtain ⟨m, hm⟩ := asset_permit_call_refines (ia := ia) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (owner := owner) (spender := spender) (value := value) (deadline := deadline)
    (v := v) (r := r) (s := s) hdeleg hpre hcase hdel1 hg hg' hs
  obtain ⟨res', h1, h2, h3⟩ := hm (max n m) (le_max_right _ _)
  rw [hterm _ (le_max_left _ _)] at h1
  cases h1
  exact ⟨h3, h2⟩

/-- **`opRefines` form (vault).** -/
theorem vault_permit_opRefines {i : SolmateVault.Immutables} {ctx : Context} {w : World}
    {tr : TransientStorage} {vault caller : Address} {gas : Nat} {wa : AddressSet}
    {wk : StorageKeySet} {owner spender : Address} {value deadline v r s : Word}
    {res : MessageResult} {n : Nat}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false)
    (hcase : DomainCase i.initialChainId (ofNat ctx.block.chainId) (w.sload vault 0#256))
    (hdel1 : ctx.fork < .prague ∨ delegatedAddress? (w.code 1) = none)
    (hg : 100000 ≤ gas) (hg' : gas < 2 ^ 64) (hs : PermitSlotsOk ctx.crypto owner spender)
    (hterm : ∀ fuel, n ≤ fuel → processMessageCall fuel ctx w tr
      (callMsg (SolmateVault.runtimeCodeWith i) vault caller
        (permitData owner spender value deadline v r s) gas wa wk) = .ok res) :
    PermitCallRefines ctx.crypto (domainSeparator ctx.crypto i.initialChainId
        i.initialDomainSeparator (ofNat ctx.block.chainId) (w.sload vault 0#256) vault)
      ctx.block.timestamp vault owner spender value deadline v r s w res.world ∧
    PermitResult ctx.crypto (domainSeparator ctx.crypto i.initialChainId
        i.initialDomainSeparator (ofNat ctx.block.chainId) (w.sload vault 0#256) vault)
      ctx.block.timestamp w vault owner spender value deadline v r s res := by
  obtain ⟨m, hm⟩ := vault_permit_call_refines (i := i) (tr := tr) (caller := caller) (wa := wa)
    (wk := wk) (owner := owner) (spender := spender) (value := value) (deadline := deadline)
    (v := v) (r := r) (s := s) hdeleg hpre hcase hdel1 hg hg' hs
  obtain ⟨res', h1, h2, h3⟩ := hm (max n m) (le_max_right _ _)
  rw [hterm _ (le_max_left _ _)] at h1
  cases h1
  exact ⟨h3, h2⟩

end Verified.Solmate.ERC4626.Permit

end

section

/-!
## The events of `permit`

Corollaries of `PermitPost`: `Approval(owner, spender, value)` on success, nothing on failure.
-/

namespace Verified.Solmate.ERC4626.Permit
open Verified.Solmate.ERC20 QEDefi.ERC4626 Verified.Solmate.ERC20.Permit

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

open Classical in
/-- The logs `permit` emits from the start machine `m`: `Approval(owner, spender, value)` by
the executing token if the permit is valid, none otherwise. -/
noncomputable def permitEvents (ds : Word) (owner spender : Address) (value deadline v r s : Word)
    (m : Machine) : Array Log :=
  if PermitValid m.ctx.crypto ds m.ctx.block.timestamp owner spender value deadline v r s
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto owner)) then
    #[approvalLog m.frame.msg.currentTarget owner spender value]
  else #[]

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

end Verified.Solmate.ERC4626.Permit

end
