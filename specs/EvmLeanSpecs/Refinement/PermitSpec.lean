import EvmLeanSpecs.Refinement.PermitCall
import EvmLeanSpecs.Refinement.Abstraction

/-!
# `permit` refines the model

The bytecode theorems (`PermitAsset`, `PermitVault`, `PermitCall`) against the extended ledger
`Vault.PermitToken` (`../Vault/Permit.lean`):

* `noncesView`, `permitView`: the nonces and the extended ledger of the Solmate token at `token`,
  read from storage (`tokenView` for the ledger; nonces at `keccak(a ‖ 5)`). Reading needs no
  hash hypothesis.
* `validAt`: the model's validity predicate, instantiated with the bytecode's check
  (`PermitValid`, any `Crypto`).
* `PermitSlotsOk`: the hash hypotheses for the two written slots, pointwise and plausible
  (`KeccakFresh`, never injectivity): `allowance[owner][spender]` is fresh
  (`Erc20.AllowanceSlotOk`), `nonces[owner]` is fresh among the address-keyed rows of slots 3,
  4, 5 and is not slot 2, and the two written slots differ.
* `PermitRepOn P Pn`: the storage represents a `PermitToken`, for the allowance entries in `P`
  and the nonces in `Pn` (entries whose slot is not a written one; nested-mapping and
  nonce frames are only available pointwise).
* `rep_permitWorld`: `permitWorld` represents the model's `permit` result.
* `asset_permit_refines` / `vault_permit_refines` (frame form, any frame) and
  `asset_permit_call_refines` / `vault_permit_call_refines` (top level): the model's
  `PermitToken.permit` returns `some l'` exactly when the call succeeds, and then the new
  storage represents `l'` and the logs are `Approval(owner, spender, value)`; `none` exactly when
  it reverts, with the world unchanged.
* `PermitCallRefines` / `asset_permit_opRefines`, `vault_permit_opRefines`: the same in the shape
  of `Invariants.CallRefines` (over the extended state), for every terminating top-level call:
  what trace integration consumes.
-/

namespace EvmLeanSpecs.Refinement.Permit

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault

/-! ## The abstraction -/

/-- The nonces of the Solmate token at `token`, read from storage. -/
noncomputable def noncesView (crypto : Crypto) (w : World) (token : Address) : Address →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun a => (w.sload token (nonceSlot crypto a)).toNat

/-- The extended ledger (balances, allowances, total supply, nonces) of the token at `token`. -/
noncomputable def permitView (crypto : Crypto) (w : World) (token : Address) :
    PermitToken Address :=
  ⟨tokenView crypto w token, noncesView crypto w token⟩

/-- A nonce of the view. -/
@[simp] theorem noncesView_apply (crypto : Crypto) (w : World) (token a : Address) :
    noncesView crypto w token a = (w.sload token (nonceSlot crypto a)).toNat := by
  simp [noncesView]

/-- The model's validity predicate of a `permit` call: `PermitValid` at the nonce `n`. -/
def validAt (crypto : Crypto) (ds : Word) (timestamp : Nat) (owner spender : Address)
    (value deadline v r s : Word) (n : ℕ) : Prop :=
  PermitValid crypto ds timestamp owner spender value deadline v r s (BitVec.ofNat 256 n)

/-- `validAt` is decidable (classically). -/
noncomputable instance (crypto : Crypto) (ds : Word) (timestamp : Nat) (owner spender : Address)
    (value deadline v r s : Word) :
    DecidablePred (validAt crypto ds timestamp owner spender value deadline v r s) :=
  Classical.decPred _

/-- The model's `permit` at the view, for the bytecode's validity check. -/
noncomputable def modelPermit (crypto : Crypto) (ds : Word) (timestamp : Nat) (w : World)
    (token owner spender : Address) (value deadline v r s : Word) : Option (PermitToken Address) :=
  (permitView crypto w token).permit owner spender value.toNat
    (validAt crypto ds timestamp owner spender value deadline v r s)

/-- The model's validity at the view's nonce is the bytecode's at the stored nonce word. -/
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
  /-- `allowance[owner][spender]` is fresh (`Erc20.AllowanceSlotOk`). -/
  allow : Erc20.AllowanceSlotOk crypto Erc20.Layout.solmate owner spender
  /-- `nonces[owner]` is the hash of no other address-keyed row of `balanceOf`, `allowance`,
  `nonces` (one target against `3 · 2¹⁶⁰` candidates). -/
  nonceFresh : KeccakFresh crypto (AddressKeyed [3#256, 4#256, 5#256])
    (slotPreimage (Word.ofAddress owner) 5#256)
  /-- `nonces[owner]` is not the `totalSupply` slot. -/
  nonceTotal : nonceSlot crypto owner ≠ 2#256
  /-- The two written slots differ. -/
  sep : Erc20.allowanceSlot crypto Erc20.Layout.solmate owner spender ≠ nonceSlot crypto owner

/-- The storage of `token` in `w` represents the extended ledger `l`: the ledger in the sense
of `Shares.RepOn P`, the nonces of the owners in `Pn`. -/
structure PermitRepOn (P : Address → Address → Prop) (Pn : Address → Prop) (crypto : Crypto)
    (w : World) (token : Address) (l : PermitToken Address) : Prop where
  /-- The ledger. -/
  ledger : Shares.RepOn P (Erc20.view crypto Erc20.Layout.solmate w token) l.token
  /-- The nonces. -/
  nonce : ∀ a, Pn a → (w.sload token (nonceSlot crypto a)).toNat = l.nonces a

/-- The allowance entries known after `permit(owner, spender, …)`: the written entry, and every
entry whose slot is neither written slot. -/
def PermitAllowances (crypto : Crypto) (owner spender : Address) (o sp : Address) : Prop :=
  ((o = owner ∧ sp = spender) ∨
    Erc20.allowanceSlot crypto Erc20.Layout.solmate o sp ≠
      Erc20.allowanceSlot crypto Erc20.Layout.solmate owner spender) ∧
  Erc20.allowanceSlot crypto Erc20.Layout.solmate o sp ≠ nonceSlot crypto owner

/-- The nonces known after `permit(owner, spender, …)`: the owner's, and every nonce whose slot
is not the written allowance slot. -/
def PermitNonces (crypto : Crypto) (owner spender : Address) (a : Address) : Prop :=
  a = owner ∨ nonceSlot crypto a ≠ Erc20.allowanceSlot crypto Erc20.Layout.solmate owner spender

/-- The view represents itself. -/
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
  have hbal : ∀ a, Erc20.balanceSlot crypto Erc20.Layout.solmate a ≠ nonceSlot crypto owner :=
    fun a => hns a 3#256 (by simp) (.inr (by decide))
  have hbal' := Erc20.balanceSlot_ne_allowanceSlot hs.allow
  have hat : Erc20.allowanceSlot crypto Erc20.Layout.solmate owner spender ≠ 2#256 :=
    hs.allow.2.2
  -- reading the final world
  have hread : ∀ k, (permitWorld crypto w token owner spender value).sload token k =
      if k = Erc20.allowanceSlot crypto Erc20.Layout.solmate owner spender then value
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
      (Erc20.balanceSlot crypto Erc20.Layout.solmate a)).toNat = _
    rw [hread, ht]
    simp [hbal' a, hbal a, Token.approve, Token.setAllowance, tokenView, toToken, Erc20.view, permitView]
  · -- allowances
    intro o sp ⟨h1, h2⟩
    show ((permitWorld crypto w token owner spender value).sload token
      (Erc20.allowanceSlot crypto Erc20.Layout.solmate o sp)).toNat = _
    rw [hread, ht]
    rcases h1 with ⟨rfl, rfl⟩ | h1
    · simp [Token.approve, Token.setAllowance]
    · simp only [h1, h2, ↓reduceIte]
      have hne : ¬ (o = owner ∧ sp = spender) := by rintro ⟨rfl, rfl⟩; exact h1 rfl
      by_cases ho : o = owner
      · subst ho
        have hsp : sp ≠ spender := fun e => hne ⟨rfl, e⟩
        simp [Token.approve, Token.setAllowance, hsp, tokenView, toToken, Erc20.view,
          permitView]
      · simp [Token.approve, Token.setAllowance, ho, tokenView, toToken, Erc20.view,
          permitView]
  · -- nonces
    intro a ha
    rw [hread, hn]
    by_cases hao : a = owner
    · subst hao
      simp only [Ne.symm hs.sep, ↓reduceIte, BitVec.toNat_add]
      simp [permitView, U256]
    · have ha' : nonceSlot crypto a ≠ Erc20.allowanceSlot crypto Erc20.Layout.solmate owner spender :=
        ha.resolve_left hao
      have hna : nonceSlot crypto a ≠ nonceSlot crypto owner := hns a 5#256 (by simp) (.inl hao)
      simp only [ha', hna, ↓reduceIte]
      simp [Finsupp.update_apply, hao, permitView]

/-- `permitWorld` writes only the two slots. -/
theorem sload_permitWorld {crypto : Crypto} {w : World} {token owner spender b : Address}
    {value k : Word}
    (h : b ≠ token ∨ (k ≠ nonceSlot crypto owner ∧
      k ≠ Erc20.allowanceSlot crypto Erc20.Layout.solmate owner spender)) :
    (permitWorld crypto w token owner spender value).sload b k = w.sload b k := by
  simp only [permitWorld, World.sload_sstore]
  rcases h with h | ⟨h1, h2⟩
  · simp [h]
  · simp [h1, h2]

/-- `permitWorld` keeps every code. -/
theorem code_permitWorld (crypto : Crypto) (w : World) (token owner spender : Address)
    (value : Word) (a : Address) :
    (permitWorld crypto w token owner spender value).code a = w.code a := by
  simp only [permitWorld, World.code_sstore]

/-! ## Refinement, frame form -/

/-- The model-level post of `permit` from the start machine `m` (domain separator `ds`): the
model's `permit` at the view of the executing account succeeds iff the frame succeeds, and
then the new storage represents its result and the frame logged `Approval`; it fails iff the
frame reverts. -/
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

/-- `PermitPost` gives the model-level post, under `PermitSlotsOk`. -/
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

/-- **The per-call refinement statement of `permit`** in the shape of `Invariants.CallRefines`,
over the extended state: if the model's `permit` (at the view of `token` in `w`) gives `some l'`,
the world `w'` after the call represents `l'` (allowances in `PermitAllowances`, nonces in
`PermitNonces`) and only the two written slots of `token` changed; if it gives `none`, `w' = w`. -/
def PermitCallRefines (crypto : Crypto) (ds : Word) (timestamp : Nat) (token : Address)
    (owner spender : Address) (value deadline v r s : Word) (w w' : World) : Prop :=
  match modelPermit crypto ds timestamp w token owner spender value deadline v r s with
  | some l' => PermitRepOn (PermitAllowances crypto owner spender)
      (PermitNonces crypto owner spender) crypto w' token l' ∧
    (∀ b k, b ≠ token ∨ (k ≠ nonceSlot crypto owner ∧
      k ≠ Erc20.allowanceSlot crypto Erc20.Layout.solmate owner spender) →
      w'.sload b k = w.sload b k) ∧
    (∀ a, w'.code a = w.code a)
  | none => w' = w

/-- `PermitResult` gives `PermitCallRefines` for the result's world, under `PermitSlotsOk`. -/
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

/-- **`permit` of the asset, top level, against the model**: every large enough fuel gives a
result whose world refines the model's `permit` (`PermitCallRefines`), with the exact result
`PermitResult` (success flag, `permitWorld`, logs). -/
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

/-- **`opRefines` form (asset)**: every *terminating* top-level `permit` call (the interpreter
returns `res` for all fuel from some `n` on) refines the model: `PermitCallRefines w res.world`,
and the logs are the model's (`Approval` on success, none on failure). -/
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

end EvmLeanSpecs.Refinement.Permit
