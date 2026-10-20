import EvmLeanSpecs.Refinement.PermitVault

/-!
# `permit`, `DOMAIN_SEPARATOR()`, `nonces(owner)` as top-level calls

`processMessageCall` forms of the frame theorems (`asset_permit_halts`, `vault_permit_halts`,
`*_domainSeparator_halts`, `*_nonces_halts`), in the shape of the other `*_call` refinement
theorems: for every large enough fuel the interpreter returns a result `res` with

* `permit`: `PermitResult`: if `PermitValid` (at the owner's nonce in `w`, for the domain
  separator `DOMAIN_SEPARATOR()` computes) the call succeeds with empty output, world
  `permitWorld` and the single log `Approval(owner, spender, value)`; otherwise it reverts,
  the world is `w` and there are no logs;
* `DOMAIN_SEPARATOR()`: success, the separator as one word, world `w`;
* `nonces(owner)`: success, the nonce word, world `w`.

Assumptions as in the frame theorems, plus the top-level ones of `processMessageCall_of_halts`
(no EIP-7702 authorizations or a fork before Prague; the token is not a precompile).
-/

namespace EvmLeanSpecs.Refinement.Permit

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-- The result of a top-level `permit` call of the token at `token` from world `w`. -/
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

/-- The top-level result of a reverting call frame. -/
theorem topLevelResult_revert {t : Option Address} {mf : Machine} {out : ByteArray} :
    let r := topLevelResult t (frameResult mf (.revert out)).2.1 (frameResult mf (.revert out)).2.2
      (frameResult mf (.revert out)).1
    r.success = false ∧ r.reverted = true ∧ r.world = mf.frame.snapshot.1 ∧ r.logs = #[] := by
  simp [frameResult_revert, topLevelResult, ChildResult.success, MessageResult.success]

/-- **Top-level glue for `permit`**: a `PermitPost` frame summary of the start machine gives
`PermitResult`. -/
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

/-- The asset's code is not a delegation designator. -/
theorem delegatedAddress?_asset (ia : SolmateAsset.Immutables) :
    delegatedAddress? (SolmateAsset.runtimeCodeWith ia) = none :=
  delegatedAddress?_of_size (by
    rw [SolmateAsset.runtimeCodeWith, size_patchWords, SolmateAsset.size_runtimeCode]; decide)

set_option maxHeartbeats 1000000 in
/-- **`permit` of the asset, top level.** The domain separator is `dsOf` of the start machine,
i.e. `domainSeparator ctx.crypto ia.initialChainId ia.initialDomainSeparator
(ofNat ctx.block.chainId) (w.sload asset 0) asset`. -/
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

/-- **Top-level glue for a view**: a frame summary that succeeds with output `out` and keeps the
world gives a successful result with output `out` and world `w`. -/
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
/-- **`DOMAIN_SEPARATOR()` of the asset, top level**: returns `Permit.domainSeparator …` (the
immutable on the deployment chain, else recomputed from the short name), world unchanged. -/
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

end EvmLeanSpecs.Refinement.Permit
