# EIP-2612 `permit`, `DOMAIN_SEPARATOR()`, `nonces(owner)`

Both Solmate `ERC20`s of the target — the asset (`MockERC20`) and the vault's share token
(`MockERC4626`) — implement EIP-2612. The `Permit*.lean` files prove what their **deployed
bytecode** does (any immutables: chain id, domain separator, decimals, asset), for **every
`Crypto`**, with only the standard axioms, and relate it to an extended ledger model.

## The precompile-call rule (`EvmLeanProofs/Program/PrecompileCall*.lean`)

A `CALL*` to a precompile pushes no frame: `launchCall` runs it inside the same `step`.

* `step_staticcall_precompile` / `WP.staticcall_precompile`: one step from a `STATICCALL` whose
  target is a precompile of `m.precompiles` (any `PrecompileImpl`), with the charges of
  `step_staticcall` (`callCost`: access cost, EIP-150 forwarding, memory expansion), to the
  caller resumed with `precompileResult` (world and transient storage unchanged).
  `resume_precompile_success` / `_failure` spell the resumed frame out: flag pushed, unused gas
  returned, output copied into the output window (`returnMemory`) and kept as return data,
  fresh child substate merged.
* `ecrecoverAddress? crypto hash v r s`: what `ECRECOVER` (`Precompile.ecrecover`) returns for
  the four words `hash ‖ v ‖ r ‖ s` — `v ∈ {27, 28}`, `0 < r, s < n`, then
  `crypto.ecrecover (ofWord hash) (v − 27) r s` and the low 20 bytes of `crypto.keccak256` of the
  key; `none` = empty output. `ecrecover_words`: with ≥ 3000 gas the precompile succeeds, costs
  3000 and returns `ofWord (ofAddress a)` or nothing (`leftPad32_extract_ofWord`).
* `WP.staticcall_ecrecover`: solc's `ecrecover` call (`STATICCALL(gas, 1, in, 128, out, 32)`)
  under the standard precompiles of the context: the caller continues with `1` pushed, 3000
  gas spent beyond the call's own charges, the signer's word stored at `out` (or memory
  unchanged, `returnMemory_ecrecoverOutput`).
* Tests: `EvmLeanTest/PrecompileCall.lean` (real secp256k1 vector, agreement with the precompile).

Helpers: `Solidity/PermitExtraMemory.lean` (multi-word and unaligned reads, expansion of a
symbolic-length access inside memory), `PermitExtraWord.lean`, `PermitExtraTactic.lean`
(`wp_generalize_mem`), `PermitExtraAttr.lean` (`permit_norm`: memory sizes and expansion costs,
keeps the gas a closed sum over generalized memory).

## The model (`../Vault/Permit.lean`)

`PermitToken A = { token : Token A, nonces : A →₀ ℕ }`.
`PermitToken.permit s owner spender value valid`: if `valid (s.nonces owner)` then
`token.approve owner spender value` and `nonces[owner] := (nonces[owner] + 1) % 2²⁵⁶` (the
source's unchecked `++`; `+ 1` below `MAX`, `permit_nonce_of_lt`), else `none`. Validity is a
parameter; `liftOp` lifts the other ledger operations (nonces unchanged).

## What the bytecode computes (`PermitDefs.lean`)

`PERMIT_TYPEHASH`, `DOMAIN_TYPEHASH`, `VERSION_HASH` are the **literals in the code** (solc folds
`keccak256("…")`); `structHash`, `digest` (`keccak("\x19\x01" ‖ ds ‖ structHash)`) use
`crypto.keccak256`. `SigOk crypto ds owner spender value nonce deadline v r s :=
owner ≠ 0 ∧ ecrecoverAddress? crypto (digest …) v r s = some owner`.
`PermitValid … nonce := v < 256 ∧ timestamp ≤ deadline ∧ SigOk … nonce …` (word comparison of
`block.timestamp`). `domainSeparator crypto initialChainId initialDomainSeparator chainId
nameSlot self` = the immutable if `chainId = initialChainId`, else `computedDomainSeparator`
(`keccak(DOMAIN_TYPEHASH ‖ keccak(name bytes) ‖ VERSION_HASH ‖ chainId ‖ self)`, the name from
storage slot 0). `permitWorld`: `nonces[owner] += 1` then `allowance[owner][spender] = value`.

## Theorems

Frame form (any fresh frame: top level or callee; `asset_*` in `PermitAsset*.lean`, `vault_*`
in `PermitVault*.lean`, same scripts at other offsets):

* `asset_permit_halts`, `vault_permit_halts : Halts m (PermitPost (dsOf …) owner spender value
  deadline v r s m)`: success with empty output, `permitWorld`, transient storage and created
  accounts unchanged and `Approval(owner, spender, value)` appended **iff** `PermitValid` at
  the stored nonce; otherwise a revert; ≤ 100000 gas.
* `asset_domainSeparator_halts` / `vault_…`: returns `domainSeparator …`, world unchanged.
  Internal summary `asset_ds_wp` / `vault_ds_wp` (both branches).
* `asset_nonces_halts` / `vault_…`: returns the word of `nonces[owner]`.
* `asset_permit_refines`, `vault_permit_refines` (`PermitSpec.lean`): additionally
  `PermitRefinesPost`: `modelPermit` (= `(permitView crypto w token).permit … (validAt …)`)
  is `some l'` iff success, and then the storage represents `l'` (`PermitRepOn`) and the log is
  emitted; `none` iff revert.
* `asset_permit_events`, `vault_permit_events` (`PermitEvents.lean`): `EventsPost` form.

Top level (`PermitCall.lean`, `processMessageCall`, `∃ n, ∀ fuel ≥ n, …`):
`asset_permit_call`, `vault_permit_call` (`PermitResult`: success / `permitWorld` /
`res.logs = #[approvalLog …]` iff `PermitValid`; else revert, `res.world = w`, no logs),
`asset_domainSeparator_call`, `vault_…`, `asset_nonces_call`, `vault_…`;
`asset_permit_call_refines`, `vault_permit_call_refines` (+ `PermitCallRefines`), and the
`opRefines` form `asset_permit_opRefines`, `vault_permit_opRefines`: every terminating call's
result world satisfies `PermitCallRefines` (shape of `Invariants.CallRefines`, over the extended
state).

### Assumptions

`m.precompiles = PrecompileImpl.standard m.ctx` (true at the top level and inherited by callee
frames), address `0x01` not delegated (`fork < Prague ∨ delegatedAddress? (w.code 1) = none`),
call depth below 1024, non-static frame, no value, `100000 ≤ gas < 2⁶⁴`, and
`DomainCase initialChainId chainId nameSlot`: the deployment chain (any name), or a name in
Solidity's short form (`ShortString`: < 32 bytes; both canonical names are). **Not covered:**
`DOMAIN_SEPARATOR()` / `permit` on another chain with a long name (≥ 32 bytes, the
out-of-place encoding loop of `abi_encode_t_string_storage`).

Hash hypotheses (only for the model relation, pointwise): `PermitSlotsOk crypto owner spender`
— `AllowanceSlotOk owner spender`, `nonces[owner]` fresh among the address-keyed rows of slots
3, 4, 5 and ≠ slot 2, and the two written slots distinct. Allowances are then known for the
entries `PermitAllowances` (written entry or a different slot), nonces for `PermitNonces`.

## What is claimed cryptographically

Nothing. Every theorem holds for **every** `Crypto`: it states exactly when `permit` succeeds,
in terms of `crypto.ecrecover` and `crypto.keccak256` (`SigOk`). In particular it is **not** a
theorem here that only the owner can produce a valid permit. That is ECDSA unforgeability, a
computational assumption; `SigUnforgeable crypto Signed` (`PermitDefs.lean`, *unused by every
refinement theorem*) fixes its shape — every signature recovering to `owner` is for a digest in
`Signed owner` — for users who want to add it as a hypothesis (`signed_of_sigOk`). Likewise
the domain-separator and type-hash literals equal the real Keccak of their strings only for the
real Keccak (`lake exe difftest` runs `permit` against anvil with `Crypto.real`).

## Integration into the trace system

`Invariants.system` abstracts worlds to `Solmate.State`, which has no nonces. To admit permit
calls (`VCall.permit c owner spender value deadline v r s`, `.assetPermit …`):

1. extend the abstract state with the nonces of both tokens (e.g. `abs'` returning
   `(abs …, noncesView crypto w vault, noncesView crypto w asset)`, or `permitView` per token);
   the existing calls keep the nonces when their written slots avoid the nonce slots (add the
   nonce slots of the actors to `SlotsOk`: fresh among `AddressKeyed [3, 4, 5]`, ≠ 0, 1, 2, 6,
   7, distinct from the actors' allowance slots — then `PermitAllowances`/`PermitNonces` cover
   all actor pairs and actors);
2. the model step of a permit is `PermitToken.permit … (validAt crypto ds ts …)`: validity
   depends on `ctx.block.timestamp` and on `domainSeparator` (chain id, `w.sload token 0`), so
   the `VCall` should carry the timestamp/chain id of its context, or the step takes them from
   the `CallStep`'s context;
3. the per-call obligation is `asset_permit_opRefines` / `vault_permit_opRefines`
   (`PermitCallRefines`: the represented ledger on actor pairs, the nonces, every other slot and
   every code unchanged; or `w' = w`), with `Deployed` preserved by `code_permitWorld`;
4. events: `permit_logs` / `PermitResult` give `res.logs`; `Solmate.events` needs an
   `approval` event for a successful permit (`Approval(owner, spender, value)` by the token).

## Build

`cd specs && lake build`. Times (M-series laptop, other builds running): `PermitAssetDS` ~60 s,
`PermitAssetTail` ~75 s, `PermitAssetBody` ~60 s, `PermitAsset` ~70 s, and the same for the
vault files; the rest a few seconds.
