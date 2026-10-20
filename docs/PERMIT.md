# EIP-2612 `permit`, `DOMAIN_SEPARATOR()`, `nonces(owner)`

Both Solmate `ERC20`s of the target — the asset (`MockERC20`) and the vault's share token
(`MockERC4626`) — implement EIP-2612. The `Permit*.lean` files prove what their **deployed
bytecode** does (any immutables: chain id, domain separator, decimals, asset), for **every
`Crypto`**, with only the standard axioms, and relate it to an extended ledger model.

## The precompile-call rule (`EvmLogic/Program/PrecompileCall*.lean`)

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
* Tests: `EvmTest/PrecompileCall.lean` (real secp256k1 vector, agreement with the precompile).

Helpers: `EvmLogic/Solidity/Memory.lean` (multi-word and unaligned reads, expansion of a
symbolic-length access inside memory), `PermitExtraWord.lean`, `PermitExtraTactic.lean`
(`wp_generalize_mem`), `PermitExtraAttr.lean` (`permit_norm`: memory sizes and expansion costs,
keeps the gas a closed sum over generalized memory).

## The model (`defi/Defi/ERC20/Permit.lean`)

`PermitToken A = { token : Token A, nonces : A →₀ ℕ }`.
`PermitToken.permit s owner spender value valid`: if `valid (s.nonces owner)` then
`token.approve owner spender value` and `nonces[owner] := (nonces[owner] + 1) % 2²⁵⁶` (the
source's unchecked `++`; `+ 1` below `MAX`, `permit_nonce_of_lt`), else `none`. Validity is a
parameter; `liftOp` lifts the other ledger operations (nonces unchanged).

## What the bytecode computes (`defi/Examples/Solmate/ERC20/Permit.lean`)

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
* `asset_permit_refines`, `vault_permit_refines` (`defi/Examples/Solmate/ERC4626/PermitSpec.lean`): additionally
  `PermitRefinesPost`: `modelPermit` (= `(permitView crypto w token).permit … (validAt …)`)
  is `some l'` iff success, and then the storage represents `l'` (`PermitRepOn`) and the log is
  emitted; `none` iff revert.
* `asset_permit_events`, `vault_permit_events` (`defi/Examples/Solmate/ERC4626/PermitSpec.lean`): `EventsPost` form.

Top level (`defi/Examples/Solmate/ERC4626/PermitSpec.lean`, `processMessageCall`, `∃ n, ∀ fuel ≥ n, …`):
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
computational assumption; `SigUnforgeable crypto Signed` (`defi/Examples/Solmate/ERC20/Permit.lean`, *unused by every
refinement theorem*) fixes its shape — every signature recovering to `owner` is for a digest in
`Signed owner` — for users who want to add it as a hypothesis (`signed_of_sigOk`). Likewise
the domain-separator and type-hash literals equal the real Keccak of their strings only for the
real Keccak (`lake exe difftest` runs `permit` against anvil with `Crypto.real`).

## Integration into the trace system

Done for the any-transaction theorems (`defi/Examples/Solmate/ERC4626/Nested/Permit.lean`, `INVARIANTS.md` §6.3). The
abstraction is **not** extended with nonces (no invariant mentions them); instead the nonce
write is shown invisible to `abs`, and a `permit` frame commits the owner's approval:

1. `NonceSlotOk crypto Act owner` (owner's nonce slot fresh among `AddressKeyed [3, 4, 5]`,
   ≠ 2, 6, 7, no actor pair's allowance slot) with the trace's `SlotsOk` gives
   `PermitSlotsOk` and `PermitAllowances` for every actor pair, so
   `abs (permitWorld w token owner spender value) ≈ approve(owner → spender, value)` on that
   token (`agree_permitWorld_vault`, `agree_permitWorld_asset`);
2. `frameOk_permit`: a funded frame running `permit` (`PermitData`) with `PermitFrame`
   (`DomainOk`, `0x01` not delegated, depth < 1024) satisfies `FrameOk`, the committed call
   being `.approve owner spender value` / `.assetApprove owner spender value` (its `caller` is
   the owner); success iff `PermitValid` (`*_permit_halts`), otherwise a revert that commits
   nothing;
3. `TxOk`'s `Covered` admits such frames, `FrameAdmitted` requires the approval admitted and
   `NonceSlotOk` of the owner; `follows_tx`, `lift_any_tx`, `supply_eq_sum_any_tx`,
   `solvent_any_tx`, `price_mono_*` (approvals are `UserOp`s) cover them with unchanged
   statements;
4. `DOMAIN_SEPARATOR()` and `nonces` are covered views (`ViewData`).

The top-level traces of `defi/Examples/Solmate/ERC4626/Invariants/Deployed.lean` do not get a `permit` `VCall`: their `OpRefinesAt`
relates a call to one model operation from the abstraction alone, and a permit's success
depends on the nonce, timestamp and chain id (not in the abstraction). Direct top-level permit
transactions are covered by the any-transaction theorems (`txOk_direct`). Events: the model's
`approve` events are the permit's (`Approval(owner, spender, value)`); the top-level event
stream `trace_logs` is unchanged.

## Build

`cd defi && lake build`. Times (M-series laptop, other builds running): `Examples.Solmate.ERC20.Permit` ~60 s,
`Examples.Solmate.ERC20.Permit` ~75 s, `Examples.Solmate.ERC20.Permit` ~60 s, `Examples.Solmate.ERC20.Permit` ~70 s, and the same for the
vault files; the rest a few seconds.
