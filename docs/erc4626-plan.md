# Verifying ERC-4626 vaults with evm-lean

Goal: the first end-to-end DeFi verification on top of evm-lean. Theorems about the
**deployed bytecode** of a real ERC-4626 vault, stated against an abstract Lean model of
the vault, with the economic properties proved on the model.

```
 EIP-4626 + public invariant suites (a16z erc4626-tests, crytic/properties)
            │  formalised as
            ▼
 specs/ (Mathlib): abstract vault model + invariants + inflation-attack theorems
            ▲  refinement: every external function of the bytecode implements
            │  the corresponding model operation (under explicit hypotheses)
 EvmLeanProofs/: Solidity layer (storage layout, ABI) + program layer (CFG, loops,
            calls) + per-function summaries of the compiled vault
            ▲
 contracts/: pinned Solidity sources → pinned solc → bytecode artifacts (as Lean data),
            differential-tested against Foundry/revm
```

## Targets

1. **Solmate `ERC4626`** (transmissions11/solmate, pinned commit), concrete vault =
   Solmate's `MockERC4626` (`totalAssets = asset.balanceOf(address(this))`), asset =
   Solmate `MockERC20`. Known property: vulnerable to the first-depositor inflation
   (donation) attack. We prove the positive properties *and* that the attack exists.
2. **OpenZeppelin `ERC4626`** (v5.x, `_decimalsOffset` virtual shares) next, proving the
   inflation attack is unprofitable / bounded.

Compiler: solc `0.8.28`, optimizer on (200 runs), `evmVersion = cancun`, no via-IR.
Artifacts (runtime bytecode, ABI, method identifiers, storage layout) are committed, so
proofs never depend on a local compiler.

## Proof architecture

- **Assumptions are explicit hypotheses**, never axioms: keccak non-collision on the
  finitely many slots a theorem mentions; the asset is the pinned `MockERC20` bytecode (or,
  later, any contract satisfying an ERC-20 summary); enough gas; no EIP-7702 delegation on
  the vault/asset; the vault is not reentered during asset calls (Solmate's MockERC20 does
  not call out) — adversarial callers are arbitrary.
- **Abstraction function** `abs : World → Option VaultState` reading Solidity storage
  (balances mapping, totalSupply, allowances, asset balances) through the storage layout.
- **Refinement**: for each external function `f`, running the bytecode on calldata
  `encode(f, args)` from a world `w` with `abs w = some s` yields a world `w'` with
  `abs w' = some (Model.f s args).state` and the right return data, or reverts exactly when
  the model says so.
- **Invariants** are proved on the model (Mathlib: `ℕ`, floor/ceil division lemmas,
  `Finset.sum`), then transferred: any sequence of successful calls from arbitrary callers
  preserves them.

## Work packages (initial, in parallel)

| Package | Owns | Delivers |
|---|---|---|
| **contracts** | `contracts/`, `scripts/build-contracts.sh`, `EvmLeanProofs/Contracts/`, `Differential/` | pinned sources, solc artifacts as Lean constants + layout metadata; a differential tester running random call sequences through evm-lean and Foundry and comparing storage/returns |
| **spec** | `specs/` (own Lake package, Mathlib), `docs/erc4626-invariants.md` | invariant catalogue with sources; abstract model; invariants and the inflation-attack theorems proved on the model |
| **solidity** | `EvmLeanProofs/Solidity/` | storage-slot model (value, mapping `keccak(key ‖ slot)`, packing), keccak non-collision hypotheses, ABI encoding/decoding and selector-dispatch lemmas, ERC-20 storage abstraction |
| **program** | `EvmLeanProofs/Program/` | run composition, basic-block summaries, loop-invariant rule, CALL/STATICCALL frame lemmas with callee summaries, a "function summary" structure for compiled functions |

Then: per-function refinement of the compiled vault (`deposit`, `mint`, `withdraw`,
`redeem`, views, ERC-20 `transfer`/`approve`/`transferFrom`), invariant transfer, report.
