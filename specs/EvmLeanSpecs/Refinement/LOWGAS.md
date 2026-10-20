# Low gas: the call sites of the Solmate vault and asset

The generic gas-lockstep theorem (`EvmLeanProofs/Program/GasMono/`) relates a frame to the same
frame given more gas. It needs three facts about the code, defined in
`EvmLeanProofs/Program/GasMono/Interface.lean`:

* `GasFeedsCall code n`: every `GAS` at an instruction boundary below `n` is immediately
  followed by `CALL`/`STATICCALL` (so the only way gas is observed is as forwarded call gas);
* `RegionOk code n`: `n - 1` is a boundary holding `INVALID`, and no boundary at or after `n`
  is a `JUMPDEST` (Solidity appends data after the final `INVALID`; it is unreachable);
* `FailureReverts code p` for every return point `p ∈ callReturnPoints code n` (`q + 2` for each
  `GAS` at `q`): from **any** machine at `pc = p` with `0` (a failed call's success flag) on
  top of the stack, the frame ends with a revert or an exceptional halt, never a success.

`specs/EvmLeanSpecs/Refinement/LowGas.lean` proves all of them for the compiled Solmate
`MockERC4626` (`SolmateVault`, `n = 5216`) and `MockERC20` (`SolmateAsset`, `n = 2838`), for
**arbitrary immutables**, every `Crypto` and fork, with only the standard axioms:

| Theorem | Statement |
|---|---|
| `vault_gasFeedsCall i` | `GasFeedsCall (SolmateVault.runtimeCodeWith i) 5216` |
| `vault_regionOk i` | `RegionOk (SolmateVault.runtimeCodeWith i) 5216` |
| `vault_callReturnPoints i` | `callReturnPoints (SolmateVault.runtimeCodeWith i) 5216 = [1233, 3439, 3957, 4327]` |
| `vault_failureReverts i` | `∀ p ∈ callReturnPoints … 5216, FailureReverts (SolmateVault.runtimeCodeWith i) p` |
| `asset_gasFeedsCall ia`, `asset_regionOk ia` | the same for `SolmateAsset.runtimeCodeWith ia`, `n = 2838` |
| `asset_callReturnPoints ia` | `callReturnPoints (SolmateAsset.runtimeCodeWith ia) 2838 = [1632]` |
| `asset_failureReverts ia` | `∀ p ∈ …, FailureReverts (SolmateAsset.runtimeCodeWith ia) p` |

The per-site theorems are `vault_failureReverts_{1233,3439,3957,4327}` and
`asset_failureReverts_1632`. The final `INVALID` is at 5215 (vault) / 2837 (asset), followed by
a 32-byte data constant with no reachable `JUMPDEST`.

## The call sites

Sources: Solmate `89365b88` (`contracts/lib/solmate/src`), compiled by solc 0.8.28 (optimizer
200 runs, no via-IR). Disassembly from `contracts/artifacts/*/runtime.hex`.

### Vault 1233 — `asset.balanceOf(address(this))` (`STATICCALL` at 1232)

`MockERC4626.totalAssets` (`test/utils/mocks/MockERC4626.sol:18`), used by every conversion
and preview. A high-level external call: solc checks the flag and bubbles the callee's revert
data.

```
1233 ISZERO  DUP1  ISZERO  PUSH2 0x04df  JUMPI      ; flag 0: iszero(iszero(0)) = 0, fall through
1240 RETURNDATASIZE PUSH0 PUSH0 RETURNDATACOPY      ; copy the return data to memory 0
1244 RETURNDATASIZE PUSH0 REVERT                    ; revert(0, returndatasize())
```

### Vault 3439 — `ecrecover` in `permit` (`STATICCALL` to precompile 1 at 3438)

`ERC20.permit` (`tokens/ERC20.sol:130`, `address recoveredAddress = ecrecover(…)`). solc calls the
precompile with `STATICCALL` and treats a failed call like any external call: the same
`iszero(success) → returndatacopy; revert` sequence as at 1233 (3439–3452). (The precompile
itself only fails with too little gas; a bad signature is a *successful* call with empty
output, handled later by `require(recoveredAddress != address(0) && …, "INVALID_SIGNER")`.)

### Vault 3957 — `SafeTransferLib.safeTransferFrom` (`CALL` at 3956)

`ERC4626.deposit` / `mint` (`tokens/ERC4626.sol:51, 64`) pull the assets with
`asset.safeTransferFrom(msg.sender, address(this), assets)` (`utils/SafeTransferLib.sol:30-61`):

```solidity
success := call(gas(), token, 0, freeMemoryPointer, 100, 0, 32)
if and(iszero(and(eq(mload(0), 1), gt(returndatasize(), 31))), success) {
    success := iszero(or(iszero(extcodesize(token)), returndatasize()))
}
…
require(success, "TRANSFER_FROM_FAILED");
```

With `success = 0` the `and(…, success)` is `0`, so the inner block is skipped and `success`
stays `0`:

```
3957 SWAP2 POP POP                                   ; success into its variable slot
3960 DUP1 PUSH1 0x1f RETURNDATASIZE GT PUSH1 1 PUSH0 MLOAD EQ AND ISZERO AND ISZERO
3974 PUSH2 0x0f91 JUMPI                              ; iszero(and(…, 0)) = 1: skip the block
3985 JUMPDEST DUP1 PUSH2 0x0fd5 JUMPI                ; require(success): 0, fall through
3991 … MSTORE Error(string) "TRANSFER_FROM_FAILED" at mload(0x40) …
4049 PUSH2 0x07c8 JUMP
1992 JUMPDEST PUSH1 0x40 MLOAD DUP1 SWAP2 SUB SWAP1 REVERT
```

The value read by `MLOAD 0` and `RETURNDATASIZE` is arbitrary (the proof quantifies over it);
the masked condition does not depend on it. `SWAP2` underflows if the stack has fewer than
three items (an exceptional halt, also covered).

### Vault 4327 — `SafeTransferLib.safeTransfer` (`CALL` at 4326)

`ERC4626.withdraw` / `redeem` (`tokens/ERC4626.sol:92, 115`) send the assets with
`asset.safeTransfer(receiver, assets)` (`utils/SafeTransferLib.sol:63-92`): the same pattern as
3957 with `require(success, "TRANSFER_FAILED")` (4327–4417, then the shared revert tail at
1992).

### Asset 1632 — `ecrecover` in `permit` (`STATICCALL` at 1631)

The asset is Solmate `MockERC20`, whose only call is the `ecrecover` of `ERC20.permit`
(`tokens/ERC20.sol:130`); same bubble-revert sequence as the vault's 1233/3439 (1632–1645).

## How the proofs work

**Scan.** `insns code` (`GasMono/CodeScan.lean`) is the boundary scan written as one structural
pass over `code.data.toList`, returning `(q, opcode, next byte)` per boundary; `insns_eq`
identifies it with `boundaries` decorated with `Bytes.getD`, and `gasFeedsCall_iff`,
`regionOk_iff`, `callReturnPoints_eq` restate the predicates over it. (`decide +kernel` on the
`Bytes.getD` definitions does not finish: each lookup walks the 5 KB list.) Patching immutables
rewrites only `PUSH32` immediates, which `insns` skips, so `insns (runtimeCodeWith i) =
insns runtimeCode` holds by kernel evaluation with `i` free (`insns_vault`, `insns_asset`), and
the predicates are then decided on the canonical code.

**Failure paths.** `Fails code pc s` (`GasMono/CodeFails.lean`): every machine running `code`
at `pc` with stack exactly `s` ends its frame without success, whatever its gas, memory, return
data, world and jump table. One rule per instruction shape (`Fails.unOp`, `binOp`,
`pushValue`, `push`, `dup`, `swap`, `pop`, `jump`, `jumpi_zero`, `jumpi_ne_zero`, `jumpdest`,
`mload`, `mstore`, `returndatacopy`, `revert`, `invalid`) reduces `Fails` at `pc` to `Fails` at
the next pc; its proof absorbs every exceptional halt the instruction can raise (out of gas,
stack overflow/underflow, invalid jump destination, return data out of bounds) — the
out-of-gas branch is proved once per shape, not per step. Values that depend on untracked state
(`MLOAD`, `RETURNDATASIZE`) are universally quantified. `fails_steps`
(`GasMono/CodeFailsTactic.lean`) applies the rules, reading opcodes and immediates through the
kernel-checked patched-code facts of `Solidity/ExtraPatchedWP.lean`.

Timings (M-series laptop, `lake env lean`): the whole `LowGas.lean` checks in ≈40 s; each scan
fact 0.6–3.6 s; the bubble-revert sites ≈1 s each; the `safeTransfer*` sites ≈13 s each (kernel
checks of the code facts of 55 instructions on patched code).
