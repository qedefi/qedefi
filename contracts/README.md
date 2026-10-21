# Verification targets

Pinned Solidity sources, a reproducible build, pinned mainnet bytecode, and the artifacts used
by the Lean proofs (`qedefi/Examples/Solmate/`), the generated contract modules
(`qedefi/Examples/<Project>/Contracts/`) and the differential tester (`lake exe difftest`). The
ERC-4626 verification is described in [docs/erc4626](../docs/erc4626/README.md), the token
targets in [docs/tokens.md](../docs/tokens.md).

| Target | Asset | Vault |
|---|---|---|
| Solmate | `MockERC20` | `MockERC4626` (`totalAssets = asset.balanceOf(this)`; deposit/withdraw hooks count calls) |
| OpenZeppelin | `ERC20Mock` | `OzVault` (`src/OzVault.sol`: stock `ERC4626`, nothing overridden, `_decimalsOffset() = 0`) |
| OpenZeppelin, δ = 3 | `ERC20Mock` | `OzVaultOffset` (`src/OzVaultOffset.sol`: `OzVault` with `_decimalsOffset() = 3`) |

| Token target | Kind | Source |
|---|---|---|
| `SoladyToken` | compiled | `src/SoladyToken.sol`: Solady `ERC20` with constant metadata, unrestricted `mint`/`burn` |
| `WETH9` | mainnet bytecode | `mainnet/WETH9/` (see [Mainnet targets](#mainnet-targets)) |

`src/Targets.sol` is the compilation root.

## Pinned versions

| Component | Version |
|---|---|
| solc | `0.8.28+commit.7893614a` (svm layout, `~/.svm/0.8.28/solc-0.8.28`) |
| Foundry (`forge`, `anvil`, `cast`) | 1.8.5 (`51a52c59`), build tool and reference EVM (revm) |
| Solmate | `transmissions11/solmate` @ [`89365b88`](https://github.com/transmissions11/solmate/tree/89365b880c4f3c786bdd453d4b8e8fe410344a69) (2025-07-21) |
| OpenZeppelin Contracts | `v5.7.0` @ [`cab19933`](https://github.com/OpenZeppelin/openzeppelin-contracts/tree/v5.7.0) |
| Solady | `v0.1.26` @ [`acd959aa`](https://github.com/Vectorized/solady/tree/acd959aa4bd04720d640bf4e6a5c71037510cc4b) (`src/tokens/ERC20.sol`, `LICENSE.txt`) |
| forge-std (a16z suite only, not vendored) | `v1.17.0` @ `f3dae6e6` |
| a16z erc4626-tests (not vendored) | `a16z/erc4626-tests` @ `ac485460` (2025-07-29) |

Vendored files in `lib/` are byte-for-byte copies at their upstream paths, licence headers
and `LICENSE` files kept (Solmate AGPL-3.0-only, OpenZeppelin MIT, Solady MIT): Solmate's
`ERC20`, `ERC4626`, `FixedPointMathLib`, `SafeTransferLib`, `MockERC20`, `MockERC4626`; the
import closure of OpenZeppelin's `ERC4626` and `ERC20Mock`; Solady's `ERC20` (no imports).
Adding sources to the compilation shifts the AST ids recorded in `immutableReferences.json`
(`astId`); the bytecode does not change.

## Build

`foundry.toml`: solc 0.8.28, optimizer on, 200 runs, `evm_version = cancun`, no via-IR,
`bytecode_hash = "none"`, `cbor_metadata = false` (the bytecode depends only on sources and
settings).

```bash
scripts/build-contracts.sh           # rebuild artifacts/ and the generated Lean modules
scripts/build-contracts.sh --check   # also fail if any committed file changed
```

The script compiles with `forge build` and writes, per contract, `artifacts/<Name>/`:
`creation.hex`, `constructorArgs.hex`, `runtime.template.hex` (immutables zeroed),
`runtime.hex` (as deployed), `abi.json`, `methodIdentifiers.json`, `events.json`,
`errors.json`, `storageLayout.json`, `immutableReferences.json`; and
`artifacts/deployment.json`. It deploys everything on a local anvil, checks that the deployed
code equals the template outside the immutable positions, and generates the Lean modules.

| Contract | Runtime | Creation |
|---|---|---|
| `SolmateAsset` (`MockERC20`) | 2,870 B | 3,885 B |
| `SolmateVault` (`MockERC4626`) | 5,248 B | 6,474 B |
| `OzAsset` (`ERC20Mock`) | 1,900 B | 2,366 B |
| `OzVault` | 4,408 B | 5,098 B |
| `OzVaultOffset` | 4,411 B | 5,105 B |
| `SoladyToken` | 2,278 B | 2,306 B |

## Canonical deployment

Each family is deployed on its own fresh chain (chain id 1, Cancun) by
`0x1000000000000000000000000000000000000000`: asset at nonce 0, vault at nonce 1; the OZ
δ = 3 family likewise (`OzVaultOffset` at the vault address), `SoladyToken` alone at nonce 0
(the asset address).

| | Address | Constructor arguments |
|---|---|---|
| asset | `0x13136008B64FF592819B2FA6d43F2835C452020e` | Solmate `("Solmate Asset", "SAST", 18)`; OZ none (`"ERC20Mock"`, `"E20M"`, 18 decimals) |
| vault | `0x7c5a2c91b22d7A9226523D4Ba717DB6afB741ebd` | Solmate `(asset, "Solmate Vault", "svSAST")`; OZ `(asset)` (`"OZ Vault"`, `"ozVLT"`) |

## Immutables

solc compiles each `immutable` into 32-byte `PUSH32` placeholders filled in by the
constructor. Byte offsets of the values in the runtime code:

| Contract | Immutable | Offsets | Canonical value |
|---|---|---|---|
| SolmateAsset | `decimals` | 345 | 18 |
| | `INITIAL_CHAIN_ID` | 1063 | 1 |
| | `INITIAL_DOMAIN_SEPARATOR` | 1116 | EIP-712 separator (name, chain id, own address) |
| SolmateVault | `decimals` | 623 | 18 (`asset.decimals()`) |
| | `asset` | 688, 1170, 2014, 2169, 2668, 2995 | asset address |
| | `INITIAL_CHAIN_ID` | 1831 | 1 |
| | `INITIAL_DOMAIN_SEPARATOR` | 1879 | `0xfc86b75f…85216` |
| OzVault | `_asset` | 556, 896, 2772, 2924 | asset address |
| | `_underlyingDecimals` | 1276 | 18 (`asset.decimals()`) |
| OzVaultOffset | `_asset` | 556, 896, 2775, 2927 | asset address |
| | `_underlyingDecimals` | 1277 | 18 (`asset.decimals()`) |

`SoladyToken`, `OzAsset` and the mainnet targets have no immutables.

The runtime code of other deployments is obtained either by running the creation code
(`creationCode ++ constructorArgs`; `difftest` does this in evm-lean and anvil) or by
patching by position: `runtimeCodeWith (i : Immutables)`, with `runtimeCodeFor` computing the
immutables from deployment parameters (including Solmate's domain separator,
`solmateDomainSeparator`). `runtimeCodeWith_deployment : runtimeCodeWith deployment =
runtimeCode` is kernel-checked; `difftest` checks `runtimeCodeFor` against a deployment by a
second deployer.

## Mainnet targets

Deployed mainnet contracts are verified as deployed: the target is the runtime code itself,
pinned by its code hash. `scripts/fetch-mainnet.sh <Name> <address>` (network, read-only)
writes `mainnet/<Name>/`: `source/` (the verified sources as Sourcify serves them),
`sourcify.json` (compiler, settings, deployment, match status, bytecode transformations),
`abi.json`, `runtime.hex` (`eth_getCode` at the RPC's latest block; free endpoints serve no
archive state) and `meta.json` (address, block number and hash, code hash and size), and
checks the code against Sourcify's on-chain bytecode. Hand-written: `storageLayout.json`
(solc's format; derived from the source by C3 linearization and checked against mainnet
storage) and `genesis.json` (the storage the tests install with the code: the constructor's
state with test parameters; entries are a literal `slot` or a `mapping` slot with `keys`).
`scripts/build-contracts.sh` is offline for these: it checks `keccak(runtime.hex)` against
`meta.json`, derives `methodIdentifiers.json`, `events.json`, `errors.json` from the ABI,
checks that every selector is pushed by the dispatcher, and generates the Lean module.

| Name | Address | Code hash | Size | Read at block | Compiler (mainnet) |
|---|---|---|---|---|---|
| WETH9 | `0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2` | `0xd0a06b12ac47863b5c7be4185c2deaad1c61557033f56c7d4ea74429cbb25e23` | 3,124 B | 26,236,518 (`0xebf5f600…acfe1`) | 0.4.19+commit.c4cbbb05, optimizer off |
| USDT | `0xdAC17F958D2ee523a2206206994597C13D831ec7` | `0xb44fb4e949d0f78f87f79ee46428f23a2a5713ce6fc6e0beb3dda78c2ac1ea55` | 11,075 B | 26,236,598 (`0x5c845d3e…`) | 0.4.18+commit.9cf6e910, optimizer off |
| BNB | `0xB8c77482e45F1F44dE1745F52C74426C631bDD52` | `0xa1b62b5dd40a9c7b0f0a91ffd2578f7b1b22ca6d312846a0b88b3ae8339201c6` | 5,355 B | 26,236,596 (`0xcab61a55…`) | 0.4.12+commit.194ff033, optimizer off |
| STA | `0xa7DE087329BFcda5639247F96140f9DAbe3DeED1` | `0x2d5b2ff1b704f708f9c0f6ec97829ec6c8c9013713b9e0c301bdcb8dbf3c8429` | 3,216 B | 26,236,604 (`0x2fe4f1f0…`) | 0.5.0+commit.1d4f565a, optimizer 200 (byzantium) |
| AMPL (implementation `UFragments`) | `0xD0e3F82ab04B983C05263cF3BF52481FbAa435b1` | `0xec01e9f4bb8099df1b15c0c2b6e1fd795484681553981e77b34285b923fbc578` | 6,229 B | 26,236,604 | 0.7.6+commit.7338295f, optimizer 200 (istanbul) |
| AMPLProxy (token address, zos `AdminUpgradeabilityProxy`) | `0xD46bA6D942050d489DBd938a2C909A5d5039A161` | `0xf74669def838d4f085b394f7892fa8f014fb7ed7558b760b288692b1cc3ca054` | 2,269 B | 26,236,604 | 0.5.3+commit.10d17f24, optimizer off |
| GUSD (token address, `ERC20Proxy`) | `0x056Fd409E1d7A124BD7017459dFEa2F387b6d5Cd` | `0xfd0ab716aa170c34925e0c205ae36765d6f4e7e74d2235f6a365b4ca81e3c8f5` | 3,490 B | 26,236,997 (`0x0889f6b9…`) | 0.4.21+commit.dfe3193c, optimizer 200 |
| GUSDImpl (`ERC20Impl`) | `0x483A1E7F16F46266400f1bAF7abdF445c8D140A2` | `0x5b5d5718eed66700397b9b47da1141322e171501f795c3e7d2f25b7d930c1181` | 12,180 B | 26,236,997 | 0.8.30+commit.73712a01, optimizer 100,000 (shanghai) |
| GUSDStore (`ERC20Store`) | `0xc42B14e49744538e3C239f8ae48A1Eaaf35e68a0` | `0xe768e3d1ee8a04a3b06d8c6ec2c498fb6494c7d50312f9ffb9dcc984143ed775` | 2,026 B | 26,236,997 | 0.4.21+commit.dfe3193c, optimizer 200 |
| YAMV2 (`YAMv2`, 24 decimals) | `0xAba8cAc6866B83Ae4eec97DD07ED254282f6aD8A` | `0xba80d2f3d66c1c11fe204b02db121186e3113415910213bbe355db422dc595b1` | 3,683 B | 26,236,997 | 0.6.12+commit.27d51765, optimizer 50,000 (istanbul) |
| LEND (`EthLendToken`) | `0x80fB784B7eD66730e8b1DBd9820aFD29931aab03` | `0xb9ac5542f3276a4ee6be31d235c3f0736f37c1f0182c4369a07b8de2d1f23f1f` | 6,872 B | 26,236,997 | 0.4.16+commit.d7661dd9, optimizer off |
| ZRX (`ZRXToken`) | `0xE41d2489571d322189246DaFA5ebDe1F4699F498` | `0x44d31e602fd21d6ca2e92923b0a6626c47c1986a92e1abc87bea9ae71e553229` | 2,946 B | 26,236,997 | 0.4.11+commit.68ef5810, optimizer off |

Every Sourcify match above except GUSDImpl's is *partial* (`"match"`: the code equals the
recompilation except the metadata hash in the trailer), so those are not byte-reproducible
from source; GUSDImpl's is exact. The code hash is the pin. `layout-check.txt` (USDT, BNB,
STA, AMPL, GUSD, GUSDImpl, GUSDStore, YAMV2, LEND, ZRX) records the check of the
hand-derived layout against mainnet: every slot of the static layout and mapping rows of
known holders read with `eth_getStorageAt` and compared with the public getters
(`eth_call`) at one block (26,236,515–26,236,568 for the first four, 26,237,004 for the
others; 0 failures; `CMP` rows are packed slots or strings compared by hand). Zero-valued slots (USDT's fee,
pause, deprecation, blacklist; empty allowances) are consistent but not strong evidence;
`difftest` additionally checks each family's getters against the installed `genesis.json`
(packed `paused`/`deprecated`, fee parameters, owners) and the views against slot reads.

Recorded, not targets (read at block 26,236,588): USDC
`0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48` and PAXG `0x45804880De22913dAFE09f4980848ECE6EcbAf78`
(zos-slot proxies; PAXG's current implementation no longer charges a transfer fee). LEND, GUSD
and YAM-V2, recorded here before, are now targets.

AMPL is the one proxied target: the token address holds the proxy, whose storage holds the
token state (`AMPLProxy/genesis.json`: zos implementation slot → the implementation address,
admin `0xAD`, then `UFragments` state), and the implementation's code is installed at its
mainnet address (`AMPL/`, no storage). `difftest` runs it through `DELEGATECALL`.

GUSD is a three-contract token without `DELEGATECALL`: the token address holds `ERC20Proxy`
(0.4.21), which forwards every ERC-20 call by `CALL` to `erc20Impl` with `msg.sender` as an
argument (`transferWithSender` …) and emits the events when the implementation asks it to
(`emitTransfer`/`emitApproval`, implementation only); `ERC20Impl` (0.8.30, deployed at
block 26,155,545 on 2026-10-09: the current implementation is recent) keeps balances, allowances and
the supply in `ERC20Store` (0.4.21) through setters callable by the implementation only.
The implementation's immutables `erc20Proxy` and `erc20Store` are the mainnet addresses, so
all three are installed at their mainnet addresses, each with its own `genesis.json`
(custodian alice everywhere). Sourcify serves the proxy's flattened source under the empty
path `.sol` (`GUSD/source/.sol`, kept as served; `GUSDStore/source/ERC20Store.sol` is the same
file). `requestPrint` and the 0.4.21 `generateLockId` hash `BLOCKHASH(number − 1)`.

**WETH9 reproducibility.** Deployed at block 4,719,568 (tx `0xb9534341…2fa3`). Sourcify's
match is partial (`"match"`): recompiling with 0.4.19 gives the deployed code except the
metadata swarm hash in the 43-byte trailer at offset 3,081, so the deployed bytes cannot be
reproduced exactly from the published source by any compiler; up to the trailer they can,
with solc 0.4.19 (not installed here; the installed 0.4.26 gives different code). The check
is therefore the code hash plus Sourcify's verification, not a local recompilation. Mainnet
slots 0–2 (`name`, `symbol`, `decimals`) equal `genesis.json`.

## Lean API

Namespaces `Examples.Solmate.Contracts.{SolmateAsset, SolmateVault}`,
`Examples.OpenZeppelin.Contracts.{OzAsset, OzVault, OzVaultOffset}` and
`Examples.Solady.Contracts.SoladyToken`, each with `creationCode`,
`constructorArgs`, `runtimeCode` (a literal `ByteArray` that reduces in the kernel),
`address`, `size_runtimeCode`/`size_creationCode`, `selectors`, `events` (topic 0), `errors`,
`storageLayout`, `immutableRefs` and, with immutables, `Immutables`, `deployment`,
`runtimeCodeWith`. Shared: `Examples.Deployment.chainId`, `deployer`;
`EvmLogic.Solidity.slotOf?`, `selector?`, `patchWords`, `eq_of_data_toList_eq` (compare code
in the kernel via `.data.toList`: `ByteArray`'s `DecidableEq` does not reduce well).

Storage slots: Solmate `name 0, symbol 1, totalSupply 2, balanceOf 3, allowance 4, nonces 5`
(vault also `beforeWithdrawHookCalledCounter 6, afterDepositHookCalledCounter 7`);
OpenZeppelin `_balances 0, _allowances 1, _totalSupply 2, _name 3, _symbol 4`. Mappings:
`m[k]` at `keccak(k ‖ slot)`, `allowance[o][s]` at `keccak(s ‖ keccak(o ‖ slot))`. Solady
(no Solidity state): `totalSupply` at `0x05345cdf77eb68f44c`, `balanceOf(o)` at
`keccak(o₂₀ ‖ 0⁸ ‖ 0x87a211a2)`, `allowance(o, s)` at `keccak(o₂₀ ‖ 0⁸ ‖ 0x7f5e9f20 ‖ s₂₀)`,
`nonces(o)` at `keccak(o₂₀ ‖ 0⁸ ‖ 0x38377508)` ([docs/tokens.md](../docs/tokens.md)).

Mainnet modules (`Examples.WETH9.Contracts.WETH9`, `Examples.WeirdERC20.<T>.Contracts.<T>` for
`USDT`, `BNB`, `STA`, `AMPL` (implementation), `YAMV2`, `LEND`, `ZRX`, and
`AMPL.Contracts.AMPLProxy`, `GUSD.Contracts.{GUSD, GUSDImpl, GUSDStore}`)
have `runtimeCode`, `size_runtimeCode`, `address` (mainnet), `codeHash`, `fetchBlock`,
`genesisStorage`, `immutableRefs = []`, `selectors`, `events`, `errors`, `storageLayout`; no
creation code.

## Differential testing

`lake exe difftest [--seed N] [--sequences N] [--length N] [--family NAME[,NAME…]] [--edge]
[--low-gas PCT]`
(`qedefi/Examples/Differential/Main.lean`, run from `qedefi/`, needs anvil) deploys both families
through their creation code in evm-lean (`processMessageCall`, `Crypto.real`, Cancun) and in
anvil, then runs random call sequences from four actors: asset mint/burn/approve/transfer/
transferFrom, donations, vault deposit/mint/withdraw/redeem with third-party owners, share
transfers and approvals, Solmate `permit` with invalid signatures, every view, random
selectors, malformed calldata; amounts include 0, 1, `2²⁵⁶−1` and near-overflow values.
After every call it compares status, return/revert data, logs, receipt `gasUsed` and every
storage slot either side touched, and shrinks mismatches to a minimal sequence.
`--inject-bug` corrupts evm-lean's `deposit` to self-test the comparison.

Families: `solmate`, `oz` (default), `oz3` (OZ vault with δ = 3), and the token families
`oz20`, `solady`, `weth9`, `usdt`, `usdtfee` (fee on in genesis), `bnb`, `sta`, `ampl`, `gusd`
(proxy, implementation and store; calls to all three), `yamv2`, `lend`, `lendico` (LEND with
the ICO reopened: purchases with ether, transfers locked) and `zrx`
(`qedefi/Examples/Differential/Token.lean`); groups `vaults`, `tokens`, `all`. `--edge` makes
the token generators favour extreme amounts (0, 1, `2²⁵⁶ − 1`, `2²⁵⁵`, balance, balance + 1),
self-transfers and address arguments with dirty upper 96 bits; `--low-gas PCT` lowers the
gas limit of `PCT` % of random calls (vaults too): the previous call again with `gasUsed + δ`
(δ ∈ −2…40,000, including 2,300 and the stipend/refund neighbourhood) or the new call with its
intrinsic gas plus at most 60,000, so that out-of-gas hits every depth. `BLOCKHASH(number −
1)` is given to evm-lean as anvil's parent hash (older block hashes are not; no target reads
them). The summary counts, per operation, calls, successes, exceptional halts (failures that
consume the whole gas limit: out of gas, `INVALID`) and calls returning one zero word (ZRX's
`false`). Token families
deploy (compiled) or install (mainnet: code plus `genesis.json` storage, both sides; AMPL as
proxy plus implementation) the token, check its getters against the installed state, run a
fixed scenario of its quirks, check `balanceOf`/`allowance`/`totalSupply` against reads of the
documented slots, and run random sequences over its whole ABI (weighted; ether to payable
functions and fallbacks; ether balances compared for WETH9 and BNB). Details in
[docs/tokens.md](../docs/tokens.md). Result of `lake exe difftest --seed 2026 --family all
--sequences 30 --length 40`: 13,358 transactions (7,924 successful on both sides), **0
mismatches** over all 11 families (510 s).

Campaign of 2026-10-21 (all 16 families, 200 × 50 plus an edge-case pass of 100 × 50 with
`--edge --low-gas 15`, fresh per-family seeds): **240,460 transactions** (144,245 successful on
both sides, 7,486 exceptional halts, 19,842 with lowered gas limits), **0 mismatches**; per
family tables in [docs/tokens.md](../docs/tokens.md#differential-campaign).

A fixed first-depositor scenario runs first (alice deposits 1 wei, donates 10¹⁸, bob
deposits 2·10¹⁸ − 1, alice redeems): both sides agree; on Solmate alice ends with
1.5·10¹⁸ (bob holds 1 share), on OpenZeppelin with 0.6·10¹⁸ (bob holds 3 shares).

Result of `lake exe difftest --seed 2026 --sequences 200 --length 50`: **20,008
transactions** (11,400 successful on both sides), **0 mismatches**, for both families;
deployments from both deployers agree on code, storage and gas (651 s, dominated by JSON-RPC
round trips).

## a16z ERC-4626 property suite

`contracts/run-a16z.sh` fetches the pinned forge-std and erc4626-tests into `ext/` and runs
`a16z/ERC4626Std.t.sol` (profile `a16z`, 1,000 fuzz runs, seed `0x4626`) against both
targets (it tests the contracts, not evm-lean):

| Target | Result |
|---|---|
| Solmate (`_vaultMayBeEmpty = false`, `_unlimitedAmount = false`) | 25 / 26; **`test_maxWithdraw` fails** |
| OpenZeppelin (`_vaultMayBeEmpty = true`, `_unlimitedAmount = true`) | 26 / 26 |

The Solmate failure is a genuine deviation from EIP-4626 ("`maxWithdraw` MUST NOT revert"):
`maxWithdraw(owner) = convertToAssets(balanceOf[owner])`, and `mulDivDown` reverts when
`shares · totalAssets ≥ 2²⁵⁶` (e.g. an owner with ~4.3·10⁶⁵ shares). `convertToAssets`,
`previewRedeem`, `convertToShares`, `previewDeposit` and the corresponding `deposit`/`redeem`
paths revert the same way; the model makes these operations partial accordingly
(`QEDefi.ERC4626.Solmate.maxWithdraw_reverts_of_overflow`).
