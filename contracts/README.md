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

| Time target | Source |
|---|---|
| `VestingWallet` | OpenZeppelin `finance/VestingWallet.sol` (vendored, unmodified): linear vesting of ETH and ERC-20 balances by `block.timestamp` ([proofs](../qedefi/Examples/Time/)) |

| Proxy target | Kind | Source |
|---|---|---|
| `OzTransparentProxy` | compiled | OpenZeppelin `TransparentUpgradeableProxy` (vendored, unmodified); immutable `_admin` |
| `OzProxyAdmin` | compiled | OpenZeppelin `ProxyAdmin` (vendored, unmodified; `Ownable`), deployed by the proxy's constructor |
| `ActorImpl` | compiled | `src/ActorImpl.sol`: `uint256 public value` (slot 0) and an unrestricted `set(uint256)`; the proxy's implementation |

| Multisig target | Kind | Source |
|---|---|---|
| `MiniSafe` | compiled | `src/MiniSafe.sol`: a minimal Safe-style threshold multisig (owners, threshold, nonce; ECDSA `checkNSignatures`), the owner of the ProxyAdmin in `qedefi/Examples/Actor/Bytecode/SafeGuard.lean` |

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
import closure of OpenZeppelin's `ERC4626`, `ERC20Mock`, `VestingWallet`,
`proxy/transparent/TransparentUpgradeableProxy` and `proxy/transparent/ProxyAdmin`; Solady's
`ERC20` (no imports).
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
| `VestingWallet` | 2,264 B | 2,608 B |
| `ActorImpl` | 116 B | 142 B |
| `OzTransparentProxy` (`TransparentUpgradeableProxy`) | 1,005 B | 3,339 B (embeds `ProxyAdmin`'s) |
| `OzProxyAdmin` (`ProxyAdmin`) | 964 B | 1,200 B |
| `MiniSafe` | 1,303 B | 1,921 B |

## Canonical deployment

Each family is deployed on its own fresh chain (chain id 1, Cancun) by
`0x1000000000000000000000000000000000000000`: asset at nonce 0, vault at nonce 1; the OZ
δ = 3 family likewise (`OzVaultOffset` at the vault address), `SoladyToken` alone at nonce 0
(the asset address), `VestingWallet` alone at nonce 0 (the asset address) with beneficiary
`0x2000000000000000000000000000000000000000`, start `1700000000`, duration `31536000` (one
year). The proxy family: `ActorImpl` at nonce 0 (the asset address), then
`TransparentUpgradeableProxy(ActorImpl, initialOwner, set(1))` at nonce 1 (the vault address);
its constructor deploys the `ProxyAdmin` (owner `initialOwner`) by `CREATE` from the proxy at
the proxy's nonce 1, stores it in the immutable `_admin` and the ERC-1967 admin slot, and
delegatecalls `set(1)` into the implementation (OpenZeppelin v5.7.0's `ERC1967Proxy` reverts
with `ERC1967ProxyUninitialized` on empty data). The script checks the ProxyAdmin's address
against the admin slot, the `CREATE` address and the immutable, the implementation slot, the
proxy's slot 0 (`value = 1`) and `owner()`. `MiniSafe` alone on a fresh chain at nonce 0 (the
asset address), constructed with owners alice, bob and carol and threshold 2; the script checks
`threshold()`, `nonce()` and `isOwner` of each.

| | Address | Constructor arguments |
|---|---|---|
| asset | `0x13136008B64FF592819B2FA6d43F2835C452020e` | Solmate `("Solmate Asset", "SAST", 18)`; OZ none (`"ERC20Mock"`, `"E20M"`, 18 decimals) |
| vault | `0x7c5a2c91b22d7A9226523D4Ba717DB6afB741ebd` | Solmate `(asset, "Solmate Vault", "svSAST")`; OZ `(asset)` (`"OZ Vault"`, `"ozVLT"`) |
| `ActorImpl` | `0x13136008B64FF592819B2FA6d43F2835C452020e` | none |
| `OzTransparentProxy` | `0x7c5a2c91b22d7A9226523D4Ba717DB6afB741ebd` | `(ActorImpl, initialOwner, set(1))`, data `0x60fe47b1 ‖ 1` |
| `OzProxyAdmin` | `0x1FA0a9a904481F866eF5EfDa01f2c8F4B8090c1A` | `(initialOwner)`, passed by the proxy's constructor |
| `initialOwner` | `0x00000000000000000000000000000000000A11cE` | alice (`0xA11CE`, as in `difftest`), owner of the ProxyAdmin |
| `MiniSafe` | `0x13136008B64FF592819B2FA6d43F2835C452020e` | `([0xA11CE, 0xB0B, 0xCA401], 2)` |

ERC-1967 slots (`keccak256("eip1967.proxy.<name>") − 1`, checked against the vendored
`ERC1967Utils.sol`): implementation
`0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc`, admin
`0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103`, beacon (unused)
`0xa3f0ad74e5423aebfd80d3ef4346578335a9a72aeaee59ff6cb3582b35133d50`.

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
| VestingWallet | `_start` | 1198 | 1700000000 |
| | `_duration` | 295, 1236, 1458 | 31536000 |
| OzTransparentProxy | `_admin` | 16 | ProxyAdmin address `0x1FA0a9a9…8090c1A` |

`SoladyToken`, `OzAsset`, `ActorImpl` and `OzProxyAdmin` have no immutables. Mainnet code
carries its immutables as deployed; the Aave V3 targets record their names, offsets and values
([Aave V3](#aave-v3)).

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
checks the code against Sourcify's on-chain bytecode. A contract Sourcify does not have is taken
from Blockscout (`eth.blockscout.com`): `blockscout.json` instead of `sourcify.json`, checked
against Blockscout's deployed bytecode. Hand-written: `storageLayout.json`
(solc's format; derived from the source by C3 linearization and checked against mainnet
storage) and `genesis.json` (the storage the tests install with the code: the constructor's
state with test parameters; entries are a literal `slot` or a `mapping` slot with `keys`).
`scripts/build-contracts.sh` is offline for these: it checks `keccak(runtime.hex)` against
`meta.json`, derives `methodIdentifiers.json`, `events.json`, `errors.json` from the ABI,
checks that every selector is pushed by the dispatcher, and generates the Lean module.
Optional hand-written inputs: `immutables.json` (AST id → name of each immutable; offsets come
from Sourcify's transformations, values from the code: `immutableRefs`, `immutableValues`),
`links.json` (linked libraries when Sourcify's transformations are missing; otherwise taken from
them: `linkedLibraries`) and `librarySelectors.json` (selectors of library functions with
storage-pointer parameters, which are not in the ABI; copied from solc's `methodIdentifiers`
and merged into `methodIdentifiers.json`).

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
| SafeSingleton (Safe v1.5.0 `Safe`) | `0xFf51A5898e281Db6DfC7855790607438dF2ca44b` | `0xdda019cbd7c867a533a2a86e5c53434fdc50b13122b5a5ddb4a8df61b31c20f2` | 21,451 B | 26,255,445 (`0xf73b7eea…`) | 0.7.6+commit.7338295f, optimizer off |
| SafeProxy (a Safe v1.5.0 proxy) | `0xeD921313b818dc96d3Af083Ac54321ea628D34AF` | `0x4e381985ca68b3e5d27b4425fa581c19cf33146d3f887a3cfca96f55528ea46f` | 123 B | 26,255,445 | 0.7.6+commit.7338295f, optimizer off |

The two Safe v1.5.0 targets are also reproduced from source: `build-contracts.sh` compiles
`safe-global/safe-smart-account` tag `v1.5.0` (`source/`) with its pinned settings (solc
0.7.6, optimizer off, Istanbul) and checks the runtime code byte for byte, metadata included
(`REPRODUCE`; `mainnet/SafeProxy/notes.md` explains why the proxy's source is the tag's file).
They are used by `qedefi/Examples/Safe/Bytecode/` (the upgrade guard with a Safe owner).

Every Sourcify match above except GUSDImpl's and SafeSingleton's is *partial* (`"match"`: the
code equals the recompilation except the metadata hash in the trailer), so those are not
byte-reproducible from Sourcify's sources (SafeProxy is, from the tag's file, above);
GUSDImpl's and SafeSingleton's are exact. The code hash is the pin. `layout-check.txt` (USDT, BNB,
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
(zos-slot proxies; PAXG's current implementation no longer charges a transfer fee).

AMPL is the one proxied target: the token address holds the proxy, whose storage holds the
token state (`AMPLProxy/genesis.json`: zos implementation slot → the implementation address,
admin `0xAD`, then `UFragments` state), and the implementation's code is installed at its
mainnet address (`AMPL/`, no storage). `difftest` runs it through `DELEGATECALL`.

GUSD is a three-contract token without `DELEGATECALL`: the token address holds `ERC20Proxy`
(0.4.21), which forwards every ERC-20 call by `CALL` to `erc20Impl` with `msg.sender` as an
argument (`transferWithSender` …) and emits the events when the implementation asks it to
(`emitTransfer`/`emitApproval`, implementation only); `ERC20Impl` (0.8.30, deployed at
block 26,155,545) keeps balances, allowances and
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
with solc 0.4.19 (0.4.26 gives different code). The check
is therefore the code hash plus Sourcify's verification, not a local recompilation. Mainnet
slots 0–2 (`name`, `symbol`, `decimals`) equal `genesis.json`.

## Aave V3

Aave V3's Ethereum Core market (WETH reserve), as deployed; facts, immutables, libraries and
storage in [docs/aave-v3.md](../docs/aave-v3.md). Modules
`Examples.AaveV3.Contracts.<Name>` (`qedefi/Examples/AaveV3/Contracts/`).

| Name | Address | Code hash | Size | Read at block | Compiler (mainnet) | Verification |
|---|---|---|---|---|---|---|
| AToken (`ATokenInstance`, rev. 5) | `0xadC45Df3cf1584624C97338BEF33363BF5b97AdA` | `0x3bd38f9cd664b4169375c69f362dc585ed97adf6da6f8b6d5569ecb8690d9eb5` | 10,477 B | 26,243,038 | 0.8.27+commit.40a35a09, optimizer 200 (cancun) | Sourcify `match` |
| ATokenProxy (aEthWETH) | `0x4d5F47FA6A74757f35C14fD3a6Ef8E3C9BC514E8` | `0x82c6d153799b3226525e3b7ec27b843ef44c5f6bca21fcf8b3c80db61ba64881` | 2,400 B | 26,243,038 | 0.8.10+commit.fc410830, optimizer 100,000 (berlin) | Sourcify `exact_match` |
| VariableDebtToken (`VariableDebtTokenInstance`, rev. 5) | `0xb27C52c7f84819e3157993489741cB60786aE330` | `0xb17b28c6f03e856dc7dd8ffbfc05a1643797cf20343ca511b4e6064236f38033` | 7,198 B | 26,243,038 | 0.8.27+commit.40a35a09, optimizer 200 (cancun) | Sourcify `match` |
| VariableDebtTokenProxy (variableDebtEthWETH) | `0xeA51d7853EEFb32b6ee06b1C12E6dcCA88Be0fFE` | `0x82c6d153799b3226525e3b7ec27b843ef44c5f6bca21fcf8b3c80db61ba64881` | 2,400 B | 26,243,038 | 0.8.10+commit.fc410830, optimizer 100,000 (berlin) | Sourcify `exact_match` |
| Pool (`PoolInstance`, rev. 11) | `0x728a138A4823392C2EFA55e028d434F526fE03CF` | `0x530cdbba5eb9487cd5d041bb74b7a1936ad3230bf9e361893ecd025373c7fbe5` | 21,146 B | 26,243,038 | 0.8.27+commit.40a35a09, optimizer 200 (cancun) | Sourcify `match` |
| PoolProxy | `0x87870Bca3F3fD6335C3F4ce8392D69350B4fA4E2` | `0x96107dc4006b4c7fecd1827cfb275ffeef31e6194cd50466f85f8eb24ccf2679` | 2,400 B | 26,243,038 | 0.8.10+commit.fc410830, optimizer 100,000 (berlin) | Sourcify `exact_match` |
| InterestRateStrategy (`DefaultReserveInterestRateStrategyV2`) | `0x9ec6F08190DeA04A54f8Afc53Db96134e5E3FdFB` | `0x1dc68bd8ed7951a5b2b72ebc76e0dea1878e6aca2dec51213ace96ca615d53b4` | 4,038 B | 26,243,038 | 0.8.20+commit.a1b79de6, optimizer 200 (shanghai) | Sourcify `exact_match` |
| PoolLogic (library) | `0xD70593841C57cbaA04957cc3EAcE95708e48853b` | `0x0fe8b38a44e9cb253e9e8c1abb79beb4ac2aae00dedaf4207a3215eeab678cee` | 7,311 B | 26,243,038 | 0.8.27+commit.40a35a09, optimizer 200 (shanghai) | Sourcify `match` |
| SupplyLogic (library) | `0x584C7d8c4cb05304FE5Ac7fbc97f20A10Fb07564` | `0xd7a886e7fff585881ef03af514c58a96b9c188f9502bc0d0a49fb472cd2eee6e` | 10,302 B | 26,243,038 | 0.8.27+commit.40a35a09, optimizer 200 (shanghai) | Sourcify `match` |
| BorrowLogic (library) | `0x52Da0ce88202D1542543598D1e1e27F0d344726A` | `0xdb9bb1c68eae0ef32f1653dc1bbb7b7ac50636d2e090a5d8d8056c62367a18d2` | 9,587 B | 26,243,058 | 0.8.27+commit.40a35a09, optimizer 200 (shanghai) | Blockscout (partial; not on Sourcify) |
| FlashLoanLogic (library) | `0x6D414cd0d5eAf8C43200ac0c325A7E2Ad83B8be6` | `0x1edf7521bf3ca547c4f0efdee102d98b23adc7618467417d4fa1a02a20990adb` | 8,227 B | 26,243,059 | 0.8.27+commit.40a35a09, optimizer 200 (shanghai) | Blockscout (partial; not on Sourcify) |
| LiquidationLogic (library) | `0x96D5686812e33Ab509ECCDb38C89d15607B2a413` | `0xef11fa2346ecdfa4640a056724ccd69dbd709dfda916a60afb5e669c345ae0c4` | 12,101 B | 26,243,039 | 0.8.27+commit.40a35a09, optimizer 200 (shanghai) | Sourcify `match` |

All are below the 24,576-byte limit. Despite Sourcify's partial `match`, every target is
reproduced byte for byte by recompiling the verified standard-JSON input locally (up to
immutables, library links and call protection, which then equal the deployed bytes; checked
once, not part of the build). `layout-check.txt` (AToken, VariableDebtToken and Pool against
the state of their proxies, the strategy, the three proxies) at block 26,243,102: 0 failures.
The token and Pool states live in the proxies' storage; `genesis.json` of `ATokenProxy`,
`VariableDebtTokenProxy` and `PoolProxy` set the EIP-1967 implementation slot and the
initialized state (test balances for the aToken; no Pool reserves).

## Lean API

Namespaces `Examples.Solmate.Contracts.{SolmateAsset, SolmateVault}`,
`Examples.OpenZeppelin.Contracts.{OzAsset, OzVault, OzVaultOffset, OzTransparentProxy,
OzProxyAdmin, ActorImpl}` and
`Examples.Solady.Contracts.SoladyToken`, each with `creationCode`,
`constructorArgs`, `runtimeCode` (a literal `ByteArray` that reduces in the kernel),
`address`, `size_runtimeCode`/`size_creationCode`, `selectors`, `events` (topic 0), `errors`,
`storageLayout`, `immutableRefs` and, with immutables, `Immutables`, `deployment`,
`runtimeCodeWith`. The proxy family also has `OzTransparentProxy.{implementationSlot,
adminSlot, beaconSlot, implementation, initialOwner, proxyAdmin, initData}`,
`OzProxyAdmin.{initialOwner, proxy, ownerSlot}` and `ActorImpl.{proxy, valueSlot}`. Shared:
`Examples.Deployment.chainId`, `deployer`;
`EvmLogic.Solidity.slotOf?`, `selector?`, `patchWords`, `eq_of_data_toList_eq` (compare code
in the kernel via `.data.toList`: `ByteArray`'s `DecidableEq` does not reduce well).

Storage slots: Solmate `name 0, symbol 1, totalSupply 2, balanceOf 3, allowance 4, nonces 5`
(vault also `beforeWithdrawHookCalledCounter 6, afterDepositHookCalledCounter 7`);
OpenZeppelin `_balances 0, _allowances 1, _totalSupply 2, _name 3, _symbol 4`; `ProxyAdmin`
`_owner 0`; `ActorImpl` `value 0` (in the proxy's storage when called through it; the proxy
itself has no Solidity state, only the ERC-1967 slots). Mappings:
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

## Snapshots

A snapshot is a deployed system at one pinned block, fetched once and used offline: the code,
the verified sources and the part of the chain state that a set of calls reads, as an
`EvmLean.World` with its block environment. `snapshots/<Name>/targets.json` (hand-written)
names the chain, the contracts and optional extra calls; the block is pinned at fetch time
unless given.

```bash
lake exe snapshot fetch contracts/snapshots/<Name>                 # network, read-only
lake exe snapshot check contracts/snapshots/<Name> [--verbose]     # offline
```

`fetch` (any JSON-RPC archive endpoint via `--rpc URL`, or Alchemy with `ALCHEMY_KEY` from the
environment or from a gitignored `.env` in the working directory; the URL is never printed or
saved) uses only `eth_get*`/`eth_call`, no `debug_*` tracing; requests a rate-limited endpoint
refuses (HTTP/JSON-RPC 429, empty answers) are resent after a growing pause. The state
is found with the Lean interpreter as the tracer: seed calls (the given ones, plus every
argument-free view of each target and of its EIP-1967/ZeppelinOS/beacon implementation) run
on the state fetched so far, `Snapshot.runObserved` records every account, slot and
`BLOCKHASH` they read (reverted frames included), the reads the snapshot does not determine
are fetched at the pinned block, and this repeats until nothing new is read (seeds that read
nothing new are not rerun; each round follows reads one hop deeper, so a loop over reserves
behind oracle adapters behind feeds takes hundreds of rounds: `"maxRounds"`, default 256).
Sources come from Sourcify, else the chain's public Blockscout, for every contract read (paths
sanitized; a failing provider only loses those sources). It writes:

| File | Contents |
|---|---|
| `state.json` | chain id, block and hash, fork, block environment, accounts (nonce, balance, code hash, every fetched slot, zeros included) |
| `code/<keccak>.hex` | runtime code by hash; `check` rehashes every file |
| `calls.json` | the seed calls with the node's `eth_call` result at the block |
| `contracts/<address>/` | `source/`, `abi.json`, `verification.json` (provider, name, compiler, settings) |
| `meta.json` | summary: counts, discovery rounds, verified contracts, RPC host |
| `sequence.json` | `snapshot fork` only: the node's record of the transaction sequence |

`check` replays every recorded call in the interpreter: it passes iff the call reads only
state the snapshot determines and returns exactly the node's success flag and output bytes.
Lean code loads a snapshot with `Snapshot.State.load` (`State.world`, `State.context`) and runs
calls with `Snapshot.simulate`, which also returns the reads, so a run that leaves the snapshot
is detected (`State.missing`) instead of reading zeros. The fork comes from the timestamp on
Ethereum mainnet and must be set in `targets.json` elsewhere (L2-specific EVM behaviour is not
modelled).

Only `targets.json` is committed: the fetched files carry third-party sources and chain state, and
are gitignored. Tested on:

| Snapshot | Chain | Block | Accounts | Slots | Calls reproduced |
|---|---|---|---|---|---|
| Strata's USDe market (tranches, CDO, accounting, strategy, APR feed, cooldowns) | 1 | 26,239,549 | 27 | 160 | 162 / 162 |
| USDC on Base (proxy and implementation) | 8453 | 52,889,654 | 3 | 15 | 19 / 19 |
| `AaveV3`: Aave V3 Core market (Pool rev. 11, see below) | 1 | 26,243,000 | 198 | 789 | 364 / 364, sequence 25 / 25 |

### Aave V3 and the anvil fork differential

`snapshots/AaveV3/targets.json` (committed) names the PoolAddressesProvider
`0x2f39…4E9e`, Pool `0x8787…A4E2` (`PoolInstance`, `POOL_REVISION` 11), PoolConfigurator,
ACLManager, AaveOracle, AaveProtocolDataProvider, the shared interest-rate strategy
(`DefaultReserveInterestRateStrategyV2`), WETH, USDC and wstETH with their aTokens and variable
debt tokens (revision 5), and the price sources the oracle uses for them (Chainlink ETH/USD
and USDC/USD `EACAggregatorProxy` over `DualAggregator`s, the USDC and wstETH price-cap
adapters). 108 seed calls (reserve data, normalized income and debt, configurations, oracle
prices, data-provider views, `calculateInterestRates`, aToken and debt-token balances and
scaled balances, `getUserAccountData` of four large positions found from recent `Borrow`/
`Supply` logs) plus 256 argument-free views. The four positions hold collateral in many
reserves, so the reads reach 190 accounts (118 codes, 188 verified contracts) in 197 rounds
(about 4 minutes on Alchemy's free tier, mostly sources). All 364 calls reproduce `eth_call`.

`targets.json` may also hold a `sequence` of state-changing steps (`Snapshot/Sequence.lean`):
transactions, and the cheats anvil offers (`setBalance`, `setCode`, `setStorage`,
`increaseTime`).

```bash
lake exe snapshot fork contracts/snapshots/<Name> [--rpc URL] [--anvil URL | --port N]   # network, anvil
lake exe snapshot check contracts/snapshots/<Name>                                     # offline, includes the sequence
```

`fork` (`Snapshot/Fork.lean`) starts anvil forked from the same RPC at the snapshot block
(the URL reaches anvil through the environment, via an RPC alias in `<dir>/anvil/foundry.toml`,
never as an argument; `--hardfork` from the snapshot, base fee and gas price 0, any sender
impersonated, blocks 12 s apart so runs are reproducible) and runs the steps there, one block
per transaction; it then runs them in the interpreter from the snapshot state, each
transaction in the environment of the block anvil mined it in, processed as `Tx.process`
does at gas price zero (refund cap, EIP-7623 floor), fetching at the snapshot block whatever
the runs read and the snapshot lacks (as `fetch` does, so the saved snapshot covers the
sequence; a slot written and later read is fetched too, as its original value). For each
transaction it records anvil's status, return or revert data (`callTracer`), logs, receipt
`gasUsed`, and, read back from anvil at that block, the balance and nonce of every account
and the value of every slot either side touched (the interpreter's reads, anvil's
`prestateTracer` diff) into `sequence.json`, then compares; a slot or account the
interpreter changed that the record lacks is a difference. `check` replays the record offline.

The AaveV3 sequence: three fresh accounts get 100 ether; A wraps and supplies 10 WETH and
borrows 5,000 USDC; C supplies 10 WETH and borrows 19,000 USDC (health factor 1.09); L
supplies 50 WETH, borrows 20,000 USDC and approves the Pool; 30 days pass; A approves, repays
2,500 USDC and withdraws 2 WETH; C's borrow of 10,000 more reverts (`0x6679996d`) and a
liquidation of the healthy C reverts (`0x930bb771`); the ETH/USD feed's code is replaced by a
constant 2,200 USD answer; L liquidates 5,000 USDC of C's debt for WETH and 2,000 for aWETH;
L's `repay(USDC, max)` reverts inside USDC (`Error(string)`); `getUserAccountData(C)` as a
transaction. Result: **25 / 25 steps identical** (22 transactions: status, return/revert
data, all 79 logs, 518 slots and 253 balances/nonces compared, `gasUsed` equal to the unit
for every transaction), 11 s per run; the record is identical across runs. Corrupting one
recorded timestamp makes the following transactions mismatch (status, output, storage, gas).

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
[docs/tokens.md](../docs/tokens.md#differential-testing).

Over all 16 families, 200 sequences of 50 calls with `--low-gas 5`, then 100 of 50 with
`--edge --low-gas 15` (per-family seeds, each run reproducible with `lake exe difftest --seed S --family F`): **240,460
transactions** (144,245 successful on both sides, 7,486 exceptional halts, 19,842 with lowered
gas limits), **0 mismatches**. The vault families also check that deployments from two
deployers agree on code, storage and gas.

A fixed first-depositor scenario runs first (alice deposits 1 wei, donates 10¹⁸, bob
deposits 2·10¹⁸ − 1, alice redeems): both sides agree; on Solmate alice ends with
1.5·10¹⁸ (bob holds 1 share), on OpenZeppelin with 0.6·10¹⁸ (bob holds 3 shares).

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
