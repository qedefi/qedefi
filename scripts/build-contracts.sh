#!/usr/bin/env bash
# Build the verification targets with the pinned compiler, extract their artifacts and
# generate the Lean constants in qedefi/Verified/<Project>/Contracts/ (the reentrancy
# demonstrators: qedefi/Examples/Reentrancy/Contracts/). Two kinds of target:
#   compiled  Solidity sources under contracts/ (forge, solc 0.8.28), deployed on anvil;
#   mainnet   deployed mainnet bytecode pinned in contracts/mainnet/<Name>/ (fetched once by
#             scripts/fetch-mainnet.sh; this script is offline and checks the code hash).
#
#   scripts/build-contracts.sh            # rebuild artifacts and Lean files
#   scripts/build-contracts.sh --check    # rebuild and fail if anything committed changed
#
# Requires: Foundry (forge, cast, anvil) and solc 0.8.28 in the svm layout (~/.svm/0.8.28),
# jq. Outputs (all committed):
#   contracts/artifacts/<Name>/{creation.hex, constructorArgs.hex, runtime.template.hex,
#     runtime.hex, abi.json, methodIdentifiers.json, events.json, errors.json,
#     storageLayout.json, immutableReferences.json}
#   contracts/artifacts/deployment.json
#   contracts/mainnet/<Name>/{methodIdentifiers.json, events.json, errors.json}
#   qedefi/Verified/Solmate/Contracts/{SolmateAsset,SolmateVault}{,Data}.lean
#   qedefi/Verified/OpenZeppelin/Contracts/{OzAsset,OzVault,OzVaultOffset}{,Data}.lean
#   qedefi/Verified/OpenZeppelin/Contracts/{OzTransparentProxy,OzProxyAdmin,ActorImpl}{,Data}.lean
#   qedefi/Verified/Safe/Contracts/MiniSafe{,Data}.lean
#   qedefi/Verified/Solady/Contracts/SoladyToken{,Data}.lean
#   qedefi/Verified/OpenZeppelin/Contracts/VestingWallet{,Data}.lean
#   qedefi/Examples/Reentrancy/Contracts/{VulnerableBank,CEIBank,GuardedBank,Attacker}{,Data}.lean
#     (<Name>Data.lean: bytes, immutables, selectors, layout; <Name>.lean: the code facts and
#     the kernel code table)
#   qedefi/Verified/<Project>/Contracts/<Name>.lean for each mainnet target (MAINNET below)
#
# Immutables. solc emits the runtime code with zero placeholders where immutables go
# (`runtime.template.hex`, positions in `immutableReferences.json`); the constructor fills
# them in. The canonical runtime code (`runtime.hex`, `runtimeCode` in Lean) is the code
# actually deployed by the creation code with the canonical parameters below, obtained from
# anvil; the script checks that it differs from the template only at the immutable
# positions.
set -euo pipefail
export PATH="$HOME/.foundry/bin:$PATH"
cd "$(dirname "$0")/.."
ROOT=$(pwd)
C="$ROOT/contracts"
ART="$C/artifacts"
CHECK=0
[ "${1:-}" = "--check" ] && CHECK=1

# ---------------------------------------------------------------- canonical deployment
CHAIN_ID=1
DEPLOYER=0x1000000000000000000000000000000000000000
SOLMATE_ASSET_ARGS=("constructor(string,string,uint8)" "Solmate Asset" "SAST" 18)
SOLMATE_VAULT_NAME="Solmate Vault"
SOLMATE_VAULT_SYMBOL="svSAST"
# OpenZeppelin `VestingWallet(beneficiary, startTimestamp, durationSeconds)`.
VESTING_ARGS=("constructor(address,uint64,uint64)" 0x2000000000000000000000000000000000000000 1700000000 31536000)
# OpenZeppelin transparent proxy: `TransparentUpgradeableProxy(ActorImpl, PROXY_OWNER,
# set(PROXY_INIT_VALUE))`. The owner of the ProxyAdmin the constructor deploys is alice of the
# differential tester (`0xA11CE`). v5.7.0's `ERC1967Proxy` reverts on empty `_data`
# (`ERC1967ProxyUninitialized`), so the proxy is initialised by delegatecalling `set(1)`.
PROXY_OWNER=0x00000000000000000000000000000000000A11CE
PROXY_INIT_VALUE=1
# ERC-1967 slots (`bytes32(uint256(keccak256("eip1967.proxy.<name>")) - 1)`), checked against
# the vendored `ERC1967Utils.sol` below.
ERC1967_IMPLEMENTATION_SLOT=0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc
ERC1967_ADMIN_SLOT=0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103
ERC1967_BEACON_SLOT=0xa3f0ad74e5423aebfd80d3ef4346578335a9a72aeaee59ff6cb3582b35133d50
# MiniSafe (threshold multisig): `MiniSafe(MINISAFE_OWNERS, MINISAFE_THRESHOLD)`, owners alice,
# bob and carol of the differential tester.
MINISAFE_OWNERS="[0x00000000000000000000000000000000000A11CE,0x0000000000000000000000000000000000000B0B,0x00000000000000000000000000000000000CA401]"
MINISAFE_THRESHOLD=2

SOLC="$HOME/.svm/0.8.28/solc-0.8.28"
"$SOLC" --version | grep -q '0.8.28+commit.7893614a' || { echo "error: need solc 0.8.28 at $SOLC" >&2; exit 1; }

( cd "$C" && forge build --force >/dev/null )

# Artifact path and contract name of each target.
declare -A SRC=(
  [SolmateAsset]="out/MockERC20.sol/MockERC20.json"
  [SolmateVault]="out/MockERC4626.sol/MockERC4626.json"
  [OzAsset]="out/ERC20Mock.sol/ERC20Mock.json"
  [OzVault]="out/OzVault.sol/OzVault.json"
  [OzVaultOffset]="out/OzVaultOffset.sol/OzVaultOffset.json"
  [SoladyToken]="out/SoladyToken.sol/SoladyToken.json"
  [VestingWallet]="out/VestingWallet.sol/VestingWallet.json"
  [VulnerableBank]="out/Banks.sol/VulnerableBank.json"
  [CEIBank]="out/Banks.sol/CEIBank.json"
  [GuardedBank]="out/Banks.sol/GuardedBank.json"
  [Attacker]="out/Banks.sol/Attacker.json"
  [OnceAttacker]="out/Banks.sol/OnceAttacker.json"
  [ActorImpl]="out/ActorImpl.sol/ActorImpl.json"
  [OzTransparentProxy]="out/TransparentUpgradeableProxy.sol/TransparentUpgradeableProxy.json"
  [OzProxyAdmin]="out/ProxyAdmin.sol/ProxyAdmin.json"
  [MiniSafe]="out/MiniSafe.sol/MiniSafe.json"
)
declare -A SOLNAME=(
  [SolmateAsset]="lib/solmate/src/test/utils/mocks/MockERC20.sol:MockERC20"
  [SolmateVault]="lib/solmate/src/test/utils/mocks/MockERC4626.sol:MockERC4626"
  [OzAsset]="lib/openzeppelin-contracts/contracts/mocks/token/ERC20Mock.sol:ERC20Mock"
  [OzVault]="src/OzVault.sol:OzVault"
  [OzVaultOffset]="src/OzVaultOffset.sol:OzVaultOffset"
  [SoladyToken]="src/SoladyToken.sol:SoladyToken"
  [VestingWallet]="lib/openzeppelin-contracts/contracts/finance/VestingWallet.sol:VestingWallet"
  [VulnerableBank]="src/reentrancy/Banks.sol:VulnerableBank"
  [CEIBank]="src/reentrancy/Banks.sol:CEIBank"
  [GuardedBank]="src/reentrancy/Banks.sol:GuardedBank"
  [Attacker]="src/reentrancy/Banks.sol:Attacker"
  [OnceAttacker]="src/reentrancy/Banks.sol:OnceAttacker"
  [ActorImpl]="src/ActorImpl.sol:ActorImpl"
  [OzTransparentProxy]="lib/openzeppelin-contracts/contracts/proxy/transparent/TransparentUpgradeableProxy.sol:TransparentUpgradeableProxy"
  [OzProxyAdmin]="lib/openzeppelin-contracts/contracts/proxy/transparent/ProxyAdmin.sol:ProxyAdmin"
  [MiniSafe]="src/MiniSafe.sol:MiniSafe"
)
TARGETS=(SolmateAsset SolmateVault OzAsset OzVault OzVaultOffset SoladyToken
  VulnerableBank CEIBank GuardedBank Attacker OnceAttacker VestingWallet
  ActorImpl OzTransparentProxy OzProxyAdmin MiniSafe)
REENTRANCY=(VulnerableBank CEIBank GuardedBank Attacker OnceAttacker)
# Directory of each generated Lean module.
# Lean namespace prefix of each generated module (mirrors its directory).
declare -A LEANNS=(
  [SolmateAsset]="Verified.Solmate.Contracts"
  [SolmateVault]="Verified.Solmate.Contracts"
  [OzAsset]="Verified.OpenZeppelin.Contracts"
  [OzVault]="Verified.OpenZeppelin.Contracts"
  [OzVaultOffset]="Verified.OpenZeppelin.Contracts"
  [SoladyToken]="Verified.Solady.Contracts"
  [VestingWallet]="Verified.OpenZeppelin.Contracts"
  [VulnerableBank]="Examples.Reentrancy.Contracts"
  [CEIBank]="Examples.Reentrancy.Contracts"
  [GuardedBank]="Examples.Reentrancy.Contracts"
  [Attacker]="Examples.Reentrancy.Contracts"
  [OnceAttacker]="Examples.Reentrancy.Contracts"
  [ActorImpl]="Verified.OpenZeppelin.Contracts"
  [OzTransparentProxy]="Verified.OpenZeppelin.Contracts"
  [OzProxyAdmin]="Verified.OpenZeppelin.Contracts"
  [MiniSafe]="Verified.Safe.Contracts"
)
declare -A LEANDIR=(
  [SolmateAsset]="$ROOT/qedefi/Verified/Solmate/Contracts"
  [SolmateVault]="$ROOT/qedefi/Verified/Solmate/Contracts"
  [OzAsset]="$ROOT/qedefi/Verified/OpenZeppelin/Contracts"
  [OzVault]="$ROOT/qedefi/Verified/OpenZeppelin/Contracts"
  [OzVaultOffset]="$ROOT/qedefi/Verified/OpenZeppelin/Contracts"
  [SoladyToken]="$ROOT/qedefi/Verified/Solady/Contracts"
  [VestingWallet]="$ROOT/qedefi/Verified/OpenZeppelin/Contracts"
  [VulnerableBank]="$ROOT/qedefi/Examples/Reentrancy/Contracts"
  [CEIBank]="$ROOT/qedefi/Examples/Reentrancy/Contracts"
  [GuardedBank]="$ROOT/qedefi/Examples/Reentrancy/Contracts"
  [Attacker]="$ROOT/qedefi/Examples/Reentrancy/Contracts"
  [OnceAttacker]="$ROOT/qedefi/Examples/Reentrancy/Contracts"
  [ActorImpl]="$ROOT/qedefi/Verified/OpenZeppelin/Contracts"
  [OzTransparentProxy]="$ROOT/qedefi/Verified/OpenZeppelin/Contracts"
  [OzProxyAdmin]="$ROOT/qedefi/Verified/OpenZeppelin/Contracts"
  [MiniSafe]="$ROOT/qedefi/Verified/Safe/Contracts"
)

# Mainnet targets: contracts/mainnet/<Name>/ and the Lean namespace of the generated module
# (its directory mirrors the namespace).
MAINNET=(WETH9 USDT BNB STA AMPL AMPLProxy GUSD GUSDImpl GUSDStore YAMV2 LEND ZRX SafeSingleton
  SafeProxy AToken ATokenProxy VariableDebtToken VariableDebtTokenProxy Pool PoolProxy
  InterestRateStrategy PoolLogic SupplyLogic BorrowLogic FlashLoanLogic LiquidationLogic)
declare -A MNS=(
  [WETH9]="Verified.WETH9.Contracts"
  [USDT]="Verified.WeirdERC20.USDT.Contracts"
  [BNB]="Verified.WeirdERC20.BNB.Contracts"
  [STA]="Verified.WeirdERC20.STA.Contracts"
  [AMPL]="Verified.WeirdERC20.AMPL.Contracts"
  [AMPLProxy]="Verified.WeirdERC20.AMPL.Contracts"
  [GUSD]="Verified.WeirdERC20.GUSD.Contracts"
  [GUSDImpl]="Verified.WeirdERC20.GUSD.Contracts"
  [GUSDStore]="Verified.WeirdERC20.GUSD.Contracts"
  [YAMV2]="Verified.WeirdERC20.YAMV2.Contracts"
  [LEND]="Verified.WeirdERC20.LEND.Contracts"
  [ZRX]="Verified.WeirdERC20.ZRX.Contracts"
  [SafeSingleton]="Verified.Safe.Contracts"
  [SafeProxy]="Verified.Safe.Contracts"
)
for t in AToken ATokenProxy VariableDebtToken VariableDebtTokenProxy Pool PoolProxy InterestRateStrategy \
    PoolLogic SupplyLogic BorrowLogic FlashLoanLogic LiquidationLogic; do
  MNS[$t]="Verified.AaveV3.Contracts"
done
# Mainnet targets whose runtime code is also rebuilt here from the verified source, with the
# compiler and settings Sourcify records (svm layout, ~/.svm/<version>/solc-<version>), and
# checked byte for byte (metadata included): Safe v1.5.0 (safe-global/safe-smart-account tag
# v1.5.0, solc 0.7.6, optimizer off, Istanbul).
REPRODUCE=(SafeSingleton SafeProxy)

# Names of all immutables, by AST id (forge artifacts carry each source's AST).
IMM_NAMES=$(find "$C/out" -name '*.json' -not -path '*/build-info/*' -print0 \
  | xargs -0 jq -c '[.. | objects | select(.nodeType? == "VariableDeclaration"
                     and .mutability? == "immutable") | {key: (.id|tostring), value: .name}]' \
  | jq -s 'add | from_entries')

strip0x() { sed 's/^0x//'; }

# ---------------------------------------------------------------- deploy on anvil
PORT=$((20000 + RANDOM % 20000))
RPC="http://127.0.0.1:$PORT"
anvil --port "$PORT" --chain-id "$CHAIN_ID" --hardfork cancun --silent --auto-impersonate \
  --base-fee 0 --gas-price 0 >/dev/null 2>&1 &
ANVIL=$!
trap 'kill $ANVIL 2>/dev/null || true' EXIT
for _ in $(seq 50); do cast chain-id --rpc-url "$RPC" >/dev/null 2>&1 && break; sleep 0.1; done
fund() { cast rpc --rpc-url "$RPC" anvil_setBalance "$DEPLOYER" 0x56bc75e2d63100000 >/dev/null; }
fund

deploy() { # deploy <initcode-hex-with-args> ; prints the new address
  local addr
  addr=$(cast send --rpc-url "$RPC" --unlocked --from "$DEPLOYER" --gas-limit 10000000 \
    --json --create "$1" | jq -r '(.data // .) | .contractAddress')
  cast to-check-sum-address "$addr"
}

declare -A ARGS ADDR
ARGS[SolmateAsset]=$(cast abi-encode "${SOLMATE_ASSET_ARGS[@]}" | strip0x)
ARGS[OzAsset]=""

# Solmate family: deployer nonces 0 (asset) and 1 (vault).
ADDR[SolmateAsset]=$(deploy "$(jq -r .bytecode.object "$C/${SRC[SolmateAsset]}")${ARGS[SolmateAsset]}")
ARGS[SolmateVault]=$(cast abi-encode "constructor(address,string,string)" \
  "${ADDR[SolmateAsset]}" "$SOLMATE_VAULT_NAME" "$SOLMATE_VAULT_SYMBOL" | strip0x)
ADDR[SolmateVault]=$(deploy "$(jq -r .bytecode.object "$C/${SRC[SolmateVault]}")${ARGS[SolmateVault]}")
declare -A CODE
for t in SolmateAsset SolmateVault; do CODE[$t]=$(cast code --rpc-url "$RPC" "${ADDR[$t]}" | strip0x); done

# OpenZeppelin family: a fresh chain, so the same deployer nonces 0 and 1.
cast rpc --rpc-url "$RPC" anvil_reset >/dev/null
fund
ADDR[OzAsset]=$(deploy "$(jq -r .bytecode.object "$C/${SRC[OzAsset]}")")
ARGS[OzVault]=$(cast abi-encode "constructor(address)" "${ADDR[OzAsset]}" | strip0x)
ADDR[OzVault]=$(deploy "$(jq -r .bytecode.object "$C/${SRC[OzVault]}")${ARGS[OzVault]}")
for t in OzAsset OzVault; do CODE[$t]=$(cast code --rpc-url "$RPC" "${ADDR[$t]}" | strip0x); done

# OpenZeppelin with decimals offset 3: the same asset, then `OzVaultOffset`.
cast rpc --rpc-url "$RPC" anvil_reset >/dev/null
fund
oz3asset=$(deploy "$(jq -r .bytecode.object "$C/${SRC[OzAsset]}")")
ARGS[OzVaultOffset]=$(cast abi-encode "constructor(address)" "$oz3asset" | strip0x)
ADDR[OzVaultOffset]=$(deploy "$(jq -r .bytecode.object "$C/${SRC[OzVaultOffset]}")${ARGS[OzVaultOffset]}")
CODE[OzVaultOffset]=$(cast code --rpc-url "$RPC" "${ADDR[OzVaultOffset]}" | strip0x)
[ "$(cast code --rpc-url "$RPC" "$oz3asset" | strip0x)" = "${CODE[OzAsset]}" ] \
  || { echo "error: OzAsset code differs between families" >&2; exit 1; }

# Solady: a single token at deployer nonce 0.
cast rpc --rpc-url "$RPC" anvil_reset >/dev/null
fund
ARGS[SoladyToken]=""
ADDR[SoladyToken]=$(deploy "$(jq -r .bytecode.object "$C/${SRC[SoladyToken]}")")
CODE[SoladyToken]=$(cast code --rpc-url "$RPC" "${ADDR[SoladyToken]}" | strip0x)

# Time: an OpenZeppelin `VestingWallet` at deployer nonce 0 (no value sent).
cast rpc --rpc-url "$RPC" anvil_reset >/dev/null
fund
ARGS[VestingWallet]=$(cast abi-encode "${VESTING_ARGS[@]}" | strip0x)
ADDR[VestingWallet]=$(deploy "$(jq -r .bytecode.object "$C/${SRC[VestingWallet]}")${ARGS[VestingWallet]}")
CODE[VestingWallet]=$(cast code --rpc-url "$RPC" "${ADDR[VestingWallet]}" | strip0x)

# Reentrancy demonstrators: a fresh chain, deployer nonces 0 (VulnerableBank) to 3 (Attacker).
cast rpc --rpc-url "$RPC" anvil_reset >/dev/null
fund
for t in "${REENTRANCY[@]}"; do
  ARGS[$t]=""
  ADDR[$t]=$(deploy "$(jq -r .bytecode.object "$C/${SRC[$t]}")")
  CODE[$t]=$(cast code --rpc-url "$RPC" "${ADDR[$t]}" | strip0x)
done

# OpenZeppelin transparent proxy: `ActorImpl` at deployer nonce 0, the proxy at nonce 1. The
# proxy's constructor deploys the `ProxyAdmin` (`CREATE` from the proxy at its nonce 1), records
# it as the immutable `_admin` and in the ERC-1967 admin slot, and delegatecalls `set(1)` into
# the implementation (the proxy's slot 0 becomes 1; the implementation's storage stays empty).
for v in IMPLEMENTATION ADMIN BEACON; do
  sl="ERC1967_${v}_SLOT"
  grep -q "bytes32 internal constant ${v}_SLOT = ${!sl};" \
    "$C/lib/openzeppelin-contracts/contracts/proxy/ERC1967/ERC1967Utils.sol" \
    || { echo "error: ERC-1967 ${v} slot differs from ERC1967Utils.sol" >&2; exit 1; }
done
cast rpc --rpc-url "$RPC" anvil_reset >/dev/null
fund
ARGS[ActorImpl]=""
ADDR[ActorImpl]=$(deploy "$(jq -r .bytecode.object "$C/${SRC[ActorImpl]}")")
PROXY_INIT_DATA=$(cast calldata "set(uint256)" "$PROXY_INIT_VALUE" | strip0x)
ARGS[OzTransparentProxy]=$(cast abi-encode "constructor(address,address,bytes)" \
  "${ADDR[ActorImpl]}" "$PROXY_OWNER" "0x$PROXY_INIT_DATA" | strip0x)
ADDR[OzTransparentProxy]=$(deploy "$(jq -r .bytecode.object "$C/${SRC[OzTransparentProxy]}")${ARGS[OzTransparentProxy]}")
ADDR[OzProxyAdmin]=$(cast parse-bytes32-address \
  "$(cast storage --rpc-url "$RPC" "${ADDR[OzTransparentProxy]}" "$ERC1967_ADMIN_SLOT")")
ARGS[OzProxyAdmin]=$(cast abi-encode "constructor(address)" "$PROXY_OWNER" | strip0x)
PROXY_OWNER=$(cast to-check-sum-address "$PROXY_OWNER")
for t in ActorImpl OzTransparentProxy OzProxyAdmin; do CODE[$t]=$(cast code --rpc-url "$RPC" "${ADDR[$t]}" | strip0x); done
[ "${ADDR[OzProxyAdmin]}" = "$(cast compute-address "${ADDR[OzTransparentProxy]}" --nonce 1 | sed 's/.*: *//')" ] \
  || { echo "error: ProxyAdmin is not the proxy's CREATE at nonce 1" >&2; exit 1; }
[ "$(cast parse-bytes32-address "$(cast storage --rpc-url "$RPC" "${ADDR[OzTransparentProxy]}" "$ERC1967_IMPLEMENTATION_SLOT")")" = "${ADDR[ActorImpl]}" ] \
  || { echo "error: proxy implementation slot is not ActorImpl" >&2; exit 1; }
[ "$(cast to-dec "$(cast storage --rpc-url "$RPC" "${ADDR[OzTransparentProxy]}" 0)")" = "$PROXY_INIT_VALUE" ] \
  && [ "$(cast to-dec "$(cast storage --rpc-url "$RPC" "${ADDR[ActorImpl]}" 0)")" = 0 ] \
  || { echo "error: proxy initialisation did not set the proxy's slot 0" >&2; exit 1; }
[ "$(cast call --rpc-url "$RPC" "${ADDR[OzProxyAdmin]}" "owner()(address)")" = "$PROXY_OWNER" ] \
  || { echo "error: ProxyAdmin owner is not $PROXY_OWNER" >&2; exit 1; }
case "$(jq -r .bytecode.object "$C/${SRC[OzTransparentProxy]}")" in
  *"$(jq -r .bytecode.object "$C/${SRC[OzProxyAdmin]}" | strip0x)"*) ;;
  *) echo "error: the proxy's creation code does not embed ProxyAdmin's" >&2; exit 1 ;;
esac

# MiniSafe: a fresh chain, deployer nonce 0.
cast rpc --rpc-url "$RPC" anvil_reset >/dev/null
fund
ARGS[MiniSafe]=$(cast abi-encode "constructor(address[],uint256)" "$MINISAFE_OWNERS" \
  "$MINISAFE_THRESHOLD" | strip0x)
ADDR[MiniSafe]=$(deploy "$(jq -r .bytecode.object "$C/${SRC[MiniSafe]}")${ARGS[MiniSafe]}")
CODE[MiniSafe]=$(cast code --rpc-url "$RPC" "${ADDR[MiniSafe]}" | strip0x)
[ "$(cast call --rpc-url "$RPC" "${ADDR[MiniSafe]}" "threshold()(uint256)")" = "$MINISAFE_THRESHOLD" ] \
  && [ "$(cast call --rpc-url "$RPC" "${ADDR[MiniSafe]}" "nonce()(uint256)")" = 0 ] \
  || { echo "error: MiniSafe: threshold or nonce differ from the canonical deployment" >&2; exit 1; }
for o in $(tr -d '[]' <<<"$MINISAFE_OWNERS" | tr ',' ' '); do
  [ "$(cast call --rpc-url "$RPC" "${ADDR[MiniSafe]}" "isOwner(address)(bool)" "$o")" = true ] \
    || { echo "error: MiniSafe: $o is not an owner" >&2; exit 1; }
done

[ "${ADDR[SolmateAsset]}" = "${ADDR[OzAsset]}" ] && [ "${ADDR[SolmateVault]}" = "${ADDR[OzVault]}" ] \
  && [ "$oz3asset" = "${ADDR[OzAsset]}" ] && [ "${ADDR[OzVaultOffset]}" = "${ADDR[OzVault]}" ] \
  && [ "${ADDR[SoladyToken]}" = "${ADDR[OzAsset]}" ] && [ "${ADDR[VestingWallet]}" = "${ADDR[OzAsset]}" ] \
  && [ "${ADDR[ActorImpl]}" = "${ADDR[OzAsset]}" ] && [ "${ADDR[OzTransparentProxy]}" = "${ADDR[OzVault]}" ] \
  || { echo "error: deployment addresses differ between families" >&2; exit 1; }

# ---------------------------------------------------------------- Lean helpers
# Hex string to a Lean cons chain of `UInt8` literals, 16 per line.
lean_bytes() {
  printf '%s' "$1" | sed 's/../0x&, /g' | sed 's/, $//' | tr -d ' ' | tr ',' '\n' \
    | awk 'BEGIN{ORS=""} {print $0 " ::"; if (NR % 16 == 0) print "\n    "; else print " "} END{print "[]"}'
}

# Lean field name and type of each immutable.
imm_field() {
  case "$1" in
    asset|_asset) echo "asset" ;;
    _admin) echo "admin" ;;
    decimals) echo "decimals" ;;
    _underlyingDecimals) echo "underlyingDecimals" ;;
    INITIAL_CHAIN_ID) echo "initialChainId" ;;
    INITIAL_DOMAIN_SEPARATOR) echo "initialDomainSeparator" ;;
    _start) echo "start" ;;
    _duration) echo "duration" ;;
    *) echo "error: unknown immutable $1" >&2; exit 1 ;;
  esac
}
imm_type() { case "$1" in asset|_asset|_admin) echo "Address" ;; *) echo "Word" ;; esac; }
imm_toword() { case "$1" in asset|_asset|_admin) echo "Word.ofAddress i.$2" ;; *) echo "i.$2" ;; esac; }

# Lean expression of a solc storage type, recursively through the `types` table.
JQ_TYPE='def ty($types; t): $types[t] as $x
  | if $x.encoding == "mapping" then "(.mapping \(ty($types; $x.key)) \(ty($types; $x.value)))"
    elif $x.encoding == "bytes" then "(.bytes \"\($x.label)\")"
    elif $x.encoding == "dynamic_array" then "(.dynamicArray \(ty($types; $x.base)))"
    else "(.inplace \"\($x.label)\" \($x.numberOfBytes))" end;'

# Selectors, events, custom errors and storage layout of the artifacts in directory $1
# ($2 = forge: compiled here; abi: from the verified ABI and a hand-derived layout).
lean_meta() {
  local d=$1 sel ev er lay
  if [ "$2" = forge ]; then
    sel="(\`forge inspect … methodIdentifiers\`)"; ev="(\`forge inspect … events\`)"
    er="(\`forge inspect … errors\`)"; lay="(\`forge inspect … storageLayout\`)"
  else
    sel="(from the verified ABI)"; ev="(from the verified ABI)"; er="(from the verified ABI)"
    lay="(hand-derived from the verified source: \`storageLayout.json\`)"
  fi
  echo "/-- Function selectors $sel. -/"
  echo "def selectors : List (String × UInt32) := ["
  jq -r 'to_entries | map("  (\"\(.key)\", 0x\(.value))") | join(",\n")' "$d/methodIdentifiers.json"
  echo "]"
  echo
  echo "/-- Event signatures and their topic $ev. -/"
  echo "def events : List (String × Word) := ["
  jq -r 'to_entries | map("  (\"\(.key)\", \(.value))") | join(",\n")' "$d/events.json"
  echo "]"
  echo
  echo "/-- Custom-error selectors $er. -/"
  echo "def errors : List (String × UInt32) := ["
  jq -r 'if length == 0 then "" else to_entries | map("  (\"\(.key)\", 0x\(.value))") | join(",\n") end' "$d/errors.json" | sed '/^$/d'
  echo "]"
  echo
  echo "/-- Storage layout $lay. -/"
  echo "def storageLayout : List StorageVar := ["
  jq -r "$JQ_TYPE"' .types as $types | [.storage[] |
    "  { label := \"\(.label)\", slot := \(.slot), offset := \(.offset),\n    type := \(ty($types; .type)) }"]
    | join(",\n")' "$d/storageLayout.json"
  echo "]"
  echo
}

# Documentation of the canonical deployment of target $1 in its data module.
deploy_doc() {
  case "$1" in
    ActorImpl) cat <<DOC
Canonical deployment (\`Examples.Deployment.deployer\`, \`Examples.Deployment.chainId\`): deployer
\`${DEPLOYER}\` (nonce 0), chain id ${CHAIN_ID}, this contract at
\`${ADDR[ActorImpl]}\`: the implementation of
\`OzTransparentProxy\` (deployer nonce 1, at \`proxy\`). The proxy's constructor delegatecalls
\`set(${PROXY_INIT_VALUE})\`, so \`value\` is ${PROXY_INIT_VALUE} in the proxy's storage; this contract's own
storage stays empty.
DOC
    ;;
    OzTransparentProxy) cat <<DOC
Canonical deployment (\`Examples.Deployment.deployer\`, \`Examples.Deployment.chainId\`): deployer
\`${DEPLOYER}\` (nonce 1, after \`ActorImpl\` at nonce 0), chain id
${CHAIN_ID}, this contract at \`${ADDR[OzTransparentProxy]}\`, constructed as
\`TransparentUpgradeableProxy(implementation, initialOwner, initData)\`. The constructor deploys
the \`ProxyAdmin\` (\`OzProxyAdmin\`, owned by \`initialOwner\`) at \`proxyAdmin\` (\`CREATE\` from
this contract at nonce 1), keeps it in the immutable \`_admin\` and in the ERC-1967 admin slot,
stores \`implementation\` in the ERC-1967 implementation slot and delegatecalls \`initData\` into
it (OpenZeppelin v5.7.0's \`ERC1967Proxy\` rejects empty data). Canonical storage of the proxy:
implementation slot \`implementation\`, admin slot \`proxyAdmin\`, slot 0 (\`ActorImpl.value\`) ${PROXY_INIT_VALUE}.
DOC
    ;;
    OzProxyAdmin) cat <<DOC
Canonical deployment (\`Examples.Deployment.chainId\`): created by the constructor of
\`OzTransparentProxy\` (\`CREATE\` from the proxy
\`${ADDR[OzTransparentProxy]}\` at its nonce 1), chain id ${CHAIN_ID}, owner
\`initialOwner\`; this contract at \`${ADDR[OzProxyAdmin]}\`. \`constructorArgs\` is
the owner, as the proxy passes it.
DOC
    ;;
    MiniSafe) cat <<DOC
Canonical deployment (\`Examples.Deployment.deployer\`, \`Examples.Deployment.chainId\`): deployer
\`${DEPLOYER}\` (nonce 0, on a fresh chain), chain id ${CHAIN_ID}, this contract at
\`${ADDR[MiniSafe]}\`, constructed as \`MiniSafe(owners, ${MINISAFE_THRESHOLD})\` with the owners
\`initialOwners\` (\`isOwner\` true for each, threshold ${MINISAFE_THRESHOLD}, nonce 0).
DOC
    ;;
    *) cat <<DOC
Canonical deployment (\`Examples.Deployment.deployer\`, \`Examples.Deployment.chainId\`): deployer
\`${DEPLOYER}\`, chain id ${CHAIN_ID}, this contract at
\`${ADDR[$1]}\`.
DOC
    ;;
  esac
}

# Slot of the state variable $2 in the storage layout of target $1.
lean_slot() { jq -r --arg l "$2" '.storage[] | select(.label == $l) | .slot' "$ART/$1/storageLayout.json"; }

# Extra definitions of target $1 in its data module (canonical parameters, slots).
lean_extra() {
  case "$1" in
    OzTransparentProxy) cat <<DOC
/-- ERC-1967 implementation slot, \`keccak256("eip1967.proxy.implementation") - 1\`. -/
def implementationSlot : Word := ${ERC1967_IMPLEMENTATION_SLOT}

/-- ERC-1967 admin slot, \`keccak256("eip1967.proxy.admin") - 1\`. -/
def adminSlot : Word := ${ERC1967_ADMIN_SLOT}

/-- ERC-1967 beacon slot, \`keccak256("eip1967.proxy.beacon") - 1\` (unused by this proxy). -/
def beaconSlot : Word := ${ERC1967_BEACON_SLOT}

/-- The implementation of the canonical deployment (\`ActorImpl\`, deployer nonce 0). -/
def implementation : Address := ${ADDR[ActorImpl]}

/-- The owner of the \`ProxyAdmin\` in the canonical deployment (\`initialOwner\`). -/
def initialOwner : Address := ${PROXY_OWNER}

/-- The \`ProxyAdmin\` deployed by the canonical constructor (\`OzProxyAdmin\`). -/
def proxyAdmin : Address := ${ADDR[OzProxyAdmin]}

/-- The constructor's initialisation calldata: \`set(${PROXY_INIT_VALUE})\` of \`ActorImpl\`. -/
def initData : ByteArray := ⟨⟨
    $(lean_bytes "$PROXY_INIT_DATA")⟩⟩

DOC
    ;;
    OzProxyAdmin) cat <<DOC
/-- The owner of the canonical deployment (the proxy's \`initialOwner\`). -/
def initialOwner : Address := ${PROXY_OWNER}

/-- The proxy whose constructor deploys this contract (\`OzTransparentProxy\`). -/
def proxy : Address := ${ADDR[OzTransparentProxy]}

/-- Storage slot of \`Ownable._owner\` (from \`storageLayout\`). -/
def ownerSlot : Nat := $(lean_slot OzProxyAdmin _owner)

DOC
    ;;
    MiniSafe) cat <<DOC
/-- The owners of the canonical deployment (the constructor's \`owners\`). -/
def initialOwners : List Address := [
  $(tr -d '[]' <<<"$MINISAFE_OWNERS" | sed 's/,/,\n  /g')]

/-- The threshold of the canonical deployment. -/
def initialThreshold : Nat := ${MINISAFE_THRESHOLD}

/-- Storage slot of \`threshold\` (from \`storageLayout\`). -/
def thresholdSlot : Nat := $(lean_slot MiniSafe threshold)

/-- Storage slot of \`nonce\` (from \`storageLayout\`). -/
def nonceSlot : Nat := $(lean_slot MiniSafe nonce)

/-- Storage slot of the mapping \`isOwner\` (from \`storageLayout\`). -/
def isOwnerSlot : Nat := $(lean_slot MiniSafe isOwner)

DOC
    ;;
    ActorImpl) cat <<DOC
/-- The proxy of the canonical deployment (\`OzTransparentProxy\`), whose storage holds \`value\`. -/
def proxy : Address := ${ADDR[OzTransparentProxy]}

/-- Storage slot of \`value\` (from \`storageLayout\`). -/
def valueSlot : Nat := $(lean_slot ActorImpl value)

DOC
    ;;
  esac
}

TMP=$(mktemp -d)
trap 'kill $ANVIL 2>/dev/null || true; rm -rf "$TMP"' EXIT

# ---------------------------------------------------------------- per contract
for t in "${TARGETS[@]}"; do
  a="$C/${SRC[$t]}"
  d="$ART/$t"
  mkdir -p "$d"
  jq -r .bytecode.object "$a" | strip0x > "$d/creation.hex"
  printf '%s\n' "${ARGS[$t]}" > "$d/constructorArgs.hex"
  jq -r .deployedBytecode.object "$a" | strip0x > "$d/runtime.template.hex"
  printf '%s\n' "${CODE[$t]}" > "$d/runtime.hex"
  jq .abi "$a" > "$d/abi.json"
  ( cd "$C" && forge inspect "${SOLNAME[$t]}" methodIdentifiers --json ) | jq -S . > "$d/methodIdentifiers.json"
  ( cd "$C" && forge inspect "${SOLNAME[$t]}" events --json ) | jq -S . > "$d/events.json"
  ( cd "$C" && forge inspect "${SOLNAME[$t]}" errors --json ) | jq -S . > "$d/errors.json"
  ( cd "$C" && forge inspect "${SOLNAME[$t]}" storageLayout --json ) > "$d/storageLayout.json"
  # Immutable references with names and canonical (deployed) values.
  code="${CODE[$t]}"
  jq --argjson names "$IMM_NAMES" --arg code "$code" '
    (.deployedBytecode.immutableReferences // {}) | to_entries
    | map({name: $names[.key], astId: (.key|tonumber),
           offsets: [.value[] | .start], length: (.value[0].length),
           value: ("0x" + $code[(.value[0].start*2):(.value[0].start*2 + 64)])})
    | sort_by(.name)' "$a" > "$d/immutableReferences.json"

  # The deployed code must equal the template with the immutables filled in.
  tmpl=$(cat "$d/runtime.template.hex")
  [ ${#tmpl} -eq ${#code} ] || { echo "error: $t: deployed size differs from template" >&2; exit 1; }
  masked="$code"
  for off in $(jq -r '.[] | .offsets[]' "$d/immutableReferences.json"); do
    masked="${masked:0:$((off*2))}$(printf '0%.0s' $(seq 64))${masked:$((off*2+64))}"
  done
  [ "$masked" = "$tmpl" ] || { echo "error: $t: deployed code differs outside immutables" >&2; exit 1; }

  # ------------------------------------------------------------ Lean file
  mkdir -p "${LEANDIR[$t]}"
  f="${LEANDIR[$t]}/$t.lean"
  nimm=$(jq length "$d/immutableReferences.json")
  rsize=$(( ${#code} / 2 ))
  csize=$(( $(wc -c < "$d/creation.hex" | tr -d ' ') / 2 ))
  {
    cat <<EOF
import EvmLogic.Solidity.Immutables
import EvmLogic.Solidity.Layout

/-!
# \`$t\`: compiled bytecode and metadata (generated)

Generated by \`scripts/build-contracts.sh\` from
\`contracts/${SOLNAME[$t]}\`
(solc 0.8.28, optimizer 200 runs, Cancun, no via-IR, no metadata). Do not edit; rerun the
script. Raw artifacts: \`contracts/artifacts/$t/\`.

$(deploy_doc "$t")
-/

namespace ${LEANNS[$t]}.$t
open EvmLean EvmLogic EvmLogic.Solidity

set_option maxRecDepth 100000 in
/-- Creation (init) code, without constructor arguments ($csize bytes). -/
def creationCode : ByteArray := ⟨⟨
    $(lean_bytes "$(cat "$d/creation.hex")")⟩⟩

/-- ABI-encoded constructor arguments of the canonical deployment. -/
def constructorArgs : ByteArray := ⟨⟨
    $(lean_bytes "${ARGS[$t]}")⟩⟩

set_option maxRecDepth 100000 in
/-- Runtime code as deployed by \`creationCode ++ constructorArgs\` in the canonical deployment
($rsize bytes; immutables filled in). -/
def runtimeCode : ByteArray := ⟨⟨
    $(lean_bytes "$code")⟩⟩

/-- The canonical address of this contract. -/
def address : Address := ${ADDR[$t]}

EOF
    lean_extra "$t"
    if [ "$nimm" -gt 0 ]; then
      echo "/-- The immutables of the contract (solc fills them into the runtime code at deployment). -/"
      echo "structure Immutables where"
      jq -r '.[] | .name' "$d/immutableReferences.json" | while read -r n; do
        echo "  /-- Solidity immutable \`$n\`. -/"
        echo "  $(imm_field "$n") : $(imm_type "$n")"
      done
      echo "  deriving DecidableEq, Repr"
      echo
      echo "/-- Names and byte offsets of the 32-byte immutable slots in the runtime code. -/"
      echo "def immutableRefs : List ImmutableRef := ["
      jq -r '[.[] | "  { name := \"\(.name)\", offsets := \(.offsets | tostring | gsub(",";", ")) }"] | join(",\n")' "$d/immutableReferences.json"
      echo "]"
      echo
      echo "/-- The words written at each immutable offset for the given values. -/"
      echo "def Immutables.patches (i : Immutables) : List (Nat × Word) :="
      first=1
      jq -r '.[] | "\(.name) \(.offsets | map(tostring) | join(" "))"' "$d/immutableReferences.json" | while read -r n offs; do
        fld=$(imm_field "$n")
        w=$(imm_toword "$n" "$fld")
        list=$(for o in $offs; do echo "($o, $w)"; done \
          | awk 'BEGIN{ORS=""} NR>1{print ",\n    "} {print}')
        if [ $first -eq 1 ]; then printf '  [%s]' "$list"; first=0; else printf ' ++\n  [%s]' "$list"; fi
      done
      echo
      echo
      echo "/-- The runtime code with the given immutables (patched by position). -/"
      echo "def runtimeCodeWith (i : Immutables) : ByteArray := patchWords runtimeCode i.patches"
      echo
      echo "/-- The immutables of the canonical deployment. -/"
      echo "def deployment : Immutables where"
      jq -r '.[] | "\(.name) \(.value)"' "$d/immutableReferences.json" | while read -r n v; do
        if [ "$(imm_type "$n")" = "Address" ]; then
          echo "  $(imm_field "$n") := 0x${v:26}"
        else
          stripped=$(printf '%s' "${v:2}" | sed 's/^0*//')
          if [ ${#stripped} -le 15 ]; then echo "  $(imm_field "$n") := $((16#${stripped:-0}))"
          else echo "  $(imm_field "$n") := $v"; fi
        fi
      done
      echo
    else
      echo "/-- The contract has no immutables: its runtime code is independent of the deployment. -/"
      echo "def immutableRefs : List ImmutableRef := []"
      echo
    fi
    lean_meta "$d" forge
    echo "end ${LEANNS[$t]}.$t"
  } > "$TMP/${t}Data.lean"
  mv "$TMP/${t}Data.lean" "${LEANDIR[$t]}/${t}Data.lean"
  # The kernel-checked facts about the code, in their own module so that importers needing only
  # the bytes, immutables, selectors or layout do not wait for the code table.
  {
    cat <<EOF
import ${LEANNS[$t]}.${t}Data
import EvmLogic.Program.Code

/-!
# \`$t\`: code facts (generated)

Generated by \`scripts/build-contracts.sh\`; do not edit. The sizes of the code, the kernel
lookup table of \`runtimeCode\` and, with immutables, that the canonical deployment patches
\`runtimeCode\` into itself. The data (bytes, immutables, selectors, layout) is in
\`${LEANNS[$t]}.${t}Data\`.
-/

namespace ${LEANNS[$t]}.$t
open EvmLean EvmLogic EvmLogic.Solidity

/-- \`runtimeCode\` has the size of the compiled runtime code. -/
theorem size_runtimeCode : runtimeCode.size = $rsize := by decide +kernel

/-! Kernel lookup table of \`runtimeCode\` (bytes and jump destinations), checked once:
\`runtimeCode.codeTable\`, \`runtimeCode.codeTable_ok\`. -/
code_table runtimeCode

/-- \`creationCode\` has the size of the compiled creation code. -/
theorem size_creationCode : creationCode.size = $csize := by decide +kernel

EOF
    if [ "$nimm" -gt 0 ]; then
      echo "/-- Patching the canonical immutables into \`runtimeCode\` gives \`runtimeCode\`. -/"
      echo "theorem runtimeCodeWith_deployment : runtimeCodeWith deployment = runtimeCode :="
      echo "  eq_of_data_toList_eq (by decide +kernel)"
      echo
    fi
    echo "end ${LEANNS[$t]}.$t"
  } > "$TMP/$t.lean"
  mv "$TMP/$t.lean" "$f"
done
# The proxy's only immutable is `_admin`, the ProxyAdmin its constructor deployed.
[ "$(jq -r 'map(.name) | join(" ")' "$ART/OzTransparentProxy/immutableReferences.json")" = _admin ] \
  && [ "$(cast parse-bytes32-address "$(jq -r '.[0].value' "$ART/OzTransparentProxy/immutableReferences.json")")" = "${ADDR[OzProxyAdmin]}" ] \
  || { echo "error: OzTransparentProxy: immutable _admin is not the ProxyAdmin" >&2; exit 1; }

# ---------------------------------------------------------------- mainnet targets
# ABI signature of an ABI entry (tuples expanded).
JQ_SIG='def ty: if (.type | startswith("tuple")) then
      "(" + ([.components[] | ty] | join(",")) + ")" + (.type | ltrimstr("tuple")) else .type end;
  def sig: "\(.name)(" + ([.inputs[] | ty] | join(",")) + ")";'
# Signature → selector/topic table of the ABI entries of kind $2 in $1, hashed by $3
# (`sig`: 4-byte selector, `keccak`: 32-byte topic).
abi_table() {
  jq -r "$JQ_SIG"' .[] | select(.type == "'"$2"'") | sig' "$1" | sort -u | while read -r sg; do
    if [ "$3" = sig ]; then printf '%s\t%s\n' "$sg" "$(cast sig "$sg" | strip0x)"
    else printf '%s\t%s\n' "$sg" "$(cast keccak "$sg")"; fi
  done | jq -R -s 'split("\n") | map(select(length > 0) | split("\t") | {key: .[0], value: .[1]})
                   | from_entries' | jq -S .
}
# Resolve a genesis storage entry to a 32-byte slot: a literal `slot`, or `mapping` (the
# mapping's slot) with `keys` (addresses, outermost first).
genesis_slot() {
  local e=$1 slot k
  if [ "$(jq -r 'has("slot")' <<<"$e")" = true ]; then slot=$(jq -r .slot <<<"$e")
  else
    slot=$(jq -r .mapping <<<"$e")
    for k in $(jq -r '.keys[]' <<<"$e"); do slot=$(cast index address "$k" "$slot"); done
  fi
  cast to-uint256 "$slot"
}
# Rebuild the runtime code of mainnet target $1 from contracts/mainnet/$1/source.
reproduce() {
  local d="$C/mainnet/$1" ver solc fq file name
  ver=$(jq -r '.compilation.compilerVersion' "$d/sourcify.json" | sed 's/+.*//')
  solc="$HOME/.svm/$ver/solc-$ver"
  [ -x "$solc" ] || { echo "error: $1: need solc $ver at $solc" >&2; exit 1; }
  fq=$(jq -r '.compilation.fullyQualifiedName' "$d/sourcify.json")
  file=${fq%:*}; name=${fq##*:}
  ( cd "$d/source" && find . -name '*.sol' | sed 's|^\./||' | sort ) | while read -r p; do
    jq -n --arg p "$p" --rawfile c "$d/source/$p" '{($p): {content: $c}}'
  done | jq -s --slurpfile s "$d/sourcify.json" \
    '{language: "Solidity", sources: add,
      settings: ($s[0].compilation.compilerSettings
        + {outputSelection: {"*": {"*": ["evm.deployedBytecode.object"]}}})}' \
    > "$TMP/$1.input.json"
  "$solc" --standard-json < "$TMP/$1.input.json" > "$TMP/$1.output.json"
  [ "$(jq -r --arg f "$file" --arg n "$name" '.contracts[$f][$n].evm.deployedBytecode.object' \
      "$TMP/$1.output.json")" = "$(cat "$d/runtime.hex")" ] \
    || { echo "error: $1: solc $ver does not reproduce runtime.hex" >&2; exit 1; }
}
for t in "${REPRODUCE[@]}"; do reproduce "$t"; done

declare -A MADDR MSIZE
for t in "${MAINNET[@]}"; do
  d="$C/mainnet/$t"
  code=$(cat "$d/runtime.hex")
  hash=$(jq -r .codeHash "$d/meta.json")
  [ "$(cast keccak "0x$code")" = "$hash" ] || { echo "error: $t: runtime.hex does not hash to $hash" >&2; exit 1; }
  MADDR[$t]=$(jq -r .address "$d/meta.json")
  MSIZE[$t]=$(( ${#code} / 2 ))
  abi_table "$d/abi.json" function sig > "$d/methodIdentifiers.json"
  # Library functions with storage-pointer parameters are not in the ABI, and their selectors
  # hash solc's internal signatures (`mapping(address => DataTypes.ReserveData) storage`, …):
  # hand-copied from solc's methodIdentifiers into librarySelectors.json, checked below like
  # the others.
  if [ -f "$d/librarySelectors.json" ]; then
    jq -S -s '.[0] + .[1]' "$d/methodIdentifiers.json" "$d/librarySelectors.json" > "$TMP/sel.json"
    mv "$TMP/sel.json" "$d/methodIdentifiers.json"
  fi
  abi_table "$d/abi.json" event keccak > "$d/events.json"
  abi_table "$d/abi.json" error sig > "$d/errors.json"
  # Every ABI selector must be pushed by the dispatcher (PUSHn of the selector without its
  # leading zero bytes).
  for sel in $(jq -r '.[]' "$d/methodIdentifiers.json"); do
    s=$(printf '%s' "$sel" | sed 's/^\(00\)*//'); n=$(( ${#s} / 2 ))
    op=$(printf '%02x' $(( 0x5f + n )))
    case "$code" in *"$op$s"*) ;; *) echo "error: $t: selector $sel not in the runtime code" >&2; exit 1 ;; esac
  done
  # Genesis storage as Lean `(slot, value)` pairs.
  entries=()
  if [ -f "$d/genesis.json" ]; then
    while read -r e; do
      entries+=("  -- $(jq -r .label <<<"$e")"$'\n'"  ($(genesis_slot "$e"),"$'\n'"   $(cast to-uint256 "$(jq -r .value <<<"$e")"))")
    done < <(jq -c '.storage[]' "$d/genesis.json")
  fi
  genesis=""
  for i in "${!entries[@]}"; do
    [ "$i" -gt 0 ] && genesis+=","$'\n'
    genesis+="${entries[$i]}"
  done

  # Immutables: names hand-written in immutables.json (AST id → name), offsets from Sourcify's
  # bytecode transformations, values read from the code (the same word at every offset).
  # Without immutables.json they are not tracked (the code is installed as deployed).
  imm_lean="/-- Not tracked for mainnet code: it is installed as deployed, immutables (if any) filled in. -/
def immutableRefs : List ImmutableRef := []"
  if [ -f "$d/immutables.json" ]; then
    imms=$(jq -c --slurpfile s "$d/sourcify.json" '[.[] as $i | {name: $i.name, id: $i.id,
      offsets: ([$s[0].runtimeTransformations[] | select(.reason == "immutable" and .id == $i.id) | .offset] | sort)}]' \
      "$d/immutables.json")
    [ "$(jq -c '[.[].id] | sort' <<<"$imms")" = "$(jq -c '[.runtimeTransformations[] | select(.reason == "immutable") | .id] | unique' "$d/sourcify.json")" ] \
      || { echo "error: $t: immutables.json does not name exactly Sourcify's immutables" >&2; exit 1; }
    refs=(); vals=()
    while read -r name offs; do
      v=""
      for o in $offs; do
        w=${code:$((o*2)):64}
        [ -z "$v" ] && v=$w
        [ "$w" = "$v" ] || { echo "error: $t: immutable $name differs between offsets" >&2; exit 1; }
      done
      refs+=("  { name := \"$name\", offsets := [$(printf '%s' "$offs" | sed 's/ /, /g')] }")
      vals+=("  (\"$name\", 0x$v)")
    done < <(jq -r '.[] | "\(.name) \(.offsets | map(tostring) | join(" "))"' <<<"$imms")
    imm_lean="/-- The immutables of the deployed code: names (\`immutables.json\`) and byte offsets of their 32-byte
slots (Sourcify's bytecode transformations). Their mainnet values are part of \`runtimeCode\`. -/
def immutableRefs : List ImmutableRef := [
$(IFS=$'\n'; printf '%s' "${refs[*]}" | sed '$!s/$/,/')
]

/-- The value of each immutable in \`runtimeCode\` (the same word at each of its offsets). -/
def immutableValues : List (String × Word) := [
$(IFS=$'\n'; printf '%s' "${vals[*]}" | sed '$!s/$/,/')
]"
  fi
  # Linked external libraries (PUSH20 <library> before a DELEGATECALL): from Sourcify's
  # transformations, else hand-written in links.json (name, offsets); the address is read from
  # the code and must follow a PUSH20 at every offset.
  links=""
  if [ -f "$d/sourcify.json" ]; then
    links=$(jq -c '[.runtimeTransformations // [] | .[] | select(.reason == "library")] | group_by(.id)
      | map({name: (.[0].id | split(":") | last), offsets: (map(.offset) | sort)})' "$d/sourcify.json")
  fi
  if [ -f "$d/links.json" ]; then links=$(jq -c . "$d/links.json"); fi
  link_lean=""
  if [ -n "$links" ] && [ "$links" != "[]" ]; then
    lrows=()
    while read -r name offs; do
      a=""
      for o in $offs; do
        [ "${code:$((o*2-2)):2}" = 73 ] || { echo "error: $t: no PUSH20 before library $name at $o" >&2; exit 1; }
        w=${code:$((o*2)):40}
        [ -z "$a" ] && a=$w
        [ "$w" = "$a" ] || { echo "error: $t: library $name has two addresses" >&2; exit 1; }
      done
      lrows+=("  (\"$name\", $(cast to-check-sum-address "0x$a"), [$(printf '%s' "$offs" | sed 's/ /, /g')])")
    done < <(jq -r '.[] | "\(.name) \(.offsets | map(tostring) | join(" "))"' <<<"$links")
    link_lean="
/-- Linked external libraries: name, address, byte offsets of the 20-byte address (each after a
\`PUSH20\`; the code \`DELEGATECALL\`s the library there). The libraries are separate mainnet targets. -/
def linkedLibraries : List (String × Address × List Nat) := [
$(IFS=$'\n'; printf '%s' "${lrows[*]}" | sed '$!s/$/,/')
]
"
  fi
  if [ -f "$d/sourcify.json" ]; then
    verif="Sourcify runtime match: $(jq -r .sourcify.runtimeMatch "$d/meta.json")"
  else
    verif="Blockscout: $(jq -r 'if .blockscout.fullyVerified then "full" else "partial" end' "$d/meta.json") verification"
  fi

  ns="${MNS[$t]}"
  dir="$ROOT/qedefi/$(printf '%s' "$ns" | tr . /)"
  mkdir -p "$dir"
  f="$dir/$t.lean"
  opt=$(jq -r 'if .optimizer.enabled then "\(.optimizer.runs) runs" else "off" end' "$d/meta.json")
  {
    cat <<LEAN
import EvmLogic.Solidity.Immutables
import EvmLogic.Solidity.Layout

/-!
# \`$t\`: deployed mainnet bytecode and metadata (generated)

Generated by \`scripts/build-contracts.sh\` from \`contracts/mainnet/$t/\`: the runtime code
of \`$(jq -r .contractName "$d/meta.json")\` at \`${MADDR[$t]}\` on Ethereum mainnet, read
at block $(jq -r .block "$d/meta.json") by \`scripts/fetch-mainnet.sh\`. Verified source in
\`contracts/mainnet/$t/source/\` (solc $(jq -r .compiler "$d/meta.json"), optimizer $opt;
$verif). Do not edit; rerun the script.

There is no creation code: tests and proofs start from \`runtimeCode\` installed at
\`address\` with storage \`genesisStorage\` (the constructor's state with test parameters,
\`contracts/mainnet/$t/genesis.json\`).
-/

namespace $ns.$t
open EvmLean EvmLogic EvmLogic.Solidity

set_option maxRecDepth 100000 in
/-- Runtime code as deployed on mainnet (${MSIZE[$t]} bytes). -/
def runtimeCode : ByteArray := ⟨⟨
    $(lean_bytes "$code")⟩⟩

/-- \`runtimeCode\` has the size of the deployed code. -/
theorem size_runtimeCode : runtimeCode.size = ${MSIZE[$t]} := by decide +kernel

/-- The mainnet address of the contract (also its address in tests). -/
def address : Address := ${MADDR[$t]}

/-- \`keccak256 runtimeCode\` (checked by the build script). -/
def codeHash : Word := $hash

/-- The mainnet block at which \`runtimeCode\` was read. -/
def fetchBlock : Nat := $(jq -r .block "$d/meta.json")

$imm_lean
$link_lean
/-- Storage of the test deployment as \`(slot, value)\` pairs; every other slot is zero. -/
def genesisStorage : List (Word × Word) := [
$genesis
]

LEAN
    lean_meta "$d" abi
    echo "end $ns.$t"
  } > "$TMP/$t.lean"
  mv "$TMP/$t.lean" "$f"
done

jq -n --arg deployer "$DEPLOYER" --argjson chainId "$CHAIN_ID" \
  --arg sa "${ADDR[SolmateAsset]}" --arg sv "${ADDR[SolmateVault]}" \
  --arg oa "${ADDR[OzAsset]}" --arg ov "${ADDR[OzVault]}" \
  --arg saArgs "${ARGS[SolmateAsset]}" --arg svArgs "${ARGS[SolmateVault]}" --arg ovArgs "${ARGS[OzVault]}" \
  --arg o3 "${ADDR[OzVaultOffset]}" --arg o3Args "${ARGS[OzVaultOffset]}" --arg sl "${ADDR[SoladyToken]}" \
  --arg vw "${ADDR[VestingWallet]}" --arg vwArgs "${ARGS[VestingWallet]}" \
  --arg vb "${ADDR[VulnerableBank]}" --arg cb "${ADDR[CEIBank]}" --arg gb "${ADDR[GuardedBank]}" \
  --arg at "${ADDR[Attacker]}" --arg oa2 "${ADDR[OnceAttacker]}" \
  --arg ai "${ADDR[ActorImpl]}" --arg tp "${ADDR[OzTransparentProxy]}" --arg tpArgs "${ARGS[OzTransparentProxy]}" \
  --arg pa "${ADDR[OzProxyAdmin]}" --arg paArgs "${ARGS[OzProxyAdmin]}" --arg owner "$PROXY_OWNER" \
  --arg initData "0x$PROXY_INIT_DATA" --argjson initValue "$PROXY_INIT_VALUE" \
  --arg implSlot "$ERC1967_IMPLEMENTATION_SLOT" --arg adminSlot "$ERC1967_ADMIN_SLOT" --arg beaconSlot "$ERC1967_BEACON_SLOT" \
  --arg ms "${ADDR[MiniSafe]}" --arg msArgs "${ARGS[MiniSafe]}" --argjson msOwners "$(tr -d '[]' <<<"$MINISAFE_OWNERS" | jq -R 'split(",")')" \
  --argjson msThreshold "$MINISAFE_THRESHOLD" \
  --argjson mainnet "$(for t in "${MAINNET[@]}"; do jq -c --arg t "$t" '{($t): {address, block, codeHash, codeSize}}' "$C/mainnet/$t/meta.json"; done | jq -s 'add // {}')" \
  '{chainId: $chainId, deployer: $deployer, evmVersion: "cancun", solc: "0.8.28+commit.7893614a",
    note: "Each family is deployed on its own fresh chain: the asset at deployer nonce 0, the vault at nonce 1.",
    solmate: {asset: {contract: "MockERC20", address: $sa, args: ["Solmate Asset", "SAST", 18], argsHex: $saArgs},
              vault: {contract: "MockERC4626", address: $sv, args: [$sa, "Solmate Vault", "svSAST"], argsHex: $svArgs}},
    openzeppelin: {asset: {contract: "ERC20Mock", address: $oa, args: [], argsHex: ""},
                   vault: {contract: "OzVault", address: $ov, args: [$oa], argsHex: $ovArgs}},
    openzeppelinOffset3: {asset: {contract: "ERC20Mock", address: $oa, args: [], argsHex: ""},
                          vault: {contract: "OzVaultOffset", address: $o3, args: [$oa], argsHex: $o3Args}},
    solady: {token: {contract: "SoladyToken", address: $sl, args: [], argsHex: ""}},
    time: {vestingWallet: {contract: "VestingWallet", address: $vw,
           args: ["0x2000000000000000000000000000000000000000", 1700000000, 31536000], argsHex: $vwArgs}},
    reentrancy: {note: "A fresh chain: deployer nonces 0 to 3.",
                 vulnerableBank: {contract: "VulnerableBank", address: $vb},
                 ceiBank: {contract: "CEIBank", address: $cb},
                 guardedBank: {contract: "GuardedBank", address: $gb},
                 attacker: {contract: "Attacker", address: $at},
                 onceAttacker: {contract: "OnceAttacker", address: $oa2}},
    openzeppelinTransparentProxy: {
      note: "ActorImpl at deployer nonce 0, the proxy at nonce 1; the proxy constructor deploys the ProxyAdmin (CREATE from the proxy at nonce 1) and delegatecalls initData (set(1)) into the implementation.",
      implementation: {contract: "ActorImpl", address: $ai, args: [], argsHex: ""},
      proxy: {contract: "TransparentUpgradeableProxy", address: $tp, args: [$ai, $owner, $initData], argsHex: $tpArgs},
      proxyAdmin: {contract: "ProxyAdmin", address: $pa, deployer: $tp, args: [$owner], argsHex: $paArgs},
      initialOwner: $owner, initValue: $initValue,
      erc1967: {implementationSlot: $implSlot, adminSlot: $adminSlot, beaconSlot: $beaconSlot}},
    miniSafe: {contract: "MiniSafe", address: $ms, args: [$msOwners, $msThreshold], argsHex: $msArgs},
    mainnetNote: "Mainnet targets have no creation code: their runtime code is installed at their mainnet address with genesis.json storage.",
    mainnet: $mainnet}' \
  > "$ART/deployment.json"

for t in "${MAINNET[@]}"; do
  echo "$t: mainnet runtime ${MSIZE[$t]} B at ${MADDR[$t]}"
done
for t in "${TARGETS[@]}"; do
  echo "$t: runtime $(( $(wc -c < "$ART/$t/runtime.hex") / 2 )) B, creation $(( $(wc -c < "$ART/$t/creation.hex") / 2 )) B, at ${ADDR[$t]}"
done

if [ $CHECK -eq 1 ]; then
  git -C "$ROOT" diff --exit-code -- contracts/artifacts contracts/mainnet \
    qedefi/Verified/Solmate/Contracts qedefi/Verified/OpenZeppelin/Contracts \
    qedefi/Verified/Solady/Contracts qedefi/Examples/Reentrancy/Contracts \
    qedefi/Verified/OpenZeppelin/Contracts \
    $(for t in "${MAINNET[@]}"; do printf '%s ' "qedefi/$(printf '%s' "${MNS[$t]}" | tr . /)"; done) \
    || { echo "error: generated files are out of date" >&2; exit 1; }
  echo "generated files are up to date"
fi
