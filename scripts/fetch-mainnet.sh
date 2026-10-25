#!/usr/bin/env bash
# Fetch a deployed mainnet contract as a verification target (network access; read-only).
#
#   scripts/fetch-mainnet.sh <Name> <address> [rpc-url]
#
# Writes contracts/mainnet/<Name>/:
#   source/…        verified sources, as Sourcify serves them (licence headers kept)
#   sourcify.json   compiler, settings, deployment, match status, bytecode transformations
#   abi.json        ABI of the verified contract
#   runtime.hex     eth_getCode at a pinned block (no 0x)
#   meta.json       address, block number and hash, code hash and size, compiler
# and checks that the fetched code equals the bytecode Sourcify verified. Contracts Sourcify
# does not have are taken from the public Blockscout instead (eth.blockscout.com, verified via
# its bytecode database): `blockscout.json` replaces `sourcify.json` (compiler, settings,
# external libraries, verification status; no bytecode transformations), and the check is
# against Blockscout's deployed bytecode. The hand-written
# files (storageLayout.json, genesis.json, notes) are left alone. `scripts/build-contracts.sh`
# is offline: it checks runtime.hex against meta.json's codeHash and generates the Lean module.
#
# The block is the RPC's latest block at fetch time: free endpoints serve only recent state
# (no archive reads). Code of a non-proxy contract never changes, so the code hash is the pin.
set -euo pipefail
export PATH="$HOME/.foundry/bin:$PATH"
cd "$(dirname "$0")/.."
NAME=$1
ADDR=$(cast to-check-sum-address "$2")
RPC=${3:-https://ethereum-rpc.publicnode.com}
D="contracts/mainnet/$NAME"
mkdir -p "$D/source"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

status=$(curl -sS -m 60 -o "$TMP/sourcify.json" -w '%{http_code}' \
  "https://sourcify.dev/server/v2/contract/1/$ADDR?fields=all")
if [ "$status" = 200 ] && jq -e '.match' "$TMP/sourcify.json" >/dev/null; then
  PROVIDER=sourcify
  jq -r '.sources | keys[]' "$TMP/sourcify.json" | while read -r p; do
    mkdir -p "$D/source/$(dirname "$p")"
    jq -j --arg p "$p" '.sources[$p].content' "$TMP/sourcify.json" > "$D/source/$p"
  done
  jq '{address, chainId, match, runtimeMatch, creationMatch, verifiedAt, compilation, deployment,
       proxyResolution, runtimeTransformations: .runtimeBytecode.transformations,
       runtimeCborAuxdata: .runtimeBytecode.cborAuxdata}' "$TMP/sourcify.json" > "$D/sourcify.json"
  jq '.abi' "$TMP/sourcify.json" > "$D/abi.json"
  VERIFIED=$(jq -r '.runtimeBytecode.onchainBytecode' "$TMP/sourcify.json")
else
  PROVIDER=blockscout
  curl -sS -f -m 60 "https://eth.blockscout.com/api/v2/smart-contracts/$ADDR" > "$TMP/bs.json"
  jq -e '.is_verified == true' "$TMP/bs.json" >/dev/null \
    || { echo "error: $ADDR is verified neither on Sourcify nor on Blockscout" >&2; exit 1; }
  jq -c '[{file_path, source_code}] + .additional_sources | .[]' "$TMP/bs.json" | while read -r e; do
    p=$(jq -r .file_path <<<"$e")
    case "$p" in /*|*..*) echo "error: unsafe source path $p" >&2; exit 1 ;; esac
    mkdir -p "$D/source/$(dirname "$p")"
    jq -j .source_code <<<"$e" > "$D/source/$p"
  done
  jq --arg addr "$ADDR" '{address: $addr, chainId: "1", provider: "blockscout", name, filePath: .file_path,
       compilerVersion: (.compiler_version | ltrimstr("v")), compilerSettings: .compiler_settings,
       externalLibraries: .external_libraries, isFullyVerified: .is_fully_verified,
       isPartiallyVerified: .is_partially_verified, verifiedAt: .verified_at}' "$TMP/bs.json" > "$D/blockscout.json"
  jq '.abi' "$TMP/bs.json" > "$D/abi.json"
  VERIFIED=$(jq -r '.deployed_bytecode' "$TMP/bs.json")
fi

BLOCK=$(( $(cast block-number --rpc-url "$RPC") - 3 ))  # a few blocks back: load-balanced nodes lag
BHASH=$(cast block --rpc-url "$RPC" "$BLOCK" -f hash)
cast code --rpc-url "$RPC" -B "$BLOCK" "$ADDR" | sed 's/^0x//' > "$D/runtime.hex"
CODE=$(cat "$D/runtime.hex")
[ -n "$CODE" ] || { echo "error: no code at $ADDR" >&2; exit 1; }
[ "0x$CODE" = "$VERIFIED" ] \
  || { echo "error: on-chain code differs from the bytecode $PROVIDER verified" >&2; exit 1; }
HASH=$(cast keccak "0x$CODE")
if [ "$PROVIDER" = sourcify ]; then
  jq -n --arg name "$NAME" --arg addr "$ADDR" --argjson block "$BLOCK" --arg bhash "$BHASH" \
    --arg hash "$HASH" --argjson size $(( ${#CODE} / 2 )) --slurpfile s "$D/sourcify.json" \
    '{name: $name, address: $addr, chainId: 1, block: $block, blockHash: $bhash, codeHash: $hash,
      codeSize: $size, contractName: $s[0].compilation.name,
      compiler: $s[0].compilation.compilerVersion,
      optimizer: $s[0].compilation.compilerSettings.optimizer,
      sourcify: {match: $s[0].match, runtimeMatch: $s[0].runtimeMatch, creationMatch: $s[0].creationMatch}}' \
    > "$D/meta.json"
else
  jq -n --arg name "$NAME" --arg addr "$ADDR" --argjson block "$BLOCK" --arg bhash "$BHASH" \
    --arg hash "$HASH" --argjson size $(( ${#CODE} / 2 )) --slurpfile s "$D/blockscout.json" \
    '{name: $name, address: $addr, chainId: 1, block: $block, blockHash: $bhash, codeHash: $hash,
      codeSize: $size, contractName: $s[0].name, compiler: $s[0].compilerVersion,
      optimizer: $s[0].compilerSettings.optimizer,
      blockscout: {fullyVerified: $s[0].isFullyVerified, partiallyVerified: $s[0].isPartiallyVerified}}' \
    > "$D/meta.json"
fi
echo "$NAME: $ADDR, $(( ${#CODE} / 2 )) B, code hash $HASH, block $BLOCK"
