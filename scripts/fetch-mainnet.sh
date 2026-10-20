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
# and checks that the fetched code equals the bytecode Sourcify verified. The hand-written
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

curl -sS -f -m 60 "https://sourcify.dev/server/v2/contract/1/$ADDR?fields=all" > "$TMP/sourcify.json"
jq -e '.match' "$TMP/sourcify.json" >/dev/null || { echo "error: $ADDR is not verified on Sourcify" >&2; exit 1; }
jq -r '.sources | keys[]' "$TMP/sourcify.json" | while read -r p; do
  mkdir -p "$D/source/$(dirname "$p")"
  jq -j --arg p "$p" '.sources[$p].content' "$TMP/sourcify.json" > "$D/source/$p"
done
jq '{address, chainId, match, runtimeMatch, creationMatch, verifiedAt, compilation, deployment,
     proxyResolution, runtimeTransformations: .runtimeBytecode.transformations,
     runtimeCborAuxdata: .runtimeBytecode.cborAuxdata}' "$TMP/sourcify.json" > "$D/sourcify.json"
jq '.abi' "$TMP/sourcify.json" > "$D/abi.json"

BLOCK=$(( $(cast block-number --rpc-url "$RPC") - 3 ))  # a few blocks back: load-balanced nodes lag
BHASH=$(cast block --rpc-url "$RPC" "$BLOCK" -f hash)
cast code --rpc-url "$RPC" -B "$BLOCK" "$ADDR" | sed 's/^0x//' > "$D/runtime.hex"
CODE=$(cat "$D/runtime.hex")
[ -n "$CODE" ] || { echo "error: no code at $ADDR" >&2; exit 1; }
[ "0x$CODE" = "$(jq -r '.runtimeBytecode.onchainBytecode' "$TMP/sourcify.json")" ] \
  || { echo "error: on-chain code differs from Sourcify's verified bytecode" >&2; exit 1; }
HASH=$(cast keccak "0x$CODE")
jq -n --arg name "$NAME" --arg addr "$ADDR" --argjson block "$BLOCK" --arg bhash "$BHASH" \
  --arg hash "$HASH" --argjson size $(( ${#CODE} / 2 )) --slurpfile s "$D/sourcify.json" \
  '{name: $name, address: $addr, chainId: 1, block: $block, blockHash: $bhash, codeHash: $hash,
    codeSize: $size, contractName: $s[0].compilation.name,
    compiler: $s[0].compilation.compilerVersion,
    optimizer: $s[0].compilation.compilerSettings.optimizer,
    sourcify: {match: $s[0].match, runtimeMatch: $s[0].runtimeMatch, creationMatch: $s[0].creationMatch}}' \
  > "$D/meta.json"
echo "$NAME: $ADDR, $(( ${#CODE} / 2 )) B, code hash $HASH, block $BLOCK"
