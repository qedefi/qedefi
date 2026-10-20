#!/usr/bin/env bash
# Build the ERC-4626 verification targets with the pinned compiler, extract their artifacts
# and generate the Lean constants in defi/Examples/{Solmate,OpenZeppelin}/Contracts/.
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
#   defi/Examples/Solmate/Contracts/{SolmateAsset,SolmateVault}.lean
#   defi/Examples/OpenZeppelin/Contracts/{OzAsset,OzVault}.lean
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

SOLC="$HOME/.svm/0.8.28/solc-0.8.28"
"$SOLC" --version | grep -q '0.8.28+commit.7893614a' || { echo "error: need solc 0.8.28 at $SOLC" >&2; exit 1; }

( cd "$C" && forge build --force >/dev/null )

# Artifact path and contract name of each target.
declare -A SRC=(
  [SolmateAsset]="out/MockERC20.sol/MockERC20.json"
  [SolmateVault]="out/MockERC4626.sol/MockERC4626.json"
  [OzAsset]="out/ERC20Mock.sol/ERC20Mock.json"
  [OzVault]="out/OzVault.sol/OzVault.json"
)
declare -A SOLNAME=(
  [SolmateAsset]="lib/solmate/src/test/utils/mocks/MockERC20.sol:MockERC20"
  [SolmateVault]="lib/solmate/src/test/utils/mocks/MockERC4626.sol:MockERC4626"
  [OzAsset]="lib/openzeppelin-contracts/contracts/mocks/token/ERC20Mock.sol:ERC20Mock"
  [OzVault]="src/OzVault.sol:OzVault"
)
TARGETS=(SolmateAsset SolmateVault OzAsset OzVault)
# Directory of each generated Lean module.
# Lean namespace prefix of each generated module (mirrors its directory).
declare -A LEANNS=(
  [SolmateAsset]="Examples.Solmate.Contracts"
  [SolmateVault]="Examples.Solmate.Contracts"
  [OzAsset]="Examples.OpenZeppelin.Contracts"
  [OzVault]="Examples.OpenZeppelin.Contracts"
)
declare -A LEANDIR=(
  [SolmateAsset]="$ROOT/defi/Examples/Solmate/Contracts"
  [SolmateVault]="$ROOT/defi/Examples/Solmate/Contracts"
  [OzAsset]="$ROOT/defi/Examples/OpenZeppelin/Contracts"
  [OzVault]="$ROOT/defi/Examples/OpenZeppelin/Contracts"
)

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

[ "${ADDR[SolmateAsset]}" = "${ADDR[OzAsset]}" ] && [ "${ADDR[SolmateVault]}" = "${ADDR[OzVault]}" ] \
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
    decimals) echo "decimals" ;;
    _underlyingDecimals) echo "underlyingDecimals" ;;
    INITIAL_CHAIN_ID) echo "initialChainId" ;;
    INITIAL_DOMAIN_SEPARATOR) echo "initialDomainSeparator" ;;
    *) echo "error: unknown immutable $1" >&2; exit 1 ;;
  esac
}
imm_type() { case "$1" in asset|_asset) echo "Address" ;; *) echo "Word" ;; esac; }
imm_toword() { case "$1" in asset|_asset) echo "Word.ofAddress i.$2" ;; *) echo "i.$2" ;; esac; }

# Lean expression of a solc storage type, recursively through the `types` table.
JQ_TYPE='def ty($types; t): $types[t] as $x
  | if $x.encoding == "mapping" then "(.mapping \(ty($types; $x.key)) \(ty($types; $x.value)))"
    elif $x.encoding == "bytes" then "(.bytes \"\($x.label)\")"
    elif $x.encoding == "dynamic_array" then "(.dynamicArray \(ty($types; $x.base)))"
    else "(.inplace \"\($x.label)\" \($x.numberOfBytes))" end;'

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
  f="${LEANDIR[$t]}/$t.lean"
  nimm=$(jq length "$d/immutableReferences.json")
  rsize=$(( ${#code} / 2 ))
  csize=$(( $(wc -c < "$d/creation.hex" | tr -d ' ') / 2 ))
  {
    cat <<EOF
import EvmLogic.Solidity.Immutables
import EvmLogic.Solidity.Layout
import EvmLogic.Program.Code

/-!
# \`$t\`: compiled bytecode and metadata (generated)

Generated by \`scripts/build-contracts.sh\` from
\`contracts/${SOLNAME[$t]}\`
(solc 0.8.28, optimizer 200 runs, Cancun, no via-IR, no metadata). Do not edit; rerun the
script. Raw artifacts: \`contracts/artifacts/$t/\`.

Canonical deployment (\`Examples.Deployment.deployer\`, \`Examples.Deployment.chainId\`): deployer
\`${DEPLOYER}\`, chain id ${CHAIN_ID}, this contract at
\`${ADDR[$t]}\`.
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

/-- \`runtimeCode\` has the size of the compiled runtime code. -/
theorem size_runtimeCode : runtimeCode.size = $rsize := by decide +kernel

/-! Kernel lookup table of \`runtimeCode\` (bytes and jump destinations), checked once:
\`runtimeCode.codeTable\`, \`runtimeCode.codeTable_ok\`. -/
code_table runtimeCode

/-- \`creationCode\` has the size of the compiled creation code. -/
theorem size_creationCode : creationCode.size = $csize := by decide +kernel

/-- The canonical address of this contract. -/
def address : Address := ${ADDR[$t]}

EOF
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
      echo "/-- Patching the canonical immutables into \`runtimeCode\` gives \`runtimeCode\`. -/"
      echo "theorem runtimeCodeWith_deployment : runtimeCodeWith deployment = runtimeCode :="
      echo "  eq_of_data_toList_eq (by decide +kernel)"
      echo
    else
      echo "/-- The contract has no immutables: its runtime code is independent of the deployment. -/"
      echo "def immutableRefs : List ImmutableRef := []"
      echo
    fi
    echo "/-- Function selectors (\`forge inspect … methodIdentifiers\`). -/"
    echo "def selectors : List (String × UInt32) := ["
    jq -r 'to_entries | map("  (\"\(.key)\", 0x\(.value))") | join(",\n")' "$d/methodIdentifiers.json"
    echo "]"
    echo
    echo "/-- Event signatures and their topic (\`forge inspect … events\`). -/"
    echo "def events : List (String × Word) := ["
    jq -r 'to_entries | map("  (\"\(.key)\", \(.value))") | join(",\n")' "$d/events.json"
    echo "]"
    echo
    echo "/-- Custom-error selectors (\`forge inspect … errors\`). -/"
    echo "def errors : List (String × UInt32) := ["
    jq -r 'if length == 0 then "" else to_entries | map("  (\"\(.key)\", 0x\(.value))") | join(",\n") end' "$d/errors.json" | sed '/^$/d'
    echo "]"
    echo
    echo "/-- Storage layout (\`forge inspect … storageLayout\`). -/"
    echo "def storageLayout : List StorageVar := ["
    jq -r "$JQ_TYPE"' .types as $types | [.storage[] |
      "  { label := \"\(.label)\", slot := \(.slot), offset := \(.offset),\n    type := \(ty($types; .type)) }"]
      | join(",\n")' "$d/storageLayout.json"
    echo "]"
    echo
    echo "end ${LEANNS[$t]}.$t"
  } > "$TMP/$t.lean"
  mv "$TMP/$t.lean" "$f"
done

jq -n --arg deployer "$DEPLOYER" --argjson chainId "$CHAIN_ID" \
  --arg sa "${ADDR[SolmateAsset]}" --arg sv "${ADDR[SolmateVault]}" \
  --arg oa "${ADDR[OzAsset]}" --arg ov "${ADDR[OzVault]}" \
  --arg saArgs "${ARGS[SolmateAsset]}" --arg svArgs "${ARGS[SolmateVault]}" --arg ovArgs "${ARGS[OzVault]}" \
  '{chainId: $chainId, deployer: $deployer, evmVersion: "cancun", solc: "0.8.28+commit.7893614a",
    note: "Each family is deployed on its own fresh chain: the asset at deployer nonce 0, the vault at nonce 1.",
    solmate: {asset: {contract: "MockERC20", address: $sa, args: ["Solmate Asset", "SAST", 18], argsHex: $saArgs},
              vault: {contract: "MockERC4626", address: $sv, args: [$sa, "Solmate Vault", "svSAST"], argsHex: $svArgs}},
    openzeppelin: {asset: {contract: "ERC20Mock", address: $oa, args: [], argsHex: ""},
                   vault: {contract: "OzVault", address: $ov, args: [$oa], argsHex: $ovArgs}}}' \
  > "$ART/deployment.json"

for t in "${TARGETS[@]}"; do
  echo "$t: runtime $(( $(wc -c < "$ART/$t/runtime.hex") / 2 )) B, creation $(( $(wc -c < "$ART/$t/creation.hex") / 2 )) B, at ${ADDR[$t]}"
done

if [ $CHECK -eq 1 ]; then
  git -C "$ROOT" diff --exit-code -- contracts/artifacts defi/Examples/Solmate/Contracts \
    defi/Examples/OpenZeppelin/Contracts \
    || { echo "error: generated files are out of date" >&2; exit 1; }
  echo "generated files are up to date"
fi
