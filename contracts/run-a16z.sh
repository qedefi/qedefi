#!/usr/bin/env bash
# Run the a16z ERC-4626 property suite against the Solmate and OpenZeppelin targets.
#   contracts/run-a16z.sh [extra forge test args, e.g. --fuzz-runs 10000]
# Fetches the pinned test dependencies into contracts/ext/ (not committed).
set -euo pipefail
export PATH="$HOME/.foundry/bin:$PATH"
cd "$(dirname "$0")"
FORGE_STD_COMMIT=f3dae6e6ee381f25eb6a246f7da9b85c91a68219   # forge-std v1.17.0
A16Z_COMMIT=ac485460e014f22807c1ff687e0b4dc3af96ee40        # a16z/erc4626-tests main, 2025-07-29
fetch() { # fetch <dir> <url> <commit>
  if [ "$(git -C "$1" rev-parse HEAD 2>/dev/null || true)" != "$3" ]; then
    rm -rf "$1"; mkdir -p "$1"
    git -C "$1" init -q
    git -C "$1" fetch -q --depth 1 "$2" "$3"
    git -C "$1" checkout -q FETCH_HEAD
  fi
}
fetch ext/forge-std https://github.com/foundry-rs/forge-std "$FORGE_STD_COMMIT"
fetch ext/erc4626-tests https://github.com/a16z/erc4626-tests "$A16Z_COMMIT"
FOUNDRY_PROFILE=a16z forge test "$@"
