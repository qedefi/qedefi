#!/usr/bin/env bash
# Fetch the pinned execution-spec-tests fixtures (v5.4.0, the final Osaka release; the
# "develop" build, which fills tests up to Osaka and the BPO forks) into tests/fixtures-eest.
# Only the `blockchain_tests` and `transaction_tests` formats are kept.
set -euo pipefail
RELEASE=v5.4.0
URL="https://github.com/ethereum/execution-spec-tests/releases/download/$RELEASE/fixtures_develop.tar.gz"
DEST="$(cd "$(dirname "$0")/.." && pwd)/tests/fixtures-eest"
if [ -d "$DEST/fixtures/blockchain_tests" ]; then echo "EEST fixtures already present"; exit 0; fi
mkdir -p "$DEST"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
curl -fsSL -o "$TMP/fixtures.tar.gz" "$URL"
tar xzf "$TMP/fixtures.tar.gz" -C "$DEST" fixtures/.meta fixtures/blockchain_tests fixtures/transaction_tests
echo "EEST fixtures $RELEASE at $DEST/fixtures"
