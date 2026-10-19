#!/usr/bin/env bash
# Fetch the pinned ethereum/tests fixtures (Cancun refill) into tests/fixtures.
set -euo pipefail
PIN=08839f54ebdeb808ff4171a7ddb8803dfa8963a8
DEST="$(dirname "$0")/../tests/fixtures"
if [ -d "$DEST/.git" ]; then echo "fixtures already present"; exit 0; fi
git init -q "$DEST"
git -C "$DEST" remote add origin https://github.com/ethereum/tests.git
git -C "$DEST" fetch -q --depth 1 origin "$PIN"
git -C "$DEST" checkout -q FETCH_HEAD
echo "fixtures at $PIN"
