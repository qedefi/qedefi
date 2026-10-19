#!/usr/bin/env bash
# Fail if the semantics uses any trust escape hatch (see DESIGN.md, principle 1-2).
set -euo pipefail
cd "$(dirname "$0")/.."
pattern='\bsorry\b|^\s*axiom\b|\bopaque\b|\bpartial def\b|\bunsafe\b|@\[extern|implemented_by|native_decide|panic!|\bget!|\bhead!|\bgetLast!|\]!'
if grep -rnE "$pattern" EvmLean EvmLean.lean; then
  echo "error: trust escape hatch found in EvmLean/" >&2
  exit 1
fi
echo "trust check passed"
