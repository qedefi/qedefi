#!/usr/bin/env bash
# Per-declaration elaboration and kernel times of one Lean file (top N), from
# `trace.profiler`.
#
#   scripts/profile-file.sh PATH/TO/File.lean [N]
#
# Run from the package that owns the file (`defi/` for `defi/...`). Times are wall seconds of
# `elaborating proof of …` (tactic proof, including its kernel check when synchronous) and
# `typechecking declarations […]` (kernel).
set -euo pipefail
f=${1:?usage: profile-file.sh FILE [N]}
n=${2:-20}
export PATH="$HOME/.elan/bin:$PATH"
out=$(mktemp)
trap 'rm -f "$out"' EXIT
lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=200 -DElab.async=false "$f" \
  > "$out" 2>&1 || true
echo "== elaboration (s) =="
grep -E '^\[Elab.(async|command)\] \[[0-9.]+\]' "$out" | \
  sed -E 's/^\[Elab.[a-z]+\] \[([0-9.]+)\] [^ ]+ (.*)$/\1 \2/' | sort -rn | head -n "$n"
echo "== kernel (s) =="
grep -E '\[Kernel\] \[[0-9.]+\]' "$out" | \
  sed -E 's/^ *\[Kernel\] \[([0-9.]+)\] [^ ]+ typechecking declarations (.*)$/\1 \2/' | sort -rn | head -n "$n"
echo "== errors =="
grep -E 'error' "$out" | head -5 || true
