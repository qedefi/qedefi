#!/usr/bin/env bash
# Clean, cache-free build of the proof libraries with per-module timings.
#
#   scripts/bench-build.sh OUTDIR
#
# Deletes `.lake/build` and `qedefi/.lake/build` (keeps `qedefi/.lake/packages`, i.e. Mathlib from
# cache), builds `EvmLean` untimed, then times `EvmLogic` (root package) and `QEDefi Examples`
# (qedefi package) separately with `--wfail` at Lake's default parallelism. Writes
# `OUTDIR/{evmlogic,qedefi}.log` (Lake's output, with per-module durations) and
# `OUTDIR/summary.txt` (wall and CPU seconds of each phase).
set -euo pipefail
out=${1:?usage: bench-build.sh OUTDIR}
mkdir -p "$out"
export PATH="$HOME/.elan/bin:$PATH"
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
rm -rf .lake/build qedefi/.lake/build
lake build --wfail EvmLean > "$out/evmlean.log" 2>&1

phase() { # name dir targets...
  local name=$1 dir=$2; shift 2
  local t0 t1
  t0=$(date +%s.%N 2>/dev/null || python3 -c 'import time;print(time.time())')
  ( cd "$dir" && /usr/bin/time -p lake build --wfail -v "$@" ) > "$out/$name.log" 2> "$out/$name.time"
  t1=$(python3 -c 'import time;print(time.time())')
  echo "$name: $(grep -E '^(real|user|sys)' "$out/$name.time" | tr '\n' ' ')" >> "$out/summary.txt"
}
: > "$out/summary.txt"
phase evmlogic "$root" EvmLogic
phase qedefi "$root/qedefi" QEDefi Examples
cat "$out/summary.txt"
