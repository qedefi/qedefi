#!/usr/bin/env bash
# Symbolic-execution benchmark: time per executed instruction on `deposit`'s path.
#
#   scripts/bench-symexec.sh [RUNS]
#
# Elaborates the internal summaries `mintShares_wp`, `afterDeposit_wp` and `deposit_refines` (the
# whole `deposit` path with its revert branches; `ERC4626/DepositInternal.lean` and the first part
# of `ERC4626/Deposit.lean`) as a standalone file, with `trace.EvmLean.symStep` on, and an empty
# file with the same imports. Reports the instructions executed by the symbolic-execution
# tactics, the elaboration time beyond the imports (best of RUNS, default 3), and their ratio.
# Needs the defi package built up to Deposit's imports.
set -euo pipefail
runs=${1:-3}
export PATH="$HOME/.elan/bin:$PATH"
root=$(cd "$(dirname "$0")/.." && pwd)
src="$root/defi/Examples/Solmate/ERC4626/Deposit.lean"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
end=$(grep -n '^theorem mint_refines' "$src" | cut -d: -f1)
imports=$(grep -n '^import' "$src" | tail -1 | cut -d: -f1)
# The step trace exists from the code-table change on; older trees time without it.
opt=""
grep -q 'EvmLean.symStep' "$root/EvmLogic/Tactic/EvmStep.lean" && opt='set_option trace.EvmLean.symStep true'
# Where `mintShares_wp`/`afterDeposit_wp` live in their own module (`DepositInternal`), that
# module's body is prepended, so both trees elaborate the same proofs.
int="$root/defi/Examples/Solmate/ERC4626/DepositInternal.lean"
{ if [ -f "$int" ]; then
    grep '^import' "$int"; grep '^import' "$src" | grep -v 'ERC4626.DepositInternal$'
  else head -n "$imports" "$src"; fi
} > "$tmp/Empty.lean"
{ cat "$tmp/Empty.lean"; echo "$opt"
  if [ -f "$int" ]; then grep -v '^import' "$int"; fi
  sed -n "$((imports + 1)),$((end - 4))p" "$src"; echo 'end Examples.Solmate.ERC4626'; echo 'end'
} > "$tmp/Bench.lean"
cd "$root/defi"
best() { # file → best wall seconds
  local b=""
  for _ in $(seq "$runs"); do
    local t0 t1
    t0=$(python3 -c 'import time;print(time.time())')
    lake env lean "$1" > "$tmp/out.txt" 2>&1 || { cat "$tmp/out.txt" >&2; exit 1; }
    t1=$(python3 -c 'import time;print(time.time())')
    b=$(python3 -c "import sys;t=$t1-$t0;b='$b';print(t if b=='' else min(t,float(b)))")
  done
  echo "$b"
}
te=$(best "$tmp/Empty.lean")
tb=$(best "$tmp/Bench.lean")
n=$(grep -c 'EvmLean.symStep\]' "$tmp/out.txt" || true)
python3 -c "
te=$te; tb=$tb; n=$n
print(f'instructions: {n}')
print(f'imports: {te:.1f} s, file: {tb:.1f} s, beyond imports: {tb-te:.1f} s')
print(f'per instruction: {1000*(tb-te)/max(n,1):.1f} ms')"
