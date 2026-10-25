#!/usr/bin/env bash
# Dump every project theorem as `name <TAB> statement-hash <TAB> axioms` (sorted), from the
# current build outputs (no rebuild). Compare two dumps with scripts/compare-statements.py.
#
#   scripts/dump-statements.sh OUT.tsv
#
# Run after building; covers EvmLean, EvmLogic, QEDefi, Verified, Examples, Difftest and
# QEDefiTest.
set -euo pipefail
out=$(cd "$(dirname "${1:?usage: dump-statements.sh OUT.tsv}")" && pwd)/$(basename "$1")
root=$(cd "$(dirname "$0")/.." && pwd)
export PATH="$HOME/.elan/bin:$PATH"
tmp=$(mktemp -t dumpstmts).lean
trap 'rm -f "$tmp"' EXIT
cd "$root/qedefi"
{
  echo 'import EvmLogic'; echo 'import QEDefi'; echo 'import Verified'; echo 'import Examples'
  echo 'import Difftest'
  find QEDefiTest -name '*.lean' | sed 's|\.lean$||; s|/|.|g; s/^/import /'
  cat <<'EOF'
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let ours (m : Name) : Bool :=
    [`EvmLean, `EvmLogic, `QEDefi, `Verified, `Examples, `Difftest, `QEDefiTest].any (·.isPrefixOf m)
  let mut out : Array String := #[]
  for (name, ci) in env.constants.toList do
    if let .thmInfo t := ci then
      if name.isInternalDetail then continue
      if let some idx := env.getModuleIdxFor? name then
        if ours env.header.moduleNames[idx.toNat]! then
          let axs ← liftCoreM (Lean.collectAxioms name)
          let axStr := String.intercalate "," ((axs.map toString).qsort (· < ·)).toList
          out := out.push s!"{name}\t{t.type.hash}\t{axStr}"
  IO.FS.writeFile (System.FilePath.mk (← IO.getEnv "OUTF").get!)
    (String.intercalate "\n" (out.qsort (· < ·)).toList)
EOF
} > "$tmp"
lake build QEDefiTest > /dev/null
OUTF="$out" lake env lean "$tmp"
echo "$(wc -l < "$out" | tr -d ' ') theorems -> $out"
