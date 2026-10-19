#!/usr/bin/env bash
# Fail if the semantics uses any trust escape hatch (DESIGN.md, principles 1–2).
# Backtick-quoted spans (docs mentioning e.g. `opaque`) are ignored.
set -euo pipefail
cd "$(dirname "$0")/.."
hits=$(find EvmLean EvmLean.lean -name '*.lean' -print0 | xargs -0 perl -ne '
  my $l = $_; $l =~ s/`[^`]*`//g;
  print "$ARGV:$.: $_" if $l =~ /\bsorry\b|^\s*(private\s+|protected\s+)?(axiom|opaque|partial\s+def|unsafe)\b|\@\[extern|implemented_by|native_decide|panic!|\bget!|\bhead!|\bgetLast!|\]!/;
  close ARGV if eof;')
if [ -n "$hits" ]; then
  echo "$hits"
  echo "error: trust escape hatch found in EvmLean/" >&2
  exit 1
fi
echo "trust check passed"
