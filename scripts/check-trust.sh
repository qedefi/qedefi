#!/usr/bin/env bash
# Fail if a trust escape hatch is used (docs/architecture.md, principles 1–2).
#
# * The semantics (EvmLean/): no `sorry`, `axiom`, `opaque`, `partial def`, `unsafe`,
#   `@[extern]`, `implemented_by`, `native_decide`, `panic!`, `get!`, `head!`, `getLast!`,
#   `!`-indexing.
# * The proof libraries (EvmLogic/, qedefi/QEDefi/, qedefi/Examples/): no `sorry`, `axiom`,
#   `native_decide`.
#
# Comments and backtick-quoted spans (docs mentioning e.g. `opaque`) are ignored.
set -euo pipefail
cd "$(dirname "$0")/.."
scan() { # scan <regex> <paths...>
  local re=$1; shift
  find "$@" -name '*.lean' -print0 | xargs -0 perl -ne '
    BEGIN { $re = shift @ARGV; $d = 0 }
    my $l = $_; my $code = "";
    # drop block comments (nested `/- … -/`, including docstrings) and line comments
    while (length $l) {
      if ($d > 0) {
        if ($l =~ s/^.*?(\/-|-\/)//s) { $d += ($1 eq "/-") ? 1 : -1 } else { $l = "" }
      } elsif ($l =~ s/^(.*?)(\/-|--)//s) {
        $code .= $1; if ($2 eq "/-") { $d = 1 } else { $l = "" }
      } else { $code .= $l; $l = "" }
    }
    $code =~ s/`[^`]*`//g;
    print "$ARGV:$.: $_" if $code =~ /$re/;
    if (eof) { close ARGV; $d = 0 }' "$re"
}
semantics=$(scan '\bsorry\b|^\s*(private\s+|protected\s+)?(axiom|opaque|partial\s+def|unsafe)\b|\@\[extern|implemented_by|native_decide|panic!|\bget!|\bhead!|\bgetLast!|\]!' \
  EvmLean EvmLean.lean)
proofs=$(scan '\bsorry\b|^\s*(private\s+|protected\s+)?axiom\b|native_decide' \
  EvmLogic EvmLogic.lean qedefi/QEDefi qedefi/QEDefi.lean qedefi/Examples qedefi/Examples.lean)
status=0
if [ -n "$semantics" ]; then
  echo "$semantics"
  echo "error: trust escape hatch found in EvmLean/" >&2
  status=1
fi
if [ -n "$proofs" ]; then
  echo "$proofs"
  echo "error: sorry/axiom/native_decide found in a proof library" >&2
  status=1
fi
[ $status -eq 0 ] && echo "trust check passed"
exit $status
