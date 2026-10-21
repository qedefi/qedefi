#!/usr/bin/env python3
"""Compare two theorem dumps from scripts/dump-statements.sh.

usage: scripts/compare-statements.py BEFORE.tsv AFTER.tsv

Fails if any theorem disappeared, changed its statement, or changed its axioms. New theorems
are listed but allowed. With a rename, map names first (e.g. sed) before comparing.
"""
import sys


def load(path):
    rows = {}
    for line in open(path).read().splitlines():
        name, h, axioms = (line.split("\t") + [""])[:3]
        rows[name] = (h, axioms)
    return rows


before, after = load(sys.argv[1]), load(sys.argv[2])
missing = sorted(n for n in before if n not in after)
changed = sorted(n for n in before if n in after and after[n][0] != before[n][0])
axioms = sorted(n for n in before if n in after and after[n][1] != before[n][1])
new = sorted(set(after) - set(before))
union = sorted({a for _, ax in after.values() for a in ax.split(",") if a})
print(f"before {len(before)}, after {len(after)}, new {len(new)}")
for label, names in [("missing", missing), ("statement changed", changed), ("axioms changed", axioms)]:
    print(f"{label}: {len(names)}" + (f"  e.g. {names[:5]}" if names else ""))
print(f"axioms used: {union}")
sys.exit(1 if missing or changed or axioms else 0)
