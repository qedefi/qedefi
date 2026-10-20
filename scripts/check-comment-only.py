#!/usr/bin/env python3
"""Check that changes to Lean files since a base revision touch only comments, whitespace
and `open` lines.

usage: scripts/check-comment-only.py <base-rev> [paths...]
"""
import re
import subprocess
import sys


def strip(src: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and src.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
        elif src[i] == '"':
            j = i + 1
            while j < len(src) and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append(src[i : j + 1])
            i = j + 1
        else:
            out.append(src[i])
            i += 1
    code = "".join(out)
    lines = [l for l in code.splitlines() if not re.match(r"\s*open\b", l)]
    return re.sub(r"\s+", " ", " ".join(lines)).strip()


def main() -> int:
    base, paths = sys.argv[1], sys.argv[2:]
    changed = subprocess.run(
        ["git", "diff", "--name-only", "--diff-filter=M", base, "--", *paths],
        capture_output=True, text=True, check=True,
    ).stdout.split()
    bad = []
    for f in changed:
        if not f.endswith(".lean"):
            continue
        old = subprocess.run(["git", "show", f"{base}:{f}"], capture_output=True, text=True).stdout
        if strip(old) != strip(open(f).read()):
            bad.append(f)
    for f in bad:
        print(f"code changed: {f}")
    print(f"{len(changed)} files changed, {len(bad)} with code changes")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
