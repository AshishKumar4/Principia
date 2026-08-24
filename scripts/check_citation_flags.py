#!/usr/bin/env python3
"""Require every unresolved citation-honesty flag to be explicitly tracked."""

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "scripts/citation-debt.txt"
FLAG_RE = re.compile(
    r"quoted from memory|not re-verified against (?:a|the) copy",
    re.IGNORECASE,
)


def debt_key(path: Path, line: str) -> str:
    digest = hashlib.sha256(line.strip().encode("utf-8")).hexdigest()[:16]
    return f"{path.relative_to(ROOT).as_posix()}:{digest}"


def manifest_entries() -> set[str]:
    return {
        line.strip()
        for line in MANIFEST.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    }


def current_entries() -> set[str]:
    entries: set[str] = set()
    for path in sorted((ROOT / "Atlas").rglob("*.lean")):
        for line in path.read_text(encoding="utf-8").splitlines():
            if FLAG_RE.search(line):
                entries.add(debt_key(path, line))
    return entries


def main() -> int:
    expected = manifest_entries()
    current = current_entries()
    untracked = sorted(current - expected)
    stale = sorted(expected - current)

    if untracked:
        print("UNTRACKED CITATION DEBT:", file=sys.stderr)
        for entry in untracked:
            print(f"  {entry}", file=sys.stderr)
    if stale:
        print("STALE CITATION-DEBT ENTRIES:", file=sys.stderr)
        for entry in stale:
            print(f"  {entry}", file=sys.stderr)
    if untracked or stale:
        print(
            "Update scripts/citation-debt.txt in the same reviewed change.",
            file=sys.stderr,
        )
        return 1

    print(f"Citation debt manifest OK ({len(current)} unresolved flags tracked)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
