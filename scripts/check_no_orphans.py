#!/usr/bin/env python3
"""Fail if any Atlas source file is unreachable from Atlas.lean."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMPORT_RE = re.compile(r"^import\s+(Atlas(?:\.[A-Za-z0-9_]+)*)", re.MULTILINE)


def module_path(module: str) -> Path:
    return ROOT / f"{module.replace('.', '/')}.lean"


def atlas_imports(path: Path) -> set[str]:
    return set(IMPORT_RE.findall(path.read_text(encoding="utf-8")))


def main() -> int:
    source_files = {ROOT / "Atlas.lean", *(ROOT / "Atlas").rglob("*.lean")}
    reachable: set[Path] = set()
    missing: set[Path] = set()
    frontier = [ROOT / "Atlas.lean"]

    while frontier:
        path = frontier.pop()
        if path in reachable:
            continue
        if not path.is_file():
            missing.add(path)
            continue
        reachable.add(path)
        frontier.extend(module_path(module) for module in atlas_imports(path))

    orphans = sorted(source_files - reachable)
    if missing or orphans:
        if missing:
            print("MISSING ATLAS IMPORT TARGETS:", file=sys.stderr)
            for path in sorted(missing):
                print(f"  {path.relative_to(ROOT)}", file=sys.stderr)
        if orphans:
            print("ORPHAN ATLAS SOURCES (not reachable from Atlas.lean):", file=sys.stderr)
            for path in orphans:
                print(f"  {path.relative_to(ROOT)}", file=sys.stderr)
        return 1

    print(f"Atlas import closure OK ({len(source_files)} source files reachable)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
