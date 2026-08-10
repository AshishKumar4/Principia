#!/usr/bin/env python3
"""Gate 4: frozen-import closure check.

Computes the transitive Atlas-import closure of Atlas/Specs/** and asserts every
file in it is either itself under Atlas/Specs/ or explicitly listed in
scripts/frozen-imports.txt (and therefore guarded by the commit-msg hook).
Closes the drift channel where a spec silently depends on an editable proof file.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FROZEN = {
    line.strip()
    for line in (ROOT / "scripts/frozen-imports.txt").read_text().splitlines()
    if line.strip() and not line.startswith("#")
}
IMPORT_RE = re.compile(r"^import\s+(Atlas\.[A-Za-z0-9_.]+)", re.M)


def module_to_path(mod: str) -> Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def imports_of(path: Path) -> set[str]:
    return set(IMPORT_RE.findall(path.read_text()))


def main() -> int:
    seeds = list((ROOT / "Atlas/Specs").rglob("*.lean"))
    seen: set[Path] = set()
    frontier = list(seeds)
    while frontier:
        f = frontier.pop()
        if f in seen or not f.exists():
            continue
        seen.add(f)
        for mod in imports_of(f):
            frontier.append(module_to_path(mod))

    violations = []
    for f in sorted(seen):
        rel = f.relative_to(ROOT).as_posix()
        if rel.startswith("Atlas/Specs/") or rel == "Atlas/Specs.lean":
            continue
        if rel not in FROZEN:
            violations.append(rel)

    if violations:
        print("FROZEN-CLOSURE VIOLATIONS (spec-load-bearing files not in "
              "scripts/frozen-imports.txt):", file=sys.stderr)
        for v in violations:
            print(f"  {v}", file=sys.stderr)
        return 1
    print(f"Frozen-import closure OK ({len(seen)} files in closure, "
          f"{len(FROZEN)} frozen-by-import)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
