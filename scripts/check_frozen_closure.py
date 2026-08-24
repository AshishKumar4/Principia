#!/usr/bin/env python3
"""Gate 4: frozen-spec and witness dependency integrity.

The frozen spec closure may leave Atlas/Specs/** only through files listed in
scripts/frozen-imports.txt. The complete Atlas closure reachable from witness files
must match scripts/witness-closure.txt exactly. Frozen entries must stay reachable
from one of those semantic roots.
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
WITNESS_MANIFEST = {
    line.strip()
    for line in (ROOT / "scripts/witness-closure.txt").read_text().splitlines()
    if line.strip() and not line.startswith("#")
}
IMPORT_RE = re.compile(r"^import\s+(Atlas\.[A-Za-z0-9_.]+)", re.M)


def module_to_path(mod: str) -> Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def imports_of(path: Path) -> set[str]:
    return set(IMPORT_RE.findall(path.read_text()))


def closure(seeds: list[Path]) -> set[Path]:
    seen: set[Path] = set()
    frontier = list(seeds)
    while frontier:
        path = frontier.pop()
        if path in seen or not path.exists():
            continue
        seen.add(path)
        for module in imports_of(path):
            frontier.append(module_to_path(module))
    return seen


def main() -> int:
    spec_closure = closure(list((ROOT / "Atlas/Specs").rglob("*.lean")))
    witness_closure = closure(list((ROOT / "Atlas/Witnesses").rglob("*.lean")))

    violations = []
    for path in sorted(spec_closure):
        relative = path.relative_to(ROOT).as_posix()
        if relative.startswith("Atlas/Specs/") or relative == "Atlas/Specs.lean":
            continue
        if relative not in FROZEN:
            violations.append(relative)

    actual_witness = {
        path.relative_to(ROOT).as_posix()
        for path in witness_closure
    }
    witness_added = sorted(actual_witness - WITNESS_MANIFEST)
    witness_removed = sorted(WITNESS_MANIFEST - actual_witness)

    semantic_closure = {
        path.relative_to(ROOT).as_posix()
        for path in spec_closure | witness_closure
    }
    stale_frozen = sorted(
        path for path in FROZEN
        if not (ROOT / path).is_file() or path not in semantic_closure
    )

    if violations:
        print("FROZEN-CLOSURE VIOLATIONS (spec-load-bearing files not in "
              "scripts/frozen-imports.txt):", file=sys.stderr)
        for violation in violations:
            print(f"  {violation}", file=sys.stderr)
    if witness_added:
        print("UNREVIEWED WITNESS DEPENDENCIES:", file=sys.stderr)
        for path in witness_added:
            print(f"  + {path}", file=sys.stderr)
    if witness_removed:
        print("STALE WITNESS DEPENDENCIES:", file=sys.stderr)
        for path in witness_removed:
            print(f"  - {path}", file=sys.stderr)
    if stale_frozen:
        print("STALE FROZEN-IMPORT ENTRIES:", file=sys.stderr)
        for path in stale_frozen:
            print(f"  {path}", file=sys.stderr)

    if violations or witness_added or witness_removed or stale_frozen:
        return 1

    print(
        f"Frozen dependency integrity OK ({len(spec_closure)} spec-closure files, "
        f"{len(witness_closure)} witness-closure files, {len(FROZEN)} frozen-by-import)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
