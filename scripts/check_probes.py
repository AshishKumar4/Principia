#!/usr/bin/env python3
"""Recompile every committed Lean review probe."""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    probes = sorted((ROOT / "audits/probes").rglob("*.lean"))
    if not probes:
        print("FAILED: no committed Lean probes found", file=sys.stderr)
        return 1

    env = os.environ.copy()
    env["PATH"] = f"{Path.home() / '.elan/bin'}:{env.get('PATH', '')}"
    failures: list[Path] = []
    for probe in probes:
        relative = probe.relative_to(ROOT)
        print(f"  recompiling {relative}")
        result = subprocess.run(
            ["lake", "env", "lean", str(relative)],
            cwd=ROOT,
            env=env,
            check=False,
        )
        if result.returncode != 0:
            failures.append(relative)

    if failures:
        print("FAILED LEAN PROBES:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print(f"Committed probe closure OK ({len(probes)} probes recompiled)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
