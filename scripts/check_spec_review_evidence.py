#!/usr/bin/env python3
"""Link frozen-surface changes to spec-review commits and audit evidence."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SPEC_REVIEW = "[spec-review]"


def git(*args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout


def frozen_paths() -> set[str]:
    return {
        line.strip()
        for line in (ROOT / "scripts/frozen-imports.txt").read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    }


def is_frozen(path: str, frozen: set[str]) -> bool:
    return path == "Atlas/Specs.lean" or path.startswith("Atlas/Specs/") or path in frozen


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", required=True)
    parser.add_argument("--head", required=True)
    args = parser.parse_args()

    try:
        merge_base = git("merge-base", args.base, args.head).strip()
        changed = {
            line for line in git("diff", "--name-only", merge_base, args.head).splitlines() if line
        }
        messages = git("log", "--format=%B%x00", f"{merge_base}..{args.head}").split("\x00")
    except RuntimeError as error:
        print(f"FAILED: {error}", file=sys.stderr)
        return 2

    frozen_changed = sorted(path for path in changed if is_frozen(path, frozen_paths()))
    if not frozen_changed:
        print("Spec-review evidence gate: no frozen-surface changes")
        return 0

    tagged = [message for message in messages if SPEC_REVIEW in message]
    review_artifacts = sorted(path for path in changed if re.match(r"^audits/reviews/.+\.md$", path))

    if not tagged:
        print("FAILED: frozen-surface changes lack a [spec-review] commit:", file=sys.stderr)
        for path in frozen_changed:
            print(f"  {path}", file=sys.stderr)
        return 1
    if not review_artifacts:
        print(
            "FAILED: [spec-review] changes must add or update audits/reviews/<node>.md",
            file=sys.stderr,
        )
        return 1

    print(
        f"Spec-review evidence OK ({len(frozen_changed)} frozen files, "
        f"{len(review_artifacts)} review artifacts)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
