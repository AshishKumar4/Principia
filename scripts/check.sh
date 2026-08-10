#!/usr/bin/env bash
# Full verification gate. Must pass before any merge to main (see CLAUDE.md).
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

echo "== gate 1/5: kernel verification (lake build) =="
lake build

echo "== gate 2/5: axiom audit =="
lake env lean scripts/AxiomAudit.lean

echo "== gate 3/5: forbidden-token scan =="
# Authoritative soundness lives in gates 1-2; this catches tokens the audit can miss
# (axiom/unsafe declarations that are merely present, native_decide) plus sorry, early.
if grep -rnE --include='*.lean' \
    '(^|[^[:alnum:]_])(sorry|admit|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*(axiom|unsafe)[[:space:]]' \
    Atlas/ Atlas.lean; then
  echo "FAILED: forbidden tokens found above" >&2
  exit 1
fi

echo "== gate 4/5: frozen-import closure =="
python3 scripts/check_frozen_closure.py

echo "== gate 5/5: external kernel re-verification (lean4checker, if installed) =="
if command -v lean4checker >/dev/null 2>&1 || [ -x "$HOME/.local/bin/lean4checker" ]; then
  lake env "${HOME}/.local/bin/lean4checker" Atlas 2>/dev/null || lake env lean4checker Atlas
  echo "lean4checker passed."
else
  echo "SKIPPED (lean4checker not installed — advisory until installed; see CLAUDE.md)."
fi

echo "All gates passed."
