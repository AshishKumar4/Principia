#!/usr/bin/env bash
# Full verification gate. Must pass before any merge to main (see CLAUDE.md).
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

echo "== gate 1/3: kernel verification (lake build) =="
lake build

echo "== gate 2/3: axiom audit =="
lake env lean scripts/AxiomAudit.lean

echo "== gate 3/3: forbidden-token scan =="
# Authoritative soundness lives in gates 1-2; this catches tokens the audit can miss
# (axiom/unsafe declarations that are merely present, native_decide) plus sorry, early.
if grep -rnE --include='*.lean' \
    '(^|[^[:alnum:]_])(sorry|admit|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*(axiom|unsafe)[[:space:]]' \
    Atlas/ Atlas.lean; then
  echo "FAILED: forbidden tokens found above" >&2
  exit 1
fi

echo "All gates passed."
