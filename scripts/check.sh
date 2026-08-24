#!/usr/bin/env bash
# Full verification gate. Must pass before any merge to main (see CLAUDE.md).
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

echo "== gate 1/10: kernel verification (lake build) =="
lake build
# CandidateLab has no root aggregator by design (candidate-owned tree); every
# committed module must still build, or non-entrypoint files rot silently.
candidatelab_modules=$(find CandidateLab -name '*.lean' | sed 's/\.lean$//; s#/#.#g' | sort)
if [ -n "${candidatelab_modules}" ]; then
  # shellcheck disable=SC2086
  lake build ${candidatelab_modules}
fi

echo "== gate 2/10: axiom audit =="
lake env lean scripts/AxiomAudit.lean

echo "== gate 3/10: forbidden-token scan =="
# Authoritative soundness lives in gates 1-2; this catches tokens the audit can miss
# (axiom/unsafe declarations that are merely present, native_decide) plus sorry, early.
if grep -rnE --include='*.lean' \
    '(^|[^[:alnum:]_])(sorry|admit|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*(axiom|unsafe)[[:space:]]' \
    Atlas/ Atlas.lean CandidateLab/; then
  echo "FAILED: forbidden tokens found above" >&2
  exit 1
fi

echo "== gate 4/10: frozen-spec and witness dependency integrity =="
python3 scripts/check_frozen_closure.py

echo "== gate 5/10: external kernel re-verification (lean4checker) =="
if [ ! -x "$HOME/.local/bin/lean4checker" ]; then
  echo "FAILED: lean4checker is required at ~/.local/bin/lean4checker." >&2
  echo "Install the pinned checker version documented in CLAUDE.md." >&2
  exit 1
fi
lake env "$HOME/.local/bin/lean4checker" Atlas
echo "lean4checker passed (external kernel re-verification of all Atlas modules)."


echo "== gate 6/10: Atlas orphan-source detector =="
python3 scripts/check_no_orphans.py

echo "== gate 7/10: citation-debt manifest =="
python3 scripts/check_citation_flags.py

echo "== gate 8/10: witness-surface audit =="
lake env lean scripts/WitnessAudit.lean

echo "== gate 9/10: committed probe recompilation =="
python3 scripts/check_probes.py

echo "== gate 10/10: committed candidates formal audit =="
# Every committed candidate must pass its own sandboxed Lean evaluation
# (compile + generated checker + classical-trio audit) through the platform.
for candidate in candidates/*/; do
  echo "  auditing ${candidate}"
  python3 -m principia --repo . evaluate "${candidate}" \
    --output .principia/gate-evaluations
done
echo "All gates passed."
