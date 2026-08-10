# Audit artifacts

> This directory is edited and maintained by Claude and presented as-is.

Committed, reproducible evidence for every spec-freeze review (Workflow v2,
CLAUDE.md):

- `probes/<node>/` — the kernel-probe Lean files a review compiled against the
  built library. Recompile with `lake env lean <file>` to reproduce a verdict.
- `reviews/<node>.md` — the review verdict summaries (defects found, probe
  results, freeze recommendation), for both the Fable adversarial pass and the
  Codex cross-model pass.

Reviews before 2026-08-07 predate this policy. Their verdicts are quoted in
PROGRESS.md and commit messages, but their probe files (CCR roundtrip, Fock
symmetrizer, Cayley scalar, Bool PVM, Stone generator) lived in session-temporary
scratchpads and were LOST with those sessions — the committed record proves the
claimed theorems compile (they are re-derivable from the frozen specs), but Git
alone cannot prove those specific review probes ran. That gap is exactly why this
policy now exists; a backfill node re-creating the key probes as committed
artifacts is queued in BLUEPRINT (X.3).
