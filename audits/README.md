# Audit artifacts

> This directory is edited and maintained by Claude and presented as-is.

Committed, reproducible evidence for every spec-freeze review (Workflow v2,
CLAUDE.md):

- `probes/<node>/` — the kernel-probe Lean files a review compiled against the
  built library. Recompile with `lake env lean <file>` to reproduce a verdict.
- `reviews/<node>.md` — the review verdict summaries (defects found, probe
  results, freeze recommendation), for both the Fable adversarial pass and the
  Codex cross-model pass.

Reviews before 2026-08-07 predate this policy. Their original probe files lived
in session-temporary scratchpads and were LOST with those sessions — that gap is
why this policy exists. The X.3 backfill (2026-08-23) recreated the five lost
probes as committed artifacts: `probes/P2.2-slice1/` (Fock symmetrizer),
`probes/P2.2-slice2/` (CCR roundtrip and the 2·½=1 normalization pin),
`probes/P2.3c/` (Cayley scalar model), `probes/P2.3d/` (Bool PVM),
`probes/P2.3g/` (Stone generator). Git now proves these recreated probes compile
against the frozen specs on every gate run; the historical fact that the
*original* probes ran in those reviews remains transcript-only and is recorded in
PROGRESS.md.
