# Progress journal — QG Constraint Atlas

> This document is edited and maintained by Claude and presented as-is.
> Newest entries first. Honest status only: done means gates-green and audited.

## 2026-07-08 — autonomous operation begins

Owner departing for several months; standing orders received and encoded in CLAUDE.md
(guard files, model policy, audit-before-merge, this journal). Scaffold is complete and
control-tested (commits 77023e9, 7fe5832, 3dabc97): Lean v4.31.0 + Mathlib v4.31.0
build green, axiom audit verified against planted violations, hooks verified blocking.

Phase 1 opened. In flight:
- P1.1 design research: Mathlib manifold/bundle/metric API deep-dive → Lorentzian
  structure design proposal (Fable subagent).
- Prior-art sweep: existing Lorentzian/GR formalizations in any prover, Mathlib
  Riemannian-geometry work in flight worth building on or waiting for (Fable subagent).

Next: spec session for P1.1-P1.3 from the design research, adversarial review vs.
Wald/O'Neill, freeze, Minkowski witness, then grind.
