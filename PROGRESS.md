# Progress journal — QG Constraint Atlas

> This document is edited and maintained by Claude and presented as-is.
> Newest entries first. Honest status only: done means gates-green and audited.

## 2026-07-08 — prior-art sweep in; Phase 1 DAG refined; spec session dispatched

Prior-art Fable agent delivered. Headlines:
- **Open field confirmed**: no Lorentzian manifolds, Schwarzschild, or singularity
  theorem formalized in ANY prover. Nearest kin: Isabelle AFP Schutz_Spacetime
  (order-theoretic SR) and Budapest FOL relativity (axiomatic, no geometry).
- **Mathlib alignment is live**: PR #26221 (Rothgang-Massot, ~6k lines, draft) is
  building covariant derivatives, Levi-Civita, geodesic flow, exp map. P1.4 must
  build ON it. Biggest true gap on our path: smooth dependence of ODE solutions on
  initial conditions (new node P1.4a). Gouëzel's Riemannian structure bakes in
  positive-definiteness → our pseudo-metric is a parallel sibling structure (matches
  design agent). Zulip design-floating deferred to owner's return (outward-facing).
- **Synthetic route assessed and parked**: Cavalletti-Manini-Mondino 2025-26 prove
  a synthetic Penrose for continuous spacetimes via optimal transport — but Mathlib
  has zero OT, the math is fresh/unsettled, and witnesses would need the smooth
  computations anyway. Classical Wald/O'Neill spine stands.
- **Adjudicated a design conflict**: prior-art agent wanted causal-space-generality
  specs; design agent rejected the abstraction (deletion test). Ruled for concrete
  relations with interface-thin order-lemma proofs (locality until reuse is real);
  K-P extraction deferred until a second instance exists.
- BLUEPRINT.md Phase 1 refined accordingly (P1.4a, P1.5b, P1.6 battery added).
- Dispatched: Fable spec-drafting session for P1.1-P1.3 on branch `phase-1`.

## 2026-07-08 — P1.1-P1.3 design proposal in, spot-audited

Fable design agent delivered the P1.1-P1.3 proposal; I verified its key Mathlib claims
directly against the pinned v4.31.0 source (all confirmed):
- Mathlib now HAS: Gouëzel's Riemannian bundle metrics (`Geometry/Manifold/{VectorBundle,
  Riemannian}/…`, `ContMDiffRiemannianMetric`, `riemannianMetricVectorSpace` at
  Riemannian/Basic.lean:103 — the constant-metric smoothness pattern our Minkowski
  witness needs), covariant derivatives + torsion, Sylvester signature (`sigNeg`,
  QuadraticForm/Signature.lean) = O'Neill's index ν. Nothing pseudo-Riemannian/
  Lorentzian/causal exists (grepped) — our gap is real and upstreamable.
- Recommended design (accepted pending prior-art report): Option A — general
  `PseudoRiemannianMetric` in Gouëzel's spelling minus positivity (no fiber-norm
  diamond problem in indefinite signature), `IsLorentzian` as index-1 Prop via
  `sigNeg`, `TimeOrientation` as continuous timelike section; chronology/causality as
  `Relation.TransGen` of single-C¹-segment reachability (= O'Neill's piecewise
  definition, transitivity free); Kronheimer-Penrose abstraction rejected (fails
  deletion test — Penrose thm needs topology+metric, not just order), but Wald ch. 8
  order lemmas to be proven interface-thin for later extraction.
- Risk register: general-spacetime lemmas (even "I⁺ open") gated on P1.4
  (exponential map/normal neighborhoods — genuine infra node); P1.2 Minkowski
  cone-characterization witness is the big honest proof (~1-3 wk); page-level
  citations must be verified during adversarial spec review.
- Full declaration list for the spec session is in the design report (session
  transcript); spec session dispatches after the prior-art sweep lands.

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
