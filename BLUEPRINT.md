# Blueprint — QG Constraint Atlas

> This document is edited and maintained by Claude and presented as-is.

The dependency DAG of the project. Every work item is a node here; grind sessions claim
nodes and update statuses. Statuses: `todo`, `spec` (statement frozen, unproven),
`proving`, `done` (on main, gates green). Decomposing a node adds child nodes; nodes are
never weakened in place (see CLAUDE.md).

Grounding: `RESEARCH.md` — what already exists (physlib, OSforGFF), which mathematics is
theorem-level vs open, and the Mathlib gap map this blueprint routes around.

## Phase 0 — foundations & gates `[done]`

- P0.1 `done` Research consolidation (`RESEARCH.md`).
- P0.2 `done` Project scaffold: Lean v4.31.0 + Mathlib v4.31.0, layout, CI gates
  (axiom audit, token scan, spec-freeze hooks), this blueprint.

## Phase 1 — GR spine → Penrose singularity theorem

The formal statement that classical GR predicts its own breakdown. Source of truth:
Wald ch. 8-9; O'Neill, *Semi-Riemannian Geometry*; Penrose 1965 (PRL 14, 57).
Mathlib has smooth manifolds and is weak on (semi-)Riemannian geometry; this phase is
mostly infrastructure with a famous theorem on top.

Design decisions (2026-07-08, from the design + prior-art research; details in
PROGRESS.md): signature-generic `PseudoRiemannianMetric` in Gouëzel's
`ContMDiffRiemannianMetric` spelling minus positivity, `IsLorentzian` via `sigNeg`;
chronology/causality as `Relation.TransGen` of single-C¹-segment reachability
(= O'Neill's piecewise defs, transitivity free); concrete relations, NOT a
Kronheimer-Penrose abstraction (deletion test — extract later if a second instance
materializes; keep order-lemma proofs interface-thin). Prior art: no Lorentzian/GR/
singularity formalization exists in any prover; align with Mathlib PR #26221
(covariant derivatives/Levi-Civita/geodesics, Rothgang-Massot) rather than build beside
it. Canonical sources: Wald ch. 8-9; O'Neill ch. 14; Minguzzi Living Rev. Rel. 22:3.

- P1.1 `done` Spec FROZEN: `PseudoRiemannianMetric` + index + `IsLorentzian` + causal
  character of vectors + `TimeOrientation` (`Atlas/Specs/Spacetime/Metric.lean`).
  Drafted, dossier-anchored (docs/dossiers/P1-causality-sources.md), adversarially
  reviewed (probe-verified), revised, frozen 2026-07-08.
- P1.2 `done` Spec FROZEN: causal curves (Mathlib curve idiom), `≪`/`⤳` via TransGen,
  I⁺/J⁺, achronal sets (`Atlas/Specs/Spacetime/CausalStructure.lean`). Same review
  cycle. Note: segment class is everywhere-differentiable (wider than piecewise-C¹);
  coincidence of induced relations is node P1.3b(iv).
- P1.3 `done` Spec FROZEN: inextendibility (subtype-atTop endpoint filter), Cauchy
  surfaces (O'Neill/Geroch timelike-exactly-once crossing form — NOT Minguzzi's
  acausal convention), D± (causal curves, arbitrary S), global hyperbolicity
  (`Atlas/Specs/Spacetime/GlobalHyperbolicity.lean`). Same review cycle.
- P1.3b `todo` Cauchy-surface theorem battery (from the review): (i) every
  inextendible causal curve meets a Cauchy surface at least once (O'Neill Lemma
  14.29 / Wald Prop. 8.3.4; needs P1.4+ machinery); (ii) crossing-uniqueness from
  achronality — free lemma, reviewer's probe3 has a complete proof; (iii) equivalence
  with Wald's D(Σ)=M definition; (iv) differentiable-segment vs piecewise-C¹ relation
  equivalence (post-P1.4; Darboux-monotonicity argument sketched in review).
- P1.W1 `todo` Witness: Minkowski metric on `EuclideanSpace ℝ (Fin 4)` — constant η
  section smooth (via `riemannianMetricVectorSpace` pattern), Lorentzian signature
  (Sylvester, weights (-1,1,1,1)), time orientation, causal-character examples.
- P1.W2 `todo` Witness (the big one): Minkowski cone characterization
  `p ≪ q ↔ q - p ∈ future cone` (FTC + Cauchy-Schwarz argument), expected-false
  examples, `{t=0}` is a Cauchy surface, Minkowski globally hyperbolic.
- P1.4a `todo` Infrastructure: smooth dependence of ODE solutions on initial
  conditions — THE load-bearing Mathlib gap between geodesics and conjugate-point
  theory; pure Mathlib-upstream node (coordinate with Kudryashov/Yin work if merged).
- P1.4 `todo` Lorentzian geodesics + exponential map + normal/convex neighborhoods —
  build ON Mathlib PR #26221's covariant-derivative layer (metric-agnostic), not
  beside it. Gates all general-spacetime causal lemmas (even "I⁺ is open").
- P1.5 `todo` Jacobi fields, index form, conjugate/focal points along null geodesics
  (nothing exists even Riemannianly — largest new development of the phase).
- P1.5b `todo` Raychaudhuri for null congruences (screen bundle; scalar Riccati
  comparison core), NEC as named atlas hypothesis.
- P1.6 `todo` Causality-theory battery (post-P1.4): I⁺ open, push-up lemmas, limit
  curve theorem (Arzelà-Ascoli exists; parametrization is the delicacy — Minguzzi),
  achronal boundaries are C⁰ hypersurfaces (formalization-hostile), Geroch
  topological splitting via volume-function time (smooth splitting NOT needed).
- P1.6b `todo` Spec: trapped surfaces.
- P1.7 `todo` **Target: Penrose singularity theorem** (Wald Thm 9.5.1; Penrose PRL
  14, 57 (1965)) — null incompleteness from global hyperbolicity + noncompact Cauchy
  surface + NEC + trapped surface. Endgame topology (compact ∂I⁺ vs noncompact
  Cauchy surface) is Mathlib-comfortable once P1.5/P1.6 exist.

## Phase 2 — flat-space QFT spine → Haag's theorem

The Lorentzian definition of a QFT, formalized for the first time in any prover, and
the no-go that the interaction picture does not exist. Source of truth: Streater &
Wightman; Reed-Simon II. Heavy Mathlib gaps: completed Hilbert tensor products → Fock
space, unbounded operator theory, Stone's theorem (see RESEARCH.md infrastructure map).

- P2.1 `todo` Infrastructure: Hilbert space tensor product (completed) — Mathlib gap,
  upstream candidate.
- P2.2 `todo` Infrastructure: symmetric Fock space over a Hilbert space;
  creation/annihilation as unbounded operators.
- P2.3 `todo` Infrastructure: Stone's theorem / one-parameter unitary groups (Mathlib
  gap, highest upstream value; prerequisite for dynamics anywhere in the atlas).
- P2.4 `todo` Spec: unitary representations of the (universal cover of the) Poincaré
  group; add physlib dependency here for Lorentz/SL(2,ℂ) groundwork.
- P2.5 `todo` Spec: Wightman axioms (fields as operator-valued tempered distributions,
  covariance, microcausality, spectrum condition, cyclic vacuum). Each axiom a named,
  separable hypothesis — these are the atlas's core reusable fence-posts.
- P2.6 `todo` **Witness: the free scalar field satisfies the Wightman axioms**
  (world-first if landed; validates P2.5 is non-vacuous).
- P2.7 `todo` **Target: Haag's theorem** (Streater-Wightman Thm 4-16 form).
- P2.8 `todo` Stretch: Reeh-Schlieder theorem.

## Phase 3 — the classic unification no-gos

The theorems that force any TOE to be structurally strange. Hardest phase; S-matrix
and current-algebra machinery needed. Sequenced after Phase 2 because both consume the
Wightman/Poincaré-representation layer.

- P3.1 `todo` Spec: conserved currents and charges; Lorentz-covariant stress tensor as
  named hypotheses.
- P3.2 `todo` **Target: Weinberg-Witten theorem** (no composite massless spin-2 with
  covariant conserved stress tensor) — the atlas's crown jewel for QG relevance.
- P3.3 `todo` Spec: S-matrix symmetries. **Target: Coleman-Mandula theorem.**

## Phase 4 — the interface: QFT on curved spacetime

Where QM and GR rigorously coexist today, and where the cracks (Hawking radiation,
information paradox) become statable. Source: Wald, *QFT in Curved Spacetime*;
Hollands-Wald axioms. Consumes Phase 1 (spacetimes) + Phase 2 (algebraic/QFT layer).

- P4.1 `todo` Spec: algebraic quantization of the free scalar field on a globally
  hyperbolic spacetime (CCR algebra of solutions; needs GNS completion — Mathlib's
  `GelfandNaimarkSegal` cyclic-vector TODO is an upstream node).
- P4.2 `todo` Hadamard states as a named hypothesis.
- P4.3 `todo` **Target: a formal Hawking-effect derivation** (Fredenhagen-Haag style)
  — stretch goal, gated on P4.1/P4.2 experience.

## Cross-cutting — the atlas layer

- X.1 `todo` Hypothesis registry: every named physical assumption (NEC, microcausality,
  spectrum condition, covariant stress tensor, ...) as a first-class, documented,
  reusable structure in `Atlas/Specs/Hypotheses/`, so "which assumption does candidate
  theory X drop" is a formal query.
- X.2 `todo` Upstreaming tracker: infrastructure nodes PRed to Mathlib
  (P2.1/P2.3/P4.1-GNS), physics nodes offered to physlib.

## Verification gates (all phases)

Per CLAUDE.md: specs frozen with source citations before proving; witnesses before
downstream use; `scripts/check.sh` (kernel build + axiom audit + token scan) green
before merge to main; commit per verified lemma.
