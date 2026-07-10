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
  achronality — DONE (IsAchronal.eq_of_futureTimelikeOn, with P1.W2); (iii) equivalence
  with Wald's D(Σ)=M definition; (iv) differentiable-segment vs piecewise-C¹ relation
  equivalence (post-P1.4; Darboux-monotonicity argument sketched in review).
- P1.W1 `done` Witness: Minkowski metric on `EuclideanSpace ℝ (Fin 4)` — constant η
  section smooth (via `riemannianMetricVectorSpace` pattern), Lorentzian signature
  (Sylvester, weights (-1,1,1,1)), time orientation, causal-character examples.
- P1.W2 `done` Witness (the big one): Minkowski cone characterization
  `p ≪ q ↔ q - p ∈ future cone` (FTC + Cauchy-Schwarz argument), expected-false
  examples, `{t=0}` is a Cauchy surface, Minkowski globally hyperbolic.
- P1.4a — smooth dependence of ODE solutions on initial conditions. Design report
  2026-07-09 (verified: PR states checked via gh). KEY REDUCTION: geodesic spray is
  autonomous + homogeneous, so FIXED-TIME smoothness in the initial condition
  suffices for exp/Jacobi/conjugate points — joint (t,x) smoothness NOT load-bearing.
  Sub-nodes:
  - P1.4a.i `external` Banach fixed-time C^k = Mathlib PR #34288 (winstonyin,
    Robbin/IFT route, OPEN, awaiting-author, C^k generalization mid-way). Do NOT
    build independently; optionally co-contribute after coordination.
  - P1.4a.ii `external` joint (t,x) C^k — Yin/Kudryashov declared roadmap
    (arXiv:2602.13247); not needed for Penrose.
  - P1.4a.iii `todo` manifold-level C^k local flow (chart transfer, mirrors
    IntegralCurve/ExistUnique plumbing) — OURS, ~2-4 sessions, gated on #34288
    stabilizing + owner's Zulip coordination (docs/OWNER-ACTIONS.md).
  - P1.4a.iv `todo` variational equation (flow derivative solves linearized ODE) —
    OURS unless it falls out of #34288's IFT derivative computation; feeds P1.5.
  - P1.4a.v `reserve` linear ODE global existence (whole-geodesic Jacobi fields).
- P1.4 `todo` Lorentzian geodesics + exponential map + normal/convex neighborhoods —
  build ON the Mathlib connections/geodesics stack: #26221 is stalling and being
  superseded by #36036 (grunweg placeholder uniting connections+geodesics work,
  verified OPEN 2026-07). Gates all general-spacetime causal lemmas ("I⁺ is open").
  The spray/homogeneity/exp-definition layer is #34288-independent — can start
  before P1.4a.i merges (work branch only).
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

- P2.1 — completed Hilbert tensor products. Design adjudicated 2026-07-10: Route A =
  `UniformSpace.Completion` of Mathlib's algebraic inner-product tensor product.
  KEY FINDING: RESEARCH.md was stale — Mathlib (Omar PR #27228, Oct 2025, in our pin)
  already has inner/norm on binary E ⊗ F with isometry API, and Completion is a
  Hilbert space by instance composition; post-pin #40074 (TJHeeringa, merged
  2026-06-30) adds mapL with the cross-norm bound. TJHeeringa is actively landing
  P2.1a/b-shaped material upstream NOW — coordinate before building (owner action).
  Sub-nodes: P2.1a `todo` def ⊗̂ + tmulₕ + density (1 session); P2.1b `todo`
  mapₕ/congrₕ/assoc/comm laws (1-2; cross-norm needs #40074 or tracked vendor);
  P2.1c `todo` adjoint_mapₕ (0.5-1); P2.1d `todo` HilbertBasis.tensorProduct +
  ≃ ℓ²(ι₁×ι₂) (1); P2.1e `todo` PiTensorProduct SEMILINEAR lift — the one uncertain
  implementation point, upstream-shaped (1); P2.1f `todo` PiTensorProduct inner
  product + reindex isometry + mulEquiv isometry (2); P2.1W `todo` witnesses (1).
  Prior art: Isabelle Hilbert_Space_Tensor_Product (Unruh 2024, ℓ²-route — wrong for
  Mathlib) is the ONLY completed Hilbert ⊗ in any prover; no Fock space anywhere.
- P2.2 `todo` Infrastructure: symmetric Fock space (WORLD-FIRST in any prover) —
  symmetrizer projector route (NOT the SymmetricPower quotient: no inner product,
  universal property in flux upstream); BosonFock = lp 2 over completed symmetric
  powers; a/a† as LinearPMaps with mutual formal adjointness + CCR on the
  finite-particle domain; Segal field essential self-adjointness via a NEW Nelson
  analytic-vector node (RS X.39) feeding our proven
  isEssentiallySelfAdjoint_of_deficiencySpace_eq_bot. Est. 8-13 sessions on P2.1.
- P2.3 — Stone's theorem + unbounded-operator infrastructure. Design adjudicated
  2026-07-09 (docs/dossiers/P2-stone-design.md): Cayley route; our uncontested lane =
  Cayley transform, unbounded spectral theorem, Stone (world-firsts in any prover);
  bounded-normal core is in-flight elsewhere (SpectralThm/LeanOA — contribute, don't
  fork). Sub-nodes: a `done` + b `done` (spec frozen 9dfc680, witnesses + DeficiencySpaceEqKerAdjoint + EssentialSelfAdjointnessCriterion proven 2026-07-09, incl. keystone adjoint_closure_eq_adjoint); c `done` (spec frozen cc066e0; all seven targets proven 2026-07-10 — full von Neumann Cayley correspondence, world-first); d PVMs `todo` (align SpectralThm; SOT-σ-additivity!);
  e bounded spectral thm `external/contested`; f unbounded spectral thm `todo`;
  g `done` (spec frozen + witnesses + bounded-generator thm, 2026-07-09; mult-operator functional-calculus identification split to future node); h Stone forward `todo`; i Stone converse `todo`;
  j multiplication form + C₀-semigroups `stretch`. Owner Zulip RFC before d/e code
  (docs/OWNER-ACTIONS.md).
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
