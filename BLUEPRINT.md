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

- P1.1 `todo` Spec: Lorentzian metric on a smooth manifold (signature, nondegeneracy),
  time orientation. Witness: Minkowski space ℝ^{1,3}.
- P1.2 `todo` Spec: causal structure — timelike/null/causal curves, chronological and
  causal futures I⁺/J⁺, achronal sets. Witnesses + expected-false examples (e.g.
  spacelike-separated points are not chronologically related in Minkowski).
- P1.3 `todo` Spec: global hyperbolicity, Cauchy surfaces. Witness: Minkowski.
- P1.4 `todo` Geodesics, exponential map, conjugate points in the Lorentzian setting
  (gap: Mathlib geodesic theory is nascent — infrastructure node, Mathlib-upstreamable).
- P1.5 `todo` Raychaudhuri equation for null congruences (expansion, shear, vorticity).
- P1.6 `todo` Spec: trapped surfaces; null energy condition as a named hypothesis
  (this is an atlas hypothesis — it gets its own reusable structure).
- P1.7 `todo` **Target: Penrose singularity theorem** — null geodesic incompleteness
  from global hyperbolicity + noncompact Cauchy surface + NEC + trapped surface.

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
