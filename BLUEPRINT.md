# Blueprint — QG Constraint Atlas

> This document is edited and maintained by Claude and presented as-is.

The dependency DAG of the project. Every work item is a node here; grind sessions claim
nodes and update statuses. Statuses (Workflow v2, keep them distinct — never conflate
in reports): `todo` → `designed` (dossier exists) → `spec` (statement frozen, unproven)
→ `witnessed` (non-vacuity landed) → `proving` → `done` (proven AS the frozen Props +
witnessed + merged + gates green). `external` = upstream-owned. Decomposing a node adds
child nodes; nodes are never weakened in place (see CLAUDE.md). Novelty claims are
"to our knowledge" pending external verification.

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
  Sub-nodes: P2.1a `done` (spec frozen 2026-07-10 + witnesses; notation left-assoc fixed in review); P2.1b `done` 2026-08-07 (congrₕ/commₕ/lidₕ/assocₕ isometry layer + Completion.congrₗᵢ
  upstreamable bonus; general mapₕ still #40074-gated; grinder probes to fold into P2.1W);
  P2.1c `done` (unitary adjoint laws; general case #40074-gated) + P2.1d `done` 2026-08-07 (HilbertBasis.tensorProductₕ +
  ≃ ℓ²(ι₁×ι₂) (1); P2.1e `done` 2026-08-07 (innerAux via conj∘lift+flip — no semilinear Pi machinery
  needed; uncertain node closed by unmapped fourth route; upstream candidate); P2.1f `done` 2026-08-07 (Inner global + NormedAddCommGroup/InnerProductSpace SCOPED
  in PiTensorProduct.InnerNorm — projective-seminorm diamond is real, scope discipline
  documented in-file: never open InnerNorm alongside Mathlib PiTensorProduct norm
  imports; remainder split to P2.1f.ii `todo`: TensorPower.mulEquiv isometry).
  Superseded line: PiTensorProduct inner
  product + reindex isometry + mulEquiv isometry (2); P2.1W `todo` witnesses (1).
  Prior art: Isabelle Hilbert_Space_Tensor_Product (Unruh 2024, ℓ²-route — wrong for
  Mathlib) is the ONLY completed Hilbert ⊗ in any prover; no Fock space anywhere.
- P2.2 — symmetric Fock space (WORLD-FIRST in any prover). Slice 1 `done` 2026-08-07
  (spec frozen 4a0b277 w/ governance ruling: frozen-by-import P2.1 files now
  hook-guarded; witnesses landed; instance-bridge API flagged for pre-slice-2-grind).
  Slice 2 spec FROZEN 2026-08-07 51f2ce3 (a/a† as LinearPMaps with kernel-verified sqrt/CCR roundtrip; FockBridge frozen-by-import, hook-covered). Slice-2 witnesses `done`; CCR/adjointness/commute + segalField_isSymmetric ALL PROVEN 2026-08-07 (the canonical commutation relations as kernel theorems). Remaining: Segal ess-self-adjointness (Nelson node, RS X.39), field-operator slice. Design:
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
  fork). Sub-nodes: a `done` + b `done` (spec frozen 9dfc680, witnesses + DeficiencySpaceEqKerAdjoint + EssentialSelfAdjointnessCriterion proven 2026-07-09, incl. keystone adjoint_closure_eq_adjoint); c `done` (spec frozen cc066e0; all seven targets proven 2026-07-10 — full von Neumann Cayley correspondence, world-first); d PVM spec FROZEN 2026-07-10 e4ef3d9 (VectorMeasure-shaped weak σ-additivity; adequacy kernel-probed; SpectralThm-aligned, their univ=1 gap flagged) — `done` (witnesses landed 2026-07-10: Bool PVM + impostor refutations + junk-value PVM);
  e bounded spectral thm `external/contested`; f targets FROZEN with d (IsSpectralIntegral relation + RS VIII.6 existence/uniqueness Props) — proofs gated on node e;
  g `done` (spec frozen + witnesses + bounded-generator thm, 2026-07-09; mult-operator functional-calculus identification split to future node); h Stone forward `todo`; i Stone converse `todo`;
  j multiplication form + C₀-semigroups `stretch`. Owner Zulip RFC before d/e code
  (docs/OWNER-ACTIONS.md).
- P2.4 — Poincaré layer. Design adjudicated 2026-08-07 (docs/dossiers/
  P2-wightman-design.md): physlib dependency DEFERRED TO P3 (evidence-based: no
  cover/reps/Poincaré content; carrier friction); minimal restricted-Lorentz +
  Poincaré on the Phase-1 M4 carrier; covering group NOT load-bearing for spin 0.
  Sub-nodes: P2.4a `spec` FROZEN 2026-08-10 (extraction byte-verified, dual-condition
  approval; anchor-bearing witness files added to frozen-imports.txt; probes committed
  audits/probes/P2.4a/); P2.4W `done` 2026-08-10 (rotation via composed reflections, full (cosh,sinh)
  boost family w/ rapidity addition, Poincare elements + MulAction twist, mass-shell
  equivariance, parity/PT single-condition-failure witnesses — gate satisfied);
  P2.4b spec `spec` FROZEN 2026-08-10 (joint continuity; proven Stone-bridge anchor;
  probes at audits/probes/P2.4b/ incl. kernel-certified obstruction: NO nontrivial
  1-dim rep exists — Wigner; trivial rep = only freeze-time model). witnessed 2026-08-10: regular rep on L²(M4)
  landed IN FULL incl. joint continuity (D2 gate DISCHARGED — proof-consumption
  unblocked); trivial rep promoted w/ two-way generator computation. Was: PoincareRep spec
  (+ OneParameterUnitaryGroup anchor = Stone bridge), after P2.4W; regular-rep
  witness on L²(M4) parallel non-blocking.
- P2.5 — Wightman axioms. Design adjudicated 2026-08-07 (same dossier): fixed-domain
  field structure (no LinearPMap composition), six named axiom Props; spectrum
  condition in DISTRIBUTIONAL SUPPORT FORM (joint PVM/SNAG eliminated from critical
  path — deferred post-Stone node); microcausality frozen WITH the kernel anchor to
  P1.2 causal relations. Sub-nodes: P2.5a `witnessed` — spec FROZEN 2026-08-24
  (𝓕η with the η-pairing integral and `U(t)=exp(+itH)` sign anchor;
  closedForwardCone; distribution-support bridge; Bochner integrability; inverse
  Poincaré pullback on Schwartz space; witnesses + 5 kernel probes). Review cycle:
  initial Fable approval, independent Codex found 4 defects (missing Poincaré
  action, periodic sign probe, wrong Reed–Simon attribution, incomplete Bochner
  contract), all repaired; independent Codex and renewed Fable re-reviews both
  `FREEZE-READY` at confidence 0.99 (`audits/reviews/P2.5a*`). P2.5a `done`
  2026-08-24: frozen, witnessed, independently reviewed, and gates-green.
  P2.5b `todo`: freeze the WightmanField structure and six named axiom Props.
- P2.6 — **free scalar field satisfies Wightman (flagship)**. The proof engines
  consume the proven CCR trio, P1.W2 cone lemmas, and frozen P2.5a utilities.
  - P2.6a `done` 2026-08-23: second quantization Γ, functor/conjugation laws,
    and strong continuity (`tendsto_secondQuantization`,
    `continuous_secondQuantization`).
  - P2.6b `done` 2026-08-24: physical shell measure `d³p/(2ω_p)` with explicit
    `(2π)³` Fourier-coordinate conversion; H1 from a Fin-3 Lorentz determinant
    and ENNReal measure change of variables; measure-level
    `lorentz_massShellMeasure_preserving`; exact Wigner one-particle
    `PoincareRep` on `L²(massShellMeasure m)` with semidirect laws, unitarity,
    Stone translation pin, and full joint strong continuity H3. Independently
    reviewed, merged, and gates-green (`audits/reviews/P2.6b*`).
  - P2.6c `proving`: Pauli–Jordan route. L0 symbols/energy, L1 propagator
    through the pointwise Klein–Gordon equation, L2 smooth cone cutoff including
    `‖∇χ‖ ≤ -∂ₜχ`, and L3 compact-support divergence/weighted integration by
    parts landed by 2026-08-24. Independently reviewed
    (`audits/reviews/P2.6c-L0-L3*`). Next: L4 local-energy monotonicity and
    finite speed, L5 four-dimensional slicing, L6 assembly.
  - P2.6d `todo`: free-field assembly (eight Wightman axiom verifications).
  Nelson analytic vectors remain parallel and non-blocking.
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

## Phase 5 — string-theoretic theorems `[designed]`

Owner-approved 2026-08-08; design grounding: docs/dossiers/horizon-roadmap.md.
Everything here is real mathematics with named sources; the conjectural layers of
string theory enter only as hypothesis nodes.

- P5.1 `todo` Virasoro representation layer on our Fock assets (coordinate with the
  Lean Virasoro/Sugawara development, arXiv:2510.21741; do not duplicate).
- P5.2 `designed` **Target: no-ghost theorem** (Goddard-Thorn 1972; Brower 1972) —
  flagship; positivity on the physical quotient at c = 24.
- P5.3 `todo` Kac determinant formula (Feigin-Fuchs 1983) → critical dimension
  D = 26 extraction.
- P5.4 `todo` Green-Schwarz anomaly-polynomial identity (Phys. Lett. B149, 117) —
  finite Lie-algebra character computation.
- P5.5 `todo` Partition-function T-duality identity on Mathlib modular forms.
- P5.6 `todo` HLS supersymmetric Coleman-Mandula extension (after P3.3; adds Lie
  superalgebras).
- P5.H `todo` Hypothesis nodes only, never proof targets: S-duality, M-theory
  existence, AdS/CFT (GKPW), mirror symmetry.

## Phase 6 — QFT completion horizon `[designed]`

Dependency ladder and walls: docs/dossiers/horizon-roadmap.md. Sequenced after
P2.7; each lane is its own multi-node program when opened.

- P6.1 `todo` OS→Wightman reconstruction; composition target with OSforGFF
  (arXiv:2603.15770) for a fully formal Lorentzian free field from the Euclidean side.
- P6.2 `todo` Structural battery: Reeh-Schlieder, PCT, spin-statistics.
- P6.3 `todo` P(φ)₂ constructive interacting Wightman theory (Glimm-Jaffe-Spencer
  1974 route): Gaussian measures on 𝒮′, hypercontractivity, Nelson estimates.
- P6.4 `todo` Haag-Kastler nets; DHR sectors; abstract Doplicher-Roberts duality.
  Gated on a von Neumann algebra layer in Lean.
- P6.5 `todo` Microlocal analysis lane (wavefront sets, distribution extension) →
  Epstein-Glaser renormalization → pAQFT/BV; largest infrastructure item on the map.
- P6.6 `todo` KMS/Tomita-Takesaki thermal layer (alliance: SpectralThm needs our
  P2.3 Stone lane).
- P6.W WALL (recorded, not scheduled): 4D nonperturbative existence — Clay-status
  open mathematics; SM only as perturbative AQFT with BRST-quotient observables.

## Phase 7 — GR completion horizon `[designed]`

Track decomposition and sources: docs/dossiers/horizon-roadmap.md. Extends Phase 1
after P1.7.

- P7.1 `todo` FLRW cosmology + Hawking 1966 cosmological singularity theorem —
  cheapest post-P1.7 target; witness battery from de Sitter/Milne.
- P7.2 `todo` Hawking-Penrose 1970 (generic condition is the formalization-hostile
  piece).
- P7.3 `todo` Black-hole mechanics: area theorem + horizon topology (Hawking 1972),
  zeroth/first laws; rigidity scoped to the analytic case only.
- P7.4 `todo` Statement-freezes as named hypotheses (proofs deferred to dedicated
  infrastructure programs): Choquet-Bruhat local EVFE, ADM positive mass,
  GW peeling/memory.
- P7.W WALL (recorded): cosmic censorship, Kerr stability, non-analytic rigidity,
  BKL — open mathematics, not roadmap items.

## Cross-cutting — the atlas layer

- X.1 `todo` Hypothesis registry: every named physical assumption (NEC, microcausality,
  spectrum condition, covariant stress tensor, ...) as a first-class, documented,
  reusable structure in `Atlas/Specs/Hypotheses/`, so "which assumption does candidate
  theory X drop" is a formal query.
- X.2 `todo` Upstreaming tracker: infrastructure nodes PRed to Mathlib
  (P2.1/P2.3/P4.1-GNS), physics nodes offered to physlib.
- X.3 `done` 2026-08-23 Audit-artifact backfill (Workflow v2): the five lost
  pre-policy review probes re-created as committed files — audits/probes/
  P2.2-slice1 (Fock symmetrizer), P2.2-slice2 (CCR roundtrip + 2·½=1 pin),
  P2.3c (Cayley scalar), P2.3d (Bool PVM), P2.3g (Stone generator) — recompiled
  by gate 9 on every run; Git-reproducible evidence for the early freezes restored.
- X.4 `todo` Codex cross-model review backfill of the early frozen specs
  (all pre-Workflow-v2 Atlas specs except P2.5a) — one pass, verdicts to
  audits/reviews/. P2.5a independently demonstrated this process on 2026-08-24:
  Codex found four defects that the original Fable pass missed, then approved the
  repaired surface on re-review.
- X.5 `designed` Incompatibility engine (upgrades X.1; design in
  docs/dossiers/horizon-roadmap.md): hypothesis Prop-classes, candidates extending
  exactly what they assume, `#atlas_check` applicability command, independence
  witnesses beside non-vacuity witnesses, pre-grind candidate gates (randomized
  testing, proof-producing refutation, finite-model search) with committed probe
  artifacts. First artifacts landed 2026-08-23: `#atlas_check` hypothesis-inventory
  command (Atlas/Meta/AtlasCheck.lean, syntactic-honest by declared scope) and the
  first independence witnesses (CandidateLab/Bell/Independence.lean — locality and
  measurement independence each individually load-bearing for the CH bound, both
  countermodels reaching the algebraic maximum against the frozen functional);
  ledger INCOMPATIBILITIES.md seeded (7 entries, each with certificate + primary
  sources). Prop-class registry deferred until Phase-3 no-gos give it real
  consumers (deletion test).
- X.6 — platform vertical slice (not a theorem node; no DAG status applies; landed
  on phase-2, 2026-08-23): `principia/` stdlib-only layer (artifact schemas,
  evidence/candidate registries, bwrap-sandboxed evaluator and agent runner,
  discovery loop, CLI; 325 behavior tests) + Bell pilot — local realism as a Lean
  candidate over Mathlib's CHSH, NIST loophole-free records (Shalm et al., PRL 115,
  250402) with independently recomputed martingale p-values; empirically refuted
  end-to-end with committed evidence. Next evidence slices: one GR observable, one
  collider likelihood.

## Verification gates (all phases)

Per CLAUDE.md: specs frozen with source citations before proving; witnesses before
downstream use; `scripts/check.sh` (kernel build + axiom audit + token scan) green
before merge to main; commit per verified lemma.
