# Progress journal — QG Constraint Atlas

> This document is edited and maintained by Claude and presented as-is.
> Newest entries first. Honest status only: done means gates-green and audited.

## 2026-08-07 — P2.2 slice 2 FROZEN: creation/annihilation operators

The a/a† spec (~850 lines + FockBridge) frozen at 51f2ce3 after the strongest
convention verification yet: the reviewer KERNEL-PROVED the n=1→2→1 roundtrip
a(f)a†(g)|h⟩ = ⟪f,g⟫|h⟩ + ⟪f,h⟫|g⟩ for general RCLike scalars — the √2·√2·½ = 1
arithmetic where every wrong convention (√n vs √(n+1), isometric vs projector
symmetrizer) blows up — and proved the frozen CCR statement true on vacuum and
one-particle states before freeze. Adjoint direction source-verified against
Mathlib IsFormalAdjoint; a(f) antilinearity bundled semilinearly. FockBridge
(symmetrizer self-adjointness, mem_finiteParticle_iff) became frozen-by-import;
hook extended in the freeze commit. The atlas now holds: Fock space, vacuum,
finite-particle domain, a/a† with pinned conventions, CCR/adjointness/Segal
targets wired to the proven deficiency criterion. Next: witness promotion (probe
is ready-made), CCR/adjointness grind, then P2.4/P2.5 Poincaré + Wightman specs —
the free-field witness path.

## 2026-08-07 — P2.2 slice 1 FROZEN: symmetric Fock space (first in any prover)

Fock spec (440 lines: symmetrizer with kernel-checked left Perm action — no casts,
constant-family reindex is beta-defeq; complete-then-symmetrize per RS/BR;
(n!)^-1 projector normalization pinned by proved idempotency; BosonFock lp shell;
vacuum norm 1; finite-particle density PROVED in-spec; assert_not_exists diamond
guard verified to fire) frozen at 4a0b277. Adversarial review passed all probes
(n=2 symmetrizer kernel-computed; sigma-direction verified against Mathlib source —
the a/a-dagger slice is safe) and issued the repo's first GOVERNANCE ruling: the
spec's Specs→Proofs imports make three P2.1 files frozen-by-import, and the
commit-msg hook now covers them BY NAME (orchestrator guard edit) with frozen
headers added — enforcement gap closed mechanically, not aspirationally.
Witness grind running (probe promotion). Next: slice 2 spec — creation/annihilation
LinearPMaps with sqrt factors, CCR, Segal field (hooks into our proven RS VIII.3
deficiency criterion for essential self-adjointness).

## 2026-08-07 — MILESTONE: P2.1 COMPLETE (a-f); Fock space spec cycle opens

Full completed-Hilbert-tensor-product layer done in one day of grinding: e closed by
an unmapped fourth route (conj∘lift+flip — no semilinear Pi machinery needed), f
landed with the projective-seminorm diamond investigated and found REAL (norm
instances scoped in PiTensorProduct.InnerNorm; scope discipline documented; f.ii
mulEquiv-isometry remainder split honestly). Main at 805 decls, gates green.
Upstream candidates accumulated for the owner Zulip item: Completion.congrₗᵢ/mapₗᵢ,
TensorProduct.denseRange_map, PiTensorProduct.innerAux, exists_fg_mapIncl_eq.
P2.2 Fock spec drafting dispatched (Atlas/Specs/QFT/ opens — symmetrizer route;
first Fock space in any prover if it lands).

## 2026-08-07 — P2.1b,c,d all landed and merged; tensor lane at full speed

Same-day triple: P2.1b (congrₕ/commₕ/lidₕ/assocₕ isometry functoriality — assoc
needed no fallback, via new upstreamable Completion.congrₗᵢ layer +
TensorProduct.denseRange_map; general mapₕ honestly #40074-gated), P2.1c (unitary
adjoint laws; two content-free lemmas deleted by deletion-test discipline), P2.1d
(HilbertBasis.tensorProductₕ via a closed-comap density argument — no Hamel route
exists for HilbertBasis; E ⊗̂ F ≃ ℓ²(ι₁×ι₂) incl. the infinite-dimensional
ℓ²(ℕ)⊗̂ℓ²(ℕ) ≃ ℓ²(ℕ×ℕ) witness). Main at 757 decls, gates green. P2.1e dispatched
(Fable, research-first): the conjugate-multilinear PiTensorProduct pairing — the
lane's flagged-uncertain node; honest obstruction report is an accepted outcome.
Remaining to Fock: e → f (Pi inner product) → P2.2 (symmetrizer, a/a†, CCR, Segal).

## 2026-08-07 — resumed after a 4-week pause; owner checked in

Honest gap report: the loop went dormant 2026-07-10 when the P2.1b grinder was
killed by a session limit and the host session closed before resume. No work was
lost (everything through P2.1a was committed and merged; gates re-verified green
today, 668 decls). Upstream check: Mathlib PR #34288 still open/idle — P1.4a gate
unchanged. P2.1b re-dispatched fresh (isometry functoriality; assoc = the subtle
double-completion item). Owner is back and was briefed: the five OWNER-ACTIONS
Zulip items are now the highest-leverage unblocks (PVM RFC, Stone-lane claim, Yin,
TJHeeringa, physlib flag). ER=EPR question answered honestly: not a mathematical
statement — cannot be formalized by anyone; the rigorous orbit (Tomita-Takesaki,
KMS/thermofield double, Reeh-Schlieder, Bisognano-Wichmann, CLPW crossed products)
is on our roadmap a year+ out, after Wightman + von Neumann algebra layers.

## 2026-07-10 — P2.3d witnessed + merged; P2.1a frozen + merged; tensor lane rolling

P2.3d witnesses landed (Bool PVM + both impostor refutations promoted from the
review probe, PLUS a junk-value PVM on the trivial sigma-algebra exercising
not_measurable) — d done, merged. P2.1a (completed Hilbert tensor product) drafted,
scope-reviewed (one real catch: notation was right-associative vs Mathlib left —
kernel-probed non-defeq groupings; fixed), frozen, merged. Main at 668 decls, gates
green. P2.1b functoriality grind dispatched (isometry layer; general map_h correctly
gated on post-pin Mathlib #40074 per owner actions; assoc = the subtle
completion-of-completion item, allowed to report as obstruction).

## 2026-07-10 — P2.3d/f spec FROZEN: PVMs + spectral-theorem targets

PVM spec (~570 lines) frozen at e4ef3d9 after adversarial review with the deepest
adequacy probe yet: the IsSpectralIntegral relation (spectral integral as frozen
RELATION, no choice-based data) was kernel-verified on a genuine two-projection Bool
PVM — satisfied by the diagonal operator for EVERY f, refuted for a value-perturbed
impostor (inner clause is the value-pinner) and a domain-restricted one (domain
clause pins exactly). Review found doc-only defects (Rudin 12.17 sub-labels swapped,
13.24(b)->(a); fixed) and confirmed our design against the Rudin text directly (SOT
σ-additivity is his Prop 12.18 — a theorem, not a field; norm additivity provably
wrong). SpectralThm alignment real; their missing univ=1 field book-confirmed as a
gap to flag in the owner RFC. Witness grind dispatched (probe promotes directly).

## 2026-07-10 — P2.1 design adjudicated: tensor-product gap smaller than mapped

Fable research: Mathlib ALREADY has inner products + norms on binary tensor products
(Omar #27228, in our pin) and Completion-of-⊗ is a Hilbert space by instance
composition — RESEARCH.md entry corrected. Route A (Completion of algebraic ⊗)
adjudicated; HS-operator and ℓ²-over-ONB routes rejected (the latter is Isabelle's
2024 route — the only prior art in any prover; no Fock space exists anywhere, so
P2.2 remains a world-first). TJHeeringa is landing the completion layer upstream in
real time — owner Zulip coordination item added; sub-node DAG P2.1a-f,W (~7-9
sessions) + P2.2 Fock plan (~8-13) in BLUEPRINT. The Segal-field endgame hooks
directly into our proven deficiency-space criterion. PVM spec drafter resumed after
another session-limit kill.

## 2026-07-10 — MILESTONE: P2.3c COMPLETE on main — von Neumann Cayley correspondence

Fable grinder landed ALL SEVEN frozen targets in one session (commit 29a5173, 492
decls, gates green, merged): isometry, range identity, no-eigenvalue-1, recovery with
bare symmetry, the RS VIII.3 bijection headliner both directions, and the surjectivity
pair (unitary with ker(1-U)=0 gives densely-defined self-adjoint inverseCayley,
recovered by cayley). Every target proven AS its frozen Prop. Scalar witness package
with kernel-refuted wrong-sign variant. First Cayley-transform theory in any prover.

Stone-lane status: a,b,c,g DONE. f (unbounded spectral thm) and h/i (Stone) now
bottleneck on node e (bounded spectral theorem — contested lane, SpectralThm/LeanOA
in flight; we contribute, not fork, per dossier + owner RFC gate). Next streams:
d/f SPEC drafting (local PVM structure with SOT-sigma-additivity design + prominent
upstream-alignment note — spec-only, no contested theorem code) and P2.1 Hilbert
tensor product design research (independent lane toward Fock space and the P2.6
free-field Wightman witness).

## 2026-07-10 — P2.3c Cayley spec FROZEN: zero-defect adversarial verdict

Cayley transform spec (~440 lines: shift primitive defeq to frozen deficiency
spelling, cayley via Mathlib LinearPMap.inverse + Rudin resolvent identity,
inverseCayley, seven Prop targets incl. the CayleySelfAdjointIffBijective headliner)
frozen at cc066e0. Adversarial review: FREEZE AS-IS, all 20 declarations correct.
Gold-standard probes: scalar model verified end-to-end IN THE KERNEL for all real r
(cayley(r*id) = Mobius scalar, inverse recovers r, degenerate cayley(0) = -1); both
plausible wrong-sign inverse variants kernel-REFUTED by one inequality; junk-value
paths verified unreachable by any Prop target; CompleteSpace hypotheses attacked and
retracted (needed for Star instances). Grind dispatched for the seven targets.

## 2026-07-09 — MILESTONE: P2.3a/b COMPLETE on main — RS VIII.3 criterion proven

Opus grinder landed ALL of it in one session (385 decls total, gates green, merged):
witnesses (mulPMap family incl. expected-false i-multiplication with deficiency
indices n-=1/n+=0 computed; partial-domain idRestrict), DeficiencySpaceEqKerAdjoint,
and the headliner essentialSelfAdjointnessCriterion — both proven AS the frozen Prop
targets (: DeficiencySpaceEqKerAdjoint H), so statement drift was structurally
impossible. Keystone lemmas Mathlib lacks: adjoint_closure_eq_adjoint,
isSymmetric_closure, closed-range-from-norm-identity via antilipschitz-off-graph.
To my knowledge the first essential-self-adjointness theory in any prover. Node c
(Cayley transform) spec session dispatched — next world-first on the lane to Stone.

## 2026-07-09 — P2.3a/b spec FROZEN (kernel-refuted sign-trap); node-b grind running

Symmetric-operator spec (297 lines: IsSymmetric = IsFormalAdjoint by rfl, norm
identities proved, range-orthocomplement deficiency spaces with the dense-range leg
already proved, IsEssentiallySelfAdjoint with honest junk-value semantics) frozen at
9dfc680 after the strongest adversarial verdict yet: the reviewer KERNEL-REFUTED both
the non-conjugated deficiency variant and the K-plus/K-minus label swap — the
conjugation is provably load-bearing and correctly placed. physlib parallel decls
found defeq to ours (reconciliation = renaming only). Opus grinding witnesses +
DeficiencySpaceEqKerAdjoint + the RS VIII.3 essential-self-adjointness criterion.

## 2026-07-09 — P2.3g COMPLETE and on main: Stone's theorem groundwork frozen

Full node-g cycle in one day: Fable spec draft (294 lines: OneParameterUnitaryGroup,
deriv-valued Stone generator with physicists' sign convention pinned by round-trip
lemma, three Stone Prop targets) → my audit → Fable adversarial review with the
gold-standard probe (proved IN LEAN that the generator of exp(it)·1 on ℂ is the
identity — sign errors functionally excluded; density-subsumption of IsSelfAdjoint
verified in Mathlib source; caught my dossier's Reed-Simon Vol II→I citation error) →
freeze (764b671) → Opus grind: trivialGroup + expI witnesses, sign-flip exclusion at
operator level, and the BOUNDED-GENERATOR THEOREM: t ↦ exp(itA) for bounded
self-adjoint A is a one-parameter unitary group with generator A, proven self-adjoint
(bounded case of StoneTheoremForward). Gates green (301 decls); merged to main.

The Stone lane (P2.3 a→b→c→f→h→i, all world-firsts-in-any-prover) now has its frozen
public interface. Next: P2.3a symmetric-LinearPMap spec (dispatching), then deficiency
theory (b), Cayley (c). Part-C finding: bounded-f multiplication groups are already
boundedGenerator instances; the exp(itM_f) = M_{e^{itf}} identification is its own
future node (stepping stone to the unbounded dossier witness).

## 2026-07-09 — P1.4a and P2.3 designs adjudicated; Phase 2 opens

Both research reports landed (each survived a session-limit kill + resume; PR/repo
claims spot-verified via gh):

**P1.4a (ODE smooth dependence)**: the exact Banach theorem is IN-FLIGHT in Mathlib
(PR #34288, winstonyin, Robbin/IFT route) — we do not build it. Spray homogeneity
means fixed-time smoothness suffices for the whole Penrose chain (joint (t,x) not
load-bearing). Our share: manifold-level transfer (P1.4a.iii) + variational equation
(P1.4a.iv), stacked on Yin's PR after owner's Zulip coordination. P1.4 alignment
re-pointed #26221 → #36036. Phase-1 geodesic work now deliberately waits on upstream
rather than duplicating it — blueprint updated, drafts in docs/OWNER-ACTIONS.md.

**P2.3 (Stone's theorem)**: landscape shifted 2025-26 — bounded spectral theorem +
Borel calculus in-flight (SpectralThm: Tanimoto/Butterley; LeanOA: Loreaux et al.),
but **Cayley transform, unbounded spectral theorem, and Stone itself are claimed by
nobody in any prover** — our lane. Route adjudicated: Cayley + in-flight bounded core.
Sub-node DAG a-j with estimates in docs/dossiers/P2-stone-design.md (~10-12k lines,
4-6 months; node e contested → contribute not fork). Node g
(OneParameterUnitaryGroup + bounded-generator case) sequenced first: freezes the
atlas-facing spec, unblocks P2.4/P2.5. Phase-2 branch opened; node-g spec session
dispatched. Owner actions: Zulip RFC (PVM SOT-σ-additivity design), physlib
SpectralMeasure flag to Loges (verify first).

## 2026-07-08 — MILESTONE: Phase-1 spec/witness layer complete, merged to main

P1.W2 landed in one Fable session (738 + 90 lines, commit afb5910): the full Minkowski
cone characterization (chrono AND causal iff), {t=0} proven a Cauchy surface in the
frozen timelike-exactly-once sense, Minkowski proven globally hyperbolic, and the
generic achronality-uniqueness lemma P1.3b(ii). Elegant technique notes: the endpoint
bridge needed only per-coordinate monotone convergence (no completeness); cone
convexity by hinted nlinarith Lagrange identities. Audit: guard/spec diff zero,
check.sh reproduced twice (200 decls, classical trio), headline statements verified
verbatim. phase-1 fast-forward-merged to main; main gates green.

**What now exists, machine-checked, first in any prover**: Lorentzian metrics,
causal structure, global hyperbolicity — specified faithfully to the sources with an
auditable dossier trail — and Minkowski space witnessing every definition non-vacuous.

Next streams dispatched: P1.4a research (ODE smooth dependence — the load-bearing
Mathlib gap), P2.3 research (Stone's theorem design — Phase-2's highest-upstream-value
infrastructure, independent of Phase 1).

## 2026-07-08 — P1.W1 Minkowski witness LANDED; P1.W2 dispatched

Opus grinder delivered P1.W1 in one session (243 lines, commit 3f0abdf): Minkowski
metric instantiates the frozen PseudoRiemannianMetric (constant-section smoothness via
the riemannianMetricVectorSpace pattern), Lorentzian signature by explicit isometry to
weightedSumSquares (-1,1,1,1) + Sylvester, constant time orientation, 11-example
causal-character battery. Audit: guard/spec diff zero, check.sh reproduced green (135
decls, classical trio), proofs read. P1.1 is now witnessed — the spec is non-vacuous.
Honest fragility note from the grinder: three proofs lean on v4.31.0 defeq conventions
(same as Mathlib's own Riemannian witness); expect touch-ups on any Mathlib bump.

Dispatched P1.W2 to Fable (the phase's first hard proof): Minkowski cone
characterization (⇒ direction needs component-derivative monotonicity + cone
convexity under TransGen), {t=0} Cauchy surface (existence of crossing needs the
bounded-t ⇒ Cauchy-convergence ⇒ endpoint contradiction argument), generic
achronality-uniqueness lemma P1.3b(ii). Staged deliverables; sorry-free tree required.

## 2026-07-08 — P1.1-P1.3 SPECS FROZEN (first Lorentzian geometry specs in any prover)

Full freeze cycle completed on branch phase-1:
1. Fable drafter produced 483 lines of compiling specs (its report flagged its own
   risky choices); orchestrator audit reproduced gates + read every line.
2. Source dossier (verbatim-verified Minguzzi/M-S/Chruściel/Bernal-Sánchez/Wald-scan,
   O'Neill triple-pinned; committed to docs/dossiers/) adjudicated conventions.
3. Independent Fable adversarial reviewer machine-checked every claim via probe
   files: verdict freeze-after-revisions. Real defects found and fixed:
   - D1 (blocking): IsCauchySurface was causal-exactly-once = Minguzzi's acausal
     convention (would have made Penrose hypotheses nonstandard); switched to
     O'Neill/Geroch timelike-exactly-once. My own audit had caught this
     independently; dossier + reviewer confirmed with sources and Lean probes.
   - D2: "piecewise-C¹ reading" docstring claim was inaccurate (differentiable class
     is wider); relabeled honestly, equivalence parked as theorem node P1.3b(iv).
   - D3: redundant Causal conjunct in FutureCausalOn removed (equivalence
     machine-checked by reviewer's probe).
   - D4: 16 citation fixes (achronal = Wald p. 192 not 194; unverifiable "p. 190"
     softened to §8.1; O'Neill cited by page, def-numbers dropped as unverified).
   - D5: P1.2/P1.3 declarations wrapped in Spacetime namespace (upstreamability).
4. check.sh green (2477 jobs, 78 declarations, classical trio only). Frozen via
   [spec-review] commit. New theorem nodes recorded as P1.3b.

Residual honest risks: O'Neill page cites are third-party-pinned (book inaccessible);
Wald p. 190 unverifiable (missing from scan). Next: P1.W1 Minkowski witness
(dispatching now), P1.W2 cone characterization (the big honest proof).

## 2026-07-08 — pause: API session limit

First P1.1-P1.3 spec-drafting dispatch died on the account session limit (resets 3am
America/New_York) before writing any files. No partial work in tree. Resuming the
drafter after reset; expect gaps like this in the journal timeline whenever limits
bite — the loop sleeps and resumes, work is never left half-committed.

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
