# Owner actions — outward-facing items deferred to Ashish

> This document is edited and maintained by Claude and presented as-is.
> These are actions I deliberately do not take autonomously (posting publicly as you).
> Each is ready to fire when you return; none blocks current work, but items marked
> GATE unblock specific blueprint nodes.

## 1. Zulip: coordinate P1.4a with Winston Yin (GATE for P1.4a.iii/iv builds)

Post to leanprover.zulipchat.com #mathlib4 (draft from the P1.4a design report,
2026-07-09):

> I'm working toward geodesics/conjugate-point theory (target: Lorentzian causality
> and the Penrose singularity theorem) on top of the integral-curves library.
> PR #34288 (smooth dependence on the initial condition) is exactly the load-bearing
> prerequisite. @Winston Yin: what's the status of the C^k generalization, and are
> (a) the manifold-level C^k local flow and (b) the variational-equation
> characterization of the flow derivative on your roadmap? If not, I'd like to
> contribute them on top of your PR — and I'm happy to help push #34288 itself
> (review, the n=1 → C^k generalization, splitting into smaller PRs). Also interested
> in the joint (t,x)-smoothness statement your paper lists as in progress, though my
> use case can bypass it via spray homogeneity.

## 2. Zulip: float the PseudoRiemannianMetric design (recommended before upstreaming)

From the P1.1 design + prior-art reports (2026-07-08): before PRing our
signature-generic `PseudoRiemannianMetric` (Gouëzel's `ContMDiffRiemannianMetric`
spelling minus positivity) to Mathlib, float the design in #maths — Gouëzel's
Riemannian structure bakes positive-definiteness into the fiber typeclass, so the
pseudo case needs the parallel-structure decision blessed by the maintainers
(Gouëzel, Rothgang, Massot are the people).

## 3. Zulip RFC: PVM design + claim the Stone lane (GATE for P2.3 nodes d/e)

Before we write PVM/bounded-spectral code, post an RFC in #mathlib4 proposing the
`ProjectionValuedMeasure` design (σ-additivity ONLY in weak/strong operator topology —
the decision SpectralThm, LeanOA, and physlib are about to make incompatibly) and
claiming our uncontested lane: Cayley transform, unbounded spectral theorem, Stone's
theorem. Named counterparts: Tanimoto/Butterley (SpectralThm — he needs our Stone for
his own Tomita/KMS TODO; natural alliance), Loreaux/Bannon/Dedecker (LeanOA),
Loges (physlib), Doll (Mathlib LinearPMap PRs, open #29624). Details:
docs/dossiers/P2-stone-design.md.

## 4. Flag physlib SpectralMeasure design issue to Gregory Loges

Their `SpectralMeasure` (merged 2026-07-01, physlib #1239) reportedly extends
`VectorMeasure` with NORM countable additivity — genuine PVMs are only SOT-σ-additive,
which would exclude every operator with infinitely many spectral components. VERIFY
against physlib source first (my gh code-search didn't confirm), then raise the issue
and offer our Mathlib-grade nodes a/b as the replacement their in-code TODO requests.

## 5. Zulip: coordinate P2.1 tensor-product completion layer with TJHeeringa

TJHeeringa is landing our P2.1a/b-shaped material in Mathlib right now (mapL merged
#40074 2026-06-30; congrL #40846 and LinearMap.fromCompletion #40151 open). Before we
build the completion layer, announce the completed-⊗/Fock plan in the existing Zulip
threads and offer co-development. Also: a Mathlib pin bump past #40074 is a
spec-review-level decision (physlib-interop constraint) — alternative is a tracked
vendor copy of mapL + norm_mapL_le with a delete-on-bump note.

## Book-in-hand citation verification (review condition D1, 2026-08-10)

With physical copies of Streater-Wightman (Princeton Landmarks ed.), O'Neill, Wald,
Reed-Simon I/II, Bratteli-Robinson II: pin the S&W section numbers in
Atlas/Specs/Spacetime/{Poincare,PoincareRep}.lean (web sources CONFLICT on the
section offsets — do not pin from the web; P2.4a's "§1-1" likely needs a
docstring-only [spec-review] errata), and clear every in-file "quoted from memory"
honesty flag across the frozen specs.

## 6. Watchlist (no action, awareness)

- Mathlib PR #34288 (smooth dependence) — merge unblocks P1.4a.iii/iv.
- Mathlib PR #36036 (connections/geodesics placeholder, supersedes #26221) — P1.4
  alignment target.
- Mathlib PR #40062 (Yin's ODE refactor) — may move the API under #34288.
