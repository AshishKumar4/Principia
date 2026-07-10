import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# P2.3d/P2.3f — Projection-valued measures and the unbounded spectral theorem

Frozen spec (blueprint nodes P2.3d structure / P2.3f targets): proof sessions must not
edit this file; changes require a spec review and a `[spec-review]` commit (see
CLAUDE.md).

## ⚠ Upstream alignment — read before building on this file

**This design is deliberately provisional at the community level.** Per
`docs/OWNER-ACTIONS.md` item 3, a Zulip RFC proposing the `ProjectionValuedMeasure`
design (σ-additivity ONLY in the weak/strong operator sense) and coordinating with the
converging pipelines is **owner-gated** and has not yet been posted. Three external
projects are approaching the same definition:

* **SpectralThm** (Tanimoto/Butterley, `github.com/oliver-butterley/SpectralThm`,
  fetched and read 2026-07-10): their `ResolutionOfIdentity α H` in `Resolutions.lean`
  stores a total `measureOf' : Set α → (H →L[ℂ] H)` with junk value `0` off the
  σ-algebra and weak σ-additivity as `HasSum (fun i ↦ ⟪x, E (w i) y⟫) ⟪x, E (⋃ i, w i) y⟫`
  — field-for-field the layout of Mathlib's `MeasureTheory.VectorMeasure`, so that the
  scalar complex measures are literal field reuse. This spec **agrees** with all of
  those choices (independently re-derived below; no code was copied — design alignment
  only). It **differs** in that (i) they store idempotency and self-adjointness of the
  values via a bespoke `IsOrthogonalProjection` (with a sorried bridge waiting on a
  Mathlib PR), while we store only self-adjointness and *derive* idempotency from
  multiplicativity, landing in Mathlib's `IsStarProjection` (already in v4.31.0);
  (ii) they store finite additivity as a separate field, which is derivable from
  `empty'` + weak σ-additivity and therefore omitted here; (iii) they currently have
  **no** `E univ = 1` field, which Rudin (Def 12.17(b)) requires and we include.
* **LeanOA** (Loreaux/Bannon/Dedecker, checked 2026-07-10): no PVM or spectral-measure
  development exists in the repository (CFC, W*-topologies, masas only). No constraint.
* **physlib** (Loges): a `SpectralMeasure` structure reportedly (— *unverified*, see
  `docs/OWNER-ACTIONS.md` item 4) demanding **norm** countable additivity, which is
  wrong for genuine PVMs (see the σ-additivity convention below).

After the owner's RFC and any SpectralThm/LeanOA convergence, this design **may be
revised by a `[spec-review]` pass**; downstream proof nodes should treat the field
*layout* (not the mathematical content) as potentially in flux until that happens.

## Contents

* `ProjectionValuedMeasure α H`: a projection-valued measure on the measurable space
  `α` with values in the bounded operators on a complex Hilbert space `H` — Rudin's
  *resolution of the identity* (Def 12.17), Reed & Simon's *projection-valued measure*
  (I, §VII.3, §VIII.3) — with self-adjoint values, `∅ ↦ 0`, `univ ↦ 1`,
  multiplicativity `P (s ∩ t) = P s * P t`, and σ-additivity **only in the weak
  sense** (see Conventions), plus a `FunLike` coercion and basic API.
* Kernel-checked consequences pinning the definition: the values are star projections
  (`isIdempotentElem`, `isStarProjection`), commute (`commute`), absorb along
  inclusions (`mul_of_subset`), and satisfy `⟪x, P s x⟫ = ‖P s x‖²`
  (`inner_apply_self`).
* The scalar spectral measures: `scalarMeasure P x y : ComplexMeasure α` with
  `s ↦ ⟪x, P s y⟫` (literal field reuse from the structure), and the diagonal measure
  `diagMeasure P x : Measure α` with `s ↦ ‖P s x‖ₑ²` (a genuine finite positive
  measure of total mass `‖x‖²`; its σ-additivity is *proved* here from the weak
  field — the non-vacuity check of the σ-additivity design).
* `IsSpectralIntegral P f A`: the Prop-valued relation "`A` is the spectral integral
  `∫ f dP` on its natural domain", spelled through `diagMeasure` (Reed & Simon I,
  Thm VIII.6; Rudin, ch. 13); `IsBoundedIntegral P f T` for the everywhere-defined
  bounded case (Rudin, Thm 12.21).
* Prop-valued target statements: `BoundedSpectralIntegralExists` (node P2.3d/e
  boundary) and the node-P2.3f headliners `UnboundedSpectralTheoremExists` /
  `UnboundedSpectralTheoremUnique` (Reed & Simon I, Thm VIII.6).

## Conventions

* **σ-additivity is stated in the weak sense, and only there.** The field `m_iUnion'`
  says: for every `x y : H`, the set function `s ↦ ⟪x, P s y⟫` is countably additive
  as a `ℂ`-valued function (`HasSum` over any measurable pairwise-disjoint sequence).
  This is exactly how the sources state it (Rudin, Def 12.17(e): "`E_{x,y}` is a
  complex measure"; Reed & Simon I, §VII.3 state the strong form and use the weak one
  interchangeably). Adjudication of the alternatives:
  - **Norm σ-additivity is WRONG** and is never postulated. Counterexample sketch: on
    `ℓ²(ℕ)` let `P s` be the orthogonal projection onto `span {eᵢ : i ∈ s}` (the
    multiplication PVM of indicator functions) and take `wᵢ = {i}`. Then
    `∑_{i<n} P {i}` is the projection onto `span {e₀, …, e_{n−1}}` and
    `‖P (⋃ᵢ wᵢ) − ∑_{i<n} P {i}‖ = 1` for every `n` — the tail is a nonzero
    projection — so the series never converges in operator norm, although it
    converges strongly and weakly. The same argument kills norm σ-additivity for
    *every* PVM taking infinitely many mutually orthogonal nonzero values, i.e. for
    the spectral measure of every operator with infinite spectrum (Rudin, remarks
    following Def 12.17: the series converges in the strong operator topology, "not
    usually in the norm topology"). A norm-σ-additive "PVM" structure would make the
    node-P2.3f existence target *false*. This is the design decision the three
    converging projects are about to make incompatibly (see the alignment preamble).
  - **Strong (SOT) σ-additivity is a theorem, not a field.** For partial sums of
    mutually orthogonal projections, weak convergence upgrades to strong:
    `‖(P (⋃ᵢ wᵢ) − ∑_{i<n} P wᵢ) x‖² = ⟪x, (P (⋃ᵢ wᵢ) − ∑_{i<n} P wᵢ) x⟫` since the
    partial defects are again projections. Freezing the weak form keeps the structure
    minimal; the SOT form is a grind-node lemma (P2.3d).
  - **Encoding**: `m_iUnion'` is shaped *exactly* like the `m_iUnion'` field of
    `MeasureTheory.VectorMeasure` (hence of `ComplexMeasure = VectorMeasure α ℂ`), so
    `scalarMeasure` below is literal field reuse with zero glue. SpectralThm made the
    same choice. The rejected alternative — a field `∀ x y, ∃ μ : ComplexMeasure α, ∀ s,
    μ s = ⟪x, P s y⟫` — hides the additivity behind an existential and was discarded.
* **Junk values, following `MeasureTheory.VectorMeasure`.** `measureOf'` is total on
  `Set α` with the junk value `0` on non-measurable sets (`not_measurable'`), and the
  set-algebra fields (`inter'`, `m_iUnion'`) carry explicit `MeasurableSet`
  hypotheses. The junk value `0` is itself a star projection
  (`IsStarProjection.zero`), so the pointwise fields (`isSelfAdjoint'`) and the
  derived algebraic lemmas (`isIdempotentElem`, `commute`) hold *unconditionally* —
  no measurability guards needed. The rejected alternative — a measurable-set-indexed
  domain `∀ s, MeasurableSet s → (H →L[ℂ] H)` — would diverge from Mathlib's measure
  design (and from SpectralThm) and cause dependent-type friction at every
  application.
* **Minimal field set.** Idempotency of the values is *derived* (`P s = P (s ∩ s) =
  P s * P s` for measurable `s`, junk otherwise) — storing it (as SpectralThm does)
  would be redundant with `inter'`. Finite additivity is derivable from `empty'` +
  `m_iUnion'` by summing over the sequence `s, t, ∅, ∅, …` (a grind-node lemma; this
  is why no `m_union'` field exists here, diverging from SpectralThm). `empty'` itself
  is kept even though it follows from `m_iUnion'` on the constant-`∅` sequence: it
  matches the `VectorMeasure` field layout, which is what makes `scalarMeasure`
  definitional.
* **Inner-product convention.** `⟪·,·⟫` is Mathlib's inner product on a complex
  Hilbert space: conjugate-linear in the *first* slot. So `scalarMeasure P x y :
  s ↦ ⟪x, P s y⟫` is `ℂ`-linear in `y` — this matches Reed & Simon's `(x, P_Ω y)`.
  Rudin's `E_{x,y}(ω) = (E(ω) x, y)` is linear in the first slot, so his `E_{x,y}` is
  our `scalarMeasure y x`.
* **`CompleteSpace H` is a structure hypothesis**: self-adjointness of the values is
  stated through the star algebra `H →L[ℂ] H`, whose `star` (= adjoint) instance
  requires completeness. PVMs live on Hilbert spaces in every source; nothing is lost.
* **The spectral integral is a relation here, not a construction.** `PVM.integral`
  as *data* — the `LinearPMap` with the natural domain
  `{x | ∫ ‖f‖² dμ_x < ∞}` and weakly-defined values — requires the Riesz
  representation of a bounded sesquilinear form and the Cauchy–Schwarz estimate for
  spectral integrals; constructing it *is* the substance of proof nodes P2.3d/f. Per
  the house precedent for data whose construction is the proof (`stoneEquiv` in the
  P2.3g spec, `cayleyEquiv` in the P2.3c spec), the construction is deferred to the
  proof node, and what is frozen instead is the *characterizing relation*
  `IsSpectralIntegral P f A`, spelled entirely through the kernel-checked
  `diagMeasure`:
  - `mem_domain_iff` — the natural domain, verbatim Reed & Simon/Rudin:
    `x ∈ D(A) ↔ ∫⁻ ‖f‖² dμ_x < ∞`;
  - `inner_apply` — the diagonal values: `⟪x, A x⟫ = ∫ f dμ_x` (Bochner integral
    against the finite measure `μ_x`; integrable on the domain since
    `L²(μ_x) ⊆ L¹(μ_x)` for finite `μ_x`);
  - `norm_sq_apply` — the graph norm: `‖A x‖² = ∫ ‖f‖² dμ_x` (Rudin, Thm 13.24(b)).
  The diagonal clauses determine `A` given `(P, f)`: the natural domain is a
  submodule, so complex polarization recovers `⟪y, A x⟫` for `y, x ∈ D(A)` from the
  diagonal, and density of the natural domain (a grind-node theorem) does the rest.
  The off-diagonal form `⟪y, A x⟫ = ∫ f d(scalarMeasure y x)` of Reed & Simon is
  *not* used in the frozen statements because integration against a
  `VectorMeasure`/`ComplexMeasure` does not exist in Mathlib v4.31.0 (SpectralThm is
  hand-rolling it in `ComplexMeasure/Integral.lean`); it becomes derived API once
  either their version or ours lands. Including `norm_sq_apply` alongside
  `inner_apply` keeps the relation manifestly equivalent to the textbook one without
  leaning on the density theorem at spec level; both clauses hold for the genuine
  spectral integral, so the existence targets are not weakened.
* **The natural-domain `Submodule` and the `LinearPMap` shape are deferred with the
  construction.** A standalone `integralDomain` submodule (closure under `+` needs
  `μ_{x+y} ≤ 2μ_x + 2μ_y`, under `•` needs `μ_{c·x} = |c|² μ_x`) would serve no
  frozen statement once the relation above carries the targets; it belongs to the
  proof node that builds `PVM.integral`. Deferred-with-reasons, not omitted.
* **Bounded integrals** are frozen through the same diagonal device:
  `IsBoundedIntegral P f T` for `T : H →L[ℂ] H`. Here polarization needs no density —
  the diagonal `x ↦ ⟪x, T x⟫` on all of `H` determines `T` outright (uniqueness is a
  grind-node lemma via `LinearMap.IsSymmetric.inner_map_self_eq_zero`-style
  polarization) — so the single clause suffices. The existence target
  `BoundedSpectralIntegralExists` is stated for globally bounded measurable `f`
  (Rudin, Thm 12.21 states it for `f ∈ L^∞(E)`; the essential-boundedness refinement
  is future API on top of this statement, to be coordinated in the RFC — the global
  bound covers everything nodes P2.3e/f consume).
* **The node-P2.3f targets** quantify over `ProjectionValuedMeasure ℝ H` with the
  standard Borel σ-algebra on `ℝ` (Mathlib's `Real.measurableSpace`), and spell "`A`
  is `∫ λ dP(λ)`" as `IsSpectralIntegral P Complex.ofReal A`. Following house
  precedent, existence is an `∃` statement (like `StoneTheoremConverse`) and
  uniqueness is `∃`-free. The `IsSelfAdjoint A` hypothesis in the uniqueness target
  matches Reed & Simon's statement verbatim; it is conjecturally redundant (any `A`
  spectrally integrating a real-valued `f` should be self-adjoint), and a proof node
  may additionally prove the unconditional form — but never *this* target weakened.
  The bijection packaging (`spectralEquiv : {A // IsSelfAdjoint A} ≃ PVM ℝ H`-style)
  is data and is deferred to the proof node, exactly as `stoneEquiv`/`cayleyEquiv`.
* **Namespace.** The structure and its API live in
  `OperatorTheory.ProjectionValuedMeasure`; Prop-valued targets live in
  `OperatorTheory`, parallel to the P2.3a–c/g specs. Since the namespace matches the
  structure's name, dot notation (`P.scalarMeasure`, `P.IsSpectralIntegral`) resolves
  everywhere — the `LinearPMap` caveat of the P2.3a/b spec does not apply.

## Target statements (not theorems here)

The node-P2.3f theorems are recorded as `Prop`-valued definitions
(`UnboundedSpectralTheoremExists`, `UnboundedSpectralTheoremUnique`), plus the
bounded-integral existence statement `BoundedSpectralIntegralExists` on the
P2.3d/P2.3e boundary (P2.3e is SpectralThm's contested lane — see the dossier; we
freeze the statement because node P2.3f consumes it through truncations either way).
A stuck proof node must be decomposed, never allowed to weaken them.

## Witness plan (node P2.3d grind, not this file)

* **Two-point indicator PVM**: on `α = Bool` with the `⊤` σ-algebra (every set
  measurable, so the junk field is vacuous) and `H = ℂ × ℂ`, send `s ↦` the diagonal
  projection onto the coordinates in `s`. All fields compute: `empty'`/`univ'` by
  `ext`, `inter'` by case analysis on membership, `m_iUnion'` because every
  pairwise-disjoint family in a finite σ-algebra is eventually empty below any point.
* **Multiplication PVM on `L²(μ)`** (the real witness, feeding the P2.3 witness
  ladder): `s ↦` multiplication by the indicator of `s`, whose `diagMeasure` at `g`
  is `‖1_s g‖² = ∫_s |g|² dμ` — the density measure. Expected-false examples: norm
  σ-additivity fails for the coordinate PVM on `ℓ²` (the counterexample above).
The structure API is designed so both witnesses are field-by-field constructions with
no `choice`; `diagMeasure_apply`/`scalarMeasure_apply` are `simp`/`rfl`-level for
them.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional
  Analysis*, revised and enlarged edition (1980): §VII.3 (projection-valued measures
  for bounded operators, properties (a)–(d); strong σ-additivity stated, weak used),
  §VIII.3, **Thm VIII.6** (the spectral theorem in PVM form: a one-to-one
  correspondence between self-adjoint operators `A` and projection-valued measures
  `{P_Ω}` on `ℝ` with `A = ∫ λ dP_λ`, natural domain
  `D(A) = {x : ∫ λ² d(x, P_λ x) < ∞}`).
* W. Rudin, *Functional Analysis*, 2nd ed. (1991): **Def 12.17** (resolution of the
  identity: (a) self-adjoint projection values, (b) `E(∅) = 0`, `E(Ω) = I`,
  (c) `E(ω' ∩ ω'') = E(ω')E(ω'')`, (d) finite additivity, (e) `E_{x,y}` is a complex
  measure — our field set is (a)+(b)+(c)+(e) with (d) derived) and the remarks
  following it (SOT-not-norm convergence); **Thm 12.21** (the bounded `Ψ(f)`,
  `f ∈ L^∞(E)`); ch. 13, **Thm 13.24** (the unbounded `Ψ(f)` with natural domain
  `D(Ψ(f)) = {x : ∫ |f|² dE_{x,x} < ∞}` and `‖Ψ(f) x‖² = ∫ |f|² dE_{x,x}`) and
  **Thm 13.30** (the spectral theorem for self-adjoint operators, existence and
  uniqueness, via the Cayley transform of Thm 13.19 — our node-P2.3f route).
  Theorem-number confidence: 12.17/12.21/13.19 verified against the dossier;
  13.24/13.30 chapter-level (section numbers not re-verified against a copy).
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, GTM 265 (2012),
  chs. 4–5 (spectral measures and spectral integrals; the diagonal/graph-norm
  characterization of the spectral integral). Chapter-level citation.
* J. von Neumann, "Allgemeine Eigenwerttheorie Hermitescher Funktionaloperatoren",
  *Math. Ann.* 102 (1930), 49–131 (origin of the spectral theorem for unbounded
  self-adjoint operators).
-/

namespace OperatorTheory

open MeasureTheory
open scoped Function -- for the `Disjoint on w` notation

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A **projection-valued measure** on the measurable space `α`, acting on the complex
Hilbert space `H`: a map from sets to bounded operators with self-adjoint values,
`∅ ↦ 0`, `univ ↦ 1`, junk value `0` on non-measurable sets, multiplicativity on
measurable intersections, and σ-additivity in the weak sense — for each `x y : H` the
set function `s ↦ ⟪x, P s y⟫` is a complex measure (`scalarMeasure`).

This is Rudin's *resolution of the identity* (*Functional Analysis*, 2nd ed.,
Def 12.17) and Reed & Simon's *projection-valued measure* (I, §VII.3, §VIII.3). The
values are automatically idempotent (`isIdempotentElem`, from multiplicativity), hence
star projections (`isStarProjection`). σ-additivity is **not** stated in operator norm
— that is false for every PVM with infinitely many orthogonal values (see the module
docstring) — nor as an SOT field (derivable, grind node). Junk-value and field-layout
conventions follow `MeasureTheory.VectorMeasure`; see the module docstring, including
the upstream-alignment preamble (this design is subject to a community RFC). -/
structure ProjectionValuedMeasure (α : Type*) [MeasurableSpace α] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The operator assigned to each set. Do not use this field directly; use the
  coercion coming from the `FunLike` instance. -/
  measureOf' : Set α → H →L[ℂ] H
  /-- Every value is self-adjoint (junk values included: `0` is self-adjoint). Do not
  use this field directly; use `ProjectionValuedMeasure.isSelfAdjoint`. -/
  isSelfAdjoint' : ∀ s : Set α, IsSelfAdjoint (measureOf' s)
  /-- The empty set is sent to `0`. Do not use this field directly; use
  `ProjectionValuedMeasure.empty`. -/
  empty' : measureOf' ∅ = 0
  /-- The whole space is sent to `1`. Do not use this field directly; use
  `ProjectionValuedMeasure.univ`. -/
  univ' : measureOf' Set.univ = 1
  /-- Non-measurable sets are sent to `0` (junk value, following
  `MeasureTheory.VectorMeasure`). Do not use this field directly; use
  `ProjectionValuedMeasure.not_measurable`. -/
  not_measurable' ⦃s : Set α⦄ : ¬MeasurableSet s → measureOf' s = 0
  /-- Multiplicativity on measurable sets: `P (s ∩ t) = P s * P t`. Do not use this
  field directly; use `ProjectionValuedMeasure.inter`. -/
  inter' ⦃s t : Set α⦄ : MeasurableSet s → MeasurableSet t →
    measureOf' (s ∩ t) = measureOf' s * measureOf' t
  /-- Weak σ-additivity: for each `x y`, the scalar set function `s ↦ ⟪x, P s y⟫` is
  countably additive. Shaped exactly like `MeasureTheory.VectorMeasure.m_iUnion'`, so
  the scalar complex measures are field reuse. Do not use this field directly; use
  `ProjectionValuedMeasure.hasSum_inner`. -/
  m_iUnion' (x y : H) ⦃w : ℕ → Set α⦄ : (∀ i, MeasurableSet (w i)) →
    Pairwise (Disjoint on w) →
    HasSum (fun i => ⟪x, measureOf' (w i) y⟫) ⟪x, measureOf' (⋃ i, w i) y⟫

namespace ProjectionValuedMeasure

variable {α : Type*} [MeasurableSpace α] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

instance : FunLike (ProjectionValuedMeasure α H) (Set α) (H →L[ℂ] H) where
  coe P := P.measureOf'
  coe_injective P Q h := by cases P; cases Q; congr

@[ext]
theorem ext {P Q : ProjectionValuedMeasure α H} (h : ∀ s, P s = Q s) : P = Q :=
  DFunLike.ext P Q h

@[simp]
theorem coe_mk (f : Set α → H →L[ℂ] H) (hsa h0 h1 hnm hi hU) :
    ⇑(mk f hsa h0 h1 hnm hi hU) = f :=
  rfl

variable (P : ProjectionValuedMeasure α H)

/-- Every value of a projection-valued measure is self-adjoint (Rudin, Def 12.17(a);
Reed & Simon I, §VII.3). Unconditional: the junk value `0` is self-adjoint. -/
theorem isSelfAdjoint (s : Set α) : IsSelfAdjoint (P s) :=
  P.isSelfAdjoint' s

/-- A projection-valued measure sends the empty set to `0` (Rudin, Def 12.17(b)). -/
@[simp]
theorem empty : P ∅ = 0 :=
  P.empty'

/-- A projection-valued measure sends the whole space to `1` (Rudin, Def 12.17(b):
`E(Ω) = I`). This is the normalization SpectralThm currently omits — see the
upstream-alignment preamble. -/
@[simp]
theorem univ : P Set.univ = 1 :=
  P.univ'

/-- A projection-valued measure vanishes on non-measurable sets (junk value, following
`MeasureTheory.VectorMeasure`). -/
theorem not_measurable {s : Set α} (hs : ¬MeasurableSet s) : P s = 0 :=
  P.not_measurable' hs

/-- Multiplicativity of a projection-valued measure: `P (s ∩ t) = P s * P t` on
measurable sets (Rudin, Def 12.17(c); Reed & Simon I, §VII.3(d)). -/
theorem inter {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    P (s ∩ t) = P s * P t :=
  P.inter' hs ht

/-- Weak σ-additivity of a projection-valued measure, in working form (Rudin,
Def 12.17(e); Reed & Simon I, §VII.3(c), weak form): over a measurable
pairwise-disjoint sequence, the scalar values `⟪x, P (w i) y⟫` sum to
`⟪x, P (⋃ i, w i) y⟫`. Only the *weak* form is an axiom; SOT σ-additivity is a
derived grind-node lemma, and norm σ-additivity is false (module docstring). -/
theorem hasSum_inner (x y : H) ⦃w : ℕ → Set α⦄ (hw : ∀ i, MeasurableSet (w i))
    (hd : Pairwise (Disjoint on w)) :
    HasSum (fun i => ⟪x, P (w i) y⟫) ⟪x, P (⋃ i, w i) y⟫ :=
  P.m_iUnion' x y hw hd

/-- The values of a projection-valued measure are idempotent — **derived** from
multiplicativity (`P s = P (s ∩ s) = P s * P s`), not stored as a field, and
unconditional because the junk value `0` is idempotent. This is where the design
diverges from SpectralThm's `ResolutionOfIdentity` (which stores idempotency); see the
upstream-alignment preamble. -/
theorem isIdempotentElem (s : Set α) : IsIdempotentElem (P s) := by
  show P s * P s = P s
  by_cases hs : MeasurableSet s
  · rw [← P.inter hs hs, Set.inter_self]
  · rw [P.not_measurable hs, mul_zero]

/-- The values of a projection-valued measure are star projections — self-adjoint
idempotents, i.e. orthogonal projections (Rudin, Def 12.17(a)). Lands in Mathlib's
`IsStarProjection` (v4.31.0), where SpectralThm still carries a bespoke
`IsOrthogonalProjection` with a sorried bridge. -/
theorem isStarProjection (s : Set α) : IsStarProjection (P s) :=
  ⟨P.isIdempotentElem s, P.isSelfAdjoint s⟩

/-- Any two values of a projection-valued measure commute (Reed & Simon I, §VII.3:
`P_{Ω₁} P_{Ω₂} = P_{Ω₁ ∩ Ω₂} = P_{Ω₂} P_{Ω₁}`). Unconditional by the junk value. -/
theorem commute (s t : Set α) : Commute (P s) (P t) := by
  show P s * P t = P t * P s
  by_cases hs : MeasurableSet s
  · by_cases ht : MeasurableSet t
    · rw [← P.inter hs ht, ← P.inter ht hs, Set.inter_comm]
    · rw [P.not_measurable ht, mul_zero, zero_mul]
  · rw [P.not_measurable hs, mul_zero, zero_mul]

/-- Absorption along inclusions, the multiplicative form of monotonicity: if `s ⊆ t`
then `P s * P t = P s` (from `P (s ∩ t) = P s`). The Loewner-order form `P s ≤ P t`
is a grind-node lemma on top of this. -/
theorem mul_of_subset {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) : P s * P t = P s := by
  rw [← P.inter hs ht, Set.inter_eq_left.mpr hst]

/-- **The diagonal identity**: `⟪x, P s x⟫ = ‖P s x‖²` — the values of a PVM have
nonnegative real diagonal matrix coefficients, because `P s` is a self-adjoint
idempotent (Rudin, §12.17: `E_{x,x}(ω) = ‖E(ω) x‖²`). Unconditional (both sides vanish
on the junk value). This is what makes `diagMeasure` a genuine positive measure. -/
theorem inner_apply_self (s : Set α) (x : H) :
    ⟪x, P s x⟫ = (‖P s x‖ : ℂ) ^ 2 := by
  have hidem : P s (P s x) = P s x := by
    conv_rhs => rw [← P.isIdempotentElem s]
    rfl
  calc ⟪x, P s x⟫ = ⟪x, P s (P s x)⟫ := by rw [hidem]
    _ = ⟪P s x, P s x⟫ := ((P.isSelfAdjoint s).isSymmetric x (P s x)).symm
    _ = (‖P s x‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _

/-- The **scalar spectral measures** of a projection-valued measure: for `x y : H`,
the complex measure `s ↦ ⟪x, P s y⟫` (Rudin, Def 12.17(e) — his `E_{x,y}` is our
`scalarMeasure y x`, see the module docstring on the inner-product convention;
Reed & Simon I, §VII.3: `(x, P_Ω y)`). Linear in `y`, conjugate-linear in `x`.

The fields are literal reuse of the structure's fields — the design reason `m_iUnion'`
is shaped like `MeasureTheory.VectorMeasure.m_iUnion'`. -/
def scalarMeasure (x y : H) : ComplexMeasure α where
  measureOf' s := ⟪x, P s y⟫
  empty' := by simp
  not_measurable' s hs := by simp [P.not_measurable hs]
  m_iUnion' := P.hasSum_inner x y

@[simp]
theorem scalarMeasure_apply (x y : H) (s : Set α) :
    P.scalarMeasure x y s = ⟪x, P s y⟫ :=
  rfl

/-- The **diagonal spectral measure** of a projection-valued measure at `x : H`: the
positive measure `s ↦ ‖P s x‖ₑ²` — by `inner_apply_self` this is `s ↦ ⟪x, P s x⟫`, the
diagonal of the scalar spectral measures (Rudin, §12.17: `E_{x,x}(ω) = ‖E(ω) x‖²` "so
each `E_{x,x}` is a positive measure"; Reed & Simon I, §VII.2–3: the spectral measures
`μ_x`). Its σ-additivity is *proved* here from the weak field `m_iUnion'` alone — the
kernel-checked witness that weak σ-additivity is the right (sufficient) axiom.

This measure carries the natural domain of the unbounded spectral integral:
`D(∫ f dP) = {x | ∫ ‖f‖² d(diagMeasure P x) < ∞}` (`IsSpectralIntegral`). -/
noncomputable def diagMeasure (x : H) : Measure α :=
  Measure.ofMeasurable (fun s _ => ‖P s x‖ₑ ^ 2)
    (by simp)
    (fun w hw hd => by
      have hsum := P.hasSum_inner x x hw hd
      simp only [P.inner_apply_self, ← Complex.ofReal_pow] at hsum
      have hsum' : HasSum (fun i => ‖P (w i) x‖ ^ 2) (‖P (⋃ i, w i) x‖ ^ 2) :=
        Complex.hasSum_ofReal.mp hsum
      calc ‖P (⋃ i, w i) x‖ₑ ^ 2
          = ENNReal.ofReal (‖P (⋃ i, w i) x‖ ^ 2) := by
            rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
        _ = ENNReal.ofReal (∑' i, ‖P (w i) x‖ ^ 2) := by rw [hsum'.tsum_eq]
        _ = ∑' i, ENNReal.ofReal (‖P (w i) x‖ ^ 2) :=
            ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hsum'.summable
        _ = ∑' i, ‖P (w i) x‖ₑ ^ 2 :=
            tsum_congr fun i => by
              rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm])

@[simp]
theorem diagMeasure_apply (x : H) {s : Set α} (hs : MeasurableSet s) :
    P.diagMeasure x s = ‖P s x‖ₑ ^ 2 :=
  Measure.ofMeasurable_apply s hs

/-- The diagonal spectral measure has total mass `‖x‖²` (from `P univ = 1`); in
particular it is finite — see the `IsFiniteMeasure` instance. -/
@[simp]
theorem diagMeasure_univ (x : H) : P.diagMeasure x Set.univ = ‖x‖ₑ ^ 2 := by
  rw [P.diagMeasure_apply x MeasurableSet.univ, P.univ, one_apply_eq_self]

instance (x : H) : IsFiniteMeasure (P.diagMeasure x) :=
  ⟨by rw [P.diagMeasure_univ x]; exact ENNReal.pow_lt_top enorm_lt_top⟩

/-- **The spectral-integral relation** (Reed & Simon I, Thm VIII.6; Rudin, Thm 13.24;
Schmüdgen, chs. 4–5): `A` *is* the spectral integral `∫ f dP` of the (possibly
unbounded, complex-valued) function `f` against the projection-valued measure `P`,
characterized on the diagonal —

* `mem_domain_iff`: the domain of `A` is the *natural domain*
  `{x | ∫ ‖f‖² dμ_x < ∞}`, where `μ_x = diagMeasure P x`;
* `inner_apply`: on it, `⟪x, A x⟫ = ∫ f dμ_x` (a Bochner integral against the finite
  measure `μ_x`, convergent since `L²(μ_x) ⊆ L¹(μ_x)`);
* `norm_sq_apply`: and `‖A x‖² = ∫ ‖f‖² dμ_x` (the graph norm; Rudin, Thm 13.24(b)).

These clauses hold for the genuine spectral integral and determine `A` from `(P, f)`
(polarization on the natural domain plus its density — grind-node lemmas), so the
relation is equivalent to the textbook `A = ∫ f dP`. The relation is spelled through
`diagMeasure` rather than the off-diagonal `⟪y, A x⟫ = ∫ f d(scalarMeasure y x)`
because Mathlib v4.31.0 has no integral against a `ComplexMeasure`; the off-diagonal
form is future derived API (module docstring). The *construction* of `∫ f dP` as a
`LinearPMap` is data, deferred to the proof node (house precedent: `stoneEquiv`,
`cayleyEquiv`). Meaningful for measurable `f`; for non-measurable `f` the Bochner
integrals take junk values and the relation is not intended to be used. -/
structure IsSpectralIntegral (f : α → ℂ) (A : H →ₗ.[ℂ] H) : Prop where
  /-- The domain of `A` is the natural domain of `∫ f dP` (Reed & Simon I,
  Thm VIII.6: `D(A) = {x : ∫ λ² dμ_x < ∞}`; Rudin, Thm 13.24). -/
  mem_domain_iff : ∀ x : H, x ∈ A.domain ↔ ∫⁻ a, ‖f a‖ₑ ^ 2 ∂(P.diagMeasure x) < ⊤
  /-- The diagonal matrix coefficients of `A` are the integrals of `f` against the
  diagonal spectral measures. -/
  inner_apply : ∀ x : A.domain, ⟪(x : H), A x⟫ = ∫ a, f a ∂(P.diagMeasure (x : H))
  /-- The graph norm of `A` is the `L²`-norm of `f` (Rudin, Thm 13.24(b):
  `‖Ψ(f) x‖² = ∫ |f|² dE_{x,x}`). -/
  norm_sq_apply : ∀ x : A.domain,
    ‖A x‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂(P.diagMeasure (x : H))

/-- **The bounded spectral-integral relation** (Rudin, Thm 12.21: `Ψ(f)` for
`f ∈ L^∞(E)`; Reed & Simon I, §VII.3): the bounded operator `T` is the weak integral
`∫ f dP`, characterized by its diagonal `⟪x, T x⟫ = ∫ f dμ_x` on all of `H`. Over `ℂ`
the diagonal determines `T` outright (polarization — no density needed), so a single
clause suffices; agreement with `IsSpectralIntegral` (via `LinearMap.toPMap ⊤`) and
uniqueness are grind-node lemmas. -/
def IsBoundedIntegral (f : α → ℂ) (T : H →L[ℂ] H) : Prop :=
  ∀ x : H, ⟪x, T x⟫ = ∫ a, f a ∂(P.diagMeasure x)

end ProjectionValuedMeasure

/-- **Target statement — existence of bounded spectral integrals** (blueprint node
P2.3d/P2.3e boundary): for every projection-valued measure `P` and every bounded
measurable `f : α → ℂ` there is a bounded operator `T = ∫ f dP` with
`⟪x, T x⟫ = ∫ f d(diagMeasure P x)` for all `x`. Rudin, *Functional Analysis*,
2nd ed., Thm 12.21 (there for `f ∈ L^∞(E)`; the globally-bounded statement frozen
here is what nodes P2.3e/f consume — the essential-boundedness refinement is future
API, see the module docstring); Reed & Simon I, §VII.3.

Stated as a `Prop`-valued definition: the proof is a grind node, and per project rules
a stuck proof decomposes into lemmas — it never weakens this statement. -/
def BoundedSpectralIntegralExists (α : Type*) [MeasurableSpace α] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ (P : ProjectionValuedMeasure α H) (f : α → ℂ), Measurable f →
    (∃ C : ℝ, ∀ a, ‖f a‖ ≤ C) → ∃ T : H →L[ℂ] H, P.IsBoundedIntegral f T

/-- **Target statement — the spectral theorem for unbounded self-adjoint operators,
existence half** (blueprint node P2.3f, the headliner): every self-adjoint operator
`A` on `H` is the spectral integral `∫ λ dP(λ)` of some projection-valued measure on
`ℝ` (with the Borel σ-algebra, Mathlib's standard instance), in the natural-domain
sense of `IsSpectralIntegral`. Note `IsSelfAdjoint` for `LinearPMap`s already forces a
dense domain (`IsSelfAdjoint.dense_domain`), so no separate density clause is needed.

Reed & Simon I, §VIII.3, **Thm VIII.6**; Rudin, *Functional Analysis*, 2nd ed., ch. 13
(Thm 13.30, via the Cayley transform Thm 13.19 — the frozen P2.3c stack is the proof
route); von Neumann (1930). Stated as a `Prop`-valued definition; per project rules a
stuck proof node decomposes it into lemmas, never weakens it. -/
def UnboundedSpectralTheoremExists (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ A : H →ₗ.[ℂ] H, IsSelfAdjoint A →
    ∃ P : ProjectionValuedMeasure ℝ H, P.IsSpectralIntegral Complex.ofReal A

/-- **Target statement — the spectral theorem for unbounded self-adjoint operators,
uniqueness half** (blueprint node P2.3f): a self-adjoint operator determines its
projection-valued measure — if `P` and `Q` both spectrally integrate `λ ↦ λ` to `A`,
then `P = Q`. Together with `UnboundedSpectralTheoremExists` this is the one-to-one
correspondence of Reed & Simon I, Thm VIII.6 (the bijection packaging is *data*,
deferred to the proof node exactly as `stoneEquiv`/`cayleyEquiv` were). The
`IsSelfAdjoint A` hypothesis matches the source statement; it is conjecturally
redundant (see the module docstring) — a proof node may prove more, never less.

Reed & Simon I, §VIII.3, Thm VIII.6 (uniqueness clause); Rudin, *Functional
Analysis*, 2nd ed., ch. 13 (uniqueness of the resolution of the identity). -/
def UnboundedSpectralTheoremUnique (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ A : H →ₗ.[ℂ] H, IsSelfAdjoint A →
    ∀ P Q : ProjectionValuedMeasure ℝ H,
      P.IsSpectralIntegral Complex.ofReal A → Q.IsSpectralIntegral Complex.ofReal A →
        P = Q

end OperatorTheory
