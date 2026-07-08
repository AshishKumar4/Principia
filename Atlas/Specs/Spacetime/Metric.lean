import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# P1.1 — Pseudo-Riemannian metrics, Lorentzian signature, causal character

Frozen spec (blueprint node P1.1): proof sessions must not edit this file; changes
require a spec review and a `[spec-review]` commit (see CLAUDE.md).

## Contents

* `PseudoRiemannianMetric I n M`: a symmetric, pointwise-nondegenerate `C^n` family of
  continuous bilinear forms on the tangent spaces of `M`.
* `PseudoRiemannianMetric.index` and `PseudoRiemannianMetric.IsLorentzian`.
* Causal character of tangent vectors: `PseudoRiemannianMetric.Timelike`, `.Null`,
  `.Spacelike`, `.Causal`.
* `PseudoRiemannianMetric.TimeOrientation` and
  `PseudoRiemannianMetric.TimeOrientation.FutureDirected`.

## Conventions

* Sign convention: mostly-plus `(-, +, ..., +)`. Timelike vectors have `g x v v < 0`,
  and a Lorentzian metric has index `1`. This is the convention of both O'Neill,
  *Semi-Riemannian Geometry with Applications to Relativity* (1983), and Wald,
  *General Relativity* (1984).
* The zero vector is spacelike (O'Neill, Ch. 3, p. 56); it is neither timelike, nor
  null, nor causal.
* Smoothness of the metric is stated in exactly the spelling of Mathlib's
  `ContMDiffRiemannianMetric` (`Mathlib.Geometry.Manifold.VectorBundle.Riemannian`),
  so the Riemannian and pseudo-Riemannian layers stay aligned and results can migrate
  between them.

## Sources

* O'Neill, *Semi-Riemannian Geometry with Applications to Relativity* (1983), Ch. 3
  (metric tensors, index, causal character) and Ch. 5 (time cones).
* Wald, *General Relativity* (1984), §8.1 (time orientation, future-directedness).
-/

open Bundle
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- A pseudo-Riemannian (= semi-Riemannian) `C^n` metric on a manifold `M` modelled on
`(E, H)`: a symmetric, pointwise-nondegenerate continuous bilinear form on each tangent
space, depending `C^n`-smoothly on the base point.

Authoritative source: O'Neill, *Semi-Riemannian Geometry*, Ch. 3, Def. 3.1: "A metric
tensor `g` on a smooth manifold `M` is a symmetric nondegenerate (0,2) tensor field on
`M` of constant index" — minus the constant-index requirement: the index is defined
pointwise by `PseudoRiemannianMetric.index`, and signature constraints are imposed by
predicates such as `PseudoRiemannianMetric.IsLorentzian`. (For a continuous
nondegenerate metric on a connected manifold the index is automatically constant, so
nothing is lost.)

The smoothness field `contMDiff` is stated in exactly the spelling of Mathlib's
`ContMDiffRiemannianMetric` (`Mathlib.Geometry.Manifold.VectorBundle.Riemannian`):
this structure is that one with positivity (`pos`, `isVonNBounded`) replaced by
`nondegenerate`. The hypothesis `[IsManifold I 1 M]` is required for the tangent
bundle to carry its fiber-bundle structure. -/
structure PseudoRiemannianMetric (I : ModelWithCorners ℝ E H) (n : ℕ∞ω) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] where
  /-- The metric at `x`, as a continuous bilinear form on the tangent space at `x`. -/
  val (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- The metric is symmetric (O'Neill, Ch. 3, Def. 3.1). -/
  symm (x : M) (v w : TangentSpace I x) : val x v w = val x w v
  /-- The metric is nondegenerate at every point (O'Neill, Ch. 3, Def. 3.1). -/
  nondegenerate (x : M) : (val x).toBilinForm.Nondegenerate
  /-- The metric is a `C^n` section of the bundle of continuous bilinear forms on the
  tangent bundle, in the spelling of Mathlib's `ContMDiffRiemannianMetric.contMDiff`. -/
  contMDiff : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
    (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (val x))

namespace PseudoRiemannianMetric

variable {I : ModelWithCorners ℝ E H} {n : ℕ∞ω} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The index of the metric `g` at the point `x`: the largest dimension of a subspace of
the tangent space at `x` on which `g` is negative definite (O'Neill,
*Semi-Riemannian Geometry*, Ch. 3, p. 54–55, "the index of `g`"), computed via
Sylvester's law of inertia as `sigNeg` of the quadratic form associated to `g` at `x`
(`Mathlib.LinearAlgebra.QuadraticForm.Signature`).

This is meaningful for finite-dimensional `E`; in infinite dimension `sigNeg` returns
the junk value `0`, and finiteness hypotheses enter at the use sites (e.g.
`PseudoRiemannianMetric.IsLorentzian`). -/
noncomputable def index (g : PseudoRiemannianMetric I n M) (x : M) : ℕ :=
  sigNeg (LinearMap.BilinMap.toQuadraticMap (g.val x).toBilinForm)

/-- A pseudo-Riemannian metric is Lorentzian if it has index `1` at every point:
one timelike direction, all complementary directions spacelike, in the mostly-plus
convention `(-, +, ..., +)`.

Authoritative source: O'Neill, *Semi-Riemannian Geometry*, Ch. 3, p. 55 ("A Lorentz
manifold is a semi-Riemannian manifold with index 1"). Note O'Neill additionally
requires `dim M ≥ 2` for a Lorentz manifold, and Wald (*General Relativity*, §1.3,
§8.1) works with `dim M = 4`; dimension hypotheses are imposed separately at theorem
sites, not here. -/
def IsLorentzian [FiniteDimensional ℝ E] (g : PseudoRiemannianMetric I n M) : Prop :=
  ∀ x : M, g.index x = 1

/-- A tangent vector `v` at `x` is timelike if `g x v v < 0` (mostly-plus convention).
O'Neill, *Semi-Riemannian Geometry*, Ch. 3, p. 56; Wald, *General Relativity*, §8.1. -/
def Timelike (g : PseudoRiemannianMetric I n M) (x : M) (v : TangentSpace I x) : Prop :=
  g.val x v v < 0

/-- A tangent vector `v` at `x` is null (= lightlike) if `g x v v = 0` and `v ≠ 0`.
O'Neill, *Semi-Riemannian Geometry*, Ch. 3, p. 56; Wald, *General Relativity*, §8.1. -/
def Null (g : PseudoRiemannianMetric I n M) (x : M) (v : TangentSpace I x) : Prop :=
  g.val x v v = 0 ∧ v ≠ 0

/-- A tangent vector `v` at `x` is spacelike if `g x v v > 0` or `v = 0`. The convention
that the zero vector is spacelike (rather than null) is O'Neill's:
*Semi-Riemannian Geometry*, Ch. 3, p. 56. -/
def Spacelike (g : PseudoRiemannianMetric I n M) (x : M) (v : TangentSpace I x) : Prop :=
  0 < g.val x v v ∨ v = 0

/-- A tangent vector is causal (= nonspacelike) if it is timelike or null. O'Neill,
*Semi-Riemannian Geometry*, Ch. 14 (causal vectors); Wald, *General Relativity*, §8.1.
The zero vector is not causal. -/
def Causal (g : PseudoRiemannianMetric I n M) (x : M) (v : TangentSpace I x) : Prop :=
  g.Timelike x v ∨ g.Null x v

/-- A time orientation of a pseudo-Riemannian metric: a continuous everywhere-timelike
vector field. Its value at each point selects the future time cone.

A time-orientable Lorentzian manifold is standardly defined as one admitting a
continuous everywhere-timelike vector field, and a time orientation as a choice of one
(up to pointwise sharing of time cones): Wald, *General Relativity*, §8.1 (pp. 188–189);
O'Neill, *Semi-Riemannian Geometry*, Ch. 5 (time cones, pp. 143–145). We take the
vector field itself as the data. Continuity is stated as continuity of the associated
section of the tangent bundle. -/
structure TimeOrientation (g : PseudoRiemannianMetric I n M) where
  /-- The orienting vector field. -/
  X (x : M) : TangentSpace I x
  /-- The orienting vector field is timelike at every point. -/
  timelike (x : M) : g.Timelike x (X x)
  /-- The orienting vector field is a continuous section of the tangent bundle. -/
  continuous : Continuous fun x ↦ TotalSpace.mk' E x (X x)

/-- A tangent vector `v` at `x` is future-directed (with respect to the time orientation
`τ`) if it is causal and lies on the same side of the light cone as the orienting field,
i.e. `g x v (τ.X x) < 0`.

For timelike vectors this is the time-cone criterion of O'Neill,
*Semi-Riemannian Geometry*, Ch. 5, Lemma 26 (p. 144): timelike `v`, `w` lie in the same
time cone iff `g v w < 0`; it extends to causal vectors since no nonzero causal vector
is orthogonal to a timelike vector. Cf. Wald, *General Relativity*, §8.1. -/
def TimeOrientation.FutureDirected {g : PseudoRiemannianMetric I n M}
    (τ : g.TimeOrientation) (x : M) (v : TangentSpace I x) : Prop :=
  g.Causal x v ∧ g.val x v (τ.X x) < 0

end PseudoRiemannianMetric
