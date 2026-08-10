import Atlas.Specs.Spacetime.Metric
import Atlas.Specs.Spacetime.Minkowski

/-!
# P1.W1 — Minkowski space: the non-vacuity witness for P1.1

Witness (blueprint node P1.W1) that the frozen P1.1 spec
(`Atlas/Specs/Spacetime/Metric.lean`) is non-vacuous: four-dimensional Minkowski space
`ℝ¹'³`, realised as `EuclideanSpace ℝ (Fin 4)` as a manifold over itself, carries a
`PseudoRiemannianMetric` of Lorentzian signature together with a time orientation.

The carrier `M4` and the constant mostly-plus form `minkowskiForm` live in the frozen
P2.4a spec `Atlas/Specs/Spacetime/Minkowski.lean` (extracted from this file under
spec review, 2026-08-07); this file instantiates the P1.1 metric bundle on them.
The standard basis is `η`-orthogonal with weights `(-1, 1, 1, 1)`, which makes both
nondegeneracy and the Sylvester signature computation direct.

## Contents

* `Spacetime.Minkowski.minkowskiMetric` — the metric.
* `Spacetime.Minkowski.minkowskiMetric_isLorentzian` — index `1` at every point.
* `Spacetime.Minkowski.minkowskiTimeOrientation` — the constant future field `∂₀`.
* A battery of expected-true / expected-false `example`s exercising the causal character
  predicates on `∂₀`, `∂₁`, `∂₀ + ∂₁` and `0`, including the P2.4a `IsSpacelike`
  predicate against the P1.1 `PseudoRiemannianMetric.Spacelike` convention.

## Sources

* O'Neill, *Semi-Riemannian Geometry with Applications to Relativity* (1983), Ch. 3
  (Minkowski space as the model Lorentz vector space of index 1).
* Wald, *General Relativity* (1984), §1.3.
-/

open Bundle RealInnerProductSpace
open scoped ContDiff Manifold

namespace Spacetime.Minkowski

set_option backward.isDefEq.respectTransparency false in
/-- Witness for P1.1 (non-vacuity): the constant Minkowski metric on `ℝ¹'³`.

The mostly-plus form `η(v, w) = ⟪v, w⟫ - 2 * (v 0) * (w 0)` on `EuclideanSpace ℝ (Fin 4)`
viewed as a manifold over itself, instantiating the frozen `PseudoRiemannianMetric`
structure (blueprint node P1.W1). Smoothness is that of a constant section of the trivial
bundle of bilinear forms, following `riemannianMetricVectorSpace`. -/
noncomputable def minkowskiMetric : PseudoRiemannianMetric 𝓘(ℝ, M4) ω M4 where
  val _ := minkowskiForm
  symm _ v w := minkowskiForm_symm v w
  nondegenerate x := by
    refine ⟨fun v hv => minkowskiForm_separatingLeft v fun w => hv w, fun w hw => ?_⟩
    exact minkowskiForm_separatingLeft w fun v => by rw [minkowskiForm_symm]; exact hw v
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! contMDiffAt_const (c := minkowskiForm)
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

@[simp]
theorem minkowskiMetric_val_apply (x : M4) (v w : M4) :
    minkowskiMetric.val x v w = ⟪v, w⟫ - 2 * v 0 * w 0 :=
  minkowskiForm_apply v w

/-- The metric in standard coordinates: `η(v, w) = -v⁰w⁰ + v¹w¹ + v²w² + v³w³`. The
computational workhorse for the causal-character examples below. -/
theorem minkowskiMetric_val_eq (x : M4) (v w : M4) :
    minkowskiMetric.val x v w = -(v 0 * w 0) + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 := by
  rw [minkowskiMetric_val_apply, PiLp.inner_apply, Fin.sum_univ_four]
  simp only [RCLike.inner_apply, conj_trivial]; ring

/-- The diagonalising weights of the Minkowski form in the standard basis:
`(-1, 1, 1, 1)`. -/
private def wt : Fin 4 → ℝ := fun i => if i = 0 then -1 else 1

/-- Witness for P1.1 (non-vacuity): the Minkowski metric is Lorentzian, i.e. has index `1`
at every point.

The standard basis diagonalises `η` with weights `(-1, 1, 1, 1)`, so the associated
quadratic form is isometric to `weightedSumSquares ℝ (-1, 1, 1, 1)`; by Sylvester's law
of inertia its `sigNeg` equals the number of negative weights, which is `1`. -/
theorem minkowskiMetric_isLorentzian : minkowskiMetric.IsLorentzian := by
  intro x
  have hequiv :
      QuadraticMap.Equivalent
        (LinearMap.BilinMap.toQuadraticMap (minkowskiMetric.val x).toBilinForm)
        (QuadraticMap.weightedSumSquares ℝ wt) :=
    ⟨{ toLinearEquiv := WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)
       map_app' := fun m => by
        change QuadraticMap.weightedSumSquares ℝ wt (WithLp.ofLp m) = minkowskiMetric.val x m m
        rw [minkowskiMetric_val_eq, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_four]
        simp only [wt, smul_eq_mul, show ((1 : Fin 4) = 0) = False from by decide,
          show ((2 : Fin 4) = 0) = False from by decide,
          show ((3 : Fin 4) = 0) = False from by decide, if_true, if_false]
        ring }⟩
  rw [PseudoRiemannianMetric.index, QuadraticForm.sigNeg_of_equiv_weightedSumSquares hequiv]
  have : {i : Fin 4 | wt i < 0} = {0} := by
    ext i; fin_cases i <;> simp [wt]
  rw [this, Set.ncard_singleton]

/-- Witness for P1.1 (non-vacuity): the constant future-pointing timelike field `∂₀`,
orienting Minkowski space in time.

The vector field `X x = e₀` (the future time direction) is everywhere timelike
(`η(e₀, e₀) = -1 < 0`), and is a constant — hence continuous — section of the tangent
bundle. -/
noncomputable def minkowskiTimeOrientation : minkowskiMetric.TimeOrientation where
  X _ := EuclideanSpace.single 0 1
  timelike x := by
    show minkowskiMetric.val x (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) < 0
    rw [minkowskiMetric_val_eq]; simp
  continuous := by
    have h : ContMDiff 𝓘(ℝ, M4) (𝓘(ℝ, M4).prod 𝓘(ℝ, M4)) ω
        (fun x : M4 => (TotalSpace.mk' M4 x (EuclideanSpace.single 0 1) :
          TangentBundle 𝓘(ℝ, M4) M4)) := by
      intro x
      rw [contMDiffAt_section]
      convert! contMDiffAt_const (c := (EuclideanSpace.single 0 1 : M4))
      simp [mfld_simps]
    exact h.continuous

/-! ### Sanity examples: causal character on the standard directions -/

/-- `∂₀ + ∂₁` is nonzero (its `∂₁`-component is `1`). -/
private theorem singleSum_ne_zero :
    (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 : M4) ≠ 0 := by
  intro h
  have hc : (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 : M4) 1 = (0 : M4) 1 := by
    rw [h]
  simp at hc

/-- `∂₀` is nonzero. -/
private theorem single0_ne_zero : (EuclideanSpace.single 0 1 : M4) ≠ 0 := by
  intro h
  have hc : (EuclideanSpace.single 0 1 : M4) 0 = (0 : M4) 0 := by rw [h]
  simp at hc

-- The future time direction `∂₀` is timelike.
example : minkowskiMetric.Timelike (0 : M4) (EuclideanSpace.single 0 1) := by
  show minkowskiMetric.val (0 : M4) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) < 0
  rw [minkowskiMetric_val_eq]; simp

-- A spatial direction `∂₁` is spacelike.
example : minkowskiMetric.Spacelike (0 : M4) (EuclideanSpace.single 1 1) := by
  left
  show 0 < minkowskiMetric.val (0 : M4) (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1)
  rw [minkowskiMetric_val_eq]; simp

-- The diagonal `∂₀ + ∂₁` is null (lightlike).
example :
    minkowskiMetric.Null (0 : M4)
      ((EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 : M4)) := by
  refine ⟨?_, singleSum_ne_zero⟩
  show minkowskiMetric.val (0 : M4) _ _ = 0
  rw [minkowskiMetric_val_eq]; simp

-- The zero vector is spacelike (O'Neill's convention).
example : minkowskiMetric.Spacelike (0 : M4) 0 := Or.inr rfl

-- The zero vector is not timelike.
example : ¬ minkowskiMetric.Timelike (0 : M4) 0 := by
  show ¬ minkowskiMetric.val (0 : M4) 0 0 < 0
  simp only [map_zero, lt_self_iff_false, not_false_eq_true]

-- The zero vector is not causal.
example : ¬ minkowskiMetric.Causal (0 : M4) 0 := by
  rintro (h | ⟨_, hne⟩)
  · exact absurd h (by
      show ¬ minkowskiMetric.val (0 : M4) 0 0 < 0
      simp only [map_zero, lt_self_iff_false, not_false_eq_true])
  · exact hne rfl

-- The zero vector is not null.
example : ¬ minkowskiMetric.Null (0 : M4) 0 := by
  rintro ⟨_, hne⟩; exact hne rfl

-- The null vector `∂₀ + ∂₁` is causal.
example :
    minkowskiMetric.Causal (0 : M4)
      ((EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 : M4)) := by
  refine Or.inr ⟨?_, singleSum_ne_zero⟩
  show minkowskiMetric.val (0 : M4) _ _ = 0
  rw [minkowskiMetric_val_eq]; simp

-- `∂₀` is future-directed for the time orientation.
example :
    minkowskiTimeOrientation.FutureDirected (0 : M4) (EuclideanSpace.single 0 1) := by
  refine ⟨Or.inl ?_, ?_⟩ <;>
    · show minkowskiMetric.val (0 : M4) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) < 0
      rw [minkowskiMetric_val_eq]; simp

-- The past direction `-∂₀` is not future-directed.
example :
    ¬ minkowskiTimeOrientation.FutureDirected (0 : M4) (-EuclideanSpace.single 0 1) := by
  rintro ⟨_, h⟩
  refine absurd h (not_lt.2 ?_)
  show 0 ≤ minkowskiMetric.val (0 : M4) (-EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
  rw [minkowskiMetric_val_eq]; simp

-- `∂₀` is not spacelike.
example : ¬ minkowskiMetric.Spacelike (0 : M4) (EuclideanSpace.single 0 1) := by
  rintro (h | h)
  · refine absurd h (not_lt.2 ?_)
    show minkowskiMetric.val (0 : M4) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) ≤ 0
    rw [minkowskiMetric_val_eq]; simp
  · exact single0_ne_zero h

/-! ### Sanity examples: the strict P2.4a `IsSpacelike` predicate -/

-- A spatial direction `∂₁` is `IsSpacelike`.
example : IsSpacelike (EuclideanSpace.single 1 1 : M4) := by
  rw [isSpacelike_iff]; norm_num [Fin.ext_iff]

-- The future time direction `∂₀` is not `IsSpacelike`.
example : ¬ IsSpacelike (EuclideanSpace.single 0 1 : M4) := by
  rw [isSpacelike_iff]
  norm_num [show ((2 : Fin 4) = 0) = False from by decide,
    show ((3 : Fin 4) = 0) = False from by decide]

-- The null diagonal `∂₀ + ∂₁` is not `IsSpacelike` (strict inequality).
example : ¬ IsSpacelike (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 : M4) := by
  rw [isSpacelike_iff]
  norm_num [Fin.ext_iff, show ((2 : Fin 4) = 0) = False from by decide,
    show ((3 : Fin 4) = 0) = False from by decide]

-- The zero vector is not `IsSpacelike` — the deliberate divergence from the P1.1
-- convention (`minkowskiMetric.Spacelike (0 : M4) 0` holds above), forced by the
-- causal anchor `isSpacelike_sub_iff_not_causallyPrecedes`.
example : ¬ IsSpacelike (0 : M4) := by
  rw [isSpacelike_iff]; norm_num

end Spacetime.Minkowski
