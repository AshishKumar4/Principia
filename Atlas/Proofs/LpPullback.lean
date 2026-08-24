import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# Pullback representations on `L^p` spaces

Generic analytic layer for P2.6b: a measure-preserving measurable equivalence of measure
spaces acts on `L^p` by pullback, and the action is a *linear isometry equivalence*.

Mathlib v4.31 provides `Lp.compMeasurePreservingₗᵢ` for a
measure-preserving map. This module adds only the invertible layer:

* `Lp.measurePreservingEquiv e he : Lp E p ν ≃ₗᵢ[𝕜] Lp E p μ`, with
  identity, composition, inverse, norm, and representative formulas.

The P2.6b consumer uses `E = 𝕜 = ℂ` and `p = 2`. It composes the
equivalence with a momentum-dependent phase, so a standalone automorphism-group
wrapper would own no useful policy and is deliberately absent.

## Scope

This file proves the single-equivalence primitive only. Representation laws and
continuity live with each geometric action.

## Sources

* Folland, *Real Analysis*, 2nd ed., §6.1 "Basic Theory of `L^p` Spaces" (section-level
  citation): the `L^p` spaces, their norm, and simple-function density.
* Reed & Simon I, *Methods of Modern Mathematical Physics I: Functional Analysis*, §III.1
  (section-level citation): `L^p` spaces as Banach-space examples.
* The isometry content rests on the pushforward-integration formula
  `∫ g ∘ f dμ = ∫ g d(f_*μ)`. Folland Ch. 2 is cited at chapter level; no
  subsection or display is asserted. Mathlib supplies the kernel-checked form as
  `AEEqFun.eLpNorm_compMeasurePreserving`, used by
  `MeasureTheory.Lp.compMeasurePreserving`.
-/

noncomputable section

namespace MeasureTheory
open scoped ENNReal


/-! ### Pullback along a measure-preserving measurable equivalence -/

section Construction

variable {α β 𝕜 E : Type*} [MeasurableSpace α] {μα : Measure α}
  [MeasurableSpace β] {μβ : Measure β}
  [NormedAddCommGroup E] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]


/-- Cast of the measure annotation in an a.e.-equality along a measure identification.
A plain `rw … at h` fails when `h`'s type mentions other proof hypotheses depending on the
measure; substituting a local variable stays type-correct. -/
private theorem eventuallyEq_congr_measure {α E : Type*} [MeasurableSpace α]
    {μ ν : Measure α} (hν : ν = μ) {g₁ g₂ : α → E} (h : g₁ =ᵐ[μ] g₂) :
    g₁ =ᵐ[ν] g₂ := by
  subst hν
  exact h

omit [Fact (1 ≤ p)] in
/-- Pulling back along `e` and then along `e.symm` returns the original class. The round trip
cannot be reduced to Mathlib's one-directional composition lemma because `⇑e ∘ ⇑e.symm` is not
definitionally `id`, so the cancellation goes through transport of an a.e. equality along the
equivalence (`ae_of_ae_map`). -/
theorem Lp.compMeasurePreserving_apply_symm {e : α ≃ᵐ β}
    (he : MeasurePreserving ⇑e μα μβ) (hs : MeasurePreserving ⇑e.symm μβ μα)
    (k : Lp E p μβ) :
    Lp.compMeasurePreserving ⇑e.symm hs (Lp.compMeasurePreserving ⇑e he k) = k := by
  ext1
  refine (Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving ⇑e he k) hs).trans ?_
  have hB : ∀ᵐ z : α ∂(Measure.map ⇑e.symm μβ),
      ((Lp.compMeasurePreserving ⇑e he k : α → E)) z = k (e z) :=
    eventuallyEq_congr_measure hs.map_eq (Lp.coeFn_compMeasurePreserving k he)
  exact (ae_of_ae_map e.measurable_invFun.aemeasurable hB).mono fun y hy => by simpa using hy

omit [Fact (1 ≤ p)] in
/-- Pulling back along `e.symm` and then along `e` returns the original class; mirror image of
`Lp.compMeasurePreserving_apply_symm`. -/
theorem Lp.compMeasurePreserving_symm_apply {e : α ≃ᵐ β}
    (he : MeasurePreserving ⇑e μα μβ) (hs : MeasurePreserving ⇑e.symm μβ μα)
    (j : Lp E p μα) :
    Lp.compMeasurePreserving ⇑e he (Lp.compMeasurePreserving ⇑e.symm hs j) = j := by
  ext1
  refine (Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving ⇑e.symm hs j) he).trans ?_
  have hB : ∀ᵐ z : β ∂(Measure.map ⇑e μα),
      ((Lp.compMeasurePreserving ⇑e.symm hs j : β → E)) z = j (e.symm z) :=
    eventuallyEq_congr_measure he.map_eq (Lp.coeFn_compMeasurePreserving j hs)
  exact (ae_of_ae_map e.measurable_toFun.aemeasurable hB).mono fun x hx => by simpa using hx

/-- **The pullback representation**: a measure-preserving measurable equivalence
`e : α ≃ᵐ β` of measure spaces induces a `𝕜`-linear isometry equivalence
`Lp E p ν ≃ₗᵢ[𝕜] Lp E p μ` by precomposition, `g ↦ g ∘ e`
(Folland, Real Analysis, 2nd ed., §6.1 setting, section-level citation; the isometry is
exactly Mathlib's pushforward-integration identity behind `norm_compMeasurePreserving`).
At `E = 𝕜 = ℂ`, `p = 2` this is the complex-linear unitary pullback of the headline case.
Contravariance: composing equivalences composes the pullbacks in reverse order
(`measurePreservingEquiv_trans`). -/
def Lp.measurePreservingEquiv (e : α ≃ᵐ β) (he : MeasurePreserving ⇑e μα μβ) :
    Lp E p μβ ≃ₗᵢ[𝕜] Lp E p μα where
  toLinearEquiv := LinearEquiv.ofLinear (Lp.compMeasurePreservingₗ 𝕜 ⇑e he)
    (Lp.compMeasurePreservingₗ 𝕜 ⇑e.symm (he.symm e))
    (LinearMap.ext fun j => by
      simpa using Lp.compMeasurePreserving_symm_apply he (he.symm e) j)
    (LinearMap.ext fun k => by
      simpa using Lp.compMeasurePreserving_apply_symm he (he.symm e) k)
  norm_map' := fun k => Lp.norm_compMeasurePreserving k he

@[simp]
theorem Lp.measurePreservingEquiv_apply (e : α ≃ᵐ β) (he : MeasurePreserving ⇑e μα μβ)
    (k : Lp E p μβ) :
    Lp.measurePreservingEquiv (𝕜 := 𝕜) (E := E) (p := p) e he k = Lp.compMeasurePreserving ⇑e he k :=
  rfl

@[simp]
theorem Lp.measurePreservingEquiv_symm_apply (e : α ≃ᵐ β) (he : MeasurePreserving ⇑e μα μβ)
    (j : Lp E p μα) :
    (Lp.measurePreservingEquiv (𝕜 := 𝕜) (E := E) (p := p) e he).symm j =
      Lp.compMeasurePreserving ⇑e.symm (he.symm e) j :=
  rfl

/-- Pointwise formula for the pullback representative. -/
theorem Lp.coeFn_measurePreservingEquiv (e : α ≃ᵐ β) (he : MeasurePreserving ⇑e μα μβ)
    (k : Lp E p μβ) :
    (Lp.measurePreservingEquiv (𝕜 := 𝕜) (E := E) (p := p) e he k : α → E) =ᵐ[μα] fun x => k (e x) :=
  Lp.coeFn_compMeasurePreserving k he

/-- Pointwise formula for the inverse pullback representative. -/
theorem Lp.coeFn_measurePreservingEquiv_symm (e : α ≃ᵐ β) (he : MeasurePreserving ⇑e μα μβ)
    (j : Lp E p μα) :
    ((Lp.measurePreservingEquiv (𝕜 := 𝕜) (E := E) (p := p) e he).symm j : β → E) =ᵐ[μβ] fun y => j (e.symm y) :=
  Lp.coeFn_compMeasurePreserving j (he.symm e)

@[simp]
theorem Lp.measurePreservingEquiv_refl :
    Lp.measurePreservingEquiv (𝕜 := 𝕜) (E := E) (p := p)
      (MeasurableEquiv.refl α) (MeasurePreserving.id μα) = 1 := by
  ext k
  simpa using
    Lp.coeFn_measurePreservingEquiv (𝕜 := 𝕜) (MeasurableEquiv.refl α)
      (MeasurePreserving.id μα) k

/-- Contravariance: pullback along `e.trans e'` (whose forward map is `e' ∘ e`) is the
composition of the pullback along `e'` followed by the pullback along `e`. -/
@[simp]
theorem Lp.measurePreservingEquiv_trans {γ : Type*} [MeasurableSpace γ] {μg : Measure γ}
    (e : α ≃ᵐ β) (he : MeasurePreserving ⇑e μα μβ)
    (e' : β ≃ᵐ γ) (he' : MeasurePreserving ⇑e' μβ μg) :
    Lp.measurePreservingEquiv (𝕜 := 𝕜) (E := E) (p := p) (e.trans e') (he'.comp he) =
      (Lp.measurePreservingEquiv (𝕜 := 𝕜) (E := E) (p := p) e' he').trans
        (Lp.measurePreservingEquiv (𝕜 := 𝕜) (E := E) (p := p) e he) := by
  refine LinearIsometryEquiv.ext fun k => ?_
  exact Lp.compMeasurePreserving_comp_apply k he' he

/-- The inverse of the pullback along `e` is the pullback along `e.symm`. -/
@[simp]
theorem Lp.measurePreservingEquiv_symm (e : α ≃ᵐ β) (he : MeasurePreserving ⇑e μα μβ) :
    (Lp.measurePreservingEquiv (𝕜 := 𝕜) (E := E) (p := p) e he).symm =
      Lp.measurePreservingEquiv (𝕜 := 𝕜) (E := E) (p := p) e.symm (he.symm e) := by
    (ext j; simp)

end Construction


/-! ### Headline instantiation pins -/

section Pinning

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The headline case used by P2.6b: a measure-preserving self-equivalence of `(α, μ)` acts as
a complex-linear isometric equivalence of `L²(μ)`. -/
example (e : α ≃ᵐ α) (he : MeasurePreserving ⇑e μ μ) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.measurePreservingEquiv e he


end Pinning
