import Atlas.Proofs.MassShellMeasure
import Atlas.Proofs.MassShellInvariance
import Atlas.Proofs.ShellOneParticle

/-!
# P2.6b — H1 at the measure level: the mass-shell measure is Lorentz invariant

Closing lane of the momentum-measure node (**P2.6b**). The Jacobian lane
`Atlas.Proofs.MassShellInvariance` proves the pointwise identity

`|det D(shellMap m Λ)(p)| = ω_(shellMap m Λ p) / ω_p`

and turns it into the Bochner change-of-variables formula
`integral_weighted_massShell_invariance`. That formula is *not* enough for the downstream
one-particle representation: a Bochner integral identity says nothing about measures unless
the integrands are integrable, and the shell weight `d³p/(2ω_p)` is not integrable on `ℝ³`.
This module therefore redoes the substitution in `ℝ≥0∞`, where no integrability hypothesis
exists, and lands the measure-level statement that `Atlas.Proofs.ShellOneParticle` assumes.

The weighted spatial measure is named here:

* `QFT.KleinGordon.spatialShellMeasure m = volume.withDensity (massShellDensity m)`,

the `d³p/(2ω_p)` factor of `massShellMeasure m = map (massShellParam m) (spatialShellMeasure m)`.

## Contents

* `QFT.KleinGordon.spatialShellMeasure` — the weighted spatial measure `d³p/(2ω_p)` on the
  physical-momentum slice, with `massShellMeasure_eq_map_spatialShellMeasure`.
* `QFT.KleinGordon.ofReal_abs_det_mul_massShellDensity` — the exact pointwise cancellation
  `|det D(shellMap m Λ)(p)| · (1/(2 ω_(shellMap m Λ p))) = 1/(2 ω_p)` in `ℝ≥0∞`.
* `QFT.KleinGordon.shellMap_measurePreserving` — `shellMap m Λ` preserves
  `spatialShellMeasure m` (`ℝ≥0∞` change of variables, so no integrability enters).
* `QFT.KleinGordon.lorentz_massShellMeasure_preserving` — `Λ` preserves
  `massShellMeasure m`, obtained by commuting `Λ ∘ massShellParam m` with
  `massShellParam m ∘ shellMap m Λ` through the pushforward definition.
* `QFT.KleinGordon.lorentzShellPreserves` — the H1 predicate
  `LorentzShellPreserves m Λ` of `Atlas.Proofs.ShellOneParticle`, discharged for every
  `0 < m` and every restricted Lorentz transformation. The conditional
  `shellPoincare m g hg` is therefore unconditional from here on.

## Conventions

Physical-momentum coordinates throughout, as in `Atlas.Proofs.MassShellInvariance`:
`massShellParam m p = (ω_p, p)` with `ω_p = √(‖p‖² + m²)`. The Fourier frequency `k` with
`p = 2πk` and its `(2π)³` Jacobian never enter, so no `2π` bookkeeping is needed.

## Sources

* E. P. Wigner, *On Unitary Representations of the Inhomogeneous Lorentz Group*, Annals of
  Mathematics 40 (1939), §6, eq. (59a) and footnote 26: the scalar product of wave functions
  on the hyperboloid `p·p = P` integrates against `|p₄|⁻¹ dp₁dp₂dp₃`, and footnote 26 records
  that the invariance of that integral under `x = Λ⁻¹x′` is the Jacobian of the substitution.
  The Jacobian is `abs_det_fderiv_shellMap` of the frozen invariance lane; what this module
  adds is the step from Wigner's integral identity to equality of the two measures.
* S. Weinberg, *The Quantum Theory of Fields*, Vol. I (1995), §2.5 — invariance of
  `d³p/2p⁰` under proper orthochronous Lorentz transformations, section level.
* Mathlib v4.31 sources, verified in-tree:
  `Mathlib/MeasureTheory/Function/Jacobian.lean`
  (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`, the `ℝ≥0∞` change of variables with no
  integrability hypothesis),
  `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean` (`Measure.ext_of_lintegral`),
  `Mathlib/MeasureTheory/Measure/WithDensity.lean`
  (`lintegral_withDensity_eq_lintegral_mul`),
  `Mathlib/MeasureTheory/Measure/Map.lean` (`Measure.map_map`).
-/

open MeasureTheory Real Spacetime.Minkowski
open scoped ENNReal

namespace QFT.KleinGordon

/-! ### The weighted spatial measure -/

/-- The **weighted spatial measure** `d³p/(2ω_p)` on the physical-momentum slice `M3`: the
factor of `massShellMeasure m` living upstream of the parametrization (Wigner 1939, §6,
eq. (59a), up to the conventional factor `1/2`). -/
noncomputable def spatialShellMeasure (m : ℝ) : Measure M3 :=
  volume.withDensity (massShellDensity m)

/-- The shell measure is the pushforward of the weighted spatial measure. -/
theorem massShellMeasure_eq_map_spatialShellMeasure (m : ℝ) :
    massShellMeasure m = Measure.map (massShellParam m) (spatialShellMeasure m) := rfl

/-! ### The Jacobian cancels the density -/

/-- **Pointwise Jacobian–density cancellation in `ℝ≥0∞`** (Wigner 1939, §6, footnote 26):
the absolute Jacobian `ω_(Λp)/ω_p` of `shellMap m Λ` times the weight at the image point is
the weight at the source point. This is the whole content of the invariance; everything
below is bookkeeping. -/
theorem ofReal_abs_det_mul_massShellDensity {m : ℝ} (hm : 0 < m)
    (Λ : RestrictedLorentzGroup) (p : M3) :
    ENNReal.ofReal |(fderiv ℝ (shellMap m Λ) p).det| * massShellDensity m (shellMap m Λ p)
      = massShellDensity m p := by
  have hp : 0 < physicalEnergy m p := physicalEnergy_pos m p hm
  have hq : 0 < physicalEnergy m (shellMap m Λ p) := physicalEnergy_pos m _ hm
  rw [abs_det_fderiv_shellMap (m := m) (Λ := Λ) (p := p) hm]
  simp only [massShellDensity]
  rw [← ENNReal.ofReal_mul (div_nonneg hq.le hp.le)]
  congr 1
  field_simp

/-! ### Invariance of the weighted spatial measure -/

/-- **H1 on the momentum slice**: `shellMap m Λ` preserves the weighted spatial measure
`d³p/(2ω_p)`.

The substitution is run in `ℝ≥0∞` (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`), which
carries no integrability hypothesis; the non-integrable weight `1/(2ω_p)` is therefore
handled exactly, and `Measure.ext_of_lintegral` upgrades the integral identity to equality of
measures. Wigner 1939, §6, eq. (59a) and footnote 26. -/
theorem shellMap_measurePreserving {m : ℝ} (hm : 0 < m) (Λ : RestrictedLorentzGroup) :
    MeasurePreserving (shellMap m Λ) (spatialShellMeasure m) (spatialShellMeasure m) := by
  have hf : Measurable (shellMap m Λ) := (continuous_shellMap m Λ).measurable
  refine ⟨hf, ?_⟩
  have hf' : ∀ x ∈ (Set.univ : Set M3),
      HasFDerivWithinAt (shellMap m Λ) (fderiv ℝ (shellMap m Λ) x) Set.univ x := by
    intro x _
    have h := hasFDerivAt_shellMap (m := m) (Λ := Λ) (p := x) hm.ne'
    rw [← fderiv_shellMap_eq (m := m) (Λ := Λ) (p := x) hm.ne'] at h
    exact h.hasFDerivWithinAt
  have himage : shellMap m Λ '' Set.univ = Set.univ := by
    rw [Set.image_univ, (surjective_shellMap m Λ hm).range_eq]
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hcomp : Measurable fun x : M3 => g (shellMap m Λ x) := hg.comp hf
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := (volume : Measure M3)) (s := (Set.univ : Set M3))
    (f := shellMap m Λ) (f' := fun x => fderiv ℝ (shellMap m Λ) x)
    MeasurableSet.univ hf' (injective_shellMap m Λ hm).injOn
    (fun q : M3 => massShellDensity m q * g q)
  rw [himage] at hcov
  simp only [Measure.restrict_univ] at hcov
  rw [lintegral_map hg hf, spatialShellMeasure,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_massShellDensity m) hcomp,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_massShellDensity m) hg]
  simp only [Pi.mul_apply]
  refine (hcov.trans (lintegral_congr fun x => ?_)).symm
  rw [← mul_assoc, ofReal_abs_det_mul_massShellDensity hm Λ x]

/-! ### Invariance of the mass-shell measure -/

/-- **H1**: every restricted Lorentz transformation preserves the positive mass-shell measure
`massShellMeasure m` for `0 < m`.

The proof commutes the two coordinate presentations of the same map,
`Λ ∘ massShellParam m = massShellParam m ∘ shellMap m Λ`
(`massShellParam_shellMap`), and pushes `shellMap_measurePreserving` through the pushforward
definition of `massShellMeasure` with `Measure.map_map`. Wigner 1939, §6, eq. (59a) and
footnote 26; Weinberg I, §2.5. -/
theorem lorentz_massShellMeasure_preserving {m : ℝ} (hm : 0 < m)
    (Λ : RestrictedLorentzGroup) :
    MeasurePreserving (lorentzMeasurableEquiv Λ) (massShellMeasure m) (massShellMeasure m) := by
  have hΛ : Measurable (lorentzMeasurableEquiv Λ) := (lorentzMeasurableEquiv Λ).measurable
  have hP : Measurable (massShellParam m) := measurable_massShellParam m
  have hS : Measurable (shellMap m Λ) := (continuous_shellMap m Λ).measurable
  have hcomm : (lorentzMeasurableEquiv Λ) ∘ (massShellParam m)
      = (massShellParam m) ∘ (shellMap m Λ) := by
    funext p
    rw [Function.comp_apply, Function.comp_apply, lorentzMeasurableEquiv_apply,
      massShellParam_shellMap m Λ p hm]
  refine ⟨hΛ, ?_⟩
  calc Measure.map (lorentzMeasurableEquiv Λ) (massShellMeasure m)
      = Measure.map ((lorentzMeasurableEquiv Λ) ∘ (massShellParam m))
          (spatialShellMeasure m) := by
        rw [massShellMeasure_eq_map_spatialShellMeasure, Measure.map_map hΛ hP]
    _ = Measure.map ((massShellParam m) ∘ (shellMap m Λ)) (spatialShellMeasure m) := by
        rw [hcomm]
    _ = Measure.map (massShellParam m) (Measure.map (shellMap m Λ) (spatialShellMeasure m)) :=
        (Measure.map_map hP hS).symm
    _ = massShellMeasure m := by
        rw [(shellMap_measurePreserving hm Λ).map_eq,
          massShellMeasure_eq_map_spatialShellMeasure]

/-- **The H1 hypothesis of `Atlas.Proofs.ShellOneParticle`, discharged.** The predicate
`LorentzShellPreserves m Λ` is no longer an assumption for `0 < m`: the conditional Wigner
action `shellPoincare m g hg` may be instantiated at
`lorentzShellPreserves hm g.lorentz` for every element of the restricted Poincaré group.
Wigner 1939, §6, eq. (59a) and footnote 26. -/
theorem lorentzShellPreserves {m : ℝ} (hm : 0 < m) (Λ : RestrictedLorentzGroup) :
    LorentzShellPreserves m Λ :=
  lorentz_massShellMeasure_preserving hm Λ

end QFT.KleinGordon
