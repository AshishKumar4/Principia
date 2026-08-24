import Atlas.Specs.Spacetime.Poincare
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Topology and volume of the restricted Poincare group

Reusable consequences of the topology frozen in P2.4a: continuity of group
components, inversion and the affine action, plus preservation of Minkowski
Lebesgue volume. These facts serve both the regular-representation witness and
the mass-shell one-particle representation.

Sources: Streater--Wightman, *PCT, Spin and Statistics, and All That*, Ch. 1;
Weinberg, *The Quantum Theory of Fields* I, Section 2.3. Citations are at
chapter/section level; no display number is asserted here.
-/

open MeasureTheory

namespace Spacetime.Minkowski

noncomputable section

namespace RestrictedLorentzGroup

/-- The inclusion into continuous linear maps is continuous by definition of the
frozen induced topology. -/
theorem continuous_coe :
    Continuous fun Λ : RestrictedLorentzGroup =>
      ((Λ : M4 ≃L[ℝ] M4) : M4 →L[ℝ] M4) :=
  continuous_induced_dom

private def clmUnit (e : M4 ≃L[ℝ] M4) : (M4 →L[ℝ] M4)ˣ where
  val := e
  inv := e.symm
  val_inv := by ext x; simp
  inv_val := by ext x; simp

private theorem ring_inverse_clm (e : M4 ≃L[ℝ] M4) :
    Ring.inverse ((e : M4 →L[ℝ] M4)) =
      ((e.symm : M4 ≃L[ℝ] M4) : M4 →L[ℝ] M4) :=
  Ring.inverse_unit (clmUnit e)

/-- Inversion is continuous on the frozen operator-norm topology of the
restricted Lorentz group. -/
instance : ContinuousInv RestrictedLorentzGroup where
  continuous_inv := by
    rw [continuous_induced_rng]
    have key : (fun Λ : RestrictedLorentzGroup =>
        (((Λ⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) : M4 →L[ℝ] M4))
        = fun Λ : RestrictedLorentzGroup =>
          Ring.inverse (((Λ : M4 ≃L[ℝ] M4) : M4 →L[ℝ] M4)) := by
      funext Λ
      rw [show ((Λ⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) =
        (Λ : M4 ≃L[ℝ] M4).symm from rfl, ← ring_inverse_clm]
    show Continuous fun Λ : RestrictedLorentzGroup =>
      (((Λ⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) : M4 →L[ℝ] M4)
    rw [key]
    refine continuous_iff_continuousAt.2 fun Λ₀ => ?_
    have h0 : ContinuousAt Ring.inverse
        (((Λ₀ : M4 ≃L[ℝ] M4) : M4 →L[ℝ] M4)) :=
      NormedRing.inverse_continuousAt (clmUnit (Λ₀ : M4 ≃L[ℝ] M4))
    exact ContinuousAt.comp
      (f := fun Λ : RestrictedLorentzGroup =>
        ((Λ : M4 ≃L[ℝ] M4) : M4 →L[ℝ] M4))
      (x := Λ₀) h0 continuous_coe.continuousAt

end RestrictedLorentzGroup

namespace PoincareGroup

/-- Both components vary continuously in the frozen product topology. -/
theorem continuous_components :
    Continuous fun g : PoincareGroup => (g.translation, g.lorentz) :=
  continuous_induced_dom

theorem continuous_translation : Continuous translation :=
  continuous_fst.comp continuous_components

theorem continuous_lorentz : Continuous lorentz :=
  continuous_snd.comp continuous_components

/-- The affine action `(g,x) ↦ Λx+a` is jointly continuous. -/
instance : ContinuousSMul PoincareGroup M4 where
  continuous_smul := by
    have h : (fun q : PoincareGroup × M4 => q.1 • q.2) =
        fun q : PoincareGroup × M4 =>
          ((q.1.lorentz : M4 ≃L[ℝ] M4) : M4 →L[ℝ] M4) q.2 +
            q.1.translation := rfl
    rw [h]
    exact (isBoundedBilinearMap_apply.continuous.comp
      (((RestrictedLorentzGroup.continuous_coe.comp continuous_lorentz).comp
        continuous_fst).prodMk continuous_snd)).add
      (continuous_translation.comp continuous_fst)

/-- Inversion `(a,Λ)⁻¹=(-Λ⁻¹a,Λ⁻¹)` is continuous. -/
instance : ContinuousInv PoincareGroup where
  continuous_inv := by
    rw [continuous_induced_rng]
    show Continuous fun g : PoincareGroup => (g⁻¹.translation, g⁻¹.lorentz)
    refine Continuous.prodMk ?_ ?_
    · show Continuous fun g : PoincareGroup =>
        -((g.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4)
          g.translation
      exact (isBoundedBilinearMap_apply.continuous.comp
        ((RestrictedLorentzGroup.continuous_coe.comp
          (continuous_inv.comp continuous_lorentz)).prodMk
          continuous_translation)).neg
    · exact continuous_inv.comp continuous_lorentz

/-- A restricted Lorentz transformation preserves Minkowski Lebesgue volume. -/
theorem volume_preserving_lorentz (Λ : RestrictedLorentzGroup) :
    MeasurePreserving ((Λ : M4 ≃L[ℝ] M4)) (volume : Measure M4) volume := by
  refine ⟨(Λ : M4 ≃L[ℝ] M4).continuous.measurable, ?_⟩
  have h : ⇑(Λ : M4 ≃L[ℝ] M4) =
      ⇑(((Λ : M4 ≃L[ℝ] M4).toLinearEquiv : M4 →ₗ[ℝ] M4)) := rfl
  rw [h, Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (by rw [RestrictedLorentzGroup.det_eq_one Λ]; norm_num),
    RestrictedLorentzGroup.det_eq_one Λ]
  norm_num

/-- The affine Poincare action preserves Minkowski Lebesgue volume. -/
theorem volume_preserving_smul (g : PoincareGroup) :
    MeasurePreserving (g • · : M4 → M4) (volume : Measure M4) volume := by
  have h : (g • · : M4 → M4) =
      (fun x : M4 => x + g.translation) ∘
        ⇑(g.lorentz : M4 ≃L[ℝ] M4) := rfl
  rw [h]
  exact (measurePreserving_add_right volume g.translation).comp
    (volume_preserving_lorentz g.lorentz)

/-- The affine action as a continuous self-map of `M4`. -/
def smulCM (g : PoincareGroup) : C(M4, M4) :=
  ⟨fun x => g • x, continuous_const_smul g⟩

theorem continuous_smulCM : Continuous smulCM :=
  ContinuousMap.continuous_of_continuous_uncurry smulCM continuous_smul

/-- The inverse of a pure translation acts by subtraction. -/
theorem translation_inv_smul (b x : M4) :
    (⟨b, 1⟩ : PoincareGroup)⁻¹ • x = x - b := by
  rw [smul_def, inv_translation, inv_lorentz]
  show (((1 : RestrictedLorentzGroup)⁻¹ : RestrictedLorentzGroup) :
      M4 ≃L[ℝ] M4) x +
    -(((1 : RestrictedLorentzGroup)⁻¹ : RestrictedLorentzGroup) :
      M4 ≃L[ℝ] M4) b = x - b
  rw [inv_one, OneMemClass.coe_one]
  show x + -b = x - b
  rw [sub_eq_add_neg]

theorem translation_preimage_ball (b : M4) (r : ℝ) :
    (fun x : M4 => (⟨b, 1⟩ : PoincareGroup)⁻¹ • x) ⁻¹'
      Metric.ball 0 r = Metric.ball b r := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_ball, translation_inv_smul]
  rw [dist_zero_right, dist_eq_norm]

end PoincareGroup

end

end Spacetime.Minkowski
