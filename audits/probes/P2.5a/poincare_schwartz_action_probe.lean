import Atlas.Witnesses.WightmanUtilities
import Atlas.Witnesses.Poincare

/-!
# P2.5a adversarial kernel probes — the Poincaré action on Schwartz space

The DRAFT spec defines the Poincaré action on `𝓢(M4, ℂ)` as the pullback by the INVERSE
affine action, `(g ▷ f)(x) = f (g⁻¹ • x)` — never by `g • x`. These probes reject the
two neighbouring constructions:

* the forward-affine impostor `f ↦ f (g • x)`: it differs from the spec action at a
  computable point (`0` versus `1` at `x = 2∂₀`), and it does not satisfy the covariance
  law `ψ(g₁ * g₂) = ψ g₁ ∘ ψ g₂` — for the mixed pair `(e₁, 1)` and `(0, R)` the two
  sides evaluate to `1` and `0` at `x = ∂₀ + e₁`;
* the wrong composition order for the true action: `▷(g₁ * g₂) = ▷g₂ ∘ ▷g₁` fails on
  the same pair at the same point (`1` versus `0`), while the correct order
  `▷(g₁ * g₂) = ▷g₁ ∘ ▷g₂` holds there. The semidirect twist makes the distinction
  visible: translations alone commute, so the mixed pair is essential.

`R` is the spatial `π`-rotation `diag(1, -1, -1, 1)` of the P2.4W witnesses, and the
mixed pair is exactly the pair whose two multiplication orders differ
(`rotationOnly_mul_translationE1_ne`).

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.5a/` only.
-/

open MeasureTheory RealInnerProductSpace
open Spacetime.Minkowski
open scoped SchwartzMap FourierTransform

/-! ## Affine arithmetic for the witness elements -/

theorem probe_smul_translationE1 (x : M4) :
    PoincareGroup.translationE1 • x = x + spaceUnit := by
  rw [PoincareGroup.smul_def]
  rfl

theorem probe_inv_smul_translationE1 (x : M4) :
    PoincareGroup.translationE1⁻¹ • x = x - spaceUnit := by
  have hinv : PoincareGroup.translationE1⁻¹ = ⟨-spaceUnit, (1 : RestrictedLorentzGroup)⟩ :=
    PoincareGroup.ext (by simp [PoincareGroup.translationE1]; rfl)
      (by simp [PoincareGroup.translationE1])
  rw [hinv, PoincareGroup.smul_def, Subgroup.coe_one]
  show x + -spaceUnit = x - spaceUnit
  rw [sub_eq_add_neg]

theorem probe_inv_smul_rotationOnly (x : M4) :
    PoincareGroup.rotationOnly⁻¹ • x = rotation12Equiv x := by
  have hself : PoincareGroup.rotationOnly⁻¹ = PoincareGroup.rotationOnly :=
    inv_eq_of_mul_eq_one_right
      (PoincareGroup.ext
        (by simp [PoincareGroup.rotationOnly])
        (by simp [PoincareGroup.rotationOnly,
          RestrictedLorentzGroup.rotation12_mul_self]))
  rw [hself, PoincareGroup.smul_def]
  simp [PoincareGroup.rotationOnly]

theorem probe_smul_rotationOnly (x : M4) :
    PoincareGroup.rotationOnly • x = rotation12Equiv x := by
  rw [PoincareGroup.smul_def]
  simp [PoincareGroup.rotationOnly]

theorem probe_rotation12Equiv_timeUnit_add_spaceUnit :
    rotation12Equiv (timeUnit + spaceUnit : M4) = timeUnit - spaceUnit := by
  ext j
  fin_cases j <;>
    simp [rotation12Equiv_apply_zero, rotation12Equiv_apply_one,
      rotation12Equiv_apply_two, rotation12Equiv_apply_three]

theorem probe_rotation12Equiv_timeUnit_add_two_spaceUnit :
    rotation12Equiv (timeUnit + spaceUnit + spaceUnit : M4)
      = timeUnit - (2 : ℝ) • spaceUnit := by
  ext j
  fin_cases j
  all_goals
    simp [rotation12Equiv_apply_zero, rotation12Equiv_apply_one,
      rotation12Equiv_apply_two, rotation12Equiv_apply_three]
  all_goals norm_num

/-- The bump vanishes at `∂₀ - 2e₁`, the point where the wrong order lands. -/
theorem probe_testFn_timeUnit_sub_two_spaceUnit :
    testFn (timeUnit - (2 : ℝ) • spaceUnit) = 0 := by
  rw [testFn_apply, bumpFuture.zero_of_le_dist ?_]
  · norm_num
  · show (1 : ℝ) ≤ _
    rw [dist_eq_norm]
    have h : (timeUnit - (2 : ℝ) • spaceUnit : M4) - timeUnit
        = (-2 : ℝ) • spaceUnit := by module
    rw [h, norm_smul]
    simp

theorem probe_smul_translateTimeUnit (x : M4) :
    translateTimeUnit • x = x + timeUnit := by
  rw [PoincareGroup.smul_def]
  rfl

/-! ## The forward-affine impostor -/

/-- The impostor: pullback along the FORWARD affine action, `ψ(g) f x = f (g • x)` —
built from the same Mathlib operators as the spec action, with the translation slot and
the linear slot swapped relative to it. -/
noncomputable def probeForwardPullbackCLM (g : PoincareGroup) : 𝓢(M4, ℂ) →L[ℂ] 𝓢(M4, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (g.lorentz : M4 ≃L[ℝ] M4)).comp
    (SchwartzMap.compSubConstCLM ℂ (-g.translation))

theorem probe_forwardPullback_apply (g : PoincareGroup) (f : 𝓢(M4, ℂ)) (x : M4) :
    probeForwardPullbackCLM g f x = f (g • x) := by
  simp only [probeForwardPullbackCLM, ContinuousLinearMap.coe_comp, Function.comp_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, SchwartzMap.compSubConstCLM_apply,
    PoincareGroup.smul_def]
  rw [sub_neg_eq_add]

/-- The impostor is not the spec action: at `x = 2∂₀` the true action returns the bump
peak `1` (the translated argument lands on the centre), while the impostor returns `0`
(the pushed argument leaves the support). -/
theorem probe_forward_pullback_ne_action :
    probeForwardPullbackCLM translateTimeUnit testFn
      ≠ PoincareGroup.schwartzActionCLM translateTimeUnit testFn := by
  intro h
  have hval := DFunLike.congr_fun h ((2 : ℝ) • timeUnit)
  rw [PoincareGroup.schwartzActionCLM_apply_apply, inv_smul_translateTimeUnit_two,
    testFn_timeUnit, probe_forwardPullback_apply, probe_smul_translateTimeUnit,
    show ((2 : ℝ) • (timeUnit : M4) + timeUnit) = (3 : ℝ) • timeUnit from by module,
    testFn_three_timeUnit] at hval
  exact one_ne_zero hval.symm

/-- Refutation: the impostor does not satisfy the covariance law. For `g₁ = (e₁, 1)`
and `g₂ = (0, R)`, the left side reads `f(Rx + e₁)` and the composite reads
`f(R(x + e₁)) = f(Rx - e₁)`; at `x = ∂₀ + e₁` these are `f(∂₀) = 1` versus
`f(∂₀ - 2e₁) = 0`. -/
theorem probe_forward_pullback_not_hom :
    ¬ ∀ g₁ g₂ : PoincareGroup,
      probeForwardPullbackCLM (g₁ * g₂)
        = (probeForwardPullbackCLM g₁).comp (probeForwardPullbackCLM g₂) := by
  intro h
  have hval := DFunLike.congr_fun
    (DFunLike.congr_fun (h PoincareGroup.translationE1 PoincareGroup.rotationOnly)
      testFn) (timeUnit + spaceUnit)
  have hl : probeForwardPullbackCLM (PoincareGroup.translationE1 *
      PoincareGroup.rotationOnly) testFn (timeUnit + spaceUnit) = 1 := by
    rw [probe_forwardPullback_apply, mul_smul,
      probe_smul_rotationOnly, probe_rotation12Equiv_timeUnit_add_spaceUnit,
      probe_smul_translationE1, sub_add_cancel, testFn_timeUnit]
  have hr : (probeForwardPullbackCLM PoincareGroup.translationE1).comp
      (probeForwardPullbackCLM PoincareGroup.rotationOnly) testFn
      (timeUnit + spaceUnit) = 0 := by
    rw [ContinuousLinearMap.coe_comp, Function.comp_apply,
      probe_forwardPullback_apply, probe_forwardPullback_apply,
      probe_smul_translationE1, probe_smul_rotationOnly,
      probe_rotation12Equiv_timeUnit_add_two_spaceUnit,
      probe_testFn_timeUnit_sub_two_spaceUnit]
  rw [hl, hr] at hval
  exact one_ne_zero hval

/-! ## Wrong composition order fails for the true action; the correct order holds -/

/-- The correct covariant order, engaged at the twisted pair: acting first with the
rotation and then translating agrees with acting by the product. -/
theorem probe_action_twist_at :
    PoincareGroup.schwartzActionCLM (PoincareGroup.translationE1 *
      PoincareGroup.rotationOnly) testFn (timeUnit + spaceUnit) = 1 := by
  rw [PoincareGroup.schwartzActionCLM_apply_apply, mul_inv_rev, mul_smul,
    probe_inv_smul_translationE1, add_sub_cancel_right, probe_inv_smul_rotationOnly,
    rotation12Equiv_single_zero, testFn_timeUnit]

/-- Refutation: the reversed order `▷(g₁ * g₂) = ▷g₂ ∘ ▷g₁` fails on the twisted pair.
The reversed composite reads `f(t⁻¹ • (r⁻¹ • x)) = f(Rx - e₁)`, which vanishes at
`x = ∂₀ + e₁`, while the product action returns the bump peak there. -/
theorem probe_wrong_composition_order_fails :
    ¬ ∀ g₁ g₂ : PoincareGroup,
      PoincareGroup.schwartzActionCLM (g₁ * g₂)
        = (PoincareGroup.schwartzActionCLM g₂).comp (PoincareGroup.schwartzActionCLM g₁) := by
  intro h
  have hval := DFunLike.congr_fun
    (DFunLike.congr_fun (h PoincareGroup.translationE1 PoincareGroup.rotationOnly)
      testFn) (timeUnit + spaceUnit)
  rw [probe_action_twist_at] at hval
  have hr : (PoincareGroup.schwartzActionCLM PoincareGroup.rotationOnly).comp
      (PoincareGroup.schwartzActionCLM PoincareGroup.translationE1) testFn
      (timeUnit + spaceUnit) = 0 := by
    rw [ContinuousLinearMap.coe_comp, Function.comp_apply,
      PoincareGroup.schwartzActionCLM_apply_apply,
      PoincareGroup.schwartzActionCLM_apply_apply, probe_inv_smul_rotationOnly,
      probe_rotation12Equiv_timeUnit_add_spaceUnit, probe_inv_smul_translationE1,
      show ((timeUnit - spaceUnit : M4) - spaceUnit)
        = timeUnit - (2 : ℝ) • spaceUnit from by module,
      probe_testFn_timeUnit_sub_two_spaceUnit]
  rw [hr] at hval
  exact one_ne_zero hval
