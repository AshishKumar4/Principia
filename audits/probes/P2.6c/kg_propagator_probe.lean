import Atlas.Proofs.KGPropagator
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# P2.6c adversarial probes — the Pauli–Jordan propagator lane (P2.6c/L1)

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.6c/` only. It pins the
landed surface of `Atlas.Proofs.KGPropagator` to **final observables** evaluated on a
concrete Cauchy datum: `phiVel ∈ 𝓢(M3, ℂ)`, a smooth bump centred at `bumpCenter ≠ 0`
with `phiVel bumpCenter = 1` and `phiVel (-bumpCenter) = 0`.

Positive checks:

* `u phiVel 0 x = 0` (`probe_zero_initial_position`) and oddness
  `u phiVel (-3) x = -u phiVel 3 x` (`probe_odd_time`);
* the initial-velocity observable `deriv (t ↦ u phiVel t bumpCenter) 0 = phiVel
  bumpCenter = 1` (`probe_initial_velocity_value`);
* the Fourier-character sign/`2π` check at a genuinely oscillating, nonperiodic phase:
  for `⟪probeK, probeX⟫ = 1/4` the propagator character evaluates exactly to `i`
  (`probe_char_quarter_phase`), is not `1` (`probe_phase_nonperiodic`), differs from its
  own inverse (`probe_sign_differs`), and differs from the `2π`-free kernel
  (`probe_no2pi_differs`).

Refutations:

* the wrong cosine initial-velocity kernel: the cosine-kernel integral
  `kgPropagator_dt` carries the position datum at time zero
  (`cosLane_initial_position`: `1 ≠ 0` observed in `probe_cosLane_carries_position`)
  and its own time derivative vanishes identically (`deriv_cosLane_zero`, instantiated
  as `probe_cosLane_velocity_is_zero` with observable `0 ≠ 1`), so it cannot be the
  initial-velocity propagator;
* the wrong forward-sign inversion: integrating `𝓕(phi)` against the conjugate of the
  propagator character returns the parity-reflected field `x ↦ phi (-x)`
  (`wrongInversion_eq_reflected`), which observes `0` where the true inversion observes
  `1` (`probe_forward_sign_fails`).
-/

open MeasureTheory Real
open scoped FourierTransform SchwartzMap

namespace QFT.KleinGordonProbe

open QFT.KleinGordon

/-! ### A concrete nonzero Cauchy datum on `M3` -/

/-- Probe centre: the unit vector along the first spatial axis. -/
noncomputable def bumpCenter : M3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- The probe bump: smooth, compactly supported in the unit ball around `bumpCenter`,
equal to `1` at the centre. -/
noncomputable def velBump : ContDiffBump (bumpCenter : M3) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The probe Cauchy datum: the bump viewed in `ℂ`, packaged as a Schwartz map. -/
noncomputable def phiVel : 𝓢(M3, ℂ) :=
  HasCompactSupport.toSchwartzMap
    (f := fun x : M3 => ((velBump x : ℝ) : ℂ))
    (velBump.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp velBump.contDiff)

theorem phiVel_apply (x : M3) : phiVel x = ((velBump x : ℝ) : ℂ) := rfl

/-- Final observable: the datum takes the value `1` at its own centre. -/
theorem phiVel_center : phiVel bumpCenter = 1 := by
  rw [phiVel_apply,
    velBump.one_of_mem_closedBall (Metric.mem_closedBall_self velBump.rIn_pos.le)]
  norm_num

/-- The parity-reflected centre leaves the support, so the datum vanishes there. This is
what makes the datum *not even* — the property every sign refutation below consumes. -/
theorem phiVel_neg_center : phiVel (-bumpCenter) = 0 := by
  have hv : (-bumpCenter : M3) - bumpCenter = (-2 : ℝ) • bumpCenter := by
    simp only [bumpCenter]
    module
  have hn : ‖bumpCenter‖ = 1 := by simp [bumpCenter]
  have hd : (1 : ℝ) ≤ dist (-bumpCenter) bumpCenter := by
    rw [dist_eq_norm, hv, norm_smul, Real.norm_eq_abs, hn]
    norm_num
  rw [phiVel_apply, velBump.zero_of_le_dist hd, Complex.ofReal_zero]

private theorem norm_ofReal_le' {r C : ℝ} (h : |r| ≤ C) :
    ‖(Complex.ofReal r : ℂ)‖ ≤ C := by simpa using h

private theorem continuous_pjChar_mom (x : M3) :
    Continuous fun k : M3 => pjChar x k := by
  have heq : (fun k : M3 => pjChar x k)
      = fun k : M3 => Complex.exp ((2 * π * inner ℝ k x) * Complex.I) :=
    funext fun k => pjChar_eq_exp x k
  rw [heq]
  fun_prop

/-! ### Positive observables of the landed propagator -/

/-- Final observable of **PJ.1a**: zero initial position at explicit parameters. -/
theorem probe_zero_initial_position :
    kgPropagator 1 phiVel 0 bumpCenter = 0 := kgPropagator_zero_time 1 phiVel _

/-- Final observable of **PJ.1a** (oddness): time reflection flips the field. -/
theorem probe_odd_time :
    kgPropagator 1 phiVel (-3) bumpCenter = -kgPropagator 1 phiVel 3 bumpCenter :=
  kgPropagator_neg_time 1 phiVel 3 bumpCenter

/-- The initial-velocity observable as an honest derivative, on the concrete datum. -/
theorem probe_initial_velocity :
    deriv (fun s : ℝ => kgPropagator 1 phiVel s bumpCenter) 0 = phiVel bumpCenter :=
  deriv_kgPropagator_zero 1 one_pos phiVel bumpCenter

/-- Final observable of **PJ.1f**: the derivative at zero recovers the value `1`. -/
theorem probe_initial_velocity_value :
    deriv (fun s : ℝ => kgPropagator 1 phiVel s bumpCenter) 0 = 1 := by
  rw [probe_initial_velocity]
  exact phiVel_center

/-! ### The Fourier-character sign/`2π` check at a nonperiodic phase -/

/-- Probe momentum: the unit vector along the first spatial axis. -/
noncomputable def probeK : M3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- Probe position: a quarter unit along the same axis, so that the pairing is the
non-integer phase `1/4`. -/
noncomputable def probeX : M3 := EuclideanSpace.single (0 : Fin 3) (1 / 4 : ℝ)

theorem probe_inner_quarter : inner ℝ probeK probeX = 1 / 4 := by
  simp [probeK, probeX, EuclideanSpace.inner_single_left]

/-- The exponent carried by the propagator character is `+2πi⟪k,x⟫`: both the `2π`
(Mathlib normalization) and the plus sign (inverse transform) are visible. -/
theorem probe_character_exponent (k x : M3) :
    pjChar x k = Complex.exp ((2 * π * inner ℝ k x) * Complex.I) :=
  pjChar_eq_exp x k

/-- Transport lemma: the split-coercion spelling of the quarter coefficient is the
coerced `π / 2`. -/
private theorem probe_coeff_quarter :
    ((2 : ℂ) * (π : ℂ) * ((1 / 4 : ℝ) : ℂ)) = ((π : ℂ) / 2) := by
  rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    show ((2 * π * (1 / 4 : ℝ) : ℝ)) = (π / 2 : ℝ) from by ring]
  push_cast
  rfl

/-- At the quarter phase the character evaluates exactly to `i`: neither trivial nor
real, hence genuinely oscillating. -/
theorem probe_char_quarter_phase : pjChar probeX probeK = Complex.I := by
  rw [probe_character_exponent, probe_inner_quarter, probe_coeff_quarter,
    Complex.exp_pi_div_two_mul_I]

private theorem probe_I_ne_one : (Complex.I : ℂ) ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre

private theorem probe_I_ne_neg_I : (Complex.I : ℂ) ≠ -Complex.I := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.neg_im, Complex.I_im] at him
  norm_num at him

/-- Nonperiodicity at the probe phase: the character is not `1`. -/
theorem probe_phase_nonperiodic : pjChar probeX probeK ≠ 1 := by
  rw [probe_char_quarter_phase]
  exact probe_I_ne_one

/-- Sign check at the probe phase: the character differs from its own inverse, i.e.
from the forward-sign character. -/
theorem probe_sign_differs : pjChar probeX probeK ≠ (pjChar probeX probeK)⁻¹ := by
  rw [probe_char_quarter_phase, Complex.inv_I]
  exact probe_I_ne_neg_I

/-- Dropping the `2π` changes the kernel value at the probe phase:
`exp(i·1/4) ≠ exp(2πi·1/4)`. -/
noncomputable def charNo2pi (k x : M3) : ℂ := Complex.exp ((inner ℝ k x) * Complex.I)

theorem probe_no2pi_differs : charNo2pi probeK probeX ≠ pjChar probeX probeK := by
  intro heq
  have hv : charNo2pi probeK probeX = Complex.cos ((1 / 4 : ℝ) : ℂ) +
      Complex.sin ((1 / 4 : ℝ) : ℂ) * Complex.I := by
    rw [charNo2pi, probe_inner_quarter, Complex.exp_mul_I]
  rw [hv, probe_char_quarter_phase] at heq
  have hre := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.mul_re, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    mul_zero, zero_mul, sub_zero] at hre
  have hpos : 0 < Real.cos ((1 : ℝ) / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  exact absurd hre (by linarith)

/-! ### Refutation: the wrong cosine initial-velocity kernel -/

/-- The cosine-kernel integral is the *position*-data lane: its value at time zero is
the datum itself (**PJ.1f** restated for contrast). -/
theorem cosLane_initial_position (m : ℝ) (phi : 𝓢(M3, ℂ)) (x : M3) :
    kgPropagator_dt m phi 0 x = phi x := kgPropagator_dt_zero m phi x

/-- Mass-gap envelope for the derivative domination. -/
private theorem omega_le_scaled (m : ℝ) (hm : 0 < m) (k : M3) :
    dispersion m k ≤ (2 * π + m) * (1 + ‖k‖) := by
  have h1 : dispersion m k ≤ 2 * π * ‖k‖ + m := dispersion_le m k hm.le
  have h2 : 0 ≤ m * ‖k‖ := mul_nonneg hm.le (norm_nonneg k)
  have h3 : (2 * π + m) * (1 + ‖k‖)
      = (2 * π * ‖k‖ + m) + (2 * π + m * ‖k‖) := by ring
  rw [h3]
  linarith [Real.pi_pos]

private theorem cosLane_integrand_deriv (m : ℝ) (phi : 𝓢(M3, ℂ)) (x : M3)
    (r : ℝ) (k : M3) :
    HasDerivAt
      (fun s : ℝ =>
        (Complex.ofReal (Real.cos (s * dispersion m k)) * (𝓕 phi) k) * pjChar x k)
      ((Complex.ofReal
            (-(dispersion m k * Real.sin (r * dispersion m k))) * (𝓕 phi) k) *
        pjChar x k) r := by
  have h0 := ((hasDerivAt_id r).mul_const (dispersion m k)).cos
  rw [show (-Real.sin (id r * dispersion m k) * (1 * dispersion m k))
      = -(dispersion m k * Real.sin (r * dispersion m k)) from by
        simp only [id_eq, one_mul]; ring] at h0
  exact (h0.ofReal_comp.mul_const ((𝓕 phi) k)).mul_const (pjChar x k)

set_option maxHeartbeats 1000000 in
private theorem cosLane_integrand_bound (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ))
    (x : M3) (r : ℝ) (k : M3) :
    ‖(Complex.ofReal
          (-(dispersion m k * Real.sin (r * dispersion m k))) * (𝓕 phi) k) *
      pjChar x k‖ ≤ (2 * π + m) * (‖k‖ * ‖(𝓕 phi) k‖ + ‖(𝓕 phi) k‖) := by
  have hΩnn : 0 ≤ dispersion m k := (dispersion_pos m k hm.ne').le
  have habs : |-(dispersion m k * Real.sin (r * dispersion m k))| ≤ dispersion m k := by
    rw [abs_neg, abs_mul, abs_of_nonneg hΩnn]
    calc dispersion m k * |Real.sin (r * dispersion m k)| ≤ dispersion m k * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hΩnn
      _ = dispersion m k := mul_one _
  have h1 := norm_ofReal_le' habs
  have h2 := omega_le_scaled m hm k
  calc ‖(Complex.ofReal
            (-(dispersion m k * Real.sin (r * dispersion m k))) * (𝓕 phi) k) *
        pjChar x k‖
      = ‖Complex.ofReal
            (-(dispersion m k * Real.sin (r * dispersion m k)))‖ * ‖(𝓕 phi) k‖ := by
        simp
    _ ≤ dispersion m k * ‖(𝓕 phi) k‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ (2 * π + m) * (1 + ‖k‖) * ‖(𝓕 phi) k‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = (2 * π + m) * (‖k‖ * ‖(𝓕 phi) k‖ + ‖(𝓕 phi) k‖) := by ring

private theorem cosLane_measurability (m : ℝ) (phi : 𝓢(M3, ℂ)) (x : M3) (r : ℝ) :
    AEStronglyMeasurable
      (fun k : M3 =>
        (Complex.ofReal (Real.cos (r * dispersion m k)) * (𝓕 phi) k) * pjChar x k)
      volume :=
  (((Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (continuous_const.mul (continuous_dispersion m)))).mul
      (𝓕 phi).continuous).mul (continuous_pjChar_mom x)).aestronglyMeasurable

private theorem cosLane_derivMeasurability (m : ℝ) (phi : 𝓢(M3, ℂ)) (x : M3) :
    AEStronglyMeasurable
      (fun k : M3 =>
        (Complex.ofReal
              (-(dispersion m k * Real.sin ((0 : ℝ) * dispersion m k))) *
            (𝓕 phi) k) * pjChar x k)
      volume :=
  (((Complex.continuous_ofReal.comp
        (((continuous_dispersion m).mul
              (Real.continuous_sin.comp
                (continuous_const.mul (continuous_dispersion m)))).neg)).mul
      (𝓕 phi).continuous).mul (continuous_pjChar_mom x)).aestronglyMeasurable

private theorem cosLane_derivVanishes (m : ℝ) (phi : 𝓢(M3, ℂ)) (x : M3) (k : M3) :
    (Complex.ofReal
          (-(dispersion m k * Real.sin ((0 : ℝ) * dispersion m k))) * (𝓕 phi) k) *
      pjChar x k = 0 := by
  simp

private theorem cosLane_bound_integrable (m : ℝ) (phi : 𝓢(M3, ℂ)) :
    Integrable (fun k : M3 =>
      (2 * π + m) * (‖k‖ * ‖(𝓕 phi) k‖ + ‖(𝓕 phi) k‖)) volume := by
  have hsplit := ((integrable_norm_fourier_mul phi 1).const_mul ((2 : ℝ) * π + m)).add
    ((integrable_norm_fourier phi).const_mul ((2 : ℝ) * π + m))
  refine hsplit.congr (Filter.Eventually.of_forall fun k => ?_)
  simp only [Pi.add_apply]
  ring
set_option maxHeartbeats 2000000 in

/-- The cosine lane has identically zero initial velocity: differentiating under the
integral (dominated by `(2π + m)(‖k‖ + 1)‖𝓕(phi)(k)‖`) kills every integrand because
`sin 0 = 0`. Hence the cosine kernel cannot serve as the initial-velocity propagator,
whose derivative observable is the nonzero datum. -/
theorem deriv_cosLane_zero (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (x : M3) :
    HasDerivAt (fun s : ℝ => kgPropagator_dt m phi s x) 0 0 := by
  have heq : (fun s : ℝ => kgPropagator_dt m phi s x)
      = fun s : ℝ => ∫ k : M3,
          (Complex.ofReal (Real.cos (s * dispersion m k)) * (𝓕 phi) k) * pjChar x k :=
    funext fun s => kgPropagator_dt_apply m phi s x
  rw [heq]
  have hmeas : ∀ᶠ r in nhds ((0 : ℝ)), AEStronglyMeasurable
      (fun k : M3 =>
        (Complex.ofReal (Real.cos (r * dispersion m k)) * (𝓕 phi) k) * pjChar x k)
      volume := Filter.Eventually.of_forall fun r => cosLane_measurability m phi x r
  have hfint : Integrable
      (fun k : M3 =>
        (Complex.ofReal (Real.cos ((0 : ℝ) * dispersion m k)) * (𝓕 phi) k) *
          pjChar x k)
      volume := integrable_kgPropagator_dt_integrand m phi 0 x
  have hdmeas : AEStronglyMeasurable
      (fun k : M3 =>
        (Complex.ofReal
              (-(dispersion m k * Real.sin ((0 : ℝ) * dispersion m k))) *
            (𝓕 phi) k) * pjChar x k)
      volume := cosLane_derivMeasurability m phi x
  have hbnd : ∀ᵐ k : M3, ∀ r ∈ (Set.univ : Set ℝ),
      ‖(Complex.ofReal
            (-(dispersion m k * Real.sin (r * dispersion m k))) * (𝓕 phi) k) *
        pjChar x k‖ ≤ (2 * π + m) * (‖k‖ * ‖(𝓕 phi) k‖ + ‖(𝓕 phi) k‖) :=
    ae_of_all volume fun k r _ => cosLane_integrand_bound m hm phi x r k
  have hbint : Integrable
      (fun k : M3 => (2 * π + m) * (‖k‖ * ‖(𝓕 phi) k‖ + ‖(𝓕 phi) k‖)) volume :=
    cosLane_bound_integrable m phi
  have hdf : ∀ᵐ k : M3, ∀ r ∈ (Set.univ : Set ℝ),
      HasDerivAt
        (fun s : ℝ =>
          (Complex.ofReal (Real.cos (s * dispersion m k)) * (𝓕 phi) k) * pjChar x k)
        ((Complex.ofReal
              (-(dispersion m k * Real.sin (r * dispersion m k))) * (𝓕 phi) k) *
          pjChar x k) r :=
    ae_of_all volume fun k r _ => cosLane_integrand_deriv m phi x r k
  obtain ⟨_, hd⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := (0 : ℝ)) (s := Set.univ)
      (μ := volume) Filter.univ_mem hmeas hfint hdmeas hbnd hbint hdf
  have hz : (∫ k : M3,
      (Complex.ofReal
            (-(dispersion m k * Real.sin ((0 : ℝ) * dispersion m k))) * (𝓕 phi) k) *
        pjChar x k) = 0 := by
    have hEqInt : (∫ k : M3,
        (Complex.ofReal
              (-(dispersion m k * Real.sin ((0 : ℝ) * dispersion m k))) *
            (𝓕 phi) k) * pjChar x k) = ∫ k : M3, (0 : ℂ) :=
      integral_congr_ae (Filter.Eventually.of_forall (cosLane_derivVanishes m phi x))
    rw [hEqInt, integral_zero]
  rwa [hz] at hd

/-- Observable contrast at time zero: the cosine lane carries the datum (`1`) while the
true velocity propagator sits at `0`. -/
theorem probe_cosLane_carries_position :
    kgPropagator_dt 1 phiVel 0 bumpCenter = 1 ∧ kgPropagator 1 phiVel 0 bumpCenter = 0 :=
  ⟨by rw [cosLane_initial_position]; exact phiVel_center, probe_zero_initial_position⟩

/-- Final refutation observable: the two lanes disagree in initial position. -/
theorem probe_wrong_cosLane_refuted :
    kgPropagator_dt 1 phiVel 0 bumpCenter ≠ kgPropagator 1 phiVel 0 bumpCenter := by
  rw [cosLane_initial_position 1 phiVel bumpCenter, phiVel_center,
    probe_zero_initial_position]
  norm_num

/-- Final refutation observable: the cosine lane's own time derivative at zero is `0`,
not the datum. -/
theorem probe_cosLane_velocity_is_zero :
    deriv (fun s : ℝ => kgPropagator_dt 1 phiVel s bumpCenter) 0 = 0 :=
  (deriv_cosLane_zero 1 one_pos phiVel bumpCenter).deriv

/-- The velocity observables of the two lanes differ: `0 ≠ 1`. -/
theorem probe_cosLane_not_velocity_lane :
    deriv (fun s : ℝ => kgPropagator_dt 1 phiVel s bumpCenter) 0 = 0 ∧
      deriv (fun s : ℝ => kgPropagator 1 phiVel s bumpCenter) 0 = 1 :=
  ⟨probe_cosLane_velocity_is_zero, probe_initial_velocity_value⟩

/-! ### Refutation: the wrong forward-sign inversion -/

/-- Integrating `𝓕(phi)` against the *conjugate* character — the forward-sign mistake —
defines this wrong inversion field. -/
noncomputable def wrongInversion (phi : 𝓢(M3, ℂ)) (x : M3) : ℂ :=
  ∫ k : M3, (𝓕 phi) k * (pjChar x k)⁻¹

private theorem pjChar_inv (x k : M3) : (pjChar x k)⁻¹ = pjChar (-x) k := by
  rw [pjChar_eq_exp, pjChar_eq_exp, inner_neg_right, Complex.ofReal_neg,
    ← Complex.exp_neg, mul_neg, neg_mul]

/-- The wrong forward-sign inversion returns the parity-*reflected* field, because the
conjugate character at `x` is the inverse character at `-x`. -/
theorem wrongInversion_eq_reflected (phi : 𝓢(M3, ℂ)) (x : M3) :
    wrongInversion phi x = phi (-x) := by
  rw [wrongInversion,
    integral_congr_ae (Filter.Eventually.of_forall fun k => by
      show (𝓕 phi) k * (pjChar x k)⁻¹ = (𝓕 phi) k * pjChar (-x) k
      rw [pjChar_inv]),
    fourier_inversion_eq]

/-- Final refutation observable: at `bumpCenter` the wrong-sign inversion observes `0`
where the correct inversion observes `1`. -/
theorem probe_forward_sign_fails :
    wrongInversion phiVel bumpCenter = 0 ∧ phiVel bumpCenter = 1 ∧
      phiVel (-bumpCenter) = 0 := by
  refine ⟨?_, phiVel_center, phiVel_neg_center⟩
  rw [wrongInversion_eq_reflected]
  exact phiVel_neg_center

/-- The wrong forward-sign kernel does not invert the transform on the concrete datum. -/
theorem probe_wrong_inversion_differs :
    wrongInversion phiVel bumpCenter ≠ phiVel bumpCenter := by
  rw [wrongInversion_eq_reflected, phiVel_center, phiVel_neg_center]
  norm_num

end QFT.KleinGordonProbe
