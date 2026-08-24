import Atlas.Proofs.KleinGordon
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# P2.6c / L1 — the Pauli–Jordan propagator of the free Klein–Gordon field

The Pauli–Jordan lane (blueprint node **P2.6c**, lemma node **L1**), built on the L0
dispersion layer of `Atlas.Proofs.KleinGordon`. For a mass `0 < m` and complex Schwartz
initial velocity `phi : 𝓢(M3, ℂ)` this file constructs the propagator field

`u phi t x = ∫ k, (sin(t Ω(k)) / Ω(k)) · 𝓕(phi)(k) · 𝐞(⟪k, x⟫)`,

with `Ω = QFT.KleinGordon.dispersion` (which already carries the `2π` of Mathlib's Fourier
normalization), `𝓕` Mathlib's Schwartz Fourier transform, and `𝐞 = Real.fourierChar`,
i.e. `𝐞 τ = exp(2πiτ)` (packaged below as `pjChar`).

## Proven prefix (named per the P2.6c contract)

* **PJ.1a** — the integral definition `kgPropagator`, with `kgPropagator_zero_time`
  (`u phi 0 x = 0`).
* **PJ.1b** — the reusable dominators. `integrable_norm_fourier_mul` gives every polynomial
  moment of `‖𝓕 phi‖` (via `SchwartzMap.integrable_pow_mul`); `abs_pjPhase_le` gives the
  mass-gap bound `|sin(tΩ)|/Ω ≤ 1/m`; `integrable_norm_mul_norm_fourier` and
  `integrable_dispersion_norm_fourier` are the first-moment and energy-weighted dominators
  that the spatial and the second time derivative consume; `integrable_kgPropagator_integrand`
  and `integrable_kgPropagator_dt_integrand` are the two absolute integrability statements.
* **PJ.1c** — the reusable kernel workhorses, all stated for an abstract momentum profile
  `ω ≥ m > 0`, an abstract amplitude, and a global dominator (the mass gap makes a local
  time window unnecessary).
  * `hasFDerivAt_pjChar` is the one analytic input on the character:
    `∂ₓ 𝐞(⟪k,x⟫) = 𝐞(⟪k,x⟫) · 2πi⟪k, ·⟫`, packaged by the momentum covectors `pjMomCLM`
    (first order) and `pjMom2CLM` (second order).
  * Continuity: `continuous_symbolKernel_integral`,
    `continuous_symbolKernelDx_integral`, `continuous_symbolKernelDxx_integral` send a
    jointly continuous symbol family with a fixed integrable dominator to a jointly
    continuous integral, with values in `ℂ`, in `M3 →L[ℝ] ℂ` and in
    `M3 →L[ℝ] M3 →L[ℝ] ℂ`. `continuous_sinKernel_integral` is the sine instance.
  * Time differentiation: `hasDerivAt_sinKernel_integral`,
    `hasDerivAt_cosKernel_integral`, `hasDerivAt_sinKernelDx_integral`.
  * Space differentiation: `hasFDerivAt_charIntegral` and `hasFDerivAt_charIntegralDx`
    differentiate under the integral once and twice; `charIntegralDx_apply_diag` evaluates
    the second derivative on the diagonal, and `laplacian_charIntegral` sums that over an
    orthonormal basis to the symbol `-4π²‖k‖²`.
* **PJ.1d** — the derived fields, each an explicit momentum integral, each identified with
  the corresponding derivative and each jointly continuous in `(t, x)`.
  * `kgPropagator_dt` — `∂ₜu` (`hasDerivAt_kgPropagator`, `continuous_kgPropagator_dt`).
  * `kgPropagator_dt2` — `∂ₜ²u` (`hasDerivAt_kgPropagator_dt`,
    `deriv_deriv_kgPropagator`, `continuous_kgPropagator_dt2`).
  * `kgPropagator_dx` — the spatial Fréchet derivative
    (`hasFDerivAt_kgPropagator_space`, `fderiv_kgPropagator_space`,
    `continuous_kgPropagator_dx`).
  * `kgPropagator_dtdx` — the mixed derivative, obtained in both orders directly:
    `hasFDerivAt_kgPropagator_dt_space` differentiates `∂ₜu` in space,
    `hasDerivAt_kgPropagator_dx` differentiates `∂ₓu` in time, and
    `kgPropagator_dtdx_comm` records that the two agree
    (`continuous_kgPropagator_dtdx`).
  * `kgPropagator_dxdx` — the second spatial derivative
    (`hasFDerivAt_kgPropagator_dx`, `continuous_kgPropagator_dxdx`).
* **PJ.1e** — the pointwise Klein–Gordon identity. `laplacian_kgPropagator` computes the
  spatial Laplacian of the field as the momentum integral `kgPropagator_laplacian` with
  symbol `-4π²‖k‖²`, and `kleinGordon_kgPropagator` is
  `∂ₜ²u = Δu - m²u`, from `-Ω² = -4π²‖k‖² - m²` (`dispersion_sq`).
* **PJ.1f** — `kgPropagator_dt_zero` and `deriv_kgPropagator_zero`: the initial velocity is
  the data itself, `∂ₜu phi 0 = phi`, via Schwartz Fourier inversion
  (`fourier_inversion_eq`); together with `kgPropagator_zero_time` this is the full Cauchy
  datum of the velocity lane.
* **PJ.1g** — `kgPropagator_neg_time`: the field is odd in time.

## Not yet proven

PJ.1a–PJ.1g are closed. Three things this file does not claim.

* The companion **position lane**: a field `v f` with `v f 0 = f` and `∂ₜv f 0 = 0`, which
  the general Cauchy problem needs beside the velocity lane built here.
* Smoothness past second order: no `ContDiff` statement is made, only the first and second
  derivatives named above.
* The join with the L2 cone cutoff of `Atlas.Proofs.KGConeCutoff`: the local energy estimate
  that turns PJ.1e plus PJ.2b into finite propagation speed.

## Conventions

* Fourier normalization is Mathlib's, exactly as frozen in L0: `𝓕 f w = ∫ e^{-2πi⟪x,w⟫} f x`
  (`Mathlib/Analysis/Fourier/FourierTransform.lean`), so reconstruction uses the opposite
  sign `𝐞(⟪k, x⟫)`. The kernel sign/`2π` convention is tracked against
  `Spacetime.Minkowski.fourierMinkowski_apply_eq_integral`
  (`𝓕η f p = ∫ a, 𝐞 (-η(a,p)) • f a`): both transforms are built from Mathlib's additive
  character `𝐞 = Real.fourierChar`, and the propagator kernel is the *inverse* character
  applied to the Euclidean pairing, which is what makes the inversion step of PJ.1f hold.
  Each spatial derivative therefore contributes `+2πi⟪k, ·⟫`, and the Laplacian contributes
  `-4π²‖k‖²`, matching the `4π²` of `dispersion`.
* The spatial derivative of a `ℂ`-valued field is its Fréchet derivative, an element of
  `M3 →L[ℝ] ℂ`. For real-valued data the Riesz identification
  `norm_gradient_eq_norm_fderiv` of L0 turns it into Mathlib's `gradient`.
* The Laplacian is Mathlib's `Laplacian.laplacian` on `M3 → ℂ`
  (`InnerProductSpace.instLaplacian`), i.e. the second Fréchet derivative traced against the
  canonical covariant tensor; `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`
  turns it into the sum of second derivatives along an orthonormal basis.
* Cauchy datum `phi` is complex Schwartz; real-valued data embed into this lane by the
  inclusion `ℝ ↪ ℂ`.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis,
  Self-Adjointness*, Academic Press (1975): §IX.1 — the Fourier transform convention whose
  `2π`-free exponent this file converts to Mathlib's normalization (see the Conventions
  section of `Atlas.Proofs.KleinGordon`); §X.7 — the free quantum field of mass `m`, whose
  one-particle energy `μ(p) = Ω` multiplies the positive-frequency part of the propagator
  constructed here; §X.13, p. 295 — the operator `B` with `B² = -Δ + m²` and `B ≥ mI`, whose
  symbol identity is the content of PJ.1e. The section-level citations were checked against
  the table of contents, and no numbered display of those sections is asserted here.
* Recovered P2.6c design contract (`local://p26c-l1-l2-contract.md`, 2026-08-07) — the
  PJ.1a–PJ.1g decomposition, the naming, and the Mathlib API pointers consumed below:
  `SchwartzMap.integrable_pow_mul`, `hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
  `hasFDerivAt_integral_of_dominated_of_fderiv_le`, `MeasureTheory.continuous_of_dominated`.
  The PJ.1d/PJ.1e layer adds `ContinuousLinearMap.integral_apply`,
  `iteratedFDeriv_two_apply`, `OrthonormalBasis.sum_sq_inner_left` and
  `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`.
-/

open MeasureTheory Real
open scoped FourierTransform Laplacian SchwartzMap

namespace QFT.KleinGordon

/-! ### The inverse Fourier character -/

/-- The inverse Fourier character attached to the space-time point `x`, evaluated at
momentum `k`: `exp(2πi⟪k,x⟫)`, i.e. Mathlib's `Real.fourierChar` applied to the Euclidean
pairing. Packaging the coercion once keeps every downstream coercion site canonical. -/
noncomputable def pjChar (x : M3) (k : M3) : ℂ := (Real.fourierChar (inner ℝ k x) : ℂ)

theorem pjChar_eq_exp (x k : M3) :
    pjChar x k = Complex.exp ((2 * π * inner ℝ k x) * Complex.I) := by
  simp [pjChar, Real.fourierChar_apply]

@[simp]
theorem norm_pjChar (x k : M3) : ‖pjChar x k‖ = 1 :=
  Circle.norm_coe _

private theorem continuous_pjChar_momentum (x : M3) :
    Continuous fun k : M3 => pjChar x k := by
  have heq : (fun k : M3 => pjChar x k)
      = fun k : M3 => Complex.exp ((2 * π * inner ℝ k x) * Complex.I) :=
    funext fun k => pjChar_eq_exp x k
  rw [heq]
  fun_prop

private theorem continuous_pjChar_spacetime (k : M3) :
    Continuous fun q : ℝ × M3 => pjChar q.2 k := by
  have heq : (fun q : ℝ × M3 => pjChar q.2 k)
      = fun q : ℝ × M3 => Complex.exp ((2 * π * inner ℝ k q.2) * Complex.I) :=
    funext fun q => pjChar_eq_exp q.2 k
  rw [heq]
  fun_prop

/-! ### The momentum covectors and the spatial derivative of the character -/

/-- The **momentum covector** `2πi⟪k, ·⟫ : M3 →L[ℝ] ℂ`. It is the derivative factor that
each spatial differentiation of the propagator kernel produces, and its operator norm is
exactly `2π‖k‖`, which is what makes every spatial derivative cost one power of `‖k‖`. -/
noncomputable def pjMomCLM (k : M3) : M3 →L[ℝ] ℂ :=
  (innerSL ℝ k).smulRight (2 * π * Complex.I)

@[simp]
theorem pjMomCLM_apply (k v : M3) :
    pjMomCLM k v = 2 * π * Complex.I * (inner ℝ k v : ℝ) := by
  simp only [pjMomCLM, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    Complex.real_smul]
  ring

@[simp]
theorem norm_pjMomCLM (k : M3) : ‖pjMomCLM k‖ = 2 * π * ‖k‖ := by
  rw [pjMomCLM, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  have hI : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by simp [abs_of_pos Real.pi_pos]
  rw [hI]
  ring

private theorem norm_pjMomCLM_apply_le (k w : M3) :
    ‖pjMomCLM k w‖ ≤ 2 * π * ‖k‖ * ‖w‖ := by
  have h := (pjMomCLM k).le_opNorm w
  rwa [norm_pjMomCLM] at h

theorem continuous_pjMomCLM : Continuous fun k : M3 => pjMomCLM k := by
  have heq : (fun k : M3 => pjMomCLM k)
      = fun k : M3 =>
        ContinuousLinearMap.apply ℝ (M3 →L[ℝ] ℂ) (2 * π * Complex.I)
          (ContinuousLinearMap.smulRightL ℝ M3 ℂ (innerSL ℝ k)) := rfl
  rw [heq]
  exact (ContinuousLinearMap.apply ℝ (M3 →L[ℝ] ℂ) (2 * π * Complex.I)).continuous.comp
    ((ContinuousLinearMap.smulRightL ℝ M3 ℂ).continuous.comp (innerSL ℝ).continuous)

/-- The **second-order momentum covector** carrying an amplitude `z`: the continuous
bilinear map `(v, w) ↦ z · (2πi⟪k,v⟫)(2πi⟪k,w⟫)`. The amplitude sits inside because the
target `M3 →L[ℝ] M3 →L[ℝ] ℂ` has no usable `ℂ`-scalar action in Mathlib's instance graph. -/
noncomputable def pjMom2CLM (k : M3) (z : ℂ) : M3 →L[ℝ] (M3 →L[ℝ] ℂ) :=
  (innerSL ℝ k).smulRight ((z * (2 * π * Complex.I)) • pjMomCLM k)

@[simp]
theorem pjMom2CLM_apply (k : M3) (z : ℂ) (v w : M3) :
    pjMom2CLM k z v w
      = z * (2 * π * Complex.I) ^ 2 * (inner ℝ k v : ℝ) * (inner ℝ k w : ℝ) := by
  simp only [pjMom2CLM, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_apply, pjMomCLM_apply, Complex.real_smul, smul_eq_mul]
  ring

theorem norm_pjMom2CLM_le (k : M3) (z : ℂ) :
    ‖pjMom2CLM k z‖ ≤ 4 * π ^ 2 * (‖k‖ ^ 2 * ‖z‖) := by
  have hI : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by simp [abs_of_pos Real.pi_pos]
  have hinner : ‖(z * (2 * π * Complex.I)) • pjMomCLM k‖ ≤ ‖z‖ * (2 * π) * (2 * π * ‖k‖) := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [norm_pjMomCLM, norm_mul, hI]
  rw [pjMom2CLM, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  calc ‖k‖ * ‖(z * (2 * π * Complex.I)) • pjMomCLM k‖
      ≤ ‖k‖ * (‖z‖ * (2 * π) * (2 * π * ‖k‖)) :=
        mul_le_mul_of_nonneg_left hinner (norm_nonneg k)
    _ = 4 * π ^ 2 * (‖k‖ ^ 2 * ‖z‖) := by ring

theorem continuous_pjMom2CLM {c : M3 → ℂ} (hc : Continuous c) :
    Continuous fun k : M3 => pjMom2CLM k (c k) := by
  have heq : (fun k : M3 => pjMom2CLM k (c k))
      = fun k : M3 =>
        (ContinuousLinearMap.smulRightL ℝ M3 (M3 →L[ℝ] ℂ) (innerSL ℝ k))
          ((c k * (2 * π * Complex.I)) • pjMomCLM k) := rfl
  rw [heq]
  exact Continuous.clm_apply
    ((ContinuousLinearMap.smulRightL ℝ M3 (M3 →L[ℝ] ℂ)).continuous.comp (innerSL ℝ).continuous)
    ((hc.mul continuous_const).smul continuous_pjMomCLM)

private theorem continuous_pjMom2CLM_symbol (k : M3) :
    Continuous fun z : ℂ => pjMom2CLM k z := by
  have heq : (fun z : ℂ => pjMom2CLM k z)
      = fun z : ℂ =>
        (ContinuousLinearMap.smulRightL ℝ M3 (M3 →L[ℝ] ℂ) (innerSL ℝ k))
          ((z * (2 * π * Complex.I)) • pjMomCLM k) := rfl
  rw [heq]
  exact (ContinuousLinearMap.smulRightL ℝ M3 (M3 →L[ℝ] ℂ) (innerSL ℝ k)).continuous.comp
    ((continuous_id.mul continuous_const).smul continuous_const)

/-- **PJ.1c** — the spatial Fréchet derivative of the propagator character:
`∂ₓ 𝐞(⟪k,x⟫) = 𝐞(⟪k,x⟫) · 2πi⟪k, ·⟫`. This is the only analytic input the whole spatial
layer needs; everything else is domination. -/
theorem hasFDerivAt_pjChar (k x : M3) :
    HasFDerivAt (fun y : M3 => pjChar y k) (pjChar x k • pjMomCLM k) x := by
  have heq : (fun y : M3 => pjChar y k)
      = fun y : M3 => Complex.exp ((2 * π * inner ℝ k y) * Complex.I) :=
    funext fun y => pjChar_eq_exp y k
  have hfun : (fun y : M3 => (2 * π * inner ℝ k y : ℂ) * Complex.I)
      = fun y : M3 => pjMomCLM k y := by
    funext y
    rw [pjMomCLM_apply]
    ring
  have hlin : HasFDerivAt (fun y : M3 => (2 * π * inner ℝ k y : ℂ) * Complex.I)
      (pjMomCLM k) x := by
    rw [hfun]
    exact (pjMomCLM k).hasFDerivAt
  rw [heq]
  exact hlin.cexp.congr_fderiv (by rw [← pjChar_eq_exp])

/-- The amplitude-weighted form of `hasFDerivAt_pjChar`, in the shape the parametric
integral consumes. -/
theorem hasFDerivAt_pjChar_const_mul (c : ℂ) (k x : M3) :
    HasFDerivAt (fun y : M3 => c * pjChar y k) ((c * pjChar x k) • pjMomCLM k) x :=
  ((hasFDerivAt_pjChar k x).const_mul c).congr_fderiv (smul_smul c (pjChar x k) _)

/-! ### PJ.1a — the propagator integral and its symmetry -/

/-- The **Pauli–Jordan phase** `sin(t Ω(k)) / Ω(k)` of momentum `k` at time `t`. The mass
gap (`dispersion_pos`) makes this bounded by `1/m` for `0 < m`, which is the analytic heart
of PJ.1b. -/
noncomputable def pjPhase (m : ℝ) (t : ℝ) (k : M3) : ℝ :=
  Real.sin (t * dispersion m k) / dispersion m k

/-- **PJ.1a** — the Pauli–Jordan propagator of the free Klein–Gordon equation of mass `m`
with Schwartz initial velocity `phi`, evaluated at time `t` and position `x`:

`u phi t x = ∫ k, (sin(t Ω(k)) / Ω(k)) · 𝓕(phi)(k) · 𝐞(⟪k, x⟫)`,

where `Ω = dispersion` (Reed & Simon II, §X.7, at section level: this is the momentum-space
shape of the free evolution operator `sin(tB)/B`). -/
noncomputable def kgPropagator (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) : ℂ :=
  ∫ k : M3,
    (Complex.ofReal (pjPhase m t k) * (𝓕 phi) k) * pjChar x k

/-- The propagator as the raw momentum integral; a syntactic handle so that downstream
rewrites never have to unfold the definition. -/
theorem kgPropagator_apply (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    kgPropagator m phi t x =
      ∫ k : M3,
        (Complex.ofReal (pjPhase m t k) * (𝓕 phi) k) * pjChar x k := rfl

/-- **PJ.1d** — the time-derivative field `∂ₜu`, the cosine-kernel integral
`cos(t Ω(k)) · 𝓕(phi)(k) · 𝐞(⟪k, x⟫)`, defined so that `hasDerivAt_kgPropagator` reads
`∂ₜu = this` pointwise. -/
noncomputable def kgPropagator_dt (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) : ℂ :=
  ∫ k : M3,
    (Complex.ofReal (Real.cos (t * dispersion m k)) * (𝓕 phi) k) * pjChar x k

/-- The time-derivative kernel as the raw momentum integral; see `kgPropagator_apply`. -/
theorem kgPropagator_dt_apply (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    kgPropagator_dt m phi t x =
      ∫ k : M3,
        (Complex.ofReal (Real.cos (t * dispersion m k)) * (𝓕 phi) k) * pjChar x k := rfl

/-- At time zero the propagator vanishes: `sin 0 = 0` kills the integrand pointwise. -/
@[simp]
theorem kgPropagator_zero_time (m : ℝ) (phi : 𝓢(M3, ℂ)) (x : M3) :
    kgPropagator m phi 0 x = 0 := by
  have heq : (fun k : M3 =>
      (Complex.ofReal (pjPhase m 0 k) * (𝓕 phi) k) * pjChar x k)
        = fun _ => (0 : ℂ) := by
    funext k
    simp [pjPhase]
  rw [kgPropagator_apply, heq, integral_zero]

/-- **PJ.1g** — the propagator is odd in time: `u phi (-t) x = -u phi t x`,
because `sin` is odd and the rest of the kernel does not see the sign of `t`. -/
theorem kgPropagator_neg_time (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    kgPropagator m phi (-t) x = -kgPropagator m phi t x := by
  have hphase : ∀ k : M3, pjPhase m (-t) k = -(pjPhase m t k) := by
    intro k
    unfold pjPhase
    rw [neg_mul, Real.sin_neg, neg_div]
  have hint : ∀ k : M3,
      (Complex.ofReal (pjPhase m (-t) k) * (𝓕 phi) k) * pjChar x k
        = -((Complex.ofReal (pjPhase m t k) * (𝓕 phi) k) * pjChar x k) := by
    intro k
    rw [hphase k, Complex.ofReal_neg, neg_mul, neg_mul]
  have heq : (fun k : M3 =>
      (Complex.ofReal (pjPhase m (-t) k) * (𝓕 phi) k) * pjChar x k)
      = fun k : M3 => -((Complex.ofReal (pjPhase m t k) * (𝓕 phi) k) * pjChar x k) :=
    funext hint
  rw [kgPropagator_apply, kgPropagator_apply, heq, integral_neg]

/-! ### PJ.1b — domination and absolute integrability -/

/-- The mass-gap bound for an arbitrary momentum profile dominating `m`:
`|sin(t ω(k)) / ω(k)| ≤ 1/m`. This is the pointwise estimate behind every dominated
convergence argument below. -/
private theorem abs_sin_div_le (m : ℝ) (hm : 0 < m) {ω : M3 → ℝ}
    (hωge : ∀ k : M3, m ≤ ω k) (r : ℝ) (k : M3) :
    |Real.sin (r * ω k) / ω k| ≤ 1 / m := by
  obtain hω := hm.trans_le (hωge k)
  rw [abs_div, abs_of_pos hω, div_le_iff₀ hω]
  refine (Real.abs_sin_le_one _).trans ?_
  calc (1 : ℝ) ≤ ω k / m := by
        rw [le_div_iff₀ hm]
        linarith [hωge k]
    _ = 1 / m * ω k := by field_simp

/-- The mass-gap bound `|sin(t Ω(k))| / Ω(k) ≤ 1/m` for `0 < m`: `|sin| ≤ 1` and `Ω ≥ m`.
This single pointwise estimate dominates every propagator integral below. -/
theorem abs_pjPhase_le (m : ℝ) (hm : 0 < m) (t : ℝ) (k : M3) :
    |pjPhase m t k| ≤ 1 / m := by
  unfold pjPhase
  exact abs_sin_div_le m hm (fun i => le_dispersion m i hm.le) t k

/-- Norm of a complexified real number against an arbitrary real ceiling; packaging keeps
every kernel-norm estimate below free of coercion friction. -/
private theorem norm_ofReal_le {r C : ℝ} (h : |r| ≤ C) : ‖Complex.ofReal r‖ ≤ C := by
  simpa using h

/-- **PJ.1b (reusable dominator)** — every polynomial moment of `‖𝓕 phi‖` is integrable:
`∫ ‖k‖ⁿ ‖𝓕(phi)(k)| dk < ∞`. Proved by `SchwartzMap.integrable_pow_mul` applied to the
Schwartz map `𝓕 phi`; this is the one dominator from which all kernel integrability and all
dominated-convergence arguments of this file follow. -/
theorem integrable_norm_fourier_mul (phi : 𝓢(M3, ℂ)) (n : ℕ) :
    Integrable (fun k : M3 => ‖k‖ ^ n * ‖(𝓕 phi) k‖) volume :=
  SchwartzMap.integrable_pow_mul volume (𝓕 phi) n

/-- **PJ.1b** — in particular `𝓕 phi` is absolutely integrable. -/
theorem integrable_norm_fourier (phi : 𝓢(M3, ℂ)) :
    Integrable (fun k : M3 => ‖(𝓕 phi) k‖) volume := by
  simpa using integrable_norm_fourier_mul phi 0

/-- **PJ.1b** — the first moment, in the spelling the spatial derivative consumes: each
spatial differentiation costs one factor `2π‖k‖`. -/
theorem integrable_norm_mul_norm_fourier (phi : 𝓢(M3, ℂ)) :
    Integrable (fun k : M3 => ‖k‖ * ‖(𝓕 phi) k‖) volume := by
  simpa using integrable_norm_fourier_mul phi 1

/-- **PJ.1b** — the energy-weighted dominator `∫ Ω(k) ‖𝓕(phi)(k)‖ dk < ∞`, from the linear
bound `Ω ≤ 2π‖k‖ + m` of L0. This is the estimate that lets the *second* time derivative
pass under the integral. -/
theorem integrable_dispersion_norm_fourier (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) :
    Integrable (fun k : M3 => dispersion m k * ‖(𝓕 phi) k‖) volume := by
  have hsplit : Integrable
      (fun k : M3 => 2 * π * (‖k‖ * ‖(𝓕 phi) k‖) + m * ‖(𝓕 phi) k‖) volume :=
    ((integrable_norm_mul_norm_fourier phi).const_mul (2 * π)).add
      ((integrable_norm_fourier phi).const_mul m)
  refine Integrable.mono' hsplit
    (((continuous_dispersion m).mul
      (continuous_norm.comp (𝓕 phi).continuous)).aestronglyMeasurable)
    (ae_of_all volume fun k => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (dispersion_nonneg m k) (norm_nonneg _))]
  exact le_trans (mul_le_mul_of_nonneg_right (dispersion_le m k hm.le) (norm_nonneg _))
    (le_of_eq (by ring))

/-- Continuity of the complexified phase `sin(c ω(k)) / ω(k)` in the momentum variable. -/
private theorem continuous_phase_momentum {ω : M3 → ℝ}
    (hωc : Continuous ω) (hωne : ∀ k : M3, ω k ≠ 0) (c : ℝ) :
    Continuous fun k : M3 => Complex.ofReal (Real.sin (c * ω k) / ω k) :=
  Complex.continuous_ofReal.comp
    ((Real.continuous_sin.comp (continuous_const.mul hωc)).div hωc hωne)

/-- Continuity of the complexified cosine `cos(c ω(k))` in the momentum variable. -/
private theorem continuous_cos_momentum {ω : M3 → ℝ}
    (hωc : Continuous ω) (c : ℝ) :
    Continuous fun k : M3 => Complex.ofReal (Real.cos (c * ω k)) :=
  Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_const.mul hωc))

/-- Continuity of the complexified phase `sin(t ω(k)) / ω(k)` in the time variable. -/
private theorem continuous_phase_time {ω : M3 → ℝ}
    (hωne : ∀ k : M3, ω k ≠ 0) (k : M3) :
    Continuous fun s : ℝ => Complex.ofReal (Real.sin (s * ω k) / ω k) :=
  Complex.continuous_ofReal.comp
    ((Real.continuous_sin.comp (continuous_id.mul continuous_const)).div
      continuous_const (fun _ => hωne k))

/-- Pointwise domination of the propagator kernel: its modulus is at most
`(1/m)·‖𝓕(phi)(k)‖`, the product of the phase bound and the character having unit modulus. -/
theorem norm_kgPropagator_integrand_le (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (t : ℝ)
    (x : M3) (k : M3) :
    ‖(Complex.ofReal (pjPhase m t k) * (𝓕 phi) k) * pjChar x k‖
      ≤ 1 / m * ‖(𝓕 phi) k‖ := by
  have hph : ‖Complex.ofReal (pjPhase m t k)‖ ≤ 1 / m :=
    norm_ofReal_le (abs_pjPhase_le m hm t k)
  simp only [norm_mul, norm_pjChar, mul_one]
  exact mul_le_mul_of_nonneg_right hph (norm_nonneg ((𝓕 phi) k))

/-- Pointwise domination of the time-derivative kernel: `|cos| ≤ 1`, so its modulus is at
most `‖𝓕(phi)(k)‖`. -/
theorem norm_kgPropagator_dt_integrand_le (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3)
    (k : M3) :
    ‖(Complex.ofReal (Real.cos (t * dispersion m k)) * (𝓕 phi) k) * pjChar x k‖
      ≤ ‖(𝓕 phi) k‖ := by
  have hco : ‖Complex.ofReal (Real.cos (t * dispersion m k))‖ ≤ 1 :=
    norm_ofReal_le (Real.abs_cos_le_one _)
  have h := mul_le_mul_of_nonneg_right hco (norm_nonneg ((𝓕 phi) k))
  simpa using h

/-- **PJ.1b** — absolute integrability of the propagator kernel over momentum space:
`∫ |sin(tΩ)|/Ω · ‖𝓕(phi)| dk < ∞` for `0 < m`. -/
theorem integrable_kgPropagator_integrand (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (t : ℝ)
    (x : M3) :
    Integrable (fun k : M3 =>
      (Complex.ofReal (pjPhase m t k) * (𝓕 phi) k) * pjChar x k) volume := by
  have hωc : Continuous (dispersion m) := continuous_dispersion m
  have hωne : ∀ k : M3, dispersion m k ≠ 0 :=
    fun k => ne_of_gt (dispersion_pos m k hm.ne')
  refine Integrable.mono' ((integrable_norm_fourier phi).const_mul (1 / m))
    ((((continuous_phase_momentum hωc hωne t).mul (𝓕 phi).continuous).mul
        (continuous_pjChar_momentum x)).aestronglyMeasurable)
    (ae_of_all volume fun k => norm_kgPropagator_integrand_le m hm phi t x k)

/-- **PJ.1b** — absolute integrability of the time-derivative kernel. -/
theorem integrable_kgPropagator_dt_integrand (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    Integrable (fun k : M3 =>
      (Complex.ofReal (Real.cos (t * dispersion m k)) * (𝓕 phi) k) * pjChar x k)
      volume := by
  refine Integrable.mono' (integrable_norm_fourier phi)
    (((Complex.continuous_ofReal.comp (Real.continuous_cos.comp
          (continuous_const.mul (continuous_dispersion m)))).mul
        (𝓕 phi).continuous).mul (continuous_pjChar_momentum x) |>.aestronglyMeasurable)
    (ae_of_all volume fun k => norm_kgPropagator_dt_integrand_le m phi t x k)

/-! #### PJ.1b — the two propagator amplitudes and their moments -/

/-- Every polynomial moment of an amplitude dominated by a multiple of `‖𝓕 phi‖` is
integrable. Both propagator amplitudes below are of that shape, so this single lemma feeds
every domination hypothesis of the spatial layer. -/
private theorem integrable_moment_amp {a : M3 → ℂ} (hac : Continuous a) (phi : 𝓢(M3, ℂ))
    {C : ℝ} (hle : ∀ k : M3, ‖a k‖ ≤ C * ‖(𝓕 phi) k‖) (n : ℕ) :
    Integrable (fun k : M3 => ‖k‖ ^ n * ‖a k‖) volume := by
  refine Integrable.mono' ((integrable_norm_fourier_mul phi n).const_mul C)
    (((continuous_norm.pow n).mul (continuous_norm.comp hac)).aestronglyMeasurable)
    (ae_of_all volume fun k => ?_)
  have hkn : (0 : ℝ) ≤ ‖k‖ ^ n := by positivity
  rw [Real.norm_of_nonneg (mul_nonneg hkn (norm_nonneg (a k)))]
  exact le_trans (mul_le_mul_of_nonneg_left (hle k) hkn) (le_of_eq (by ring))

private theorem norm_ampSin_le (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (t : ℝ) (k : M3) :
    ‖Complex.ofReal (pjPhase m t k) * (𝓕 phi) k‖ ≤ 1 / m * ‖(𝓕 phi) k‖ := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_ofReal_le (abs_pjPhase_le m hm t k)) (norm_nonneg _)

private theorem norm_ampCos_le (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (k : M3) :
    ‖Complex.ofReal (Real.cos (t * dispersion m k)) * (𝓕 phi) k‖ ≤ ‖(𝓕 phi) k‖ := by
  rw [norm_mul]
  refine (mul_le_mul_of_nonneg_right (norm_ofReal_le (Real.abs_cos_le_one _))
    (norm_nonneg _)).trans ?_
  rw [one_mul]

private theorem norm_ampCos_le' (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (k : M3) :
    ‖Complex.ofReal (Real.cos (t * dispersion m k)) * (𝓕 phi) k‖ ≤ 1 * ‖(𝓕 phi) k‖ :=
  (norm_ampCos_le m phi t k).trans (le_of_eq (one_mul _).symm)

private theorem norm_ampDt2_le (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (k : M3) :
    ‖Complex.ofReal (-(dispersion m k * Real.sin (t * dispersion m k))) * (𝓕 phi) k‖
      ≤ dispersion m k * ‖(𝓕 phi) k‖ := by
  have habs : |-(dispersion m k * Real.sin (t * dispersion m k))| ≤ dispersion m k := by
    rw [abs_neg, abs_mul, abs_of_nonneg (dispersion_nonneg m k)]
    calc dispersion m k * |Real.sin (t * dispersion m k)| ≤ dispersion m k * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (dispersion_nonneg m k)
      _ = dispersion m k := mul_one _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_ofReal_le habs) (norm_nonneg _)

private theorem continuous_ampSin (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (t : ℝ) :
    Continuous fun k : M3 => Complex.ofReal (pjPhase m t k) * (𝓕 phi) k :=
  (continuous_phase_momentum (continuous_dispersion m)
    (fun k => ne_of_gt (dispersion_pos m k hm.ne')) t).mul (𝓕 phi).continuous

private theorem continuous_ampCos (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) :
    Continuous fun k : M3 => Complex.ofReal (Real.cos (t * dispersion m k)) * (𝓕 phi) k :=
  (continuous_cos_momentum (continuous_dispersion m) t).mul (𝓕 phi).continuous

private theorem continuous_ampSin_prod (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) :
    Continuous fun p : (ℝ × M3) × M3 =>
      Complex.ofReal (pjPhase m p.1.1 p.2) * (𝓕 phi) p.2 := by
  have hωc : Continuous fun p : (ℝ × M3) × M3 => dispersion m p.2 :=
    (continuous_dispersion m).comp continuous_snd
  exact (Complex.continuous_ofReal.comp
    ((Real.continuous_sin.comp (continuous_fst.fst'.mul hωc)).div hωc
      (fun p => ne_of_gt (dispersion_pos m p.2 hm.ne')))).mul
    ((𝓕 phi).continuous.comp continuous_snd)

private theorem continuous_ampCos_prod (m : ℝ) (phi : 𝓢(M3, ℂ)) :
    Continuous fun p : (ℝ × M3) × M3 =>
      Complex.ofReal (Real.cos (p.1.1 * dispersion m p.2)) * (𝓕 phi) p.2 :=
  (Complex.continuous_ofReal.comp
    (Real.continuous_cos.comp
      (continuous_fst.fst'.mul ((continuous_dispersion m).comp continuous_snd)))).mul
    ((𝓕 phi).continuous.comp continuous_snd)

private theorem continuous_ampDt2_prod (m : ℝ) (phi : 𝓢(M3, ℂ)) :
    Continuous fun p : (ℝ × M3) × M3 =>
      Complex.ofReal (-(dispersion m p.2 * Real.sin (p.1.1 * dispersion m p.2)))
        * (𝓕 phi) p.2 := by
  have hωc : Continuous fun p : (ℝ × M3) × M3 => dispersion m p.2 :=
    (continuous_dispersion m).comp continuous_snd
  exact (Complex.continuous_ofReal.comp
    ((hωc.mul (Real.continuous_sin.comp (continuous_fst.fst'.mul hωc))).neg)).mul
    ((𝓕 phi).continuous.comp continuous_snd)

/-! #### PJ.1b — domination of the differentiated kernels -/

private theorem norm_pjDx_le {a : M3 → ℂ} (x k : M3) :
    ‖(a k * pjChar x k) • pjMomCLM k‖ ≤ 2 * π * (‖k‖ * ‖a k‖) := by
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [norm_pjMomCLM, norm_mul, norm_pjChar, mul_one]
  ring_nf
  exact le_refl _

private theorem norm_pjDxx_le {a : M3 → ℂ} (x k : M3) :
    ‖pjMom2CLM k (a k * pjChar x k)‖ ≤ 4 * π ^ 2 * (‖k‖ ^ 2 * ‖a k‖) := by
  refine (norm_pjMom2CLM_le k _).trans ?_
  rw [norm_mul, norm_pjChar, mul_one]

private theorem norm_momAmp_le {a : M3 → ℂ} (w k : M3) :
    ‖a k * pjMomCLM k w‖ ≤ 2 * π * ‖w‖ * ‖k‖ * ‖a k‖ := by
  rw [norm_mul]
  calc ‖a k‖ * ‖pjMomCLM k w‖ ≤ ‖a k‖ * (2 * π * ‖k‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left (norm_pjMomCLM_apply_le k w) (norm_nonneg (a k))
    _ = 2 * π * ‖w‖ * ‖k‖ * ‖a k‖ := by ring

private theorem continuous_momAmp {a : M3 → ℂ} (hac : Continuous a) (w : M3) :
    Continuous fun k : M3 => a k * pjMomCLM k w :=
  hac.mul (Continuous.clm_apply continuous_pjMomCLM continuous_const)

private theorem integrable_norm_momAmp {a : M3 → ℂ} (hac : Continuous a) (w : M3)
    (h : Integrable (fun k : M3 => ‖k‖ * ‖a k‖) volume) :
    Integrable (fun k : M3 => ‖a k * pjMomCLM k w‖) volume := by
  refine Integrable.mono' (h.const_mul (2 * π * ‖w‖))
    ((continuous_norm.comp (continuous_momAmp hac w)).aestronglyMeasurable)
    (ae_of_all volume fun k => ?_)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact (norm_momAmp_le w k).trans (le_of_eq (by ring))

private theorem integrable_norm_mul_momAmp {a : M3 → ℂ} (hac : Continuous a) (w : M3)
    (h : Integrable (fun k : M3 => ‖k‖ ^ 2 * ‖a k‖) volume) :
    Integrable (fun k : M3 => ‖k‖ * ‖a k * pjMomCLM k w‖) volume := by
  refine Integrable.mono' (h.const_mul (2 * π * ‖w‖))
    ((continuous_norm.mul (continuous_norm.comp (continuous_momAmp hac w))).aestronglyMeasurable)
    (ae_of_all volume fun k => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖k‖ * ‖a k * pjMomCLM k w‖ ≤ ‖k‖ * (2 * π * ‖w‖ * ‖k‖ * ‖a k‖) :=
        mul_le_mul_of_nonneg_left (norm_momAmp_le w k) (norm_nonneg k)
    _ = 2 * π * ‖w‖ * (‖k‖ ^ 2 * ‖a k‖) := by ring

private theorem integrable_momAmp_sq {a : M3 → ℂ} (hac : Continuous a) (x w : M3)
    (h : Integrable (fun k : M3 => ‖k‖ ^ 2 * ‖a k‖) volume) :
    Integrable (fun k : M3 => a k * pjMomCLM k w * pjChar x k * pjMomCLM k w) volume := by
  refine Integrable.mono' (h.const_mul (4 * π ^ 2 * ‖w‖ ^ 2))
    ((((continuous_momAmp hac w).mul (continuous_pjChar_momentum x)).mul
      (Continuous.clm_apply continuous_pjMomCLM continuous_const)).aestronglyMeasurable)
    (ae_of_all volume fun k => ?_)
  have hmom := norm_pjMomCLM_apply_le k w
  calc ‖a k * pjMomCLM k w * pjChar x k * pjMomCLM k w‖
      = ‖a k‖ * ‖pjMomCLM k w‖ * ‖pjMomCLM k w‖ := by
        simp only [norm_mul, norm_pjChar, mul_one]
    _ ≤ ‖a k‖ * (2 * π * ‖k‖ * ‖w‖) * (2 * π * ‖k‖ * ‖w‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmom (norm_nonneg (a k))) hmom
          (norm_nonneg _) (by positivity)
    _ = 4 * π ^ 2 * ‖w‖ ^ 2 * (‖k‖ ^ 2 * ‖a k‖) := by ring

private theorem integrable_charIntegrandDx {a : M3 → ℂ} (hac : Continuous a)
    (h1 : Integrable (fun k : M3 => ‖k‖ * ‖a k‖) volume) (y : M3) :
    Integrable (fun k : M3 => (a k * pjChar y k) • pjMomCLM k) volume :=
  Integrable.mono' (h1.const_mul (2 * π))
    (((hac.mul (continuous_pjChar_momentum y)).smul continuous_pjMomCLM).aestronglyMeasurable)
    (ae_of_all volume fun k => norm_pjDx_le y k)

/-! ### PJ.1c — reusable kernel workhorses -/

/-- **PJ.1c (workhorse)** — a jointly continuous symbol family `σ` with a fixed integrable
dominator `B` gives a jointly continuous scalar integral `(t, x) ↦ ∫ σ(t,x,k) 𝐞(⟪k,x⟫)`.
Every continuity statement of this file is an instance; the mass gap is what supplies the
uniform `B`, so no local time window is needed. -/
private theorem continuous_symbolKernel_integral {σ : ℝ × M3 → M3 → ℂ} {B : M3 → ℝ}
    (hσ : Continuous fun p : (ℝ × M3) × M3 => σ p.1 p.2) (hB : Integrable B volume)
    (hbound : ∀ (q : ℝ × M3) (k : M3), ‖σ q k‖ ≤ B k) :
    Continuous fun q : ℝ × M3 => ∫ k : M3, σ q k * pjChar q.2 k := by
  refine MeasureTheory.continuous_of_dominated (bound := B) ?_ ?_ hB ?_
  · exact fun q => ((hσ.comp (continuous_const.prodMk continuous_id)).mul
      (continuous_pjChar_momentum q.2)).aestronglyMeasurable
  · exact fun q => ae_of_all volume fun k => by
      simpa only [norm_mul, norm_pjChar, mul_one] using hbound q k
  · exact ae_of_all volume fun k =>
      (hσ.comp (continuous_id.prodMk continuous_const)).mul (continuous_pjChar_spacetime k)

/-- **PJ.1c (workhorse)** — the same statement one spatial derivative up: the covector-valued
integral is jointly continuous once the dominator absorbs the extra factor `2π‖k‖`. -/
private theorem continuous_symbolKernelDx_integral {σ : ℝ × M3 → M3 → ℂ} {B : M3 → ℝ}
    (hσ : Continuous fun p : (ℝ × M3) × M3 => σ p.1 p.2) (hB : Integrable B volume)
    (hbound : ∀ (q : ℝ × M3) (k : M3), 2 * π * (‖k‖ * ‖σ q k‖) ≤ B k) :
    Continuous fun q : ℝ × M3 => ∫ k : M3, (σ q k * pjChar q.2 k) • pjMomCLM k := by
  refine MeasureTheory.continuous_of_dominated (bound := B) ?_ ?_ hB ?_
  · exact fun q => (((hσ.comp (continuous_const.prodMk continuous_id)).mul
      (continuous_pjChar_momentum q.2)).smul continuous_pjMomCLM).aestronglyMeasurable
  · exact fun q => ae_of_all volume fun k =>
      (norm_pjDx_le (a := fun k => σ q k) q.2 k).trans (hbound q k)
  · exact ae_of_all volume fun k =>
      (((hσ.comp (continuous_id.prodMk continuous_const)).mul
        (continuous_pjChar_spacetime k)).smul continuous_const)

/-- **PJ.1c (workhorse)** — two spatial derivatives up, with the dominator absorbing
`4π²‖k‖²`. -/
private theorem continuous_symbolKernelDxx_integral {σ : ℝ × M3 → M3 → ℂ} {B : M3 → ℝ}
    (hσ : Continuous fun p : (ℝ × M3) × M3 => σ p.1 p.2) (hB : Integrable B volume)
    (hbound : ∀ (q : ℝ × M3) (k : M3), 4 * π ^ 2 * (‖k‖ ^ 2 * ‖σ q k‖) ≤ B k) :
    Continuous fun q : ℝ × M3 => ∫ k : M3, pjMom2CLM k (σ q k * pjChar q.2 k) := by
  refine MeasureTheory.continuous_of_dominated (bound := B) ?_ ?_ hB ?_
  · exact fun q => (continuous_pjMom2CLM
      ((hσ.comp (continuous_const.prodMk continuous_id)).mul
        (continuous_pjChar_momentum q.2))).aestronglyMeasurable
  · exact fun q => ae_of_all volume fun k =>
      (norm_pjDxx_le (a := fun k => σ q k) q.2 k).trans (hbound q k)
  · exact ae_of_all volume fun k =>
      (continuous_pjMom2CLM_symbol k).comp
        ((hσ.comp (continuous_id.prodMk continuous_const)).mul
          (continuous_pjChar_spacetime k))

/-- **PJ.1c (workhorse)** — the sine instance of `continuous_symbolKernel_integral`: for a
continuous momentum profile `ω ≥ m > 0` and a continuous absolutely-integrable amplitude
`g`, the sine-kernel integral is jointly continuous in `(t, x)`. -/
private theorem continuous_sinKernel_integral (m : ℝ) (hm : 0 < m)
    {ω : M3 → ℝ} (hωc : Continuous ω) (hωge : ∀ k : M3, m ≤ ω k)
    {g : M3 → ℂ} (hgc : Continuous g)
    (hgint : Integrable (fun k : M3 => ‖g k‖) volume) :
    Continuous fun q : ℝ × M3 =>
      ∫ k : M3,
        (Complex.ofReal (Real.sin (q.1 * ω k) / ω k) * g k) * pjChar q.2 k := by
  have hωne : ∀ k : M3, ω k ≠ 0 := fun k => ne_of_gt (hm.trans_le (hωge k))
  have hωp : Continuous fun p : (ℝ × M3) × M3 => ω p.2 := hωc.comp continuous_snd
  refine continuous_symbolKernel_integral
    ((Complex.continuous_ofReal.comp
      ((Real.continuous_sin.comp (continuous_fst.fst'.mul hωp)).div hωp
        (fun p => hωne p.2))).mul (hgc.comp continuous_snd))
    (hgint.const_mul (1 / m)) (fun q k => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_ofReal_le (abs_sin_div_le m hm hωge q.1 k))
    (norm_nonneg (g k))

/-- **PJ.1c (workhorse)** — differentiation under the integral in time: the sine-kernel
integral is everywhere differentiable in `t`, with derivative exactly the cosine-kernel
integral. The globally integrable bound `‖g‖` controls the difference quotients uniformly
in `t`. -/
private theorem hasDerivAt_sinKernel_integral (m : ℝ) (hm : 0 < m)
    {ω : M3 → ℝ} (hωc : Continuous ω) (hωge : ∀ k : M3, m ≤ ω k)
    {g : M3 → ℂ} (hgc : Continuous g)
    (hgint : Integrable (fun k : M3 => ‖g k‖) volume)
    (x : M3) (t₀ : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ k : M3, (Complex.ofReal (Real.sin (s * ω k) / ω k) * g k) * pjChar x k)
      (∫ k : M3,
        (Complex.ofReal (Real.cos (t₀ * ω k)) * g k) * pjChar x k) t₀ := by
  have hωne : ∀ k : M3, ω k ≠ 0 := fun k => ne_of_gt (hm.trans_le (hωge k))
  have hdiff : ∀ (r : ℝ) (k : M3),
      HasDerivAt
        (fun s : ℝ => (Complex.ofReal (Real.sin (s * ω k) / ω k) * g k) * pjChar x k)
        ((Complex.ofReal (Real.cos (r * ω k)) * g k) * pjChar x k) r := by
    intro r k
    have h1 : HasDerivAt (fun s : ℝ => Real.sin (s * ω k))
        (Real.cos (r * ω k) * ω k) r := by
      simpa using ((hasDerivAt_id r).mul_const (ω k)).sin
    have h2 := h1.div_const (ω k)
    have hc : Real.cos (r * ω k) * ω k / ω k = Real.cos (r * ω k) := by
      rw [mul_div_assoc, div_self (hωne k), mul_one]
    rw [hc] at h2
    exact (h2.ofReal_comp.mul_const (g k)).mul_const (pjChar x k)
  obtain ⟨_, hd⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := t₀) (s := Set.univ)
      (F := fun (r : ℝ) (k : M3) =>
          (Complex.ofReal (Real.sin (r * ω k) / ω k) * g k) * pjChar x k)
      (F' := fun (r : ℝ) (k : M3) =>
          (Complex.ofReal (Real.cos (r * ω k)) * g k) * pjChar x k)
      (bound := fun k : M3 => ‖g k‖) (μ := volume) Filter.univ_mem
      (Filter.Eventually.of_forall fun r =>
        (((continuous_phase_momentum hωc hωne r).mul hgc).mul
          (continuous_pjChar_momentum x)).aestronglyMeasurable)
      (Integrable.mono' (hgint.const_mul (1 / m))
        ((((continuous_phase_momentum hωc hωne t₀).mul hgc).mul
            (continuous_pjChar_momentum x)).aestronglyMeasurable)
        (ae_of_all volume fun k => by
          simpa only [norm_mul, norm_pjChar, mul_one] using
            mul_le_mul_of_nonneg_right
              (norm_ofReal_le (abs_sin_div_le m hm hωge t₀ k)) (norm_nonneg (g k))))
      (((continuous_cos_momentum hωc t₀).mul hgc).mul
        (continuous_pjChar_momentum x) |>.aestronglyMeasurable)
      (ae_of_all volume fun k r (_ : r ∈ Set.univ) => by
        have h := mul_le_mul_of_nonneg_right
          (norm_ofReal_le (Real.abs_cos_le_one (r * ω k))) (norm_nonneg (g k))
        simpa only [norm_mul, norm_pjChar, mul_one, one_mul] using h)
      hgint
      (ae_of_all volume fun k r (_ : r ∈ Set.univ) => hdiff r k)
  exact hd

/-- **PJ.1c (workhorse)** — differentiation under the integral in time, one step further:
the cosine-kernel integral is differentiable in `t` with derivative the `-ω sin(tω)` kernel.
The dominator is `ω ‖g‖`, which is where the energy-weighted moment of PJ.1b enters. -/
private theorem hasDerivAt_cosKernel_integral {ω : M3 → ℝ} (hωc : Continuous ω)
    (hωnn : ∀ k : M3, 0 ≤ ω k) {g : M3 → ℂ} (hgc : Continuous g)
    (hg0 : Integrable (fun k : M3 => ‖g k‖) volume)
    (hgω : Integrable (fun k : M3 => ω k * ‖g k‖) volume) (x : M3) (t₀ : ℝ) :
    HasDerivAt
      (fun s : ℝ => ∫ k : M3, (Complex.ofReal (Real.cos (s * ω k)) * g k) * pjChar x k)
      (∫ k : M3, (Complex.ofReal (-(ω k * Real.sin (t₀ * ω k))) * g k) * pjChar x k) t₀ := by
  have hcosInt : ∀ r : ℝ, Integrable (fun k : M3 =>
      (Complex.ofReal (Real.cos (r * ω k)) * g k) * pjChar x k) volume := fun r =>
    Integrable.mono' hg0
      ((((continuous_cos_momentum hωc r).mul hgc).mul
        (continuous_pjChar_momentum x)).aestronglyMeasurable)
      (ae_of_all volume fun k => by
        simpa only [norm_mul, norm_pjChar, mul_one, one_mul] using
          mul_le_mul_of_nonneg_right (norm_ofReal_le (Real.abs_cos_le_one (r * ω k)))
            (norm_nonneg (g k)))
  have hdiff : ∀ (r : ℝ) (k : M3),
      HasDerivAt
        (fun s : ℝ => (Complex.ofReal (Real.cos (s * ω k)) * g k) * pjChar x k)
        ((Complex.ofReal (-(ω k * Real.sin (r * ω k))) * g k) * pjChar x k) r := by
    intro r k
    have h0 := ((hasDerivAt_id r).mul_const (ω k)).cos
    rw [show (-Real.sin (id r * ω k) * (1 * ω k)) = -(ω k * Real.sin (r * ω k)) from by
      simp only [id_eq, one_mul]; ring] at h0
    exact (h0.ofReal_comp.mul_const (g k)).mul_const (pjChar x k)
  have hbound : ∀ (r : ℝ) (k : M3),
      ‖(Complex.ofReal (-(ω k * Real.sin (r * ω k))) * g k) * pjChar x k‖
        ≤ ω k * ‖g k‖ := by
    intro r k
    have habs : |-(ω k * Real.sin (r * ω k))| ≤ ω k := by
      rw [abs_neg, abs_mul, abs_of_nonneg (hωnn k)]
      calc ω k * |Real.sin (r * ω k)| ≤ ω k * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (hωnn k)
        _ = ω k := mul_one _
    simp only [norm_mul, norm_pjChar, mul_one]
    exact mul_le_mul_of_nonneg_right (norm_ofReal_le habs) (norm_nonneg _)
  obtain ⟨_, hd⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := t₀) (s := Set.univ)
      (F := fun (r : ℝ) (k : M3) => (Complex.ofReal (Real.cos (r * ω k)) * g k) * pjChar x k)
      (F' := fun (r : ℝ) (k : M3) =>
        (Complex.ofReal (-(ω k * Real.sin (r * ω k))) * g k) * pjChar x k)
      (bound := fun k : M3 => ω k * ‖g k‖) (μ := volume) Filter.univ_mem
      (Filter.Eventually.of_forall fun r => (hcosInt r).aestronglyMeasurable) (hcosInt t₀)
      (((Complex.continuous_ofReal.comp
        ((hωc.mul (Real.continuous_sin.comp (continuous_const.mul hωc))).neg)).mul hgc).mul
          (continuous_pjChar_momentum x)).aestronglyMeasurable
      (ae_of_all volume fun k r (_ : r ∈ Set.univ) => hbound r k) hgω
      (ae_of_all volume fun k r (_ : r ∈ Set.univ) => hdiff r k)
  exact hd

/-- **PJ.1c (workhorse)** — differentiation in time of the *covector*-valued sine kernel,
i.e. the mixed derivative `∂ₜ∂ₓ` taken in that order. The dominator carries one factor
`2π‖k‖`, so the first moment of PJ.1b is what is needed. -/
private theorem hasDerivAt_sinKernelDx_integral (m : ℝ) (hm : 0 < m)
    {ω : M3 → ℝ} (hωc : Continuous ω) (hωge : ∀ k : M3, m ≤ ω k)
    {g : M3 → ℂ} (hgc : Continuous g)
    (hgint : Integrable (fun k : M3 => ‖k‖ * ‖g k‖) volume)
    (x : M3) (t₀ : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ k : M3, ((Complex.ofReal (Real.sin (s * ω k) / ω k) * g k) * pjChar x k) • pjMomCLM k)
      (∫ k : M3,
        ((Complex.ofReal (Real.cos (t₀ * ω k)) * g k) * pjChar x k) • pjMomCLM k) t₀ := by
  have hωne : ∀ k : M3, ω k ≠ 0 := fun k => ne_of_gt (hm.trans_le (hωge k))
  have hdiff : ∀ (r : ℝ) (k : M3),
      HasDerivAt
        (fun s : ℝ =>
          ((Complex.ofReal (Real.sin (s * ω k) / ω k) * g k) * pjChar x k) • pjMomCLM k)
        (((Complex.ofReal (Real.cos (r * ω k)) * g k) * pjChar x k) • pjMomCLM k) r := by
    intro r k
    have h1 : HasDerivAt (fun s : ℝ => Real.sin (s * ω k))
        (Real.cos (r * ω k) * ω k) r := by
      simpa using ((hasDerivAt_id r).mul_const (ω k)).sin
    have h2 := h1.div_const (ω k)
    have hc : Real.cos (r * ω k) * ω k / ω k = Real.cos (r * ω k) := by
      rw [mul_div_assoc, div_self (hωne k), mul_one]
    rw [hc] at h2
    exact ((h2.ofReal_comp.mul_const (g k)).mul_const (pjChar x k)).smul_const (pjMomCLM k)
  have hcosBound : ∀ (r : ℝ) (k : M3),
      ‖((Complex.ofReal (Real.cos (r * ω k)) * g k) * pjChar x k) • pjMomCLM k‖
        ≤ 2 * π * (‖k‖ * ‖g k‖) := by
    intro r k
    refine (norm_pjDx_le (a := fun k => Complex.ofReal (Real.cos (r * ω k)) * g k) x k).trans ?_
    have hamp : ‖Complex.ofReal (Real.cos (r * ω k)) * g k‖ ≤ ‖g k‖ := by
      rw [norm_mul]
      simpa using mul_le_mul_of_nonneg_right
        (norm_ofReal_le (Real.abs_cos_le_one (r * ω k))) (norm_nonneg (g k))
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hamp (norm_nonneg k))
      (by positivity)
  have hsinInt : Integrable (fun k : M3 =>
      ((Complex.ofReal (Real.sin (t₀ * ω k) / ω k) * g k) * pjChar x k) • pjMomCLM k) volume := by
    refine Integrable.mono' (hgint.const_mul (2 * π / m))
      ((((continuous_phase_momentum hωc hωne t₀).mul hgc).mul
        (continuous_pjChar_momentum x)).smul continuous_pjMomCLM).aestronglyMeasurable
      (ae_of_all volume fun k => ?_)
    refine (norm_pjDx_le
      (a := fun k => Complex.ofReal (Real.sin (t₀ * ω k) / ω k) * g k) x k).trans ?_
    have hamp : ‖Complex.ofReal (Real.sin (t₀ * ω k) / ω k) * g k‖ ≤ 1 / m * ‖g k‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_ofReal_le (abs_sin_div_le m hm hωge t₀ k))
        (norm_nonneg _)
    calc 2 * π * (‖k‖ * ‖Complex.ofReal (Real.sin (t₀ * ω k) / ω k) * g k‖)
        ≤ 2 * π * (‖k‖ * (1 / m * ‖g k‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hamp (norm_nonneg k))
            (by positivity)
      _ = 2 * π / m * (‖k‖ * ‖g k‖) := by ring
  obtain ⟨_, hd⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := t₀) (s := Set.univ)
      (F := fun (r : ℝ) (k : M3) =>
          ((Complex.ofReal (Real.sin (r * ω k) / ω k) * g k) * pjChar x k) • pjMomCLM k)
      (F' := fun (r : ℝ) (k : M3) =>
          ((Complex.ofReal (Real.cos (r * ω k)) * g k) * pjChar x k) • pjMomCLM k)
      (bound := fun k : M3 => 2 * π * (‖k‖ * ‖g k‖)) (μ := volume) Filter.univ_mem
      (Filter.Eventually.of_forall fun r =>
        ((((continuous_phase_momentum hωc hωne r).mul hgc).mul
          (continuous_pjChar_momentum x)).smul continuous_pjMomCLM).aestronglyMeasurable)
      hsinInt
      ((((continuous_cos_momentum hωc t₀).mul hgc).mul
        (continuous_pjChar_momentum x)).smul continuous_pjMomCLM).aestronglyMeasurable
      (ae_of_all volume fun k r (_ : r ∈ Set.univ) => hcosBound r k)
      (hgint.const_mul (2 * π))
      (ae_of_all volume fun k r (_ : r ∈ Set.univ) => hdiff r k)
  exact hd

/-- Pointwise spatial derivative of the second-order integrand, in the canonical
`pjMom2CLM` shape. -/
private theorem hasFDerivAt_charAmpDx (a : M3 → ℂ) (k x : M3) :
    HasFDerivAt (fun y : M3 => (a k * pjChar y k) • pjMomCLM k)
      (pjMom2CLM k (a k * pjChar x k)) x := by
  refine ((hasFDerivAt_pjChar_const_mul (a k) k x).smul_const (pjMomCLM k)).congr_fderiv ?_
  ext v w
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, pjMomCLM_apply,
    pjMom2CLM_apply, smul_eq_mul]
  ring

/-- **PJ.1c (workhorse)** — differentiation under the integral in *space*: for a continuous
amplitude with an integrable first moment, `x ↦ ∫ a(k) 𝐞(⟪k,x⟫)` is Fréchet differentiable
with derivative the covector-valued integral against `pjMomCLM`. -/
private theorem hasFDerivAt_charIntegral {a : M3 → ℂ} (hac : Continuous a)
    (h0 : Integrable (fun k : M3 => ‖a k‖) volume)
    (h1 : Integrable (fun k : M3 => ‖k‖ * ‖a k‖) volume) (x : M3) :
    HasFDerivAt (fun y : M3 => ∫ k : M3, a k * pjChar y k)
      (∫ k : M3, (a k * pjChar x k) • pjMomCLM k) x := by
  have hint : ∀ y : M3, Integrable (fun k : M3 => a k * pjChar y k) volume := fun y =>
    Integrable.mono' h0 ((hac.mul (continuous_pjChar_momentum y)).aestronglyMeasurable)
      (ae_of_all volume fun k => by simp)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (x₀ := x) (s := Set.univ)
    (F := fun (y : M3) (k : M3) => a k * pjChar y k)
    (F' := fun (y : M3) (k : M3) => (a k * pjChar y k) • pjMomCLM k)
    (bound := fun k : M3 => 2 * π * (‖k‖ * ‖a k‖)) (μ := volume) Filter.univ_mem
    (Filter.Eventually.of_forall fun y => (hint y).aestronglyMeasurable) (hint x)
    (((hac.mul (continuous_pjChar_momentum x)).smul continuous_pjMomCLM).aestronglyMeasurable)
    (ae_of_all volume fun k y _ => norm_pjDx_le y k) (h1.const_mul (2 * π))
    (ae_of_all volume fun k y _ => hasFDerivAt_pjChar_const_mul (a k) k y)

/-- **PJ.1c (workhorse)** — the second spatial derivative under the integral, with the
second moment of the amplitude as dominator. -/
private theorem hasFDerivAt_charIntegralDx {a : M3 → ℂ} (hac : Continuous a)
    (h1 : Integrable (fun k : M3 => ‖k‖ * ‖a k‖) volume)
    (h2 : Integrable (fun k : M3 => ‖k‖ ^ 2 * ‖a k‖) volume) (x : M3) :
    HasFDerivAt (fun y : M3 => ∫ k : M3, (a k * pjChar y k) • pjMomCLM k)
      (∫ k : M3, pjMom2CLM k (a k * pjChar x k)) x := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (x₀ := x) (s := Set.univ)
    (F := fun (y : M3) (k : M3) => (a k * pjChar y k) • pjMomCLM k)
    (F' := fun (y : M3) (k : M3) => pjMom2CLM k (a k * pjChar y k))
    (bound := fun k : M3 => 4 * π ^ 2 * (‖k‖ ^ 2 * ‖a k‖)) (μ := volume) Filter.univ_mem
    (Filter.Eventually.of_forall fun y =>
      (integrable_charIntegrandDx hac h1 y).aestronglyMeasurable)
    (integrable_charIntegrandDx hac h1 x)
    ((continuous_pjMom2CLM (hac.mul (continuous_pjChar_momentum x))).aestronglyMeasurable)
    (ae_of_all volume fun k y _ => norm_pjDxx_le y k) (h2.const_mul (4 * π ^ 2))
    (ae_of_all volume fun k y _ => hasFDerivAt_charAmpDx a k y)

/-- Evaluating the covector-valued integral in a fixed direction turns it back into a
scalar character integral, with the direction absorbed into the amplitude. -/
private theorem charIntegralDx_eval {a : M3 → ℂ} (hac : Continuous a)
    (h1 : Integrable (fun k : M3 => ‖k‖ * ‖a k‖) volume) (w : M3) :
    (fun y : M3 => (∫ k : M3, (a k * pjChar y k) • pjMomCLM k) w)
      = fun y : M3 => ∫ k : M3, (a k * pjMomCLM k w) * pjChar y k := by
  funext y
  rw [ContinuousLinearMap.integral_apply (integrable_charIntegrandDx hac h1 y) w]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [smul_apply, smul_eq_mul]
  ring

/-- **PJ.1c (workhorse)** — the diagonal value of the second spatial derivative. Uniqueness
of the Fréchet derivative identifies the direction-`w` slice of the second-order integral
with the first-order integral of the `w`-weighted amplitude, which `ContinuousLinearMap`
integral evaluation then reduces to a scalar integral. -/
private theorem charIntegralDx_apply_diag {a : M3 → ℂ} (hac : Continuous a)
    (h1 : Integrable (fun k : M3 => ‖k‖ * ‖a k‖) volume)
    (h2 : Integrable (fun k : M3 => ‖k‖ ^ 2 * ‖a k‖) volume) (x w : M3) :
    (∫ k : M3, pjMom2CLM k (a k * pjChar x k)) w w
      = ∫ k : M3, a k * pjMomCLM k w * pjChar x k * pjMomCLM k w := by
  have hA0 : Integrable (fun k : M3 => ‖a k * pjMomCLM k w‖) volume :=
    integrable_norm_momAmp hac w h1
  have hA1 : Integrable (fun k : M3 => ‖k‖ * ‖a k * pjMomCLM k w‖) volume :=
    integrable_norm_mul_momAmp hac w h2
  have hGw : HasFDerivAt
      (fun y : M3 => (∫ k : M3, (a k * pjChar y k) • pjMomCLM k) w)
      ((ContinuousLinearMap.apply ℝ ℂ w).comp
        (∫ k : M3, pjMom2CLM k (a k * pjChar x k))) x :=
    (ContinuousLinearMap.apply ℝ ℂ w).hasFDerivAt.comp x
      (hasFDerivAt_charIntegralDx hac h1 h2 x)
  have hLw : HasFDerivAt
      (fun y : M3 => (∫ k : M3, (a k * pjChar y k) • pjMomCLM k) w)
      (∫ k : M3, ((a k * pjMomCLM k w) * pjChar x k) • pjMomCLM k) x := by
    rw [charIntegralDx_eval hac h1 w]
    exact hasFDerivAt_charIntegral (continuous_momAmp hac w) hA0 hA1 x
  have hpt := DFunLike.congr_fun (hGw.unique hLw) w
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.apply_apply] at hpt
  rw [hpt, ContinuousLinearMap.integral_apply
    (integrable_charIntegrandDx (continuous_momAmp hac w) hA1 x) w]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [smul_apply, smul_eq_mul]

/-- **PJ.1c (workhorse)** — the Laplacian of a character integral is the character integral
with the symbol `-4π²‖k‖²`. Summing `charIntegralDx_apply_diag` over an orthonormal basis
and using `∑ᵢ ⟪k, eᵢ⟫² = ‖k‖²` collapses the second derivative to that single factor. -/
private theorem laplacian_charIntegral {a : M3 → ℂ} (hac : Continuous a)
    (h0 : Integrable (fun k : M3 => ‖a k‖) volume)
    (h1 : Integrable (fun k : M3 => ‖k‖ * ‖a k‖) volume)
    (h2 : Integrable (fun k : M3 => ‖k‖ ^ 2 * ‖a k‖) volume) (x : M3) :
    Δ (fun y : M3 => ∫ k : M3, a k * pjChar y k) x
      = ∫ k : M3, (Complex.ofReal (-(4 * π ^ 2 * ‖k‖ ^ 2)) * a k) * pjChar x k := by
  classical
  set v := stdOrthonormalBasis ℝ M3 with hvdef
  have hfd2 : fderiv ℝ (fderiv ℝ (fun y : M3 => ∫ k : M3, a k * pjChar y k)) x
      = ∫ k : M3, pjMom2CLM k (a k * pjChar x k) := by
    rw [show fderiv ℝ (fun y : M3 => ∫ k : M3, a k * pjChar y k)
        = fun y : M3 => ∫ k : M3, (a k * pjChar y k) • pjMomCLM k from
      funext fun y => (hasFDerivAt_charIntegral hac h0 h1 y).fderiv]
    exact (hasFDerivAt_charIntegralDx hac h1 h2 x).fderiv
  have hterm : ∀ i, iteratedFDeriv ℝ 2 (fun y : M3 => ∫ k : M3, a k * pjChar y k) x
      ![v i, v i]
      = ∫ k : M3, a k * pjMomCLM k (v i) * pjChar x k * pjMomCLM k (v i) := by
    intro i
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hfd2]
    exact charIntegralDx_apply_diag hac h1 h2 x (v i)
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (fun y : M3 => ∫ k : M3, a k * pjChar y k) v) x,
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
    ← integral_finsetSum Finset.univ (fun i _ => integrable_momAmp_sq hac x (v i) h2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  have hreal : ∑ i, (inner ℝ k (v i) : ℝ) ^ 2 = ‖k‖ ^ 2 := v.sum_sq_inner_left k
  have hsq : ∑ i, ((inner ℝ k (v i) : ℝ) : ℂ) ^ 2 = ((‖k‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hreal]
    push_cast
    ring
  have hstep : ∀ i, a k * pjMomCLM k (v i) * pjChar x k * pjMomCLM k (v i)
      = ((a k * pjChar x k) * (2 * π * Complex.I) ^ 2)
        * ((inner ℝ k (v i) : ℝ) : ℂ) ^ 2 := by
    intro i
    rw [pjMomCLM_apply]
    ring
  have hIsq : ((2 : ℂ) * π * Complex.I) ^ 2 = -(4 * (π : ℂ) ^ 2) := by
    rw [mul_pow, mul_pow, Complex.I_sq]
    ring
  have hsum : ∑ i, a k * pjMomCLM k (v i) * pjChar x k * pjMomCLM k (v i)
      = (Complex.ofReal (-(4 * π ^ 2 * ‖k‖ ^ 2)) * a k) * pjChar x k := by
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep i), ← Finset.mul_sum, hsq,
      hIsq]
    push_cast
    ring
  exact hsum

/-! ### PJ.1c — continuity and time differentiability of the propagator -/

/-- **PJ.1c** — joint pointwise continuity of the propagator field `(t, x) ↦ u phi t x`, by
the sine-kernel workhorse instantiated at `ω = Ω`, `g = 𝓕(phi)` (the global dominator
`(1/m)·‖𝓕 phi‖` of PJ.1b needs no local time window thanks to the mass gap). -/
theorem continuous_kgPropagator (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) :
    Continuous fun q : ℝ × M3 => kgPropagator m phi q.1 q.2 := by
  have heqF : (fun q : ℝ × M3 => kgPropagator m phi q.1 q.2)
      = fun q : ℝ × M3 =>
          ∫ k : M3,
            (Complex.ofReal (pjPhase m q.1 k) * (𝓕 phi) k) * pjChar q.2 k := by
    funext q
    exact kgPropagator_apply m phi q.1 q.2
  rw [heqF]
  exact continuous_sinKernel_integral m hm (continuous_dispersion m)
    (fun k => le_dispersion m k hm.le) (𝓕 phi).continuous
    (integrable_norm_fourier phi)

/-- **PJ.1c** — pointwise continuity of `t ↦ u phi t x`. -/
theorem continuous_kgPropagator_time (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (x : M3) :
    Continuous fun t : ℝ => kgPropagator m phi t x := by
  rw [show (fun t : ℝ => kgPropagator m phi t x)
      = fun t : ℝ => (fun q : ℝ × M3 => kgPropagator m phi q.1 q.2) (t, x) from rfl]
  exact (continuous_kgPropagator m hm phi).comp
    (continuous_id.prodMk continuous_const)

/-- **PJ.1c** — pointwise continuity of `x ↦ u phi t x`. -/
theorem continuous_kgPropagator_space (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (t : ℝ) :
    Continuous fun x : M3 => kgPropagator m phi t x := by
  rw [show (fun x : M3 => kgPropagator m phi t x)
      = fun x : M3 => (fun q : ℝ × M3 => kgPropagator m phi q.1 q.2) (t, x) from rfl]
  exact (continuous_kgPropagator m hm phi).comp
    (continuous_const.prodMk continuous_id)

/-- **PJ.1c** — differentiation under the integral in time: for every `x` the field
`t ↦ u phi t x` is everywhere differentiable, with derivative the cosine-kernel integral
`kgPropagator_dt m phi t x`. -/
theorem hasDerivAt_kgPropagator (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (x : M3) (t₀ : ℝ) :
    HasDerivAt (fun s : ℝ => kgPropagator m phi s x) (kgPropagator_dt m phi t₀ x) t₀ := by
  have heqF : (fun s : ℝ => kgPropagator m phi s x)
      = fun s : ℝ =>
          ∫ k : M3,
            (Complex.ofReal (pjPhase m s k) * (𝓕 phi) k) * pjChar x k := by
    funext s
    exact kgPropagator_apply m phi s x
  rw [heqF]
  refine (hasDerivAt_sinKernel_integral m hm (continuous_dispersion m)
    (fun k => le_dispersion m k hm.le) (𝓕 phi).continuous
    (integrable_norm_fourier phi) x t₀).congr_deriv ?_
  exact (kgPropagator_dt_apply m phi t₀ x).symm

/-- **PJ.1d** — joint continuity of the time-derivative field `(t, x) ↦ ∂ₜu phi t x`. -/
theorem continuous_kgPropagator_dt (m : ℝ) (phi : 𝓢(M3, ℂ)) :
    Continuous fun q : ℝ × M3 => kgPropagator_dt m phi q.1 q.2 := by
  have key : Continuous fun q : ℝ × M3 => ∫ k : M3,
      (Complex.ofReal (Real.cos (q.1 * dispersion m k)) * (𝓕 phi) k) * pjChar q.2 k :=
    continuous_symbolKernel_integral (continuous_ampCos_prod m phi)
      (integrable_norm_fourier phi) (fun q k => norm_ampCos_le m phi q.1 k)
  exact key

/-! ### PJ.1d — the derived fields -/

/-- **PJ.1d** — the spatial derivative field: the covector-valued momentum integral that
`hasFDerivAt_kgPropagator_space` identifies with the Fréchet derivative `∂ₓu`. -/
noncomputable def kgPropagator_dx (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) : M3 →L[ℝ] ℂ :=
  ∫ k : M3, ((Complex.ofReal (pjPhase m t k) * (𝓕 phi) k) * pjChar x k) • pjMomCLM k

theorem kgPropagator_dx_apply (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    kgPropagator_dx m phi t x =
      ∫ k : M3, ((Complex.ofReal (pjPhase m t k) * (𝓕 phi) k) * pjChar x k) • pjMomCLM k := rfl

/-- **PJ.1d** — the mixed derivative field `∂ₜ∂ₓu = ∂ₓ∂ₜu`. Both orders are computed
directly below and both land on this integral. -/
noncomputable def kgPropagator_dtdx (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) : M3 →L[ℝ] ℂ :=
  ∫ k : M3,
    ((Complex.ofReal (Real.cos (t * dispersion m k)) * (𝓕 phi) k) * pjChar x k) • pjMomCLM k

theorem kgPropagator_dtdx_apply (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    kgPropagator_dtdx m phi t x =
      ∫ k : M3,
        ((Complex.ofReal (Real.cos (t * dispersion m k)) * (𝓕 phi) k) * pjChar x k)
          • pjMomCLM k := rfl

/-- **PJ.1d** — the second spatial derivative field `∂ₓ²u`, valued in the continuous
bilinear maps on `M3`. -/
noncomputable def kgPropagator_dxdx (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    M3 →L[ℝ] (M3 →L[ℝ] ℂ) :=
  ∫ k : M3, pjMom2CLM k ((Complex.ofReal (pjPhase m t k) * (𝓕 phi) k) * pjChar x k)

theorem kgPropagator_dxdx_apply (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    kgPropagator_dxdx m phi t x =
      ∫ k : M3, pjMom2CLM k ((Complex.ofReal (pjPhase m t k) * (𝓕 phi) k) * pjChar x k) := rfl

/-- **PJ.1d** — the second time-derivative field `∂ₜ²u`, with symbol `-Ω sin(tΩ)`. -/
noncomputable def kgPropagator_dt2 (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) : ℂ :=
  ∫ k : M3,
    (Complex.ofReal (-(dispersion m k * Real.sin (t * dispersion m k))) * (𝓕 phi) k) * pjChar x k

theorem kgPropagator_dt2_apply (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    kgPropagator_dt2 m phi t x =
      ∫ k : M3,
        (Complex.ofReal (-(dispersion m k * Real.sin (t * dispersion m k))) * (𝓕 phi) k)
          * pjChar x k := rfl

/-- **PJ.1d** — differentiation under the integral in space: at every time the field
`x ↦ u phi t x` is Fréchet differentiable, with derivative `kgPropagator_dx m phi t x`. -/
theorem hasFDerivAt_kgPropagator_space (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    HasFDerivAt (fun y : M3 => kgPropagator m phi t y) (kgPropagator_dx m phi t x) x := by
  have hac := continuous_ampSin m hm phi t
  exact hasFDerivAt_charIntegral hac
    (by simpa using integrable_moment_amp hac phi (norm_ampSin_le m hm phi t) 0)
    (by simpa using integrable_moment_amp hac phi (norm_ampSin_le m hm phi t) 1) x

/-- **PJ.1d** — the spatial derivative as an `fderiv`. -/
theorem fderiv_kgPropagator_space (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    fderiv ℝ (fun y : M3 => kgPropagator m phi t y) x = kgPropagator_dx m phi t x :=
  (hasFDerivAt_kgPropagator_space m hm phi t x).fderiv

/-- **PJ.1d** — the mixed derivative in the order `∂ₓ∂ₜ`: differentiating the cosine-kernel
field in space gives `kgPropagator_dtdx`. -/
theorem hasFDerivAt_kgPropagator_dt_space (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    HasFDerivAt (fun y : M3 => kgPropagator_dt m phi t y) (kgPropagator_dtdx m phi t x) x := by
  have hac := continuous_ampCos m phi t
  exact hasFDerivAt_charIntegral hac
    (by simpa using integrable_moment_amp hac phi (norm_ampCos_le' m phi t) 0)
    (by simpa using integrable_moment_amp hac phi (norm_ampCos_le' m phi t) 1) x

/-- **PJ.1d** — the mixed derivative in the order `∂ₜ∂ₓ`: differentiating the spatial
derivative field in time gives the same `kgPropagator_dtdx`. -/
theorem hasDerivAt_kgPropagator_dx (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (x : M3) (t₀ : ℝ) :
    HasDerivAt (fun s : ℝ => kgPropagator_dx m phi s x) (kgPropagator_dtdx m phi t₀ x) t₀ :=
  hasDerivAt_sinKernelDx_integral m hm (continuous_dispersion m)
    (fun k => le_dispersion m k hm.le) (𝓕 phi).continuous
    (integrable_norm_mul_norm_fourier phi) x t₀

/-- **PJ.1d** — the two orders of the mixed derivative agree:
`∂ₓ(∂ₜu) = ∂ₜ(∂ₓu)`, both computed directly as `kgPropagator_dtdx`. -/
theorem kgPropagator_dtdx_comm (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    fderiv ℝ (fun y : M3 => kgPropagator_dt m phi t y) x
      = deriv (fun s : ℝ => kgPropagator_dx m phi s x) t :=
  (hasFDerivAt_kgPropagator_dt_space m phi t x).fderiv.trans
    (hasDerivAt_kgPropagator_dx m hm phi x t).deriv.symm

/-- **PJ.1d** — the second spatial derivative: the covector field `x ↦ ∂ₓu` is again
Fréchet differentiable, with derivative `kgPropagator_dxdx`. -/
theorem hasFDerivAt_kgPropagator_dx (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    HasFDerivAt (fun y : M3 => kgPropagator_dx m phi t y) (kgPropagator_dxdx m phi t x) x := by
  have hac := continuous_ampSin m hm phi t
  exact hasFDerivAt_charIntegralDx hac
    (by simpa using integrable_moment_amp hac phi (norm_ampSin_le m hm phi t) 1)
    (integrable_moment_amp hac phi (norm_ampSin_le m hm phi t) 2) x

/-- **PJ.1d** — the second time derivative: `∂ₜ(∂ₜu) = kgPropagator_dt2`. -/
theorem hasDerivAt_kgPropagator_dt (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (x : M3) (t₀ : ℝ) :
    HasDerivAt (fun s : ℝ => kgPropagator_dt m phi s x) (kgPropagator_dt2 m phi t₀ x) t₀ :=
  hasDerivAt_cosKernel_integral (continuous_dispersion m)
    (fun k => dispersion_nonneg m k) (𝓕 phi).continuous (integrable_norm_fourier phi)
    (integrable_dispersion_norm_fourier m hm phi) x t₀

/-- **PJ.1d** — the second time derivative as an iterated `deriv`. -/
theorem deriv_deriv_kgPropagator (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (x : M3) (t : ℝ) :
    deriv (fun s : ℝ => deriv (fun r : ℝ => kgPropagator m phi r x) s) t
      = kgPropagator_dt2 m phi t x := by
  rw [show (fun s : ℝ => deriv (fun r : ℝ => kgPropagator m phi r x) s)
      = fun s : ℝ => kgPropagator_dt m phi s x from
    funext fun s => (hasDerivAt_kgPropagator m hm phi x s).deriv]
  exact (hasDerivAt_kgPropagator_dt m hm phi x t).deriv

/-- **PJ.1d** — joint continuity of the second time-derivative field. -/
theorem continuous_kgPropagator_dt2 (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) :
    Continuous fun q : ℝ × M3 => kgPropagator_dt2 m phi q.1 q.2 := by
  have key : Continuous fun q : ℝ × M3 => ∫ k : M3,
      (Complex.ofReal (-(dispersion m k * Real.sin (q.1 * dispersion m k))) * (𝓕 phi) k)
        * pjChar q.2 k :=
    continuous_symbolKernel_integral (continuous_ampDt2_prod m phi)
      (integrable_dispersion_norm_fourier m hm phi) (fun q k => norm_ampDt2_le m phi q.1 k)
  exact key

/-- **PJ.1d** — joint continuity of the spatial derivative field, in the operator norm of
`M3 →L[ℝ] ℂ`. This is the "jointly continuous spatial gradient" of the contract. -/
theorem continuous_kgPropagator_dx (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) :
    Continuous fun q : ℝ × M3 => kgPropagator_dx m phi q.1 q.2 := by
  have key : Continuous fun q : ℝ × M3 => ∫ k : M3,
      ((Complex.ofReal (pjPhase m q.1 k) * (𝓕 phi) k) * pjChar q.2 k) • pjMomCLM k := by
    refine continuous_symbolKernelDx_integral (continuous_ampSin_prod m hm phi)
      ((integrable_norm_mul_norm_fourier phi).const_mul (2 * π / m)) (fun q k => ?_)
    refine (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (norm_ampSin_le m hm phi q.1 k) (norm_nonneg k))
      (by positivity : (0:ℝ) ≤ 2 * π)).trans (le_of_eq ?_)
    ring
  exact key

/-- **PJ.1d** — joint continuity of the mixed derivative field. -/
theorem continuous_kgPropagator_dtdx (m : ℝ) (phi : 𝓢(M3, ℂ)) :
    Continuous fun q : ℝ × M3 => kgPropagator_dtdx m phi q.1 q.2 := by
  have key : Continuous fun q : ℝ × M3 => ∫ k : M3,
      ((Complex.ofReal (Real.cos (q.1 * dispersion m k)) * (𝓕 phi) k) * pjChar q.2 k)
        • pjMomCLM k := by
    refine continuous_symbolKernelDx_integral (continuous_ampCos_prod m phi)
      ((integrable_norm_mul_norm_fourier phi).const_mul (2 * π)) (fun q k => ?_)
    refine (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (norm_ampCos_le m phi q.1 k) (norm_nonneg k))
      (by positivity : (0:ℝ) ≤ 2 * π)).trans (le_of_eq ?_)
    ring
  exact key

/-- **PJ.1d** — joint continuity of the second spatial derivative field. -/
theorem continuous_kgPropagator_dxdx (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) :
    Continuous fun q : ℝ × M3 => kgPropagator_dxdx m phi q.1 q.2 := by
  have key : Continuous fun q : ℝ × M3 => ∫ k : M3,
      pjMom2CLM k ((Complex.ofReal (pjPhase m q.1 k) * (𝓕 phi) k) * pjChar q.2 k) := by
    refine continuous_symbolKernelDxx_integral (continuous_ampSin_prod m hm phi)
      ((integrable_norm_fourier_mul phi 2).const_mul (4 * π ^ 2 / m)) (fun q k => ?_)
    refine (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (norm_ampSin_le m hm phi q.1 k)
        (by positivity : (0:ℝ) ≤ ‖k‖ ^ 2))
      (by positivity : (0:ℝ) ≤ 4 * π ^ 2)).trans (le_of_eq ?_)
    ring
  exact key

/-! ### PJ.1e — the pointwise Klein–Gordon identity -/

/-- **PJ.1e** — the Laplacian field: the propagator integral with the extra symbol
`-4π²‖k‖²` that one spatial Laplacian contributes in Mathlib's Fourier normalization. -/
noncomputable def kgPropagator_laplacian (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) : ℂ :=
  ∫ k : M3,
    (Complex.ofReal (-(4 * π ^ 2 * ‖k‖ ^ 2) * pjPhase m t k) * (𝓕 phi) k) * pjChar x k

theorem kgPropagator_laplacian_apply (m : ℝ) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    kgPropagator_laplacian m phi t x =
      ∫ k : M3,
        (Complex.ofReal (-(4 * π ^ 2 * ‖k‖ ^ 2) * pjPhase m t k) * (𝓕 phi) k) * pjChar x k := rfl

/-- **PJ.1e** — the spatial Laplacian of the propagator field is the momentum integral with
symbol `-4π²‖k‖²`. -/
theorem laplacian_kgPropagator (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    Δ (fun y : M3 => kgPropagator m phi t y) x = kgPropagator_laplacian m phi t x := by
  have hac := continuous_ampSin m hm phi t
  have h0 : Integrable (fun k : M3 =>
      ‖Complex.ofReal (pjPhase m t k) * (𝓕 phi) k‖) volume := by
    simpa using integrable_moment_amp hac phi (norm_ampSin_le m hm phi t) 0
  have h1 : Integrable (fun k : M3 =>
      ‖k‖ * ‖Complex.ofReal (pjPhase m t k) * (𝓕 phi) k‖) volume := by
    simpa using integrable_moment_amp hac phi (norm_ampSin_le m hm phi t) 1
  have h2 : Integrable (fun k : M3 =>
      ‖k‖ ^ 2 * ‖Complex.ofReal (pjPhase m t k) * (𝓕 phi) k‖) volume :=
    integrable_moment_amp hac phi (norm_ampSin_le m hm phi t) 2
  rw [show (fun y : M3 => kgPropagator m phi t y)
      = fun y : M3 => ∫ k : M3, (Complex.ofReal (pjPhase m t k) * (𝓕 phi) k) * pjChar y k from
    funext fun y => kgPropagator_apply m phi t y,
    laplacian_charIntegral hac h0 h1 h2 x, kgPropagator_laplacian_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  push_cast
  ring

/-- **PJ.1e** — the Klein–Gordon identity between the three momentum integrals, from
`-Ω² = -4π²‖k‖² - m²` (`dispersion_sq`, i.e. `B² = -Δ + m²` of Reed & Simon II, §X.13,
p. 295). -/
theorem kgPropagator_dt2_eq_laplacian_sub (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (t : ℝ)
    (x : M3) :
    kgPropagator_dt2 m phi t x
      = kgPropagator_laplacian m phi t x
        - Complex.ofReal (m ^ 2) * kgPropagator m phi t x := by
  have hlap : Integrable (fun k : M3 =>
      (Complex.ofReal (-(4 * π ^ 2 * ‖k‖ ^ 2) * pjPhase m t k) * (𝓕 phi) k) * pjChar x k)
      volume := by
    refine Integrable.mono' ((integrable_norm_fourier_mul phi 2).const_mul (4 * π ^ 2 / m))
      ((((Complex.continuous_ofReal.comp
        (((continuous_const.mul (continuous_norm.pow 2)).neg).mul
          ((Real.continuous_sin.comp
            (continuous_const.mul (continuous_dispersion m))).div
              (continuous_dispersion m)
              (fun k => ne_of_gt (dispersion_pos m k hm.ne'))))).mul
        (𝓕 phi).continuous).mul (continuous_pjChar_momentum x)).aestronglyMeasurable)
      (ae_of_all volume fun k => ?_)
    have habs : |-(4 * π ^ 2 * ‖k‖ ^ 2) * pjPhase m t k| ≤ 4 * π ^ 2 * ‖k‖ ^ 2 * (1 / m) := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * π ^ 2 * ‖k‖ ^ 2)]
      exact mul_le_mul_of_nonneg_left (abs_pjPhase_le m hm t k) (by positivity)
    simp only [norm_mul, norm_pjChar, mul_one]
    refine le_trans (mul_le_mul_of_nonneg_right (norm_ofReal_le habs) (norm_nonneg _))
      (le_of_eq ?_)
    ring
  have hprop : Integrable (fun k : M3 =>
      Complex.ofReal (m ^ 2) * ((Complex.ofReal (pjPhase m t k) * (𝓕 phi) k) * pjChar x k))
      volume := (integrable_kgPropagator_integrand m hm phi t x).const_mul _
  rw [kgPropagator_laplacian_apply, kgPropagator_apply, ← integral_const_mul,
    ← integral_sub hlap hprop, kgPropagator_dt2_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  have hreal : -(dispersion m k * Real.sin (t * dispersion m k))
      = -(4 * π ^ 2 * ‖k‖ ^ 2) * pjPhase m t k - m ^ 2 * pjPhase m t k := by
    have hne : dispersion m k ≠ 0 := ne_of_gt (dispersion_pos m k hm.ne')
    have hstep : -(4 * π ^ 2 * ‖k‖ ^ 2) * pjPhase m t k - m ^ 2 * pjPhase m t k
        = -(dispersion m k ^ 2) * (Real.sin (t * dispersion m k) / dispersion m k) := by
      rw [pjPhase, dispersion_sq]
      ring
    rw [hstep, pow_two]
    field_simp
  simp only [hreal]
  push_cast
  ring

/-- **PJ.1e** — the free Klein–Gordon equation, pointwise and in honest derivatives:
`∂ₜ²u = Δu - m²u`. -/
theorem kleinGordon_kgPropagator (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (t : ℝ) (x : M3) :
    deriv (fun s : ℝ => deriv (fun r : ℝ => kgPropagator m phi r x) s) t
      = Δ (fun y : M3 => kgPropagator m phi t y) x
        - Complex.ofReal (m ^ 2) * kgPropagator m phi t x := by
  rw [deriv_deriv_kgPropagator m hm phi x t, laplacian_kgPropagator m hm phi t x]
  exact kgPropagator_dt2_eq_laplacian_sub m hm phi t x

/-! ### PJ.1f — the initial velocity via Fourier inversion -/

/-- **Schwartz Fourier inversion** in the kernel form the propagator consumes:
integrating `𝓕(phi)` against the inverse character `𝐞(⟪k, x⟫)` returns `phi(x)`.
This is the `2π`-normalized inversion formula (Reed & Simon II, §IX.1, at section level;
Mathlib: `FourierPair` inversion on `𝓢(M3, ℂ)`). -/
theorem fourier_inversion_eq (phi : 𝓢(M3, ℂ)) (x : M3) :
    ∫ k : M3, (𝓕 phi) k * pjChar x k = phi x := by
  have hpair : 𝓕⁻ (𝓕 phi) = phi := FourierTransform.fourierInv_fourier_eq phi
  have hpt := DFunLike.congr_fun hpair x
  rw [SchwartzMap.fourierInv_coe] at hpt
  rw [Real.fourierInv_eq] at hpt
  rw [← hpt]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [pjChar, Circle.smul_def, smul_eq_mul, mul_comm]

/-- **PJ.1f** — the initial velocity is the data itself:
`∂ₜu phi 0 x = cos(0)·𝓕(phi) integrated against the inverse character = phi x`. -/
theorem kgPropagator_dt_zero (m : ℝ) (phi : 𝓢(M3, ℂ)) (x : M3) :
    kgPropagator_dt m phi 0 x = phi x := by
  have hint : ∀ k : M3,
      (Complex.ofReal (Real.cos ((0 : ℝ) * dispersion m k)) * (𝓕 phi) k) * pjChar x k
        = (𝓕 phi) k * pjChar x k := fun _ => by simp
  rw [kgPropagator_dt_apply, integral_congr_ae (Filter.Eventually.of_forall hint),
    fourier_inversion_eq]

/-- **PJ.1f** — the initial velocity as an honest derivative:
`deriv (t ↦ u phi t x) 0 = phi x`. -/
theorem deriv_kgPropagator_zero (m : ℝ) (hm : 0 < m) (phi : 𝓢(M3, ℂ)) (x : M3) :
    deriv (fun s : ℝ => kgPropagator m phi s x) 0 = phi x :=
  (hasDerivAt_kgPropagator m hm phi x 0).deriv.trans (kgPropagator_dt_zero m phi x)

end QFT.KleinGordon
