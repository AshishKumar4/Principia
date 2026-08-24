import Atlas.Witnesses.WightmanUtilities

/-!
# P2.5a adversarial kernel probes — where the `2π` sits, and what it does to the shell

Mathlib's Fourier character is `𝐞 t = exp (2 π i t)`, so the transform on `𝓢` carries the
`e^{-2 π i ⟪x, ξ⟫}` normalization and the spec's kernel is `𝐞 (-η(a, p))`. The Fourier
variable `p` is therefore the physical four-momentum divided by `2π`. These probes pin
that down and refute the two plausible mistakes:

* dropping the `2π` from the dispersion relation — the mass-`m` shell in the *physical*
  momentum is `Ω(k) = √(4 π² k² + m²)` when `k` is the spatial *Fourier* variable, not
  `√(k² + m²)`;
* worrying that the `2π` moves the cone — it does not, because `closedForwardCone` is
  stable under positive rescaling, so the support hypothesis is normalization-blind.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.5a/` only.
-/

open MeasureTheory Real
open Spacetime.Minkowski
open scoped SchwartzMap FourierTransform

/-! ## The character carries the `2π` -/

theorem probe_fourierChar_has_2pi (t : ℝ) :
    (Real.fourierChar t : ℂ) = Complex.exp ((2 * π * t : ℝ) * Complex.I) :=
  Real.fourierChar_apply t

-- The spec's kernel, restated: the exponent is the Minkowski pairing, inside `𝐞`.
theorem probe_kernel (f : 𝓢(M4, ℂ)) (p : M4) :
    𝓕η f p = ∫ a : M4, Real.fourierChar (-(minkowskiForm a p)) • f a :=
  fourierMinkowski_apply_eq_integral f p

/-! ## The mass shell in the physical four-momentum -/

/-- `Ω(k) = √(4 π² k² + m²)` — the P2.6c dispersion relation for spatial *Fourier*
variable `k`. -/
noncomputable def probeOmega (k m : ℝ) : ℝ := Real.sqrt (4 * π ^ 2 * k ^ 2 + m ^ 2)

theorem probe_omega_sq (k m : ℝ) : probeOmega k m ^ 2 = 4 * π ^ 2 * k ^ 2 + m ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem probe_omega_nonneg (k m : ℝ) : 0 ≤ probeOmega k m := Real.sqrt_nonneg _

/-- The physical four-momentum on the shell: time component `Ω(k)`, spatial component
`2π k` (the physical momentum belonging to Fourier variable `k`). -/
noncomputable def probeShellMomentum (k m : ℝ) : M4 :=
  EuclideanSpace.single 0 (probeOmega k m) + EuclideanSpace.single 1 (2 * π * k)

theorem probe_shellMomentum_apply_zero (k m : ℝ) :
    probeShellMomentum k m 0 = probeOmega k m := by
  simp [probeShellMomentum]

theorem probe_shellMomentum_apply_one (k m : ℝ) :
    probeShellMomentum k m 1 = 2 * π * k := by
  simp [probeShellMomentum]

theorem probe_shellMomentum_apply_two (k m : ℝ) : probeShellMomentum k m 2 = 0 := by
  simp [probeShellMomentum]

theorem probe_shellMomentum_apply_three (k m : ℝ) : probeShellMomentum k m 3 = 0 := by
  simp [probeShellMomentum]

/-- `-η(P, P) = m²` on the shell: the `2π` in the exponent is exactly what turns the
Fourier-variable dispersion `Ω(k) = √(4 π² k² + m²)` into the covariant mass shell. -/
theorem probe_massShell (k m : ℝ) :
    -(minkowskiForm (probeShellMomentum k m) (probeShellMomentum k m)) = m ^ 2 := by
  rw [minkowskiForm_eq, probe_shellMomentum_apply_zero, probe_shellMomentum_apply_one,
    probe_shellMomentum_apply_two, probe_shellMomentum_apply_three]
  nlinarith [probe_omega_sq k m]

/-- Refutation: the `2π`-free dispersion `√(k² + m²)` is a different number. At
`k = m = 1` it is `√2`, while `Ω(1, 1) = √(4 π² + 1) > √2`. -/
theorem probe_naive_dispersion_wrong : Real.sqrt (1 ^ 2 + 1 ^ 2) ≠ probeOmega 1 1 := by
  have hlt : Real.sqrt (1 ^ 2 + 1 ^ 2) < probeOmega 1 1 := by
    refine Real.sqrt_lt_sqrt (by norm_num) ?_
    nlinarith [Real.two_le_pi]
  exact ne_of_lt hlt

/-! ## The shell sits in the closed forward cone, and so does its Fourier rescaling -/

theorem probe_shellMomentum_mem_cone (k m : ℝ) :
    probeShellMomentum k m ∈ closedForwardCone := by
  rw [mem_closedForwardCone_iff, probe_shellMomentum_apply_zero,
    probe_shellMomentum_apply_one, probe_shellMomentum_apply_two,
    probe_shellMomentum_apply_three]
  refine ⟨?_, probe_omega_nonneg k m⟩
  nlinarith [probe_omega_sq k m, sq_nonneg m]

/-- The Fourier variable is the physical momentum divided by `2π`, and it lies in the
same cone: the support hypothesis of the spectrum condition does not care which
normalization is used. -/
theorem probe_fourier_variable_mem_cone (k m : ℝ) :
    ((2 * π)⁻¹ • probeShellMomentum k m : M4) ∈ closedForwardCone :=
  closedForwardCone.smul_mem (by positivity) (probe_shellMomentum_mem_cone k m)

/-- Positive rescaling by `2π` is invisible to the cone, in both directions. -/
theorem probe_cone_scale_invariant (v : M4) :
    v ∈ closedForwardCone ↔ ((2 * π) • v : M4) ∈ closedForwardCone := by
  refine ⟨fun h => closedForwardCone.smul_mem (by positivity) h, fun h => ?_⟩
  have hscaled := closedForwardCone.smul_mem (c := (2 * π)⁻¹) (by positivity) h
  rwa [smul_smul, inv_mul_cancel₀ (by positivity : (2 * π) ≠ 0), one_smul] at hscaled
