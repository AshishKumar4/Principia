import Atlas.Witnesses.WightmanUtilities

/-!
# P2.5a adversarial kernel probes — the sign of the time flip

The P2.5a DRAFT spec defines the Minkowski Fourier transform as Mathlib's Schwartz
Fourier transform composed with the *time* reflection `T(x⁰, x⃗) = (-x⁰, x⃗)`. The
justification is one equation, `inner_timeReflection_right : ⟪v, T w⟫ = η(v, w)`. The
first probes refute every neighbouring pairing convention by kernel arithmetic at
`v = w = ∂₀`, where `η(∂₀, ∂₀) = -1` and `⟪∂₀, ∂₀⟫ = +1`:

* no reflection at all — Mathlib's Euclidean kernel is not the Minkowski kernel;
* the *space* reflection `S(x⁰, x⃗) = (x⁰, -x⃗)`, i.e. `-T` — it delivers `-η`;
* the total reflection `x ↦ -x` — it fixes no direction, while `T` fixes the spatial
  ones.

## Where the kernel sign is actually observable

A previous version of this file advertised the exponent pair `±1` as a discriminator
between the two kernels. That was false at the level that matters: `Real.fourierChar`
has period one, so `𝐞 1 = 𝐞 (-1) = 1`. The arguments differed; the characters did not.
The committed discriminator is now the pair `±1/4`, where the complex characters
genuinely differ: `𝐞 (1/4) = I` and `𝐞 (-1/4) = -I`.

Restricting the spec kernel `𝓕η f p = ∫ a, 𝐞 (-η(a, p)) • f a` to the time axis turns
the same choice into the time-evolution orientation. For momentum `p⁰∂₀` the selected
exponent is `+t·p⁰`, so the kernel reads `exp(+iEt)` with physical energy
`E = 2πp⁰ > 0` on the forward cone — the frozen Stone convention
`U t = exp(I * t • A)` of `OneParameterUnitaryGroup` (Reed & Simon I, §VIII.4). The
reversed sign reads `exp(-iEt)`: negative frequency, the wrong spectrum orientation.
At evolution time `t = P₀ = 1/2` the two phases are the distinct characters `I` and
`-I`.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.5a/` only.
-/
open MeasureTheory Real RealInnerProductSpace
open Spacetime.Minkowski
open scoped SchwartzMap FourierTransform

/-! ## The two pairings disagree in sign on the time direction -/

theorem probe_minkowskiForm_timeUnit : minkowskiForm timeUnit timeUnit = -1 := by
  rw [minkowskiForm_eq]
  simp [Fin.ext_iff]

theorem probe_inner_timeUnit : ⟪timeUnit, timeUnit⟫ = (1 : ℝ) := by
  simp

/-! ## Refutation 1: dropping the reflection is wrong -/

theorem probe_no_reflection_wrong : ¬ ∀ v w : M4, ⟪v, w⟫ = minkowskiForm v w := by
  intro h
  have := h timeUnit timeUnit
  rw [probe_inner_timeUnit, probe_minkowskiForm_timeUnit] at this
  norm_num at this

-- The spec's reflected pairing does satisfy it, at the same point.
theorem probe_reflection_right : ⟪timeUnit, timeReflection timeUnit⟫ = (-1 : ℝ) := by
  rw [inner_timeReflection_right, probe_minkowskiForm_timeUnit]

/-! ## Refutation 2: the space reflection `S = -T` delivers `-η`, not `η` -/

/-- The space reflection `S(x⁰, x⃗) = (x⁰, -x⃗)`, written as `-T`. -/
noncomputable def probeSpaceReflection (v : M4) : M4 := -timeReflection v

theorem probe_spaceReflection_apply_zero (v : M4) : probeSpaceReflection v 0 = v 0 := by
  simp [probeSpaceReflection]

theorem probe_spaceReflection_apply_of_ne (v : M4) {i : Fin 4} (hi : i ≠ 0) :
    probeSpaceReflection v i = -(v i) := by
  simp [probeSpaceReflection, timeReflectionCLM_apply_of_ne _ hi]

theorem probe_inner_spaceReflection (v w : M4) :
    ⟪v, probeSpaceReflection w⟫ = -minkowskiForm v w := by
  rw [probeSpaceReflection, inner_neg_right, inner_timeReflection_right]

theorem probe_space_reflection_wrong :
    ¬ ∀ v w : M4, ⟪v, probeSpaceReflection w⟫ = minkowskiForm v w := by
  intro h
  have := h timeUnit timeUnit
  rw [probe_inner_spaceReflection, probe_minkowskiForm_timeUnit] at this
  norm_num at this

/-! ## Refutation 3: `T` is neither the identity nor the total reflection -/

theorem probe_timeReflection_ne_id : timeReflection timeUnit ≠ timeUnit := by
  rw [timeReflection_timeUnit]
  intro h
  have h0 : (-timeUnit : M4) 0 = timeUnit 0 := by rw [h]
  norm_num at h0

-- `T` fixes the spatial directions; the total reflection `x ↦ -x` does not. So the
-- reflection in `𝓕η` is a single-coordinate flip, not a global sign.
theorem probe_timeReflection_ne_neg : timeReflection spaceUnit ≠ -spaceUnit := by
  rw [timeReflection_spaceUnit]
  intro h
  have h1 := congrArg (fun z : M4 => z 1) h
  norm_num at h1

/-! ## The kernel choice is observable only at non-integer arguments -/

-- `𝓕η f p = ∫ a, 𝐞 (-η(a, p)) • f a`: the exponent that the spec pins.
theorem probe_kernel_exponent (f : 𝓢(M4, ℂ)) (p : M4) :
    𝓕η f p = ∫ a : M4, Real.fourierChar (-(minkowskiForm a p)) • f a :=
  fourierMinkowski_apply_eq_integral f p

/-- Refutation of the old `±1` discriminator: at `a = p = ∂₀` the Minkowski and
Euclidean exponent arguments are `+1` and `-1` and do differ — but `Real.fourierChar`
has period one, so the two characters are both `1`. Argument difference alone is not
kernel difference. -/
theorem probe_fourierChar_one_eq :
    (Real.fourierChar (1 : ℝ) : ℂ) = (Real.fourierChar (-1 : ℝ) : ℂ) := by
  rw [Real.fourierChar_apply (1 : ℝ), Real.fourierChar_apply (-1 : ℝ),
    show (2 * π * 1 : ℝ) = 2 * π from by ring,
    show (2 * π * -1 : ℝ) = -(2 * π) from by ring,
    Complex.ofReal_neg, neg_mul, Complex.exp_neg]
  norm_num

-- The exponent arguments themselves do differ at `∂₀`; what failed was the inference
-- from argument difference to kernel difference.
theorem probe_exponent_arguments_differ :
    -(minkowskiForm timeUnit timeUnit) ≠ -(⟪timeUnit, timeUnit⟫ : ℝ) := by
  rw [probe_minkowskiForm_timeUnit, probe_inner_timeUnit]
  norm_num

/-- **The honest sign discriminator**: at the quarter arguments the two kernels take
genuinely different complex values. -/
theorem probe_fourierChar_quarter_values :
    (Real.fourierChar (1 / 4 : ℝ) : ℂ) = Complex.I ∧
      (Real.fourierChar (-1 / 4 : ℝ) : ℂ) = -Complex.I := by
  have h4 : (2 * π * (1 / 4) : ℝ) = π / 2 := by ring
  have h4' : (2 * π * (-1 / 4) : ℝ) = -π / 2 := by ring
  constructor
  · rw [Real.fourierChar_apply, h4, Complex.ofReal_div]
    norm_num
  · rw [Real.fourierChar_apply, h4', Complex.ofReal_div, Complex.ofReal_neg,
      neg_div, neg_mul, Complex.exp_neg]
    norm_num

theorem probe_fourierChar_quarter_ne :
    (Real.fourierChar (1 / 4 : ℝ) : ℂ) ≠ (Real.fourierChar (-1 / 4 : ℝ) : ℂ) := by
  rw [probe_fourierChar_quarter_values.1, probe_fourierChar_quarter_values.2]
  exact fun h => by rw [Complex.ext_iff] at h; norm_num at h

/-! ## Connection to `U(t) = exp(+itH)` and forward positive energy -/

/-- Physical energy of the Fourier variable `p⁰∂₀`: `E = 2π p⁰`. The `2π` is Mathlib's
forward-transform normalization (`Real.fourierChar`). -/
noncomputable def probeEnergy (p0 : ℝ) : ℝ := 2 * π * p0

/-- The committed probe momentum `P₀ = 1/2`, so that `t·P₀ = 1/4` at evolution time
`t = P₀`. -/
noncomputable def probeP0 : ℝ := 1 / 2

/-- The momentum `P₀∂₀` is forward: it sits in the closed cone, so its energy is
positive and the spectrum condition applies to it. -/
theorem probe_P0_mem_forwardCone : (probeP0 • timeUnit : M4) ∈ closedForwardCone := by
  rw [mem_closedForwardCone_iff]
  simp [probeP0]

theorem probe_energy_pos : 0 < probeEnergy probeP0 := by
  have hrw : probeEnergy probeP0 = Real.pi := by
    unfold probeEnergy probeP0
    ring
  rw [hrw]
  exact Real.pi_pos

-- On the time axis the selected Minkowski exponent is `+t·p⁰`: restricting
-- `-(η(a, p))` to `a = t∂₀`, `p = P₀∂₀` flips the sign of the mostly-plus pairing.
theorem probe_time_axis_exponent (t p0 : ℝ) :
    -(minkowskiForm ((t • timeUnit : M4)) ((p0 • timeUnit : M4))) = t * p0 := by
  rw [minkowskiForm_eq]
  simp [PiLp.smul_apply]

/-- The selected kernel along the time axis reads the FORWARD phase:
`𝐞(t·p⁰) = exp(+iEt)` with `E = 2πp⁰` — the frozen Stone convention
`U t = exp(I * t • A)` (Reed & Simon I, §VIII.4). -/
theorem probe_kernel_phase_forward (t p0 : ℝ) :
    (Real.fourierChar (t * p0) : ℂ)
      = Complex.exp (Complex.I * (probeEnergy p0 * t)) := by
  rw [Real.fourierChar_apply, probeEnergy]
  congr 1
  push_cast
  ring

/-- The reversed sign reads the NEGATIVE-frequency phase: `exp(-iEt)`. This is what
dropping the time reflection would commit the spec to. -/
theorem probe_kernel_phase_reversed (t p0 : ℝ) :
    (Real.fourierChar (-(t * p0)) : ℂ)
      = Complex.exp (-(Complex.I * (probeEnergy p0 * t))) := by
  rw [Real.fourierChar_apply, probeEnergy]
  congr 1
  push_cast
  ring

/-- **The committed arithmetic probe**: at evolution time `t = P₀ = 1/2` and momentum
`P₀∂₀` in the closed forward cone, the selected-kernel exponent argument is
`t·P₀ = +1/4` and the character is the nontrivial `I`; the reversed sign gives
argument `-1/4` and character `-I`. The characters differ as complex numbers, not just
as arguments. -/
theorem probe_sign_discriminator :
    (Real.fourierChar (probeP0 * probeP0) : ℂ) = Complex.I ∧
      (Real.fourierChar (-(probeP0 * probeP0)) : ℂ) = -Complex.I ∧
      Complex.I ≠ -Complex.I := by
  refine ⟨?_, ?_, ?_⟩
  · have harg : probeP0 * probeP0 = (1 / 4 : ℝ) := by
      simp only [probeP0]
      norm_num
    rw [harg]
    exact probe_fourierChar_quarter_values.1
  · have harg : -(probeP0 * probeP0) = (-1 / 4 : ℝ) := by
      simp only [probeP0]
      norm_num
    rw [harg]
    exact probe_fourierChar_quarter_values.2
  · exact fun h => by rw [Complex.ext_iff] at h; norm_num at h
