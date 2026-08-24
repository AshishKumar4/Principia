import Atlas.Witnesses.WightmanUtilities

/-!
# P2.5a adversarial kernel probes — the sign of the time flip

The P2.5a DRAFT spec defines the Minkowski Fourier transform as Mathlib's Schwartz
Fourier transform composed with the *time* reflection `T(x⁰, x⃗) = (-x⁰, x⃗)`. The
justification is one equation, `inner_timeReflection_right : ⟪v, T w⟫ = η(v, w)`. These
probes refute every neighbouring convention by kernel arithmetic at `v = w = ∂₀`, where
`η(∂₀, ∂₀) = -1` and `⟪∂₀, ∂₀⟫ = +1`:

* no reflection at all — Mathlib's Euclidean kernel is not the Minkowski kernel;
* the *space* reflection `S(x⁰, x⃗) = (x⁰, -x⃗)`, i.e. `-T` — it delivers `-η`;
* the total reflection `x ↦ -x` — it fixes no direction, while `T` fixes the spatial
  ones.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.5a/` only.
-/

open MeasureTheory RealInnerProductSpace
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

/-! ## The Fourier exponent inherits the sign -/

-- `𝓕η f p = ∫ a, 𝐞 (-η(a, p)) • f a`: the exponent that the spec pins.
theorem probe_kernel_exponent (f : 𝓢(M4, ℂ)) (p : M4) :
    𝓕η f p = ∫ a : M4, Real.fourierChar (-(minkowskiForm a p)) • f a :=
  fourierMinkowski_apply_eq_integral f p

-- At `a = p = ∂₀` the Minkowski exponent is `+1` and the Euclidean one is `-1`: the two
-- kernels are complex conjugates there, so the choice is observable, not cosmetic.
theorem probe_exponent_differs :
    -(minkowskiForm timeUnit timeUnit) ≠ -(⟪timeUnit, timeUnit⟫ : ℝ) := by
  rw [probe_minkowskiForm_timeUnit, probe_inner_timeUnit]
  norm_num
