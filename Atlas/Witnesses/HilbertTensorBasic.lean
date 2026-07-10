import Atlas.Specs.OperatorTheory.HilbertTensor
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Non-vacuity witnesses for the completed Hilbert tensor product (P2.1a)

Concrete models exercising the frozen spec `Atlas/Specs/OperatorTheory/HilbertTensor.lean`.

* **Hilbert-space instances on concrete models** (expected-true): `ℂ ⊗̂[ℂ] ℂ`,
  `EuclideanSpace ℂ (Fin 2) ⊗̂[ℂ] EuclideanSpace ℂ (Fin 3)`, and a real-scalar model
  are complete inner-product spaces by instance search alone — the `abbrev` design
  point of the spec, instantiated.
* **Scalar model `ℂ ⊗̂[ℂ] ℂ` computed** (expected-true): `⟪1 ⊗̂ 1, 1 ⊗̂ 1⟫ = 1`, the
  nondegenerate value `⟪2 ⊗̂ 3, 5 ⊗̂ 7⟫ = 210 = (2̄·5)(3̄·7)` pinning multiplicativity,
  the cross norm `‖2 ⊗̂ (-3)‖ = 6`, and nontriviality: `1 ⊗̂ 1 ≠ 0`, so
  `ℂ ⊗̂[ℂ] ℂ` is a `Nontrivial` type — the completion encloses something.
* **Orthogonality on `ℂ² ⊗̂ ℂ²`**: `⟪e₀ ⊗̂ e₀, e₁ ⊗̂ e₁⟫ = 0` (expected-true) and the
  kernel-checked refutation `⟪e₀ ⊗̂ e₀, e₁ ⊗̂ e₁⟫ ≠ 1` (expected-false: orthonormal
  pure tensors are not unit-paired), whence `e₀ ⊗̂ e₀ ≠ e₁ ⊗̂ e₁` in the completion.
* **Density instantiated**: the span of pure tensors is dense in `ℂ ⊗̂[ℂ] ℂ`.
* **`RCLike` generality exercised**: the inner-product identity on an `ℝ`-model.

The ℓ²-basis isomorphism `E ⊗̂ F ≃ ℓ²(ι₁ × ι₂)` is blueprint node P2.1d, not part of
these witnesses.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I* (1980), §II.4.
-/

open OperatorTheory HilbertTensorProduct

noncomputable section

namespace OperatorTheory.Witnesses

/-! ### Hilbert-space instances on concrete models -/

example : CompleteSpace (ℂ ⊗̂[ℂ] ℂ) := inferInstance
example : InnerProductSpace ℂ (ℂ ⊗̂[ℂ] ℂ) := inferInstance
example : NormedAddCommGroup (EuclideanSpace ℂ (Fin 2) ⊗̂[ℂ] EuclideanSpace ℂ (Fin 3)) :=
  inferInstance
example : InnerProductSpace ℂ (EuclideanSpace ℂ (Fin 2) ⊗̂[ℂ] EuclideanSpace ℂ (Fin 3)) :=
  inferInstance
example : CompleteSpace (EuclideanSpace ℂ (Fin 2) ⊗̂[ℂ] EuclideanSpace ℂ (Fin 3)) :=
  inferInstance
example : CompleteSpace (ℝ ⊗̂[ℝ] EuclideanSpace ℝ (Fin 2)) := inferInstance

/-! ### The scalar model `ℂ ⊗̂[ℂ] ℂ` -/

/-- `⟪1 ⊗̂ 1, 1 ⊗̂ 1⟫ = 1`: the unit pure tensor is a unit vector. -/
example : inner ℂ (tmulₕ ℂ (1 : ℂ) (1 : ℂ)) (tmulₕ ℂ (1 : ℂ) (1 : ℂ)) = 1 := by
  simp

/-- A nondegenerate value pinning multiplicativity of the inner product:
`⟪2 ⊗̂ 3, 5 ⊗̂ 7⟫ = (2̄ · 5) * (3̄ · 7) = 210` — not `31 = 2̄·5 + 3̄·7`, refuting an
additive impostor by computation. -/
example : inner ℂ (tmulₕ ℂ (2 : ℂ) (3 : ℂ)) (tmulₕ ℂ (5 : ℂ) (7 : ℂ)) = 210 := by
  simp [map_ofNat]
  norm_num

/-- The cross norm computed on a scalar pure tensor: `‖2 ⊗̂ (-3)‖ = 2 * 3 = 6`. -/
example : ‖tmulₕ ℂ (2 : ℂ) (-3 : ℂ)‖ = 6 := by
  simp
  norm_num

/-- The unit pure tensor is nonzero: its norm is `1`. -/
theorem tmulₕ_one_one_ne_zero : tmulₕ ℂ (1 : ℂ) (1 : ℂ) ≠ 0 := by
  intro h
  have h1 : ‖tmulₕ ℂ (1 : ℂ) (1 : ℂ)‖ = 1 := by simp
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- The completion is a nontrivial type — the spec's fences enclose something. -/
example : Nontrivial (ℂ ⊗̂[ℂ] ℂ) :=
  ⟨_, _, tmulₕ_one_one_ne_zero⟩

/-! ### Orthogonality on `ℂ² ⊗̂ ℂ²` -/

/-- The `i`-th standard basis vector of `ℂ²`. -/
def e (i : Fin 2) : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single i 1

/-- Pure tensors of orthogonal vectors are orthogonal: `⟪e₀ ⊗̂ e₀, e₁ ⊗̂ e₁⟫ = 0`. -/
theorem inner_tmulₕ_e_zero_e_one :
    inner ℂ (tmulₕ ℂ (e 0) (e 0)) (tmulₕ ℂ (e 1) (e 1)) = 0 := by
  simp [e, EuclideanSpace.inner_single_left]

/-- `⟪e₀ ⊗̂ e₀, e₀ ⊗̂ e₀⟫ = 1`: basis pure tensors are unit vectors. -/
theorem inner_tmulₕ_e_zero_self :
    inner ℂ (tmulₕ ℂ (e 0) (e 0)) (tmulₕ ℂ (e 0) (e 0)) = 1 := by
  simp [e]

/-- **Expected-false**: orthogonal basis pure tensors are *not* unit-paired —
`⟪e₀ ⊗̂ e₀, e₁ ⊗̂ e₁⟫ ≠ 1` (it is `0`). Kernel-checked refutation showing the inner
product genuinely separates pure tensors. -/
example : ¬inner ℂ (tmulₕ ℂ (e 0) (e 0)) (tmulₕ ℂ (e 1) (e 1)) = 1 := by
  rw [inner_tmulₕ_e_zero_e_one]
  exact zero_ne_one

/-- Distinct basis pure tensors stay distinct in the completion. -/
example : tmulₕ ℂ (e 0) (e 0) ≠ tmulₕ ℂ (e 1) (e 1) := by
  intro h
  have h0 := inner_tmulₕ_e_zero_e_one
  rw [← h, inner_tmulₕ_e_zero_self] at h0
  exact one_ne_zero h0

/-! ### Density and `RCLike` generality -/

/-- The frozen density statement, instantiated on the scalar model. -/
example :
    Dense (Submodule.span ℂ {t : ℂ ⊗̂[ℂ] ℂ | ∃ x y, tmulₕ ℂ x y = t} :
      Set (ℂ ⊗̂[ℂ] ℂ)) :=
  dense_span_tmulₕ ℂ

/-- The inner-product identity over `𝕜 = ℝ`, exercising the spec's `RCLike`
generality: `⟪2 ⊗̂ 3, 5 ⊗̂ 7⟫ = 210` in `ℝ ⊗̂[ℝ] ℝ`. -/
example : inner ℝ (tmulₕ ℝ (2 : ℝ) (3 : ℝ)) (tmulₕ ℝ (5 : ℝ) (7 : ℝ)) = 210 := by
  simp
  norm_num

end OperatorTheory.Witnesses
