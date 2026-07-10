import Atlas.Proofs.CayleyTheory
import Atlas.Witnesses.SymmetricOperators

/-!
# Non-vacuity witnesses for the Cayley transform (P2.3c)

Concrete scalar models of the frozen spec `Atlas/Specs/OperatorTheory/Cayley.lean`,
built on the multiplication operators `mulPMap z` of the P2.3a/b witness file:

* **The Cayley transform of `r • id` computed** (expected-true): total domain
  (`cayley_mulPMap_real_domain`) and value the Möbius scalar
  `(r - i)/(r + i)` (`cayley_mulPMap_real_apply`), of unit modulus (`norm_mobius`,
  extracted from the proven `CayleyIsometric`). Degenerate anchor `cayley 0 = -id`
  (`cayley_mulPMap_zero_apply`), the expected-value example from the spec docstring.
* **The inverse transform computed**: `inverseCayley (μ • id) = (i(1 + μ)/(1 - μ)) • id`
  for `μ ≠ 1`, with total domain (`inverseCayley_mulPMap_apply`,
  `inverseCayley_mulPMap_domain`), and the end-to-end Möbius recovery
  `inverseCayley ((r-i)/(r+i) • id) = r • id` pointwise
  (`mobius_inverse`, `inverseCayley_cayley_mulPMap_real_apply`) — plus the same
  recovery obtained abstractly from the proven `InverseCayleyCayley`.
* **Wrong-sign refutation** (expected-false): the variant inverse transform
  `+i • (x + U x)` (and equivalently the "build on `1 - U` with unchanged sign"
  variant) returns `-z` where the frozen `inverseCayley` returns `z` on the `μ = -i`
  model, and `z ≠ -z` — a kernel-checked refutation pinning the sign convention
  (`wrongInverseCayley_ne`).
* **The unitary side exercised** (expected-true): the concrete unitary `(-i) • id` on
  `ℂ` (the Cayley transform of `1 • id`) has no eigenvalue `1`
  (`ker_one_sub_negIUnitary`), its inverse Cayley transform is self-adjoint, and its
  Cayley transform is itself — instantiating the frozen targets
  `InverseCayleySelfAdjoint` and `CayleyInverseCayley`.

## Sources

* W. Rudin, *Functional Analysis*, 2nd ed. (1991), ch. 13, Thm 13.19.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II* (1975), §X.1.
-/

open OperatorTheory

noncomputable section

namespace OperatorTheory.Witnesses

/-! ### Scalar arithmetic anchors -/

theorem ofReal_add_I_ne_zero (r : ℝ) : (r : ℂ) + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

theorem mobius_ne_one (r : ℝ) : ((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I) ≠ 1 := by
  intro h
  rw [div_eq_one_iff_eq (ofReal_add_I_ne_zero r)] at h
  have := congrArg Complex.im h
  norm_num at this

/-- The Möbius inverse identity `i(1 + μ)/(1 - μ) = r` for `μ = (r - i)/(r + i)` — the
scalar sanity anchor of the frozen spec's conventions docstring. -/
theorem mobius_inverse (r : ℝ) :
    Complex.I * (1 + ((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I))
      / (1 - ((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I)) = (r : ℂ) := by
  have h := ofReal_add_I_ne_zero r
  have h1 : (1 : ℂ) - ((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (mobius_ne_one r))
  rw [div_eq_iff h1]
  field_simp
  ring

/-! ### The Cayley transform of `r • id` (expected-true witness) -/

/-- The Cayley transform of the self-adjoint `r • id` is everywhere defined:
`ran (A + i) = ℂ` (the totality clause of the frozen `CayleySelfAdjointIffBijective`,
computed by hand). -/
theorem cayley_mulPMap_real_domain (r : ℝ) :
    (LinearPMap.cayley (mulPMap (r : ℂ))).domain = ⊤ := by
  rw [LinearPMap.cayley_domain, LinearMap.range_eq_top]
  intro y
  have h := ofReal_add_I_ne_zero r
  refine ⟨⟨y / ((r : ℂ) + Complex.I), trivial⟩, ?_⟩
  have hstep : (LinearPMap.shift (mulPMap (r : ℂ)) (-Complex.I)).toFun
        ⟨y / ((r : ℂ) + Complex.I), trivial⟩
      = (r : ℂ) * (y / ((r : ℂ) + Complex.I))
        - (-Complex.I) * (y / ((r : ℂ) + Complex.I)) := rfl
  rw [hstep]
  field_simp
  ring

/-- **The Cayley transform of `r • id` is multiplication by the Möbius scalar
`(r - i)/(r + i)`** (the scalar sanity anchor of the frozen spec). -/
theorem cayley_mulPMap_real_apply (r : ℝ) (y : (LinearPMap.cayley (mulPMap (r : ℂ))).domain) :
    LinearPMap.cayley (mulPMap (r : ℂ)) y
      = (((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I)) * (y : ℂ) := by
  have h := ofReal_add_I_ne_zero r
  have hxy : mulPMap (r : ℂ) ⟨(y : ℂ) / ((r : ℂ) + Complex.I), trivial⟩
      + Complex.I • (((y : ℂ) / ((r : ℂ) + Complex.I)) : ℂ) = (y : ℂ) := by
    rw [mulPMap_apply, smul_eq_mul]
    field_simp
  rw [(isSymmetric_mulPMap_real r).cayley_apply_eq hxy, mulPMap_apply, smul_eq_mul]
  field_simp

/-- **Degenerate expected-value anchor**: `cayley 0 = -id` — the transform of the zero
operator is multiplication by `(0 - i)/(0 + i) = -1`. -/
theorem cayley_mulPMap_zero_apply (y : (LinearPMap.cayley (mulPMap ((0 : ℝ) : ℂ))).domain) :
    LinearPMap.cayley (mulPMap ((0 : ℝ) : ℂ)) y = -(y : ℂ) := by
  rw [cayley_mulPMap_real_apply 0 y]
  norm_num

/-- The isometry of the proven `CayleyIsometric`, instantiated on the scalar model. -/
theorem norm_cayley_mulPMap_real (r : ℝ)
    (y : (LinearPMap.cayley (mulPMap (r : ℂ))).domain) :
    ‖LinearPMap.cayley (mulPMap (r : ℂ)) y‖ = ‖(y : ℂ)‖ :=
  (isSymmetric_mulPMap_real r).norm_cayley_apply y

/-- The Möbius scalar has unit modulus — extracted from the proven isometry
evaluated at `y = 1` (the concrete content of `CayleyIsometric` on this model). -/
theorem norm_mobius (r : ℝ) : ‖((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I)‖ = 1 := by
  have hy : (1 : ℂ) ∈ (LinearPMap.cayley (mulPMap (r : ℂ))).domain := by
    rw [cayley_mulPMap_real_domain]; trivial
  have h := norm_cayley_mulPMap_real r ⟨1, hy⟩
  rw [cayley_mulPMap_real_apply] at h
  simpa using h

/-- Non-vacuity for the proven `InverseCayleyCayley`: end-to-end recovery of `r • id`
from its Cayley transform, via the abstract theorem. -/
example (r : ℝ) :
    LinearPMap.inverseCayley (LinearPMap.cayley (mulPMap (r : ℂ))) = mulPMap (r : ℂ) :=
  inverseCayleyCayley ℂ _ (isSymmetric_mulPMap_real r)

/-- Non-vacuity for the proven `CayleySelfAdjointIffBijective` (forward): the Cayley
transform of the self-adjoint `r • id` is everywhere defined and surjective. -/
example (r : ℝ) :
    (LinearPMap.cayley (mulPMap (r : ℂ))).domain = ⊤ ∧
      LinearMap.range (LinearPMap.cayley (mulPMap (r : ℂ))).toFun = ⊤ :=
  (cayleySelfAdjointIffBijective ℂ (mulPMap (r : ℂ)) (mulPMap_dense _)
    (isSymmetric_mulPMap_real r)).mp (isSelfAdjoint_mulPMap_real r)

/-! ### The inverse transform of `μ • id` computed -/

/-- `μ • id - 1` is injective for `μ ≠ 1`: the no-eigenvalue-`1` condition on the
scalar model. -/
theorem ker_shift_mulPMap_one {μ : ℂ} (hμ : μ ≠ 1) :
    LinearMap.ker (LinearPMap.shift (mulPMap μ) 1).toFun = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have h : (LinearPMap.shift (mulPMap μ) 1).toFun x
      = μ * (x : ℂ) - (1 : ℂ) • (x : ℂ) := rfl
  rw [h, one_smul] at hx
  have h2 : (μ - 1) * (x : ℂ) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hμ
  · exact Subtype.ext h

/-- **The inverse Cayley transform of `μ • id` is multiplication by
`i(1 + μ)/(1 - μ)`**, for `μ ≠ 1`. -/
theorem inverseCayley_mulPMap_apply {μ : ℂ} (hμ : μ ≠ 1)
    (z : (LinearPMap.inverseCayley (mulPMap μ)).domain) :
    LinearPMap.inverseCayley (mulPMap μ) z
      = Complex.I * (1 + μ) / (1 - μ) * (z : ℂ) := by
  have hμ1 : μ - 1 ≠ 0 := sub_ne_zero.mpr hμ
  have h1μ : (1 : ℂ) - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ)
  have hxz : mulPMap μ ⟨(z : ℂ) / (μ - 1), trivial⟩ - (((z : ℂ) / (μ - 1)) : ℂ) = (z : ℂ) := by
    rw [mulPMap_apply]
    field_simp
  rw [LinearPMap.inverseCayley_apply_eq (ker_shift_mulPMap_one hμ) hxz, mulPMap_apply]
  have hc : ((⟨(z : ℂ) / (μ - 1), trivial⟩ : (mulPMap μ).domain) : ℂ)
      = (z : ℂ) / (μ - 1) := rfl
  rw [hc, smul_eq_mul]
  field_simp
  ring

/-- The recovered operator is everywhere defined: `ran (μ • id - 1) = ℂ` for `μ ≠ 1`. -/
theorem inverseCayley_mulPMap_domain {μ : ℂ} (hμ : μ ≠ 1) :
    (LinearPMap.inverseCayley (mulPMap μ)).domain = ⊤ := by
  have hμ1 : μ - 1 ≠ 0 := sub_ne_zero.mpr hμ
  rw [Submodule.eq_top_iff']
  intro z
  rw [LinearPMap.mem_inverseCayley_domain_iff]
  refine ⟨⟨z / (μ - 1), trivial⟩, ?_⟩
  rw [mulPMap_apply]
  have hc : ((⟨z / (μ - 1), trivial⟩ : (mulPMap μ).domain) : ℂ) = z / (μ - 1) := rfl
  rw [hc]
  field_simp

/-- **End-to-end Möbius recovery, computed by hand**: for `μ = (r - i)/(r + i)`,
`inverseCayley (μ • id) = r • id` pointwise — the concrete content of
`InverseCayleyCayley` on the scalar model. -/
theorem inverseCayley_cayley_mulPMap_real_apply (r : ℝ)
    (z : (LinearPMap.inverseCayley
      (mulPMap (((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I)))).domain) :
    LinearPMap.inverseCayley (mulPMap (((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I))) z
      = (r : ℂ) * (z : ℂ) := by
  rw [inverseCayley_mulPMap_apply (mobius_ne_one r) z, mobius_inverse]

/-! ### Wrong-sign refutation (expected-false witness) -/

/-- The WRONG-SIGN variant of the inverse transform, `+i • (x + U x)` on `(U - 1) x`:
refutation apparatus for the sign convention of the frozen `inverseCayley`. -/
def wrongInverseCayley (U : ℂ →ₗ.[ℂ] ℂ) : ℂ →ₗ.[ℂ] ℂ :=
  ⟨((LinearPMap.shift U 1).inverse).domain,
    Complex.I • ((2 : ℂ) • ((LinearPMap.shift U 1).inverse).toFun
      + ((LinearPMap.shift U 1).inverse).domain.subtype)⟩

theorem wrongInverseCayley_apply_eq {U : ℂ →ₗ.[ℂ] ℂ}
    (hU : LinearMap.ker (LinearPMap.shift U 1).toFun = ⊥)
    {z : (wrongInverseCayley U).domain} {x : U.domain} (hxz : U x - (x : ℂ) = z) :
    wrongInverseCayley U z = Complex.I • ((x : ℂ) + U x) := by
  have hinv : (LinearPMap.shift U 1).inverse z = x :=
    _root_.LinearPMap.inverse_apply_eq hU
      (by rw [LinearPMap.shift_apply U 1 x, one_smul]; exact hxz)
  show Complex.I • ((2 : ℂ) • (LinearPMap.shift U 1).inverse z + (z : ℂ))
      = Complex.I • ((x : ℂ) + U x)
  rw [hinv, ← hxz]
  module

theorem neg_I_ne_one : (-Complex.I : ℂ) ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  norm_num at this

/-- **Kernel refutation of the wrong sign** (expected-false): on the `μ = -i` model
(the Cayley transform of `1 • id`), the frozen `inverseCayley` returns `z` (correct:
the operator is `1 • id`) while the `+i` variant returns `-z ≠ z`. The "build on
`1 - U` with unchanged sign" variant computes the same `-r • z`, so this one
inequality refutes both wrong variants. -/
theorem wrongInverseCayley_ne :
    ∃ (z : (LinearPMap.inverseCayley (mulPMap (-Complex.I))).domain)
      (hz : (z : ℂ) ∈ (wrongInverseCayley (mulPMap (-Complex.I))).domain),
      LinearPMap.inverseCayley (mulPMap (-Complex.I)) z = (z : ℂ) ∧
      wrongInverseCayley (mulPMap (-Complex.I)) ⟨(z : ℂ), hz⟩ = -(z : ℂ) ∧
      (z : ℂ) ≠ -(z : ℂ) := by
  have h2 : (1 : ℂ) - -Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hxz : mulPMap (-Complex.I) ⟨(1 : ℂ), trivial⟩ - ((1 : ℂ) : ℂ)
      = (-Complex.I - 1 : ℂ) := by
    rw [mulPMap_apply]; ring
  have hzmem : (-Complex.I - 1 : ℂ)
      ∈ (LinearPMap.inverseCayley (mulPMap (-Complex.I))).domain :=
    LinearPMap.mem_inverseCayley_domain_iff.mpr ⟨⟨1, trivial⟩, hxz⟩
  refine ⟨⟨-Complex.I - 1, hzmem⟩, hzmem, ?_, ?_, ?_⟩
  · rw [inverseCayley_mulPMap_apply neg_I_ne_one ⟨-Complex.I - 1, hzmem⟩]
    have hval : Complex.I * (1 + -Complex.I) = 1 - -Complex.I := by
      linear_combination -Complex.I_sq
    rw [hval, div_self h2, one_mul]
  · rw [wrongInverseCayley_apply_eq (ker_shift_mulPMap_one neg_I_ne_one) hxz, mulPMap_apply,
      smul_eq_mul]
    show Complex.I * ((1 : ℂ) + -Complex.I * ((1 : ℂ) : ℂ)) = -(-Complex.I - 1)
    linear_combination -Complex.I_sq
  · intro h
    have := congrArg Complex.im h
    simp at this
    exact absurd this (by norm_num)

/-! ### The unitary side: `(-i) • id` as a concrete `unitary (ℂ →L[ℂ] ℂ)` element -/

theorem negI_smul_one_mem_unitary :
    (-Complex.I) • (1 : ℂ →L[ℂ] ℂ) ∈ unitary (ℂ →L[ℂ] ℂ) := by
  have hstar : star ((-Complex.I) • (1 : ℂ →L[ℂ] ℂ)) = Complex.I • 1 := by
    rw [star_smul, star_one, Complex.star_def, map_neg, Complex.conj_I, neg_neg]
  rw [Unitary.mem_iff, hstar]
  constructor
  · ext
    simp [Complex.I_mul_I]
  · ext
    simp [Complex.I_mul_I]

/-- The concrete unitary `(-i) • id` on `ℂ` — the Cayley transform of `1 • id`
(`μ = (1 - i)/(1 + i) = -i`). -/
def negIUnitary : unitary (ℂ →L[ℂ] ℂ) :=
  ⟨(-Complex.I) • 1, negI_smul_one_mem_unitary⟩

/-- `(-i) • id` has no eigenvalue `1`: `(1 - U) z = (1 + i) z` vanishes only at
`z = 0`. -/
theorem ker_one_sub_negIUnitary : (1 - (negIUnitary : ℂ →L[ℂ] ℂ)).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro z hz
  have h : z - -Complex.I * z = 0 := hz
  have h2 : (1 + Complex.I) * z = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · refine absurd h3 ?_
    intro hc
    have := congrArg Complex.im hc
    norm_num at this
  · exact h3

/-- Non-vacuity for the proven `InverseCayleySelfAdjoint`: the inverse Cayley
transform of the concrete unitary `(-i) • id` is self-adjoint (it is `1 • id`, per
`inverseCayley_cayley_mulPMap_real_apply` at `r = 1`). -/
example : IsSelfAdjoint (LinearPMap.inverseCayley
    (((negIUnitary : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ).toPMap ⊤)) :=
  inverseCayleySelfAdjoint ℂ negIUnitary ker_one_sub_negIUnitary

/-- Non-vacuity for the proven `CayleyInverseCayley`: the concrete unitary `(-i) • id`
is recovered as the Cayley transform of its inverse transform. -/
example : LinearPMap.cayley (LinearPMap.inverseCayley
      (((negIUnitary : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ).toPMap ⊤))
    = ((negIUnitary : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ).toPMap ⊤ :=
  cayleyInverseCayley ℂ negIUnitary ker_one_sub_negIUnitary

end OperatorTheory.Witnesses

end
