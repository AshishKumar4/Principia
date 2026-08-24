import Atlas

/-!
# P2.3c kernel probes — the Cayley transform on the scalar model

* **Node**: P2.3c (Cayley transform of a symmetric operator),
  `Atlas/Specs/OperatorTheory/Cayley.lean` + `Atlas/Proofs/CayleyTheory.lean`.
* **Original review**: 2026-07-10 (BLUEPRINT P2.3: "c `done` — spec frozen cc066e0;
  all seven targets proven 2026-07-10, full von Neumann Cayley correspondence"). The
  probe file of that review lived in a session-temporary scratchpad and was lost; this
  file is the X.3 backfill (`audits/README.md`), re-created 2026-08-23.
* **What it refutes**: the *wrong-sign inverse transform*. The frozen `inverseCayley`
  sends `(U - 1) x ↦ -i • (x + U x)`; the `+i` variant (equivalently: building on
  `1 - U` while keeping the sign) is refuted here by a **computed inequality** — on the
  `μ = -i` model the frozen map returns `z` and the variant returns `-z`, and
  `z ≠ -z` for the probe's concrete `z = -i - 1` (`probe_wrong_inverse_ne`). It also
  refutes the *transposed direction convention* `(A + i)(A - i)⁻¹`: on the `r = 1`
  model the frozen transform gives `-i` while the transposed one gives `+i`, and
  `-i ≠ i` (`probe_direction_convention`).

## What is checked, and how independently

The model is built here, not imported: `probeMul z = z • id` on `ℂ` as a total
`LinearPMap`, with its own symmetry proof. Only the frozen spec API
(`LinearPMap.cayley`, `IsSymmetric.cayley_apply_eq`, `LinearPMap.inverseCayley`,
`LinearPMap.inverseCayley_apply_eq`, `LinearPMap.mem_inverseCayley_domain_iff`) and the
proved targets (`inverseCayleyCayley`, `IsSymmetric.norm_cayley_apply`) are used, so
this file is independent of `Atlas/Witnesses/CayleyScalar.lean`.

* `probe_cayley_domain`, `probe_cayley_apply` — the forward transform of the
  self-adjoint `r • id` is total, and is multiplication by the Möbius scalar
  `(r - i)/(r + i)`;
* `probe_norm_mobius` — that scalar has modulus `1`, obtained from the *proved*
  isometry evaluated at `y = 1` (a cross-check of the proof layer against the hand
  computation, not a restatement of it);
* `probe_inverseCayley_apply` — the inverse transform of `μ • id` is multiplication by
  `i(1 + μ)/(1 - μ)` for `μ ≠ 1`;
* `probe_roundtrip_apply` — the composite: `inverseCayley ((r - i)/(r + i) • id)` acts
  as `r • id`, i.e. the Möbius roundtrip closes;
* `probe_roundtrip_abstract` — the same recovery via the proved `InverseCayleyCayley`,
  agreeing with the pointwise computation;
* `probe_wrong_inverse_ne` — the sign refutation (see above).

## Sources

* W. Rudin, *Functional Analysis*, 2nd ed. (1991), ch. 13, Thm 13.19 (the Cayley
  transform `U = (A - iI)(A + iI)⁻¹`, isometry, injectivity of `I - U`, recovery
  `A = i(I + U)(I - U)⁻¹`).
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II: Fourier Analysis,
  Self-Adjointness* (1975), §X.1 (Cayley transform and the deficiency subspaces).
* J. von Neumann, "Allgemeine Eigenwerttheorie Hermitescher Funktionaloperatoren",
  *Math. Ann.* 102 (1930), 49–131.

Theorem/section numbers are quoted from the source list of the frozen spec
`Atlas/Specs/OperatorTheory/Cayley.lean`; they were not re-checked against the printed
editions in this backfill.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.3c/` only; compiles via
`lake env lean audits/probes/P2.3c/cayley_scalar_probe.lean`.
-/

open OperatorTheory

noncomputable section

namespace P23cProbe

/-! ## The probe's model: multiplication by a scalar on `ℂ` -/

/-- Multiplication by `z : ℂ` on `ℂ`, as a total `LinearPMap`. Built here so that the
probe does not inherit anything from the witness files. -/
def probeMul (z : ℂ) : ℂ →ₗ.[ℂ] ℂ := (z • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).toPMap ⊤

@[simp] theorem probeMul_domain (z : ℂ) : (probeMul z).domain = ⊤ := rfl

@[simp] theorem probeMul_apply (z : ℂ) (x : (probeMul z).domain) :
    probeMul z x = z * (x : ℂ) := rfl

/-- Multiplication by a real scalar is symmetric — the hypothesis of every frozen
statement used below. -/
theorem probe_isSymmetric_real (r : ℝ) : LinearPMap.IsSymmetric (probeMul (r : ℂ)) := by
  intro x y
  simp only [probeMul_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-! ## Scalar arithmetic of the Möbius map -/

theorem probe_ofReal_add_I_ne_zero (r : ℝ) : (r : ℂ) + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

theorem probe_mobius_ne_one (r : ℝ) :
    ((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I) ≠ 1 := by
  intro h
  rw [div_eq_one_iff_eq (probe_ofReal_add_I_ne_zero r)] at h
  have := congrArg Complex.im h
  norm_num at this

/-- `i(1 + μ)/(1 - μ) = r` for `μ = (r - i)/(r + i)`: the inverse Möbius map returns
the multiplier. -/
theorem probe_mobius_inverse (r : ℝ) :
    Complex.I * (1 + ((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I))
      / (1 - ((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I)) = (r : ℂ) := by
  have h := probe_ofReal_add_I_ne_zero r
  have h1 : (1 : ℂ) - ((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (probe_mobius_ne_one r))
  rw [div_eq_iff h1]
  field_simp
  ring

/-! ## The forward transform -/

/-- `ran (A + i) = ℂ` for `A = r • id`: the Cayley transform is everywhere defined. -/
theorem probe_cayley_domain (r : ℝ) :
    (LinearPMap.cayley (probeMul (r : ℂ))).domain = ⊤ := by
  rw [LinearPMap.cayley_domain, LinearMap.range_eq_top]
  intro y
  have h := probe_ofReal_add_I_ne_zero r
  refine ⟨⟨y / ((r : ℂ) + Complex.I), trivial⟩, ?_⟩
  have hstep : (LinearPMap.shift (probeMul (r : ℂ)) (-Complex.I)).toFun
        ⟨y / ((r : ℂ) + Complex.I), trivial⟩
      = (r : ℂ) * (y / ((r : ℂ) + Complex.I))
        - (-Complex.I) * (y / ((r : ℂ) + Complex.I)) := rfl
  rw [hstep]
  field_simp
  ring

/-- **The forward computation**: `cayley (r • id)` is multiplication by
`(r - i)/(r + i)` (Rudin, Thm 13.19, on the one-dimensional model). -/
theorem probe_cayley_apply (r : ℝ)
    (y : (LinearPMap.cayley (probeMul (r : ℂ))).domain) :
    LinearPMap.cayley (probeMul (r : ℂ)) y
      = (((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I)) * (y : ℂ) := by
  have h := probe_ofReal_add_I_ne_zero r
  have hxy : probeMul (r : ℂ) ⟨(y : ℂ) / ((r : ℂ) + Complex.I), trivial⟩
      + Complex.I • (((y : ℂ) / ((r : ℂ) + Complex.I)) : ℂ) = (y : ℂ) := by
    rw [probeMul_apply, smul_eq_mul]
    field_simp
  rw [(probe_isSymmetric_real r).cayley_apply_eq hxy, probeMul_apply, smul_eq_mul]
  field_simp

/-- **Degenerate anchor**: `cayley 0 = -id`, since `(0 - i)/(0 + i) = -1`. -/
theorem probe_cayley_zero_apply
    (y : (LinearPMap.cayley (probeMul ((0 : ℝ) : ℂ))).domain) :
    LinearPMap.cayley (probeMul ((0 : ℝ) : ℂ)) y = -(y : ℂ) := by
  rw [probe_cayley_apply 0 y]
  norm_num

/-- **Unit modulus, from the proved isometry**: `‖(r - i)/(r + i)‖ = 1`. The value is
extracted by evaluating `IsSymmetric.norm_cayley_apply` at `y = 1` and comparing with
the hand computation `probe_cayley_apply` — a cross-check of the proof layer against
the scalar arithmetic. -/
theorem probe_norm_mobius (r : ℝ) :
    ‖((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I)‖ = 1 := by
  have hy : (1 : ℂ) ∈ (LinearPMap.cayley (probeMul (r : ℂ))).domain := by
    rw [probe_cayley_domain]; trivial
  have h := (probe_isSymmetric_real r).norm_cayley_apply ⟨1, hy⟩
  rw [probe_cayley_apply] at h
  simpa using h

/-! ### The direction convention, refuted on the `r = 1` model -/

theorem probe_mobius_one :
    (((1 : ℝ) : ℂ) - Complex.I) / (((1 : ℝ) : ℂ) + Complex.I) = -Complex.I := by
  have h := probe_ofReal_add_I_ne_zero 1
  rw [div_eq_iff h]
  push_cast
  linear_combination Complex.I_sq

theorem probe_mobius_one_transposed :
    (((1 : ℝ) : ℂ) + Complex.I) / (((1 : ℝ) : ℂ) - Complex.I) = Complex.I := by
  have h : ((1 : ℝ) : ℂ) - Complex.I ≠ 0 := by
    intro hc
    have := congrArg Complex.im hc
    simp at this
  rw [div_eq_iff h]
  push_cast
  linear_combination Complex.I_sq

theorem probe_neg_I_ne_I : (-Complex.I : ℂ) ≠ Complex.I := by
  intro h
  have him := congrArg Complex.im h
  norm_num at him

/-- **The transposed direction convention, refuted**: Rudin's `(A - i)(A + i)⁻¹` sends
`1 • id` to `-i`, whereas the transposed assignment `(A + i)(A - i)⁻¹` would send it to
`+i`; and `-i ≠ i`. So the frozen direction is a decision with observable content, not
a spelling. -/
theorem probe_direction_convention :
    ∃ hy : (1 : ℂ) ∈ (LinearPMap.cayley (probeMul ((1 : ℝ) : ℂ))).domain,
      LinearPMap.cayley (probeMul ((1 : ℝ) : ℂ)) ⟨1, hy⟩ = -Complex.I ∧
      (((1 : ℝ) : ℂ) + Complex.I) / (((1 : ℝ) : ℂ) - Complex.I) = Complex.I ∧
      (-Complex.I : ℂ) ≠ Complex.I := by
  have hy : (1 : ℂ) ∈ (LinearPMap.cayley (probeMul ((1 : ℝ) : ℂ))).domain := by
    rw [probe_cayley_domain]; trivial
  refine ⟨hy, ?_, probe_mobius_one_transposed, probe_neg_I_ne_I⟩
  rw [probe_cayley_apply 1 ⟨1, hy⟩, probe_mobius_one, mul_one]

/-! ## The inverse transform -/

/-- `μ • id - 1` is injective for `μ ≠ 1`: the no-eigenvalue-`1` hypothesis, computed on
the model. -/
theorem probe_ker_shift_one {μ : ℂ} (hμ : μ ≠ 1) :
    LinearMap.ker (LinearPMap.shift (probeMul μ) 1).toFun = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have h : (LinearPMap.shift (probeMul μ) 1).toFun x
      = μ * (x : ℂ) - (1 : ℂ) • (x : ℂ) := rfl
  rw [h, one_smul] at hx
  have h2 : (μ - 1) * (x : ℂ) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hμ
  · exact Subtype.ext h

/-- **The inverse computation**: `inverseCayley (μ • id)` is multiplication by
`i(1 + μ)/(1 - μ)` for `μ ≠ 1` (Rudin, Thm 13.19: `A = i(I + U)(I - U)⁻¹`). -/
theorem probe_inverseCayley_apply {μ : ℂ} (hμ : μ ≠ 1)
    (z : (LinearPMap.inverseCayley (probeMul μ)).domain) :
    LinearPMap.inverseCayley (probeMul μ) z
      = Complex.I * (1 + μ) / (1 - μ) * (z : ℂ) := by
  have hμ1 : μ - 1 ≠ 0 := sub_ne_zero.mpr hμ
  have h1μ : (1 : ℂ) - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ)
  have hxz : probeMul μ ⟨(z : ℂ) / (μ - 1), trivial⟩ - (((z : ℂ) / (μ - 1)) : ℂ)
      = (z : ℂ) := by
    rw [probeMul_apply]
    field_simp
  rw [LinearPMap.inverseCayley_apply_eq (probe_ker_shift_one hμ) hxz, probeMul_apply]
  have hc : ((⟨(z : ℂ) / (μ - 1), trivial⟩ : (probeMul μ).domain) : ℂ)
      = (z : ℂ) / (μ - 1) := rfl
  rw [hc, smul_eq_mul]
  field_simp
  ring

/-- `ran (μ • id - 1) = ℂ` for `μ ≠ 1`: the recovered operator is everywhere defined. -/
theorem probe_inverseCayley_domain {μ : ℂ} (hμ : μ ≠ 1) :
    (LinearPMap.inverseCayley (probeMul μ)).domain = ⊤ := by
  have hμ1 : μ - 1 ≠ 0 := sub_ne_zero.mpr hμ
  rw [Submodule.eq_top_iff']
  intro z
  rw [LinearPMap.mem_inverseCayley_domain_iff]
  refine ⟨⟨z / (μ - 1), trivial⟩, ?_⟩
  rw [probeMul_apply]
  have hc : ((⟨z / (μ - 1), trivial⟩ : (probeMul μ).domain) : ℂ) = z / (μ - 1) := rfl
  rw [hc]
  field_simp

/-- **The roundtrip, computed**: for `μ = (r - i)/(r + i)`, `inverseCayley (μ • id)`
acts as `r • id`. Forward and inverse Möbius maps compose to the identity, in the
kernel. -/
theorem probe_roundtrip_apply (r : ℝ)
    (z : (LinearPMap.inverseCayley
      (probeMul (((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I)))).domain) :
    LinearPMap.inverseCayley (probeMul (((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I))) z
      = (r : ℂ) * (z : ℂ) := by
  rw [probe_inverseCayley_apply (probe_mobius_ne_one r) z, probe_mobius_inverse]

/-- **The roundtrip, abstractly**: the proved `InverseCayleyCayley` recovers the model
operator itself. Together with `probe_roundtrip_apply` (which computes the same
recovery by hand through the Möbius scalar) this pins the direction convention of the
frozen transform. -/
theorem probe_roundtrip_abstract (r : ℝ) :
    LinearPMap.inverseCayley (LinearPMap.cayley (probeMul (r : ℂ))) = probeMul (r : ℂ) :=
  inverseCayleyCayley ℂ _ (probe_isSymmetric_real r)

/-! ## The wrong-sign refutation -/

/-- The WRONG-SIGN variant of the inverse transform: `+i • (x + U x)` on `(U - 1) x`,
where the frozen `inverseCayley` has `-i`. Written in resolvent form, as the frozen
definition is. -/
def probeWrongInverse (U : ℂ →ₗ.[ℂ] ℂ) : ℂ →ₗ.[ℂ] ℂ :=
  ⟨((LinearPMap.shift U 1).inverse).domain,
    Complex.I • ((2 : ℂ) • ((LinearPMap.shift U 1).inverse).toFun
      + ((LinearPMap.shift U 1).inverse).domain.subtype)⟩

theorem probeWrongInverse_apply_eq {U : ℂ →ₗ.[ℂ] ℂ}
    (hU : LinearMap.ker (LinearPMap.shift U 1).toFun = ⊥)
    {z : (probeWrongInverse U).domain} {x : U.domain} (hxz : U x - (x : ℂ) = z) :
    probeWrongInverse U z = Complex.I • ((x : ℂ) + U x) := by
  have hinv : (LinearPMap.shift U 1).inverse z = x :=
    _root_.LinearPMap.inverse_apply_eq hU
      (by rw [LinearPMap.shift_apply U 1 x, one_smul]; exact hxz)
  show Complex.I • ((2 : ℂ) • (LinearPMap.shift U 1).inverse z + (z : ℂ))
      = Complex.I • ((x : ℂ) + U x)
  rw [hinv, ← hxz]
  module

theorem probe_neg_I_ne_one : (-Complex.I : ℂ) ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  norm_num at this

/-- **The sign refutation, by computed inequality**: on the `μ = -i` model (which is
`cayley (1 • id)`, since `(1 - i)/(1 + i) = -i`) the frozen `inverseCayley` returns
`z` — correct, the operator is `1 • id` — while the `+i` variant returns `-z`; and
`z ≠ -z` at the probe's concrete `z = -i - 1`. So the `-i` of the frozen
`inverseCayley` is forced, not conventional. The "build on `1 - U` with unchanged
sign" variant computes the same `-z`, so this single inequality refutes both. -/
theorem probe_wrong_inverse_ne :
    ∃ (z : (LinearPMap.inverseCayley (probeMul (-Complex.I))).domain)
      (hz : (z : ℂ) ∈ (probeWrongInverse (probeMul (-Complex.I))).domain),
      LinearPMap.inverseCayley (probeMul (-Complex.I)) z = (z : ℂ) ∧
      probeWrongInverse (probeMul (-Complex.I)) ⟨(z : ℂ), hz⟩ = -(z : ℂ) ∧
      (z : ℂ) ≠ -(z : ℂ) := by
  have h2 : (1 : ℂ) - -Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hxz : probeMul (-Complex.I) ⟨(1 : ℂ), trivial⟩ - ((1 : ℂ) : ℂ)
      = (-Complex.I - 1 : ℂ) := by
    rw [probeMul_apply]; ring
  have hzmem : (-Complex.I - 1 : ℂ)
      ∈ (LinearPMap.inverseCayley (probeMul (-Complex.I))).domain :=
    LinearPMap.mem_inverseCayley_domain_iff.mpr ⟨⟨1, trivial⟩, hxz⟩
  refine ⟨⟨-Complex.I - 1, hzmem⟩, hzmem, ?_, ?_, ?_⟩
  · rw [probe_inverseCayley_apply probe_neg_I_ne_one ⟨-Complex.I - 1, hzmem⟩]
    have hval : Complex.I * (1 + -Complex.I) = 1 - -Complex.I := by
      linear_combination -Complex.I_sq
    rw [hval, div_self h2, one_mul]
  · rw [probeWrongInverse_apply_eq (probe_ker_shift_one probe_neg_I_ne_one) hxz,
      probeMul_apply, smul_eq_mul]
    show Complex.I * ((1 : ℂ) + -Complex.I * ((1 : ℂ) : ℂ)) = -(-Complex.I - 1)
    linear_combination -Complex.I_sq
  · intro h
    have := congrArg Complex.im h
    simp at this
    exact absurd this (by norm_num)

end P23cProbe

end
