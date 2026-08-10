import Atlas.Specs.Spacetime.Poincare

/-!
# P2.4W — non-vacuity witnesses for the restricted Lorentz and Poincaré groups

Witness (blueprint node P2.4W) that the frozen P2.4a spec
`Atlas/Specs/Spacetime/Poincare.lean` is non-vacuous well beyond the identity: it
exhibits concrete rotations and boosts inside `RestrictedLorentzGroup`, concrete
non-identity elements of `PoincareGroup` on which the semidirect twist is visible, and
concrete mass-shell membership under those elements. It also exhibits the expected-false
side: parity and total inversion each satisfy two of the three membership conditions and
fail the third, so the determinant and orthochronicity conditions of the frozen spec each
exclude a map satisfying the other two — neither is decorative. (No automorphism violating
*only* the form condition is exhibited; every map in this file is form-preserving.)

## Contents

* `reflectCLM` / `reflectEquiv` — the reflection in the `i`-th coordinate hyperplane; it
  preserves `minkowskiForm` (the form is diagonal) but has determinant `-1`. The single
  construction from which the rotation below is assembled, and the source of the
  expected-false `reflectEquiv 1 ∉ RestrictedLorentzGroup` (parity is improper: it is
  excluded from `L↑₊` by the determinant condition alone, since it *is* orthochronous
  and form-preserving).
* `totalInversionEquiv` — `PT`, `x ↦ -x`: form-preserving and proper (`det = (-1)⁴ = 1`
  in four dimensions), excluded from `L↑₊` by orthochronicity alone.
* `RestrictedLorentzGroup.rotation12` — the spatial `π`-rotation `diag(1, -1, -1, 1)` in
  the `(1,2)`-plane, as a member: all three conditions, `≠ 1`, and `R * R = 1`.
* `RestrictedLorentzGroup.boost` — the `x¹`-boost family `(c, s)` with `c² - s² = 1`,
  `0 < c` (i.e. `c = cosh χ`, `s = sinh χ`), as members; `RestrictedLorentzGroup.boost35`
  is the rational instance `c = 5/4`, `s = 3/4` (velocity `β = 3/5`, `γ = 5/4`), with
  `≠ 1`, its inverse `(c, -s)`, `≠` its own inverse, and the rapidity-addition law
  `boost c s * boost c' s' = boost (cc' + ss') (cs' + sc')`, instantiated at
  `boost35 * boost35 = boost (17/8) (15/8)`. Qualitatively this is also why `L↑₊` is
  non-compact — the boosts form an unbounded one-parameter family — but no compactness
  claim is made or proved here.
* `PoincareGroup.translationE1` / `rotationOnly` / `boostTranslate` — translation-only,
  rotation-only and mixed elements, with the semidirect twist exercised
  (`rotationOnly * translationE1 ≠ translationE1 * rotationOnly`, both products computed),
  the `MulAction` evaluated on both orders, and the inverse of a mixed element computed
  in closed form.
* Mass shells: `e₀ ∈ massShell 1`, its images under the rotation and the boost computed
  explicitly and checked to lie on the shell both via
  `RestrictedLorentzGroup.map_massShell` and by direct computation of the form; and the
  expected-false that the *affine* action of a translation does not preserve mass shells
  — only the homogeneous part does, which is exactly what the frozen theorem asserts.

## Attribution

The rotation and mass-shell material adapts the committed reviewer probes
`audits/probes/P2.4a/rot12_member_probe.lean` and
`audits/probes/P2.4a/massshell_poincare_probe.lean` (Workflow v2 audit artifacts); the
determinant route (`LinearMap.toMatrix` in `PiLp.basisFun` + `Matrix.det`) is theirs,
factored here into the reusable `det_eq_matrix_det`. The reflection/boost families and
the Poincaré computations are new.

## Sources

* Streater & Wightman, *PCT, Spin and Statistics, and All That* (1964; Princeton
  Landmarks ed. 2000), §1-1 (`L↑₊`; the proper orthochronous conditions, which the
  members below are checked against).
* Weinberg, *The Quantum Theory of Fields*, Vol. I (1995), §2.3 (boosts and rotations as
  the generators of `L↑₊`; composition law), §2.5 (mass shells / one-particle orbits).
-/

namespace Spacetime.Minkowski

noncomputable section

/-- Application of the identity of the automorphism group `M4 ≃L[ℝ] M4`; `rfl`, restated
here because the spec's copy is `private` (upstream candidate: Mathlib has no
`one_apply` for `ContinuousLinearEquiv.automorphismGroup` at v4.31.0). -/
private theorem clm_one_apply (x : M4) : (1 : M4 ≃L[ℝ] M4) x = x := rfl

private theorem single_apply_self (i : Fin 4) :
    (EuclideanSpace.single i (1 : ℝ) : M4) i = 1 := by
  rw [PiLp.single_apply, if_pos rfl]

private theorem single_apply_of_ne {i j : Fin 4} (h : j ≠ i) :
    (EuclideanSpace.single i (1 : ℝ) : M4) j = 0 := by
  rw [PiLp.single_apply, if_neg h]

/-- The frozen determinant spelling — `LinearMap.det` of the coerced `toLinearEquiv` —
of a concrete automorphism, read off from its matrix in the standard basis. Adapted from
the reviewer probe `audits/probes/P2.4a/rot12_member_probe.lean`. -/
private theorem det_eq_matrix_det (f : M4 ≃L[ℝ] M4) (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : ∀ i j, f (EuclideanSpace.single j (1 : ℝ)) i = A i j) :
    LinearMap.det (f.toLinearEquiv : M4 →ₗ[ℝ] M4) = A.det := by
  have hmat : LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin 4)) (PiLp.basisFun 2 ℝ (Fin 4))
      (f.toLinearEquiv : M4 →ₗ[ℝ] M4) = A := by
    ext i j
    rw [LinearMap.toMatrix_apply, PiLp.basisFun_apply, PiLp.basisFun_repr]
    exact hA i j
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 4)), hmat]

/-! ### Coordinate reflections: form-preserving, determinant `-1` -/

/-- Reflection in the `i`-th coordinate hyperplane: `x ↦ x - 2xⁱ eᵢ`. -/
def reflectCLM (i : Fin 4) : M4 →L[ℝ] M4 :=
  ContinuousLinearMap.id ℝ M4
    - (2 : ℝ) • ((EuclideanSpace.proj i).smulRight (EuclideanSpace.single i 1))

theorem reflectCLM_apply (i : Fin 4) (x : M4) (j : Fin 4) :
    reflectCLM i x j = if j = i then -x j else x j := by
  have h : reflectCLM i x
      = x - (2 : ℝ) • (x i • (EuclideanSpace.single i (1 : ℝ) : M4)) := rfl
  rw [h]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  split_ifs with hj
  · subst hj; ring
  · ring

theorem reflectCLM_involutive (i : Fin 4) (x : M4) : reflectCLM i (reflectCLM i x) = x := by
  ext j
  rw [reflectCLM_apply, reflectCLM_apply]
  split_ifs <;> ring

/-- A coordinate reflection preserves the Minkowski form: `η` is diagonal, so flipping
one coordinate in both arguments leaves every term of `η(v, w)` unchanged. True for the
time reflection `i = 0` as well — reflections fail to be restricted Lorentz
transformations on the determinant (and, for `i = 0`, orthochronicity), never on the
form. -/
theorem reflectCLM_form (i : Fin 4) (v w : M4) :
    minkowskiForm (reflectCLM i v) (reflectCLM i w) = minkowskiForm v w := by
  have key : ∀ j, reflectCLM i v j * reflectCLM i w j = v j * w j := fun j => by
    rw [reflectCLM_apply, reflectCLM_apply]; split_ifs <;> ring
  rw [minkowskiForm_eq, minkowskiForm_eq, key 0, key 1, key 2, key 3]

/-- The reflection as a continuous linear automorphism of `M4`. -/
def reflectEquiv (i : Fin 4) : M4 ≃L[ℝ] M4 where
  toFun := reflectCLM i
  map_add' := map_add (reflectCLM i)
  map_smul' := map_smul (reflectCLM i)
  invFun := reflectCLM i
  left_inv := reflectCLM_involutive i
  right_inv := reflectCLM_involutive i
  continuous_toFun := (reflectCLM i).continuous
  continuous_invFun := (reflectCLM i).continuous

theorem reflectEquiv_apply (i : Fin 4) (x : M4) : reflectEquiv i x = reflectCLM i x := rfl

theorem reflectEquiv_det (i : Fin 4) :
    LinearMap.det ((reflectEquiv i).toLinearEquiv : M4 →ₗ[ℝ] M4) = -1 := by
  have hA : ∀ j k : Fin 4, reflectEquiv i (EuclideanSpace.single k (1 : ℝ)) j
      = Matrix.diagonal (fun l : Fin 4 => if l = i then (-1 : ℝ) else 1) j k := by
    intro j k
    rw [reflectEquiv_apply, reflectCLM_apply, Matrix.diagonal_apply, PiLp.single_apply]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [hjk]
  rw [det_eq_matrix_det _ _ hA, Matrix.det_diagonal]
  simp

theorem reflectEquiv_one_orthochronous :
    0 < reflectEquiv 1 (EuclideanSpace.single 0 1) 0 := by
  rw [reflectEquiv_apply, reflectCLM_apply, if_neg (by decide : ¬((0 : Fin 4) = 1)),
    single_apply_self]
  norm_num

/-- **Expected false**: a spatial reflection is *not* a restricted Lorentz
transformation. It preserves the form (`reflectCLM_form`) and is orthochronous
(`reflectEquiv_one_orthochronous`); it fails only `det = 1`. Parity is improper, and the
determinant condition of the frozen spec is exactly what excludes it — that condition is
therefore not decorative. -/
theorem reflectEquiv_one_not_mem : reflectEquiv 1 ∉ RestrictedLorentzGroup := by
  intro h
  have hdet := h.2.1
  rw [reflectEquiv_det] at hdet
  norm_num at hdet

/-! ### Total inversion `diag(-1, -1, -1, -1)` -/

/-- Total inversion `x ↦ -x`, i.e. `PT`. -/
def totalInversionEquiv : M4 ≃L[ℝ] M4 := ContinuousLinearEquiv.neg ℝ

theorem totalInversionEquiv_apply (x : M4) : totalInversionEquiv x = -x := rfl

theorem totalInversionEquiv_form (v w : M4) :
    minkowskiForm (totalInversionEquiv v) (totalInversionEquiv w) = minkowskiForm v w := by
  rw [totalInversionEquiv_apply, totalInversionEquiv_apply, minkowskiForm_eq,
    minkowskiForm_eq]
  simp only [PiLp.neg_apply]
  ring

/-- In four dimensions total inversion is proper: `det(-1) = (-1)⁴ = 1`. -/
theorem totalInversionEquiv_det :
    LinearMap.det (totalInversionEquiv.toLinearEquiv : M4 →ₗ[ℝ] M4) = 1 := by
  have hA : ∀ j k : Fin 4, totalInversionEquiv (EuclideanSpace.single k (1 : ℝ)) j
      = Matrix.diagonal (fun _ : Fin 4 => (-1 : ℝ)) j k := by
    intro j k
    rw [totalInversionEquiv_apply, PiLp.neg_apply, Matrix.diagonal_apply, PiLp.single_apply]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [hjk]
  rw [det_eq_matrix_det _ _ hA, Matrix.det_diagonal]
  norm_num

/-- **Expected false**: total inversion is *not* a restricted Lorentz transformation. It
preserves the form and is proper (`det = 1`); it fails only orthochronicity, reversing the
time direction. Together with `reflectEquiv_one_not_mem` this shows the determinant and
orthochronicity conditions of the frozen spec each exclude a map satisfying the other
two: neither is decorative. -/
theorem totalInversionEquiv_not_mem : totalInversionEquiv ∉ RestrictedLorentzGroup := by
  intro h
  have horth := h.2.2
  rw [totalInversionEquiv_apply, PiLp.neg_apply, single_apply_self] at horth
  norm_num at horth

/-! ### The spatial `π`-rotation `diag(1, -1, -1, 1)`

Adapted from the reviewer probe `audits/probes/P2.4a/rot12_member_probe.lean`, with the
map built as the composite of the two coordinate reflections it is. -/

/-- The `π`-rotation in the `(1,2)`-plane, `diag(1, -1, -1, 1)`. -/
def rotation12Equiv : M4 ≃L[ℝ] M4 := reflectEquiv 1 * reflectEquiv 2

theorem rotation12Equiv_apply (x : M4) (j : Fin 4) :
    rotation12Equiv x j = reflectCLM 1 (reflectCLM 2 x) j := rfl

theorem rotation12Equiv_apply_zero (x : M4) : rotation12Equiv x 0 = x 0 := by
  rw [rotation12Equiv_apply, reflectCLM_apply, if_neg (by decide : ¬((0 : Fin 4) = 1)),
    reflectCLM_apply, if_neg (by decide : ¬((0 : Fin 4) = 2))]

theorem rotation12Equiv_apply_one (x : M4) : rotation12Equiv x 1 = -x 1 := by
  rw [rotation12Equiv_apply, reflectCLM_apply, if_pos rfl, reflectCLM_apply,
    if_neg (by decide : ¬((1 : Fin 4) = 2))]

theorem rotation12Equiv_apply_two (x : M4) : rotation12Equiv x 2 = -x 2 := by
  rw [rotation12Equiv_apply, reflectCLM_apply, if_neg (by decide : ¬((2 : Fin 4) = 1)),
    reflectCLM_apply, if_pos rfl]

theorem rotation12Equiv_apply_three (x : M4) : rotation12Equiv x 3 = x 3 := by
  rw [rotation12Equiv_apply, reflectCLM_apply, if_neg (by decide : ¬((3 : Fin 4) = 1)),
    reflectCLM_apply, if_neg (by decide : ¬((3 : Fin 4) = 2))]

theorem rotation12Equiv_form (v w : M4) :
    minkowskiForm (rotation12Equiv v) (rotation12Equiv w) = minkowskiForm v w := by
  show minkowskiForm (reflectCLM 1 (reflectCLM 2 v)) (reflectCLM 1 (reflectCLM 2 w)) = _
  rw [reflectCLM_form, reflectCLM_form]

theorem rotation12Equiv_det :
    LinearMap.det (rotation12Equiv.toLinearEquiv : M4 →ₗ[ℝ] M4) = 1 := by
  have h : (rotation12Equiv.toLinearEquiv : M4 →ₗ[ℝ] M4)
      = ((reflectEquiv 1).toLinearEquiv : M4 →ₗ[ℝ] M4).comp
        ((reflectEquiv 2).toLinearEquiv : M4 →ₗ[ℝ] M4) := rfl
  rw [h, LinearMap.det_comp, reflectEquiv_det, reflectEquiv_det]
  norm_num

theorem rotation12Equiv_orthochronous :
    0 < rotation12Equiv (EuclideanSpace.single 0 1) 0 := by
  rw [rotation12Equiv_apply_zero, single_apply_self]
  norm_num

theorem rotation12Equiv_mem : rotation12Equiv ∈ RestrictedLorentzGroup :=
  ⟨rotation12Equiv_form, rotation12Equiv_det, rotation12Equiv_orthochronous⟩

theorem rotation12Equiv_single_one :
    rotation12Equiv (EuclideanSpace.single 1 1) = -(EuclideanSpace.single 1 (1 : ℝ) : M4) := by
  ext j
  rw [PiLp.neg_apply, rotation12Equiv_apply, reflectCLM_apply, reflectCLM_apply,
    PiLp.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all

namespace RestrictedLorentzGroup

/-- The spatial `π`-rotation `diag(1, -1, -1, 1)` as an element of `L↑₊`. -/
def rotation12 : RestrictedLorentzGroup := ⟨rotation12Equiv, rotation12Equiv_mem⟩

@[simp] theorem coe_rotation12 : (rotation12 : M4 ≃L[ℝ] M4) = rotation12Equiv := rfl

/-- **Expected false** (non-triviality): the rotation is not the identity of `L↑₊`. -/
theorem rotation12_ne_one : rotation12 ≠ 1 := by
  intro h
  have hco : rotation12Equiv (EuclideanSpace.single 1 1)
      = ((1 : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) (EuclideanSpace.single 1 1) := by
    rw [← coe_rotation12, h]
  rw [rotation12Equiv_single_one] at hco
  have h1 := congrArg (fun z : M4 => z 1) hco
  simp only [PiLp.neg_apply] at h1
  rw [single_apply_self] at h1
  norm_num [clm_one_apply] at h1

/-- The rotation has order `2` in `L↑₊`: it is a genuine involution of the group, not
just of the underlying map. -/
theorem rotation12_mul_self : rotation12 * rotation12 = 1 :=
  Subtype.ext (ContinuousLinearEquiv.ext (funext fun x => by
    show reflectCLM 1 (reflectCLM 2 (reflectCLM 1 (reflectCLM 2 x))) = x
    ext j
    rw [reflectCLM_apply, reflectCLM_apply, reflectCLM_apply, reflectCLM_apply]
    split_ifs <;> ring))

end RestrictedLorentzGroup

/-! ### Boosts

The `x¹`-boost of rapidity `χ` is `diag`-free: it mixes the `0` and `1` coordinates by
`(c, s) = (cosh χ, sinh χ)`, `c² - s² = 1`. The family is parametrized by `(c, s)`
directly, so that rational instances (here `c = 5/4`, `s = 3/4`, i.e. velocity `β = 3/5`)
keep the kernel arithmetic exact. -/

/-- The `x¹`-boost with `(cosh χ, sinh χ) = (c, s)`:
`x⁰ ↦ c x⁰ + s x¹`, `x¹ ↦ s x⁰ + c x¹`, `x²`, `x³` fixed. -/
def boostCLM (c s : ℝ) : M4 →L[ℝ] M4 :=
  ContinuousLinearMap.id ℝ M4
    + (c - 1) • ((EuclideanSpace.proj (0 : Fin 4)).smulRight (EuclideanSpace.single 0 1))
    + s • ((EuclideanSpace.proj (1 : Fin 4)).smulRight (EuclideanSpace.single 0 1))
    + s • ((EuclideanSpace.proj (0 : Fin 4)).smulRight (EuclideanSpace.single 1 1))
    + (c - 1) • ((EuclideanSpace.proj (1 : Fin 4)).smulRight (EuclideanSpace.single 1 1))

theorem boostCLM_apply (c s : ℝ) (x : M4) (j : Fin 4) :
    boostCLM c s x j
      = x j + ((c - 1) * x 0 + s * x 1) * (EuclideanSpace.single 0 (1 : ℝ) : M4) j
        + (s * x 0 + (c - 1) * x 1) * (EuclideanSpace.single 1 (1 : ℝ) : M4) j := by
  have h : boostCLM c s x
      = x + (c - 1) • (x 0 • (EuclideanSpace.single 0 (1 : ℝ) : M4))
        + s • (x 1 • (EuclideanSpace.single 0 (1 : ℝ) : M4))
        + s • (x 0 • (EuclideanSpace.single 1 (1 : ℝ) : M4))
        + (c - 1) • (x 1 • (EuclideanSpace.single 1 (1 : ℝ) : M4)) := rfl
  rw [h]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem boostCLM_apply_zero (c s : ℝ) (x : M4) : boostCLM c s x 0 = c * x 0 + s * x 1 := by
  rw [boostCLM_apply, single_apply_self,
    single_apply_of_ne (show (0 : Fin 4) ≠ 1 by decide)]
  ring

theorem boostCLM_apply_one (c s : ℝ) (x : M4) : boostCLM c s x 1 = s * x 0 + c * x 1 := by
  rw [boostCLM_apply, single_apply_self,
    single_apply_of_ne (show (1 : Fin 4) ≠ 0 by decide)]
  ring

theorem boostCLM_apply_two (c s : ℝ) (x : M4) : boostCLM c s x 2 = x 2 := by
  rw [boostCLM_apply, single_apply_of_ne (show (2 : Fin 4) ≠ 0 by decide),
    single_apply_of_ne (show (2 : Fin 4) ≠ 1 by decide)]
  ring

theorem boostCLM_apply_three (c s : ℝ) (x : M4) : boostCLM c s x 3 = x 3 := by
  rw [boostCLM_apply, single_apply_of_ne (show (3 : Fin 4) ≠ 0 by decide),
    single_apply_of_ne (show (3 : Fin 4) ≠ 1 by decide)]
  ring

/-- Boosts compose by adding rapidities: `(c, s) ∘ (c', s') = (cc' + ss', cs' + sc')`
(the hyperbolic addition formulas). No relation between `c` and `s` is needed. -/
theorem boostCLM_comp (c s c' s' : ℝ) (x : M4) :
    boostCLM c s (boostCLM c' s' x) = boostCLM (c * c' + s * s') (c * s' + s * c') x := by
  ext j
  rw [boostCLM_apply, boostCLM_apply, boostCLM_apply_zero, boostCLM_apply_one,
    boostCLM_apply]
  ring

theorem boostCLM_left_inv (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) (x : M4) :
    boostCLM c (-s) (boostCLM c s x) = x := by
  rw [boostCLM_comp]
  ext j
  rw [boostCLM_apply]
  have h1 : c * c + -s * s = 1 := by linear_combination hc
  have h2 : c * s + -s * c = 0 := by ring
  rw [h1, h2]
  ring

/-- The boost as a continuous linear automorphism of `M4`. -/
def boostEquiv (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) : M4 ≃L[ℝ] M4 where
  toFun := boostCLM c s
  map_add' := map_add (boostCLM c s)
  map_smul' := map_smul (boostCLM c s)
  invFun := boostCLM c (-s)
  left_inv := boostCLM_left_inv c s hc
  right_inv := fun x => by
    have h := boostCLM_left_inv c (-s) (by linear_combination hc) x
    rwa [neg_neg] at h
  continuous_toFun := (boostCLM c s).continuous
  continuous_invFun := (boostCLM c (-s)).continuous

theorem boostEquiv_apply (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) (x : M4) :
    boostEquiv c s hc x = boostCLM c s x := rfl

theorem boostEquiv_form (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) (v w : M4) :
    minkowskiForm (boostEquiv c s hc v) (boostEquiv c s hc w) = minkowskiForm v w := by
  rw [minkowskiForm_eq, minkowskiForm_eq]
  simp only [boostEquiv_apply, boostCLM_apply_zero, boostCLM_apply_one,
    boostCLM_apply_two, boostCLM_apply_three]
  linear_combination (v 1 * w 1 - v 0 * w 0) * hc

theorem boostEquiv_det (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) :
    LinearMap.det ((boostEquiv c s hc).toLinearEquiv : M4 →ₗ[ℝ] M4) = 1 := by
  have hA : ∀ j k : Fin 4, boostEquiv c s hc (EuclideanSpace.single k (1 : ℝ)) j
      = !![c, s, 0, 0; s, c, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] j k := by
    intro j k
    fin_cases j <;> fin_cases k <;>
      simp [boostEquiv_apply, boostCLM_apply_zero, boostCLM_apply_one,
        boostCLM_apply_two, boostCLM_apply_three]
  rw [det_eq_matrix_det _ _ hA]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  linear_combination hc

theorem boostEquiv_apply_single_zero_zero (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) :
    boostEquiv c s hc (EuclideanSpace.single 0 1) 0 = c := by
  rw [boostEquiv_apply, boostCLM_apply_zero, single_apply_self,
    single_apply_of_ne (show (1 : Fin 4) ≠ 0 by decide)]
  ring

theorem boostEquiv_apply_single_zero_one (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) :
    boostEquiv c s hc (EuclideanSpace.single 0 1) 1 = s := by
  rw [boostEquiv_apply, boostCLM_apply_one, single_apply_self,
    single_apply_of_ne (show (1 : Fin 4) ≠ 0 by decide)]
  ring

theorem boostEquiv_mem (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) (hpos : 0 < c) :
    boostEquiv c s hc ∈ RestrictedLorentzGroup :=
  ⟨boostEquiv_form c s hc, boostEquiv_det c s hc, by
    rw [boostEquiv_apply_single_zero_zero]; exact hpos⟩

/-- Composing two forward boosts stays forward: `cosh(χ + χ') > 0`. The composed
parameters satisfy `(cc' + ss')² - (cs' + sc')² = (c² - s²)(c'² - s'²) = 1`, and the
positive root is the one reached, because `(cc')² - (ss')² = c² + c'² - 1 > 0`. -/
private theorem boost_param_pos {c s c' s' : ℝ} (hc : c ^ 2 - s ^ 2 = 1) (hpos : 0 < c)
    (hc' : c' ^ 2 - s' ^ 2 = 1) (hpos' : 0 < c') : 0 < c * c' + s * s' := by
  have hs : s ^ 2 = c ^ 2 - 1 := by linarith
  have hs' : s' ^ 2 = c' ^ 2 - 1 := by linarith
  have hfac : (c * c' + s * s') * (c * c' - s * s') = c ^ 2 + c' ^ 2 - 1 := by
    have hexp : (c * c' + s * s') * (c * c' - s * s') = c ^ 2 * c' ^ 2 - s ^ 2 * s' ^ 2 := by
      ring
    rw [hexp, hs, hs']; ring
  have hc1 : 1 ≤ c := by nlinarith [sq_nonneg s]
  have hc1' : 1 ≤ c' := by nlinarith [sq_nonneg s']
  have hpos2 : 0 < c ^ 2 + c' ^ 2 - 1 := by nlinarith
  by_contra hle
  push Not at hle
  have hcc : 0 < c * c' := mul_pos hpos hpos'
  have hdiff : 0 < c * c' - s * s' := by linarith
  have hmul : 0 ≤ -(c * c' + s * s') * (c * c' - s * s') :=
    mul_nonneg (by linarith) hdiff.le
  nlinarith [hfac, hmul, hpos2]

namespace RestrictedLorentzGroup

/-- The `x¹`-boost of rapidity `χ`, with `c = cosh χ`, `s = sinh χ`, as an element of
`L↑₊`. Letting `χ` range over `ℝ` gives an unbounded one-parameter subgroup — the
qualitative reason `L↑₊` is not compact; no compactness statement is proved here. -/
def boost (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) (hpos : 0 < c) : RestrictedLorentzGroup :=
  ⟨boostEquiv c s hc, boostEquiv_mem c s hc hpos⟩

@[simp] theorem coe_boost (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) (hpos : 0 < c) :
    (boost c s hc hpos : M4 ≃L[ℝ] M4) = boostEquiv c s hc := rfl

/-- Rapidity addition in the group: `boost χ * boost χ' = boost (χ + χ')`, in the
`(cosh, sinh)` parametrization. -/
theorem boost_mul (c s c' s' : ℝ) (hc : c ^ 2 - s ^ 2 = 1) (hpos : 0 < c)
    (hc' : c' ^ 2 - s' ^ 2 = 1) (hpos' : 0 < c') :
    boost c s hc hpos * boost c' s' hc' hpos'
      = boost (c * c' + s * s') (c * s' + s * c')
        (by linear_combination (c' ^ 2 - s' ^ 2) * hc + hc')
        (boost_param_pos hc hpos hc' hpos') :=
  Subtype.ext (ContinuousLinearEquiv.ext (funext fun x => boostCLM_comp c s c' s' x))

/-- The inverse of a boost is the boost of the opposite rapidity. -/
theorem boost_inv (c s : ℝ) (hc : c ^ 2 - s ^ 2 = 1) (hpos : 0 < c) :
    (boost c s hc hpos)⁻¹ = boost c (-s) (by linear_combination hc) hpos :=
  Subtype.ext (ContinuousLinearEquiv.ext (funext fun _ => rfl))

/-- The `x¹`-boost of velocity `β = 3/5`: `γ = cosh χ = 5/4`, `γβ = sinh χ = 3/4`
(`(5/4)² - (3/4)² = 1`), chosen rational so that every kernel computation below is exact
rational arithmetic. -/
def boost35 : RestrictedLorentzGroup := boost (5 / 4) (3 / 4) (by norm_num) (by norm_num)

/-- **Expected false** (non-triviality): the boost is not the identity of `L↑₊`. -/
theorem boost35_ne_one : boost35 ≠ 1 := by
  intro h
  have h1 : boostEquiv (5 / 4) (3 / 4) (by norm_num) (EuclideanSpace.single 0 1) 1
      = ((1 : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) (EuclideanSpace.single 0 1) 1 := by
    rw [← coe_boost (5 / 4) (3 / 4) (by norm_num) (by norm_num)]
    exact congrArg (fun g : RestrictedLorentzGroup =>
      (g : M4 ≃L[ℝ] M4) (EuclideanSpace.single 0 1) 1) h
  rw [boostEquiv_apply_single_zero_one, Subgroup.coe_one, clm_one_apply,
    single_apply_of_ne (show (1 : Fin 4) ≠ 0 by decide)] at h1
  norm_num at h1

/-- A boost is not its own inverse: the two differ on the momentum `e₀`, whose spatial
component is boosted the opposite way. (Contrast `rotation12_mul_self`: the group has
both involutions and elements of infinite order.) -/
theorem boost35_ne_inv : boost35 ≠ boost35⁻¹ := by
  intro h
  have h1 : boostEquiv (5 / 4) (3 / 4) (by norm_num) (EuclideanSpace.single 0 1) 1
      = boostEquiv (5 / 4) (-(3 / 4)) (by norm_num) (EuclideanSpace.single 0 1) 1 := by
    rw [← coe_boost (5 / 4) (3 / 4) (by norm_num) (by norm_num),
      ← coe_boost (5 / 4) (-(3 / 4)) (by norm_num) (by norm_num)]
    exact congrArg (fun g : RestrictedLorentzGroup =>
      (g : M4 ≃L[ℝ] M4) (EuclideanSpace.single 0 1) 1)
      (h.trans (boost_inv (5 / 4) (3 / 4) (by norm_num) (by norm_num)))
  rw [boostEquiv_apply_single_zero_one, boostEquiv_apply_single_zero_one] at h1
  norm_num at h1

/-- Doubling the rapidity: `cosh 2χ = c² + s² = 17/8`, `sinh 2χ = 2cs = 15/8`. -/
theorem boost35_mul_self :
    boost35 * boost35 = boost (17 / 8) (15 / 8) (by norm_num) (by norm_num) := by
  rw [boost35, boost_mul]
  congr 1 <;> norm_num

end RestrictedLorentzGroup

/-! ### The Poincaré group: nontrivial elements and the semidirect twist -/

namespace PoincareGroup

open RestrictedLorentzGroup

/-- Translation-only element `(e₁, 1)`. -/
def translationE1 : PoincareGroup := ⟨EuclideanSpace.single 1 1, 1⟩

/-- Rotation-only element `(0, R)`. -/
def rotationOnly : PoincareGroup := ⟨0, rotation12⟩

/-- Mixed element `(e₁, B)`: boost, then translate. -/
def boostTranslate : PoincareGroup := ⟨EuclideanSpace.single 1 1, boost35⟩

theorem translationE1_ne_one : translationE1 ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : PoincareGroup => g.translation 1) h
  rw [one_translation] at h1
  simp only [translationE1] at h1
  rw [single_apply_self] at h1
  norm_num at h1

theorem rotationOnly_ne_one : rotationOnly ≠ 1 := fun h =>
  rotation12_ne_one (congrArg PoincareGroup.lorentz h)

theorem boostTranslate_ne_one : boostTranslate ≠ 1 := fun h =>
  boost35_ne_one (congrArg PoincareGroup.lorentz h)

/-- The twist, left: `(0, R)(e₁, 1) = (R e₁, R) = (-e₁, R)`. -/
theorem rotationOnly_mul_translationE1 :
    (rotationOnly * translationE1).translation
      = -(EuclideanSpace.single 1 (1 : ℝ) : M4) := by
  show (0 : M4) + rotation12Equiv (EuclideanSpace.single 1 1) = _
  rw [zero_add, rotation12Equiv_single_one]

/-- The twist, right: `(e₁, 1)(0, R) = (e₁, R)` — the translation is *not* rotated. -/
theorem translationE1_mul_rotationOnly :
    (translationE1 * rotationOnly).translation
      = (EuclideanSpace.single 1 (1 : ℝ) : M4) := by
  show (EuclideanSpace.single 1 1 : M4)
    + ((1 : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) 0 = _
  rw [map_zero, add_zero]

/-- **The semidirect structure is genuine**: the two orders differ. -/
theorem rotationOnly_mul_translationE1_ne :
    rotationOnly * translationE1 ≠ translationE1 * rotationOnly := by
  intro h
  have h1 := congrArg (fun g : PoincareGroup => g.translation 1) h
  simp only at h1
  rw [rotationOnly_mul_translationE1, translationE1_mul_rotationOnly,
    PiLp.neg_apply, single_apply_self] at h1
  norm_num at h1

/-- The affine action on both orders, on fully concrete data: `(0, R)(e₁, 1)` sends the
origin to `-e₁`, while `(e₁, 1)(0, R)` sends it to `e₁`. -/
theorem smul_zero_rotationOnly_mul_translationE1 :
    (rotationOnly * translationE1) • (0 : M4) = -(EuclideanSpace.single 1 (1 : ℝ) : M4) := by
  rw [smul_def, rotationOnly_mul_translationE1, map_zero, zero_add]

theorem smul_zero_translationE1_mul_rotationOnly :
    (translationE1 * rotationOnly) • (0 : M4) = (EuclideanSpace.single 1 (1 : ℝ) : M4) := by
  rw [smul_def, translationE1_mul_rotationOnly, map_zero, zero_add]

-- The spec's `mul_smul`, engaged with a nontrivial homogeneous part: acting in two steps
-- agrees with acting by the product.
example : rotationOnly • translationE1 • (0 : M4)
    = -(EuclideanSpace.single 1 (1 : ℝ) : M4) := by
  rw [← mul_smul]
  exact smul_zero_rotationOnly_mul_translationE1

/-- The inverse of a mixed element, homogeneous part: `(a, B)⁻¹ = (-B⁻¹a, B⁻¹)` with
`B⁻¹` the opposite-rapidity boost. -/
theorem boostTranslate_inv_lorentz :
    boostTranslate⁻¹.lorentz = boost (5 / 4) (-(3 / 4)) (by norm_num) (by norm_num) := by
  rw [inv_lorentz]
  exact boost_inv (5 / 4) (3 / 4) (by norm_num) (by norm_num)

/-- The inverse of a mixed element, translation part, in closed form:
`-B⁻¹e₁ = (3/4) e₀ - (5/4) e₁`. -/
theorem boostTranslate_inv_translation :
    boostTranslate⁻¹.translation
      = (3 / 4 : ℝ) • (EuclideanSpace.single 0 (1 : ℝ) : M4)
        - (5 / 4 : ℝ) • (EuclideanSpace.single 1 (1 : ℝ) : M4) := by
  show -(boostCLM (5 / 4) (-(3 / 4)) (EuclideanSpace.single 1 1)) = _
  ext j
  rw [PiLp.neg_apply, boostCLM_apply,
    single_apply_of_ne (show (0 : Fin 4) ≠ 1 by decide), single_apply_self]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The `MulAction` inverse law on the mixed element (from the spec's `MulAction`). -/
theorem boostTranslate_inv_smul (x : M4) : boostTranslate⁻¹ • boostTranslate • x = x :=
  inv_smul_smul boostTranslate x

end PoincareGroup

/-! ### Mass shells under the group

Adapted from the reviewer probe `audits/probes/P2.4a/massshell_poincare_probe.lean`. -/

open RestrictedLorentzGroup PoincareGroup

/-- The rest momentum of a unit-mass particle is on the shell. -/
theorem single_zero_mem_massShell_one : (EuclideanSpace.single 0 1 : M4) ∈ massShell 1 := by
  refine ⟨?_, by rw [single_apply_self]; norm_num⟩
  rw [minkowskiForm_eq, single_apply_self,
    single_apply_of_ne (show (1 : Fin 4) ≠ 0 by decide),
    single_apply_of_ne (show (2 : Fin 4) ≠ 0 by decide),
    single_apply_of_ne (show (3 : Fin 4) ≠ 0 by decide)]
  norm_num

/-- The rotation fixes the rest momentum: a rotation-invariant point of the shell. -/
theorem rotation12Equiv_single_zero :
    rotation12Equiv (EuclideanSpace.single 0 1) = (EuclideanSpace.single 0 (1 : ℝ) : M4) := by
  ext j
  rw [rotation12Equiv_apply, reflectCLM_apply, reflectCLM_apply, PiLp.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all

example : (rotation12 : M4 ≃L[ℝ] M4) (EuclideanSpace.single 0 1) ∈ massShell 1 :=
  map_massShell rotation12 single_zero_mem_massShell_one

/-- The boost moves the rest momentum to the moving-particle momentum
`(E, p) = (5/4, 3/4)`. -/
theorem boost35_apply_single_zero :
    (boost35 : M4 ≃L[ℝ] M4) (EuclideanSpace.single 0 1)
      = (5 / 4 : ℝ) • (EuclideanSpace.single 0 (1 : ℝ) : M4)
        + (3 / 4 : ℝ) • (EuclideanSpace.single 1 (1 : ℝ) : M4) := by
  show boostCLM (5 / 4) (3 / 4) (EuclideanSpace.single 0 1) = _
  ext j
  rw [boostCLM_apply, single_apply_self,
    single_apply_of_ne (show (1 : Fin 4) ≠ 0 by decide)]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Expected true, via the frozen theorem: the boosted momentum is still on the shell. -/
example : (boost35 : M4 ≃L[ℝ] M4) (EuclideanSpace.single 0 1) ∈ massShell 1 :=
  map_massShell boost35 single_zero_mem_massShell_one

/-- Expected true, computed directly: `η((5/4, 3/4, 0, 0), ·) = -25/16 + 9/16 = -1`, with
positive energy — the same fact as the previous `example`, obtained without the frozen
theorem, as a cross-check that `map_massShell` is not vacuously true here. -/
example : ((5 / 4 : ℝ) • (EuclideanSpace.single 0 (1 : ℝ) : M4)
    + (3 / 4 : ℝ) • (EuclideanSpace.single 1 (1 : ℝ) : M4)) ∈ massShell 1 := by
  have h : ∀ j : Fin 4, ((5 / 4 : ℝ) • (EuclideanSpace.single 0 (1 : ℝ) : M4)
      + (3 / 4 : ℝ) • (EuclideanSpace.single 1 (1 : ℝ) : M4)) j
      = 5 / 4 * (EuclideanSpace.single 0 (1 : ℝ) : M4) j
        + 3 / 4 * (EuclideanSpace.single 1 (1 : ℝ) : M4) j := by
    intro j; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [minkowskiForm_eq, h 0, h 1, h 2, h 3, single_apply_self, single_apply_self,
      single_apply_of_ne (show (0 : Fin 4) ≠ 1 by decide),
      single_apply_of_ne (show (1 : Fin 4) ≠ 0 by decide),
      single_apply_of_ne (show (2 : Fin 4) ≠ 0 by decide),
      single_apply_of_ne (show (2 : Fin 4) ≠ 1 by decide),
      single_apply_of_ne (show (3 : Fin 4) ≠ 0 by decide),
      single_apply_of_ne (show (3 : Fin 4) ≠ 1 by decide)]
    norm_num
  · rw [h 0, single_apply_self, single_apply_of_ne (show (0 : Fin 4) ≠ 1 by decide)]
    norm_num

/-- A translation of a shell point, in the same coordinates. -/
theorem translation_smul_single_zero :
    (⟨EuclideanSpace.single 0 1, 1⟩ : PoincareGroup) • (EuclideanSpace.single 0 1 : M4)
      = (2 : ℝ) • (EuclideanSpace.single 0 (1 : ℝ) : M4) := by
  rw [smul_def]
  show ((1 : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) (EuclideanSpace.single 0 1)
    + EuclideanSpace.single 0 1 = _
  rw [Subgroup.coe_one, clm_one_apply, two_smul]

/-- **Expected false**: the *affine* action does not preserve mass shells. Only the
homogeneous part does, which is precisely the content of the frozen
`RestrictedLorentzGroup.map_massShell` — there is no Poincaré-equivariance of `massShell`
to be had, and the frozen spec claims none. (`massShell` is a set of *momenta*; the
translations act on positions, so this is the expected physical answer, not a defect.) -/
theorem translation_smul_single_zero_not_mem_massShell :
    ((⟨EuclideanSpace.single 0 1, 1⟩ : PoincareGroup) • (EuclideanSpace.single 0 1 : M4))
      ∉ massShell 1 := by
  rw [translation_smul_single_zero]
  intro h
  have hf := h.1
  have h2 : ∀ j : Fin 4, ((2 : ℝ) • (EuclideanSpace.single 0 (1 : ℝ) : M4)) j
      = 2 * (EuclideanSpace.single 0 (1 : ℝ) : M4) j := fun j => by
    simp only [PiLp.smul_apply, smul_eq_mul]
  rw [minkowskiForm_eq, h2 0, h2 1, h2 2, h2 3, single_apply_self,
    single_apply_of_ne (show (1 : Fin 4) ≠ 0 by decide),
    single_apply_of_ne (show (2 : Fin 4) ≠ 0 by decide),
    single_apply_of_ne (show (3 : Fin 4) ≠ 0 by decide)] at hf
  norm_num at hf

end

end Spacetime.Minkowski
