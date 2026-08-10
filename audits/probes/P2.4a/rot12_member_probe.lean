import Atlas.Specs.Spacetime.Poincare
import Mathlib.Algebra.BigOperators.Fin

/-!
# P2.4a adversarial kernel probes — a NONTRIVIAL `RestrictedLorentzGroup` member

Constructs the spatial π-rotation in the (1,2)-plane, `diag(1, -1, -1, 1)`, proves all
three membership conditions of the frozen `RestrictedLorentzGroup` (form preservation,
`LinearMap.det` of the coerced `toLinearEquiv` `= 1` — probing the frozen det spelling
on a concrete element — and orthochronicity), shows it is `≠ 1`, and uses it to engage
the semidirect twist of `PoincareGroup` on concrete elements: left- vs
right-multiplication by a translation genuinely differ, and `mul_smul` holds with a
nontrivial homogeneous part.

This also discharges "no nontrivial member yet" ahead of P2.4W: the group spec is
non-vacuous beyond the identity.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.4a/` only.
-/

open Spacetime.Minkowski

noncomputable section

private theorem f01 : ((0 : Fin 4) = 1) = False := by decide
private theorem f02 : ((0 : Fin 4) = 2) = False := by decide
private theorem f10 : ((1 : Fin 4) = 0) = False := by decide
private theorem f12 : ((1 : Fin 4) = 2) = False := by decide
private theorem f20 : ((2 : Fin 4) = 0) = False := by decide
private theorem f21 : ((2 : Fin 4) = 1) = False := by decide
private theorem f30 : ((3 : Fin 4) = 0) = False := by decide
private theorem f31 : ((3 : Fin 4) = 1) = False := by decide
private theorem f32 : ((3 : Fin 4) = 2) = False := by decide

/-- `diag(1, -1, -1, 1)` as a continuous linear map: flip coordinates `1` and `2`. -/
def rotCLM : M4 →L[ℝ] M4 :=
  ContinuousLinearMap.id ℝ M4
    - (2 : ℝ) • ((EuclideanSpace.proj (1 : Fin 4)).smulRight (EuclideanSpace.single 1 1))
    - (2 : ℝ) • ((EuclideanSpace.proj (2 : Fin 4)).smulRight (EuclideanSpace.single 2 1))

theorem rotCLM_apply (x : M4) (i : Fin 4) :
    rotCLM x i = x i - 2 * x 1 * (EuclideanSpace.single 1 (1 : ℝ) : M4) i
      - 2 * x 2 * (EuclideanSpace.single 2 (1 : ℝ) : M4) i := by
  have h : rotCLM x = x - (2 : ℝ) • (x 1 • (EuclideanSpace.single 1 (1 : ℝ) : M4))
      - (2 : ℝ) • (x 2 • (EuclideanSpace.single 2 (1 : ℝ) : M4)) := rfl
  rw [h]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem rotCLM_apply_zero (x : M4) : rotCLM x 0 = x 0 := by
  rw [rotCLM_apply]
  simp [f02]

theorem rotCLM_apply_one (x : M4) : rotCLM x 1 = -x 1 := by
  rw [rotCLM_apply]
  simp [f12]
  ring

theorem rotCLM_apply_two (x : M4) : rotCLM x 2 = -x 2 := by
  rw [rotCLM_apply]
  simp [f21]
  ring

theorem rotCLM_apply_three (x : M4) : rotCLM x 3 = x 3 := by
  rw [rotCLM_apply]
  simp [f31, f32]

theorem rotCLM_involutive (x : M4) : rotCLM (rotCLM x) = x := by
  ext i
  rw [rotCLM_apply, rotCLM_apply, rotCLM_apply_one, rotCLM_apply_two]
  ring

/-- The rotation as a continuous linear automorphism of `M4`. -/
def rot : M4 ≃L[ℝ] M4 :=
  { toFun := rotCLM
    map_add' := map_add rotCLM
    map_smul' := map_smul rotCLM
    invFun := rotCLM
    left_inv := rotCLM_involutive
    right_inv := rotCLM_involutive
    continuous_toFun := rotCLM.continuous
    continuous_invFun := rotCLM.continuous }

theorem rot_apply (x : M4) : rot x = rotCLM x := rfl

/-! ## The three membership conditions -/

theorem rot_form_preserving (v w : M4) :
    minkowskiForm (rot v) (rot w) = minkowskiForm v w := by
  rw [minkowskiForm_eq, minkowskiForm_eq]
  simp only [rot_apply, rotCLM_apply_zero, rotCLM_apply_one, rotCLM_apply_two,
    rotCLM_apply_three]
  ring

/-- The frozen det spelling — `LinearMap.det` of the coerced `toLinearEquiv` —
evaluated on a concrete nontrivial element via `toMatrix` and `det_diagonal`. -/
theorem rot_det : LinearMap.det (rot.toLinearEquiv : M4 →ₗ[ℝ] M4) = 1 := by
  have hmat : LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin 4)) (PiLp.basisFun 2 ℝ (Fin 4))
      (rot.toLinearEquiv : M4 →ₗ[ℝ] M4) = Matrix.diagonal ![1, -1, -1, 1] := by
    ext i j
    rw [LinearMap.toMatrix_apply, PiLp.basisFun_apply, PiLp.basisFun_repr,
      Matrix.diagonal_apply]
    have key : (rot.toLinearEquiv : M4 →ₗ[ℝ] M4) (PiLp.single 2 j 1)
        = rotCLM (PiLp.single 2 j 1) := rfl
    rw [key]
    fin_cases i <;> fin_cases j <;>
      simp [rotCLM_apply_zero, rotCLM_apply_one, rotCLM_apply_two, rotCLM_apply_three]
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 4)), hmat, Matrix.det_diagonal]
  simp [Fin.prod_univ_succ]

theorem rot_orthochronous : 0 < rot (EuclideanSpace.single 0 1) 0 := by
  rw [rot_apply, rotCLM_apply]
  norm_num [PiLp.single_apply, f10, f20, f01, f02]

theorem rot_mem : rot ∈ RestrictedLorentzGroup :=
  ⟨rot_form_preserving, rot_det, rot_orthochronous⟩

/-- The rotation as a group element. -/
def R : RestrictedLorentzGroup := ⟨rot, rot_mem⟩

/-! ## Nontriviality and the group structure on it -/

theorem rot_single_one :
    rot (EuclideanSpace.single 1 1) = -(EuclideanSpace.single 1 1) := by
  ext i
  rw [PiLp.neg_apply, rot_apply, rotCLM_apply]
  have h1 : (EuclideanSpace.single 1 (1 : ℝ) : M4) 1 = 1 := by simp
  have h2 : (EuclideanSpace.single 1 (1 : ℝ) : M4) 2 = 0 := by simp [f21]
  rw [h1, h2]
  ring

theorem R_ne_one : R ≠ 1 := by
  intro h
  have hco : rot = ((1 : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) := congrArg Subtype.val h
  have h1 : rot (EuclideanSpace.single 1 1) = EuclideanSpace.single 1 1 := by
    rw [hco]; rfl
  rw [rot_single_one] at h1
  have h2 := congrArg (fun z : M4 => z 1) h1
  simp only [PiLp.neg_apply] at h2
  have h3 : (EuclideanSpace.single 1 (1 : ℝ) : M4) 1 = 1 := by simp
  rw [h3] at h2
  norm_num at h2

-- The rotation is an involution IN THE GROUP: subgroup `mul` composes correctly.
theorem R_mul_R : R * R = 1 :=
  Subtype.ext (ContinuousLinearEquiv.ext (funext fun x => rotCLM_involutive x))

/-! ## The semidirect twist, engaged on concrete elements -/

-- Left multiplication twists the translation: `(0, R)(e₁, 1) = (R e₁, R) = (-e₁, R)`.
theorem probe_twist_left :
    ((⟨0, R⟩ : PoincareGroup) * ⟨EuclideanSpace.single 1 1, 1⟩).translation
      = -(EuclideanSpace.single 1 1) := by
  show (0 : M4) + rot (EuclideanSpace.single 1 1) = _
  rw [zero_add, rot_single_one]

-- Right multiplication does not: `(e₁, 1)(0, R) = (e₁, R)`. The two products differ
-- in the translation component — the semidirect structure is genuinely non-abelian.
theorem probe_twist_right :
    ((⟨EuclideanSpace.single 1 1, 1⟩ : PoincareGroup) * ⟨0, R⟩).translation
      = EuclideanSpace.single 1 1 := by
  show EuclideanSpace.single 1 1 + ((1 : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) 0 = _
  rw [map_zero, add_zero]

-- `mul_smul` with a nontrivial homogeneous part, on fully concrete data:
-- both sides evaluate to `-e₁`.
theorem probe_mul_smul_concrete :
    (((⟨0, R⟩ : PoincareGroup) * ⟨EuclideanSpace.single 1 1, 1⟩) • (0 : M4)
        = -(EuclideanSpace.single 1 1))
      ∧ ((⟨0, R⟩ : PoincareGroup) • ((⟨EuclideanSpace.single 1 1, 1⟩ : PoincareGroup)
          • (0 : M4)) = -(EuclideanSpace.single 1 1)) := by
  constructor
  · rw [PoincareGroup.smul_def]
    show rot ((0 : M4)) + ((0 : M4) + rot (EuclideanSpace.single 1 1)) = _
    rw [map_zero, zero_add, zero_add, rot_single_one]
  · rw [PoincareGroup.smul_def, PoincareGroup.smul_def]
    show rot (((1 : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) (0 : M4)
        + EuclideanSpace.single 1 1) + (0 : M4) = _
    rw [map_zero, zero_add, add_zero, rot_single_one]

end
