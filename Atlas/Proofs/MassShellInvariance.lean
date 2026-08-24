import Atlas.Proofs.MassShellMeasure
import Atlas.Specs.Spacetime.Poincare
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# P2.6b — restricted-Lorentz invariance of the mass-shell measure

Third lane of the momentum-measure node (**P2.6b**): the change-of-variables proof that the
positive-shell weight `d³p/(2ω_p)` is invariant under every restricted Lorentz
transformation, on the physical-momentum slice `M3 = ℝ³` of the frozen carrier.

The frozen layer `Atlas.Proofs.MassShellMeasure` parametrizes the positive sheet by
`massShellParam m p = (ω_p, p)` with `ω_p = √(‖p‖² + m²)` the **physical** energy and
`p` the **physical** momentum (the Fourier frequency `k` corresponds to `p = 2πk`; this
module never leaves physical coordinates, so no `(2π)³` Jacobian enters). For a restricted
Lorentz transformation `Λ` define the transformed momentum map

* `QFT.KleinGordon.shellMap m Λ p = spatialOf (Λ (massShellParam m p))`,

the spatial part of the image four-momentum. Because `Λ` preserves `massShell m`
(`RestrictedLorentzGroup.map_massShell`), the image energy equals the physical energy of the
image momentum (`physicalEnergy_shellMap`), and the direct change-of-variables theorem of
Mathlib's Jacobian file turns the pointwise identity

* `|det D(shellMap m Λ)(p)| = ω_(shellMap m Λ p) / ω_p`

into the invariance of the weighted integral (`integral_weighted_massShell_invariance`),
i.e. Wigner's observation (1939, §6, eq. (59a), footnote 26) that integrals against
`d³p/p⁰` over the mass hyperboloid are Lorentz invariant because the Jacobian of the
transformation is compensated by the transformation of the energy.

## Contents

* `QFT.KleinGordon.spatialOf` — the spatial projection `(q¹, q², q³)` of a four-momentum;
  `QFT.KleinGordon.shellMap` — the induced momentum map `p ↦ spatialOf (Λ (ω_p, p))`, with
  continuity and smoothness (`0 < m`).
* Energy transport: `physicalEnergy_shellMap` (`ω` of the image = time component of the
  image four-momentum) and the shell round trips `massShellParam_shellMap`,
  `massShellParam_spatialOf_mem` (converse parametrization: a shell point is the
  parametrization of its own spatial part).
* `QFT.KleinGordon.lorentzEntry` — standard-basis matrix entries of `Λ`, with the column
  identities extracted from form preservation (`lorentzEntry_gamma_sq`,
  `lorentzEntry_col_gram`, `lorentzEntry_col_time`) and their row duals read off the
  transposed Gram identity (`lorentzEntry_row_gamma_sq`, `lorentzEntry_row_time`).
* Calculus: `hasFDerivAt_physicalEnergy`, `hasFDerivAt_massShellParam`,
  `dshellMap`, `hasFDerivAt_shellMap`, and the explicit entry formula
  `dshellMap_apply`.
* The determinant identity: explicit `Fin 3` rank-one and cofactor expansions
  (`det_rankOne_fin_three`, `det_updateRow_cofPair`) plus properness of `Λ`
  (`det_lorentzSpatialBlock`), yielding `abs_det_fderiv_shellMap`.
* Bijection, inverse laws, and smoothness of both directions
  (`bijective_shellMap`, `shellMap_diffeomorphism`).
* `QFT.KleinGordon.integral_weighted_massShell_invariance`: exact invariance of
  `∫ ψ d³p/(2ω_p)` under `shellMap m Λ`.

## Conventions

* Physical-momentum coordinates throughout: `massShellParam m p = (ω_p, p)`; the Fourier
  frequency coordinates of `Atlas.Proofs.KleinGordon.onShell` are related by `p = 2πk`
  and are not used here.
* Minkowski sign convention mostly-plus, time coordinate `0`; positive sheet
  `η(q, q) = -m²`, `0 < q⁰`.
* Matrix conventions: `lorentzEntry Λ μ ν = (Λ e_ν) μ` (column convention); the spatial
  block, the time column and the top row extracted from these entries satisfy the
  pseudo-orthogonality relations stated in the Lorentz-entries section.

## Sources

* E. P. Wigner, *On Unitary Representations of the Inhomogeneous Lorentz Group*, Annals of
  Mathematics 40 (1939), §6, eq. (59a) and footnote 26: the scalar product on wave
  functions carried by the hyperboloid `p·p = P` integrates against `|p₄|⁻¹dp₁dp₂dp₃`, and
  the invariance under `x = Λ⁻¹x′` follows from the Jacobian of the substitution — the
  determinant identity proved here is exactly that Jacobian computation for the positive
  sheet.
* R. F. Streater, A. S. Wightman, *PCT, Spin and Statistics, and All That* (1964;
  Princeton Landmarks ed. 2000), §1-1 (the group `L↑₊` and its action) and Ch. 3 (the
  one-particle measure `d³p/2p⁰` in the two-point function normalization).
* S. Weinberg, *The Quantum Theory of Fields*, Vol. I (1995), §2.5: invariance of
  `d³p/2p⁰` under proper orthochronous Lorentz transformations, section level.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II*, Academic Press (1975),
  §X.7 *Free quantum fields*: the one-particle space `L²(H_m, d³p/2μ(p))`, section level,
  consistent with the `(X.80)` anchor fixed in `Atlas.Proofs.KleinGordon`.
-/

open MeasureTheory Real Spacetime.Minkowski
open scoped ENNReal Matrix

namespace QFT.KleinGordon

/-! ### The spatial projection and the Lorentz-transformed momentum map -/

/-- The spatial part `(q¹, q², q³)` of a four-momentum `q : M4`, as a physical momentum
on the slice `M3`. -/
noncomputable def spatialOf (q : M4) : M3 :=
  !₂[q 1, q 2, q 3]

@[simp] theorem spatialOf_apply_zero (q : M4) : spatialOf q 0 = q 1 := by
  simp [spatialOf]

@[simp] theorem spatialOf_apply_one (q : M4) : spatialOf q 1 = q 2 := by
  simp [spatialOf]

@[simp] theorem spatialOf_apply_two (q : M4) : spatialOf q 2 = q 3 := by
  simp [spatialOf]

/-- Coordinate form of the projection: the `j`-th spatial component is the `(j+1)`-st
coordinate of the ambient four-vector. -/
theorem spatialOf_apply (q : M4) (j : Fin 3) : spatialOf q j = q j.succ := by
  fin_cases j <;> simp
/-- The spatial projection is continuous. -/
theorem spatialOf_continuous : Continuous (spatialOf : M4 → M3) := by
  show Continuous fun q : M4 => (!₂[q 1, q 2, q 3] : M3)
  fun_prop

/-- The spatial projection is smooth (each component is a coordinate functional). -/
theorem spatialOf_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n (spatialOf : M4 → M3) := by
  rw [contDiff_piLp]
  intro j
  fin_cases j <;> exact (EuclideanSpace.proj (_ : Fin 4) : M4 →L[ℝ] ℝ).contDiff

/-- The positive-shell parametrization is smooth for nonzero mass: its time component is
the smooth physical energy, its spatial components are coordinates. -/
theorem contDiff_massShellParam (m : ℝ) {n : WithTop ℕ∞} (hm : m ≠ 0) :
    ContDiff ℝ n (massShellParam m) := by
  rw [contDiff_piLp]
  intro j
  fin_cases j
  · simpa [massShellParam] using contDiff_physicalEnergy m hm
  all_goals exact (EuclideanSpace.proj (_ : Fin 3) : M3 →L[ℝ] ℝ).contDiff
/-- **The Lorentz-transformed momentum map**: the spatial momentum carried by the image
four-momentum `Λ(ω_p, p)`. This is the momentum-space action of `Λ ∈ L↑₊` conjugated to
physical coordinates (Wigner 1939, §6: the substitution `x′ = Λx` on the hyperboloid). -/
noncomputable def shellMap (m : ℝ) (Λ : RestrictedLorentzGroup) (p : M3) : M3 :=
  spatialOf ((Λ : M4 ≃L[ℝ] M4) (massShellParam m p))

variable (m : ℝ) (Λ : RestrictedLorentzGroup) (p : M3)

/-- Coordinate form of the momentum map along the three output directions. -/
theorem shellMap_apply (j : Fin 3) :
    shellMap m Λ p j = ((Λ : M4 ≃L[ℝ] M4) (massShellParam m p)) j.succ :=
  spatialOf_apply _ j

/-- Continuity of the momentum map (every mass). -/
theorem continuous_shellMap : Continuous (shellMap m Λ) :=
  (spatialOf_continuous.comp ((Λ : M4 ≃L[ℝ] M4)).continuous).comp (continuous_massShellParam m)

/-- Smoothness of the momentum map for nonzero mass: `massShellParam` is smooth, and the
Lorentz action and the spatial projection are continuous linear. -/
theorem contDiff_shellMap {n : WithTop ℕ∞} (hm : m ≠ 0) : ContDiff ℝ n (shellMap m Λ) :=
  spatialOf_contDiff.comp (((Λ : M4 ≃L[ℝ] M4)).contDiff.comp (contDiff_massShellParam m hm))

/-- The squared norm of a spatial momentum is the sum of squares of the last three
coordinates of any four-vector projecting to it. -/
private theorem norm_sq_spatialOf (q : M4) :
    ‖spatialOf q‖ ^ 2 = q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp

theorem spatialOf_massShellParam (p : M3) : spatialOf (massShellParam m p) = p := by
  ext j
  fin_cases j <;> simp

/-- **Converse parametrization**: a point of the positive sheet is the physical-momentum
parametrization of its own spatial part. This closes the range characterization of
`Atlas.Proofs.MassShellMeasure` into an equation. -/
theorem massShellParam_spatialOf (hm : 0 < m) {q : M4}
    (hq : q ∈ Spacetime.Minkowski.massShell m) :
    massShellParam m (spatialOf q) = q := by
  obtain ⟨r, hr⟩ := (mem_range_massShellParam m hm q).2 hq
  rw [← hr, spatialOf_massShellParam]

/-- On the positive sheet the physical energy of the projected momentum is the time
coordinate itself: `ω_q = q⁰` (Wigner 1939, §6: `p₄ = √(m² + p₁² + p₂² + p₃²)`). -/
theorem physicalEnergy_spatialOf_mem_massShell {q : M4}
    (hq : q ∈ Spacetime.Minkowski.massShell m) :
    physicalEnergy m (spatialOf q) = q 0 := by
  obtain ⟨hform, hpos⟩ := hq
  have hform' : q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 + m ^ 2 = q 0 ^ 2 := by
    have hx : -(q 0 * q 0) + q 1 * q 1 + q 2 * q 2 + q 3 * q 3 = -(m ^ 2) := by
      rw [← minkowskiForm_eq]; exact hform
    nlinarith
  have hsq : physicalEnergy m (spatialOf q) ^ 2 = q 0 ^ 2 := by
    rw [physicalEnergy_sq, norm_sq_spatialOf]
    linarith
  calc physicalEnergy m (spatialOf q)
      = √(physicalEnergy m (spatialOf q) ^ 2) :=
        (Real.sqrt_sq (physicalEnergy_nonneg m _)).symm
    _ = √(q 0 ^ 2) := by rw [hsq]
    _ = q 0 := Real.sqrt_sq hpos.le

/-- **Energy of the image point**: the physical energy of the transformed momentum equals
the time component of the transformed four-momentum. This is the exact relation between
the Jacobian numerator and the image energy used by the change of variables below. -/
theorem physicalEnergy_shellMap (hm : 0 < m) :
    physicalEnergy m (shellMap m Λ p)
      = ((Λ : M4 ≃L[ℝ] M4) (massShellParam m p)) 0 :=
  physicalEnergy_spatialOf_mem_massShell m
    (RestrictedLorentzGroup.map_massShell Λ (massShellParam_mem_massShell m p hm))

/-- **Round trip**: the parametrization of the transformed momentum is the transformed
four-momentum. In other words `shellMap m Λ` is `Λ` read on the momentum slice. -/
theorem massShellParam_shellMap (hm : 0 < m) :
    massShellParam m (shellMap m Λ p) = (Λ : M4 ≃L[ℝ] M4) (massShellParam m p) :=
  massShellParam_spatialOf m hm
    (RestrictedLorentzGroup.map_massShell Λ (massShellParam_mem_massShell m p hm))

/-- The `(μ, ν)` **standard-basis matrix entry** of `Λ ∈ L↑₊`: the `μ`-coordinate of the
image of the `ν`-th basis vector (column convention: columns are images of basis
vectors). -/
noncomputable def lorentzEntry (Λ : RestrictedLorentzGroup) (μ ν : Fin 4) : ℝ :=
  ((Λ : M4 ≃L[ℝ] M4) (EuclideanSpace.single ν 1)) μ

/-- The Minkowski pairing of two image basis vectors, in matrix entries: the pseudo-
Gram matrix of the columns of `Λ` is the metric itself. This is
`RestrictedLorentzGroup.form_preserving` specialized to basis vectors. -/
theorem lorentzEntry_basis_form (Λ : RestrictedLorentzGroup) (ν ξ : Fin 4) :
    -(lorentzEntry Λ 0 ν * lorentzEntry Λ 0 ξ)
      + lorentzEntry Λ 1 ν * lorentzEntry Λ 1 ξ
      + lorentzEntry Λ 2 ν * lorentzEntry Λ 2 ξ
      + lorentzEntry Λ 3 ν * lorentzEntry Λ 3 ξ
      = (if ν = 0 ∧ ξ = 0 then (-1 : ℝ) else if ν = ξ then 1 else 0) := by
  have h := RestrictedLorentzGroup.form_preserving Λ (EuclideanSpace.single ν 1)
    (EuclideanSpace.single ξ 1)
  rw [minkowskiForm_eq] at h
  simp only [lorentzEntry]
  fin_cases ν <;> fin_cases ξ <;>
    simpa [minkowskiForm_eq, PiLp.single_apply] using h

/-- Basis Gram identity with the spatial block collected into one sum. -/
private theorem lorentzEntry_basis_form_sum (Λ : RestrictedLorentzGroup) (ν ξ : Fin 4) :
    -(lorentzEntry Λ 0 ν * lorentzEntry Λ 0 ξ)
        + ∑ i : Fin 3, lorentzEntry Λ i.succ ν * lorentzEntry Λ i.succ ξ
      = (if ν = 0 ∧ ξ = 0 then (-1 : ℝ) else if ν = ξ then 1 else 0) := by
  have h := RestrictedLorentzGroup.form_preserving Λ (EuclideanSpace.single ν 1)
    (EuclideanSpace.single ξ 1)
  rw [minkowskiForm_eq] at h
  simp only [lorentzEntry]
  fin_cases ν <;> fin_cases ξ
  all_goals
    simp [minkowskiForm_eq, Fin.sum_univ_three,
      show Fin.succ (2 : Fin 3) = 3 from rfl] at h ⊢
    linear_combination h

/-- Split of the signed coordinate sum into the time part and the spatial part. -/
private theorem lorentzEntry_signSum_split (Λ : RestrictedLorentzGroup) (ν ξ : Fin 4) :
    ∑ η : Fin 4, (if η = 0 then (-1 : ℝ) else 1)
        * lorentzEntry Λ η ν * lorentzEntry Λ η ξ
      = -(lorentzEntry Λ 0 ν * lorentzEntry Λ 0 ξ)
        + ∑ i : Fin 3, lorentzEntry Λ i.succ ν * lorentzEntry Λ i.succ ξ := by
  rw [Fin.sum_univ_succ]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp

/-- Summed form of the column Gram identity against the metric signs. -/
theorem lorentzEntry_gram (Λ : RestrictedLorentzGroup) (ν ξ : Fin 4) :
    ∑ η : Fin 4, (if η = 0 then (-1 : ℝ) else 1)
        * lorentzEntry Λ η ν * lorentzEntry Λ η ξ
      = (if ν = 0 ∧ ξ = 0 then (-1 : ℝ) else if ν = ξ then 1 else 0) := by
  rw [lorentzEntry_signSum_split]
  exact lorentzEntry_basis_form_sum Λ ν ξ

variable (Λ : RestrictedLorentzGroup)

/-- The standard matrix of `Λ` (column convention). -/
noncomputable def lorentzMat : Matrix (Fin 4) (Fin 4) ℝ := fun μ ν => lorentzEntry Λ μ ν

/-- The metric matrix `diag(-1, 1, 1, 1)` of the frozen mostly-plus convention. -/
noncomputable def metricMat : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal fun μ => if μ = 0 then (-1 : ℝ) else 1

@[simp] theorem metricMat_apply (μ ξ : Fin 4) :
    metricMat μ ξ =
      (if μ = 0 ∧ ξ = 0 then (-1 : ℝ) else if μ = ξ then 1 else 0) := by
  fin_cases μ <;> fin_cases ξ <;> simp [metricMat]


theorem lorentzMat_transpose_metric_mul :
    (lorentzMat Λ)ᵀ * metricMat * lorentzMat Λ = metricMat := by
  ext μ ξ
  rw [metricMat_apply, ← lorentzEntry_gram Λ μ ξ, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun η _ => ?_
  have hterm : ((lorentzMat Λ)ᵀ * metricMat) μ η
      = (if η = 0 then (-1 : ℝ) else 1) * lorentzEntry Λ η μ := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, lorentzMat]
    rw [Finset.sum_eq_single η]
    · rw [metricMat, Matrix.diagonal_apply, if_pos rfl]
      ring
    · intro b _ hb
      rw [metricMat, Matrix.diagonal_apply, if_neg hb, mul_zero]
    · simp
  rw [hterm, lorentzMat]

/-- The rows of a restricted Lorentz transformation are pseudo-orthonormal as well: the
transposed Gram identity `A J Aᵀ = J`, obtained from the column identity through the
pseudo-inverse `J Aᵀ J` of `A`. -/
theorem lorentzMat_metric_transpose_mul :
    lorentzMat Λ * metricMat * (lorentzMat Λ)ᵀ = metricMat := by
  set A := lorentzMat Λ with hAdef
  set J := metricMat with hJdef
  have hcol : Aᵀ * J * A = J := lorentzMat_transpose_metric_mul Λ
  have hjj : J * J = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hJdef, metricMat]
  have hXA : J * Aᵀ * J * A = 1 := by
    rw [Matrix.mul_assoc J Aᵀ J, Matrix.mul_assoc J (Aᵀ * J) A, hcol, hjj]
  have hdu : IsUnit A.det := by
    have h1 : (J * Aᵀ * J).det * A.det = 1 := by
      rw [← Matrix.det_mul, hXA, Matrix.det_one]
    exact isUnit_iff_exists_inv.mpr ⟨(J * Aᵀ * J).det, (mul_comm _ _).trans h1⟩
  have hXinv : J * Aᵀ * J = A⁻¹ := by
    calc J * Aᵀ * J
        = (J * Aᵀ * J) * 1 := (mul_one _).symm
      _ = (J * Aᵀ * J) * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv A hdu]
      _ = ((J * Aᵀ * J) * A) * A⁻¹ := (Matrix.mul_assoc _ _ _).symm
      _ = 1 * A⁻¹ := by rw [hXA]
      _ = A⁻¹ := by simp
  have hfin : A * J * Aᵀ * J = 1 := by
    rw [Matrix.mul_assoc A J Aᵀ, Matrix.mul_assoc A (J * Aᵀ) J, hXinv,
      Matrix.mul_nonsing_inv A hdu]
  calc A * J * Aᵀ
      = (A * J * Aᵀ) * (J * J) := by rw [hjj, mul_one]
    _ = (A * J * Aᵀ * J) * J := by rw [← Matrix.mul_assoc (A * J * Aᵀ) J J]
    _ = 1 * J := by rw [hfin]
    _ = J := by simp

theorem lorentzMat_det_eq_one : (lorentzMat Λ).det = 1 := by
  have h := RestrictedLorentzGroup.det_eq_one Λ
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 4) ℝ |>.toBasis)
    ((Λ : M4 ≃L[ℝ] M4).toLinearEquiv : M4 →ₗ[ℝ] M4)] at h
  have hmat : lorentzMat Λ =
      LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 4) ℝ |>.toBasis)
        (EuclideanSpace.basisFun (Fin 4) ℝ |>.toBasis)
        ((Λ : M4 ≃L[ℝ] M4).toLinearEquiv : M4 →ₗ[ℝ] M4) := by
    ext μ ν
    rw [LinearMap.toMatrix_apply]
    simp [lorentzMat, lorentzEntry, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr]
  rw [hmat]
  exact h

/-- Row pseudo-Gram identity, extracted from `A J Aᵀ = J`. -/
theorem lorentzEntry_row_gram (μ ξ : Fin 4) :
    ∑ η : Fin 4, (if η = 0 then (-1 : ℝ) else 1)
        * lorentzEntry Λ μ η * lorentzEntry Λ ξ η
      = (if μ = 0 ∧ ξ = 0 then (-1 : ℝ) else if μ = ξ then 1 else 0) := by
  calc
    ∑ η : Fin 4, (if η = 0 then (-1 : ℝ) else 1)
        * lorentzEntry Λ μ η * lorentzEntry Λ ξ η
        = (lorentzMat Λ * metricMat * (lorentzMat Λ)ᵀ) μ ξ := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun η _ => ?_
          have hterm : (lorentzMat Λ * metricMat) μ η =
              lorentzEntry Λ μ η * (if η = 0 then (-1 : ℝ) else 1) := by
            simp only [Matrix.mul_apply, lorentzMat]
            rw [Finset.sum_eq_single η]
            · rw [metricMat, Matrix.diagonal_apply, if_pos rfl]
            · intro b _ hb
              rw [metricMat, Matrix.diagonal_apply, if_neg hb, mul_zero]
            · simp
          rw [hterm, Matrix.transpose_apply, lorentzMat]
          ring
    _ = metricMat μ ξ :=
      congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M μ ξ)
        (lorentzMat_metric_transpose_mul Λ)
    _ = _ := metricMat_apply μ ξ

/-- **Time-column norm identity** from form preservation:
`Λ⁰₀² = 1 + ‖(Λ¹₀,Λ²₀,Λ³₀)‖²`. -/
theorem lorentzEntry_gamma_sq :
    lorentzEntry Λ 0 0 ^ 2
      = 1 + ∑ r : Fin 3, lorentzEntry Λ r.succ 0 ^ 2 := by
  have h := lorentzEntry_basis_form_sum Λ 0 0
  simp at h
  simp_rw [pow_two]
  linarith

/-- **Time/spatial-column orthogonality**:
`∑ᵣ Λʳ₀ Λʳᵢ = Λ⁰₀ Λ⁰ᵢ` for each spatial column `i`. -/
theorem lorentzEntry_col_time (i : Fin 3) :
    ∑ r : Fin 3, lorentzEntry Λ r.succ 0 * lorentzEntry Λ r.succ i.succ
      = lorentzEntry Λ 0 0 * lorentzEntry Λ 0 i.succ := by
  have h := lorentzEntry_basis_form_sum Λ 0 i.succ
  have hne : (0 : Fin 4) ≠ i.succ := (Fin.succ_ne_zero i).symm
  simp [hne] at h
  linarith

/-- **Spatial-column Gram identity**:
`BᵀB = I + ββᵀ` for the spatial block `B` and top spatial row `β`. -/
theorem lorentzEntry_col_gram (i k : Fin 3) :
    ∑ r : Fin 3, lorentzEntry Λ r.succ i.succ * lorentzEntry Λ r.succ k.succ
      = (if i = k then 1 else 0) + lorentzEntry Λ 0 i.succ * lorentzEntry Λ 0 k.succ := by
  have h := lorentzEntry_basis_form_sum Λ i.succ k.succ
  by_cases hik : i = k
  · subst k
    simp at h ⊢
    linarith
  · simp [hik] at h ⊢
    linarith

/-- **Top-row norm identity**, the row dual of `lorentzEntry_gamma_sq`:
`Λ⁰₀² = 1 + ∑ᵢ Λ⁰ᵢ²`. -/
theorem lorentzEntry_row_gamma_sq :
    lorentzEntry Λ 0 0 ^ 2
      = 1 + ∑ i : Fin 3, lorentzEntry Λ 0 i.succ ^ 2 := by
  have h := lorentzEntry_row_gram Λ 0 0
  rw [Fin.sum_univ_succ] at h
  simp at h
  simp_rw [pow_two]
  linarith

/-- **Time/spatial-row orthogonality**:
`∑ᵢ Bⱼᵢ Λ⁰ᵢ = Λ⁰₀ Λʲ₀`. This is the identity that contracts the rank-one
Jacobian update with the cofactor matrix. -/
theorem lorentzEntry_row_time (j : Fin 3) :
    ∑ i : Fin 3, lorentzEntry Λ j.succ i.succ * lorentzEntry Λ 0 i.succ
      = lorentzEntry Λ 0 0 * lorentzEntry Λ j.succ 0 := by
  have h := lorentzEntry_row_gram Λ 0 j.succ
  rw [Fin.sum_univ_succ] at h
  have hne : (0 : Fin 4) ≠ j.succ := (Fin.succ_ne_zero j).symm
  simp [hne] at h
  calc
    ∑ i : Fin 3, lorentzEntry Λ j.succ i.succ * lorentzEntry Λ 0 i.succ
        = ∑ i : Fin 3, lorentzEntry Λ 0 i.succ * lorentzEntry Λ j.succ i.succ := by
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = lorentzEntry Λ 0 0 * lorentzEntry Λ j.succ 0 := by linarith

/-! ### Bijection and smooth inverse on the positive sheet -/

/-- `shellMap m Λ⁻¹` is a left inverse of `shellMap m Λ`. The key step is the exact
four-momentum round trip `massShellParam_shellMap`. -/
theorem shellMap_inv_shellMap (hm : 0 < m) :
    shellMap m Λ⁻¹ (shellMap m Λ p) = p := by
  rw [shellMap, massShellParam_shellMap m Λ p hm]
  change spatialOf ((Λ : M4 ≃L[ℝ] M4).symm
    ((Λ : M4 ≃L[ℝ] M4) (massShellParam m p))) = p
  rw [ContinuousLinearEquiv.symm_apply_apply, spatialOf_massShellParam]

/-- `shellMap m Λ⁻¹` is also a right inverse of `shellMap m Λ`. -/
theorem shellMap_shellMap_inv (hm : 0 < m) :
    shellMap m Λ (shellMap m Λ⁻¹ p) = p := by
  simpa using (shellMap_inv_shellMap (m := m) (Λ := Λ⁻¹) (p := p) hm)

/-- Injectivity of the Lorentz-transformed momentum map. -/
theorem injective_shellMap (hm : 0 < m) : Function.Injective (shellMap m Λ) := by
  intro q r hqr
  calc q = shellMap m Λ⁻¹ (shellMap m Λ q) :=
        (shellMap_inv_shellMap (m := m) (Λ := Λ) (p := q) hm).symm
    _ = shellMap m Λ⁻¹ (shellMap m Λ r) := congrArg (shellMap m Λ⁻¹) hqr
    _ = r := shellMap_inv_shellMap (m := m) (Λ := Λ) (p := r) hm

/-- Surjectivity of the Lorentz-transformed momentum map, with explicit preimage
`shellMap m Λ⁻¹ q`. -/
theorem surjective_shellMap (hm : 0 < m) : Function.Surjective (shellMap m Λ) := by
  intro q
  exact ⟨shellMap m Λ⁻¹ q, shellMap_shellMap_inv (m := m) (Λ := Λ) (p := q) hm⟩

/-- Bijection of physical momentum space induced by any restricted Lorentz
transformation. -/
theorem bijective_shellMap (hm : 0 < m) : Function.Bijective (shellMap m Λ) :=
  ⟨injective_shellMap m Λ hm, surjective_shellMap m Λ hm⟩

/-- Smoothness of the explicit inverse `shellMap m Λ⁻¹`. -/
theorem contDiff_shellMap_inv {n : WithTop ℕ∞} (hm : 0 < m) :
    ContDiff ℝ n (shellMap m Λ⁻¹) :=
  contDiff_shellMap m Λ⁻¹ hm.ne'

/-- **Diffeomorphism data** for the shell action: two-sided inverse laws and smoothness of
both directions. This is the Banach-space form of the induced diffeomorphism of the
positive mass hyperboloid, without introducing a second manifold-level wrapper. -/
theorem shellMap_diffeomorphism (hm : 0 < m) :
    Function.LeftInverse (shellMap m Λ⁻¹) (shellMap m Λ)
      ∧ Function.RightInverse (shellMap m Λ⁻¹) (shellMap m Λ)
      ∧ ContDiff ℝ ⊤ (shellMap m Λ)
      ∧ ContDiff ℝ ⊤ (shellMap m Λ⁻¹) := by

  refine ⟨fun q => shellMap_inv_shellMap (m := m) (Λ := Λ) (p := q) hm,
    fun q => shellMap_shellMap_inv (m := m) (Λ := Λ) (p := q) hm, ?_, ?_⟩
  · exact contDiff_shellMap m Λ hm.ne'
  · exact contDiff_shellMap_inv m Λ hm
/-! ### Fréchet derivatives of the shell parametrization and shell map -/

/-- Transport a derivative statement across equality of continuous linear maps. -/
private theorem hasFDerivAt_congr_deriv' {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D₁ D₂ : E →L[ℝ] F} {f : E → F} {x : E}
    (h : HasFDerivAt f D₁ x) (hD : D₁ = D₂) : HasFDerivAt f D₂ x := by
  rw [hD] at h
  exact h

private theorem innerSL_coe_apply (w y : M3) : (innerSL ℝ w) y = inner ℝ w y := rfl

private theorem nat_smul_real (n : ℕ) (r : ℝ) : n • r = n * r := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [succ_nsmul, ih, Nat.cast_succ, add_one_mul]

/-- **Derivative of the physical energy**:
`dω_p(h) = ⟪p,h⟫ / ω_p`. The denominator is nonzero for `m ≠ 0`. -/
theorem hasFDerivAt_physicalEnergy (hm : m ≠ 0) :
    HasFDerivAt (physicalEnergy m)
      ((physicalEnergy m p)⁻¹ • innerSL ℝ p) p := by
  have hnormsq : HasFDerivAt (fun z : M3 => ‖z‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ p) p := by
    have h0 := (hasFDerivAt_id p).norm_sq
    refine hasFDerivAt_congr_deriv' h0 ?_
    ext z
    simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      id_eq, innerSL_coe_apply, nat_smul_real, smul_eq_mul]
    ring
  have hsum : HasFDerivAt (fun z : M3 => ‖z‖ ^ 2 + m ^ 2)
      ((2 : ℝ) • innerSL ℝ p) p :=
    hasFDerivAt_congr_deriv' (hnormsq.add (hasFDerivAt_const (m ^ 2) p)) (by simp)
  have hrad : ‖p‖ ^ 2 + m ^ 2 ≠ 0 := by
    have hm2 : 0 < m ^ 2 := sq_pos_iff.mpr hm
    nlinarith [sq_nonneg ‖p‖]
  have hs := hsum.sqrt hrad
  refine hasFDerivAt_congr_deriv' hs ?_
  ext z
  simp only [smul_apply, smul_eq_mul, innerSL_coe_apply]
  have hc : ((1 : ℝ) / (2 * √(‖p‖ ^ 2 + m ^ 2))) * 2
      = (physicalEnergy m p)⁻¹ := by
    have hpos : 0 < √(‖p‖ ^ 2 + m ^ 2) := Real.sqrt_pos.2 (by positivity)
    have heq : √(‖p‖ ^ 2 + m ^ 2) = physicalEnergy m p := rfl
    rw [heq]
    field_simp [ne_of_gt hpos]
  rw [← mul_assoc, hc]

/-- The derivative of `massShellParam m` at `p`: time component
`ω_p⁻¹⟪p,h⟫`, spatial component `h`. -/
noncomputable def massShellParamDeriv (m : ℝ) (p : M3) : M3 →L[ℝ] M4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h => !₂[(physicalEnergy m p)⁻¹ * inner ℝ p h, h 0, h 1, h 2]
      map_add' := by
        intro h k
        ext j
        fin_cases j <;> simp [inner_add_right]
        all_goals ring
      map_smul' := by
        intro c h
        ext j
        fin_cases j <;> simp [real_inner_smul_right]
        all_goals ring }

@[simp] theorem massShellParamDeriv_apply_zero (h : M3) :
    massShellParamDeriv m p h 0 = (physicalEnergy m p)⁻¹ * inner ℝ p h := by
  simp [massShellParamDeriv]

@[simp] theorem massShellParamDeriv_apply_one (h : M3) :
    massShellParamDeriv m p h 1 = h 0 := by simp [massShellParamDeriv]

@[simp] theorem massShellParamDeriv_apply_two (h : M3) :
    massShellParamDeriv m p h 2 = h 1 := by simp [massShellParamDeriv]

@[simp] theorem massShellParamDeriv_apply_three (h : M3) :
    massShellParamDeriv m p h 3 = h 2 := by simp [massShellParamDeriv]

/-- Exact derivative of the positive-shell parametrization. -/
theorem hasFDerivAt_massShellParam (hm : m ≠ 0) :
    HasFDerivAt (massShellParam m) (massShellParamDeriv m p) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro j
  fin_cases j
  · have h := (hasFDerivAt_physicalEnergy m p hm).hasFDerivWithinAt (s := Set.univ)
    refine (h.congr_fderiv ?_).congr' ?_ (Set.mem_univ p)
    · ext v
      simp [massShellParamDeriv]
    · intro x hx
      simp [massShellParam]
  · have h := ((EuclideanSpace.proj 0 : M3 →L[ℝ] ℝ).hasFDerivAt (x := p)).hasFDerivWithinAt (s := Set.univ)
    refine (h.congr_fderiv ?_).congr' ?_ (Set.mem_univ p)
    · ext v
      simp [massShellParamDeriv]
    · intro x hx
      simp [massShellParam]
  · have h := ((EuclideanSpace.proj 1 : M3 →L[ℝ] ℝ).hasFDerivAt (x := p)).hasFDerivWithinAt (s := Set.univ)
    refine (h.congr_fderiv ?_).congr' ?_ (Set.mem_univ p)
    · ext v
      simp [massShellParamDeriv]
    · intro x hx
      simp [massShellParam]
  · have h := ((EuclideanSpace.proj 2 : M3 →L[ℝ] ℝ).hasFDerivAt (x := p)).hasFDerivWithinAt (s := Set.univ)
    refine (h.congr_fderiv ?_).congr' ?_ (Set.mem_univ p)
    · ext v
      simp [massShellParamDeriv]
    · intro x hx
      simp [massShellParam]

/-- The spatial projection packaged as a continuous linear map. -/
noncomputable def spatialOfCLM : M4 →L[ℝ] M3 :=
  LinearMap.toContinuousLinearMap
    { toFun := spatialOf
      map_add' := by
        intro q r
        ext j
        fin_cases j <;> simp [spatialOf]
      map_smul' := by
        intro c q
        ext j
        fin_cases j <;> simp [spatialOf] }

@[simp] theorem spatialOfCLM_apply (q : M4) : spatialOfCLM q = spatialOf q := rfl

/-- Candidate derivative of `shellMap`: compose the derivative of the shell
parametrization with `Λ` and the spatial projection. -/
noncomputable def dshellMap (m : ℝ) (Λ : RestrictedLorentzGroup) (p : M3) : M3 →L[ℝ] M3 :=
  (spatialOfCLM.comp (Λ : M4 ≃L[ℝ] M4).toContinuousLinearMap).comp
    (massShellParamDeriv m p)

/-- Exact Fréchet derivative of `shellMap`. -/
theorem hasFDerivAt_shellMap (hm : m ≠ 0) :
    HasFDerivAt (shellMap m Λ) (dshellMap m Λ p) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro j
  have hp := hasFDerivAt_massShellParam m p hm
  have hlin := ((EuclideanSpace.proj j.succ : M4 →L[ℝ] ℝ).comp
    (Λ : M4 ≃L[ℝ] M4).toContinuousLinearMap).hasFDerivAt
      (x := massShellParam m p)
  have h := (hlin.comp p hp).hasFDerivWithinAt (s := Set.univ)
  refine (h.congr_fderiv ?_).congr' ?_ (Set.mem_univ p)
  · ext v
    simp only [ContinuousLinearMap.comp_apply, dshellMap, spatialOfCLM_apply]
    exact (spatialOf_apply _ j).symm
  · intro x hx
    simp [shellMap, spatialOf_apply]

/-- The Fréchet derivative returned by Mathlib is `dshellMap`. -/
theorem fderiv_shellMap_eq (hm : m ≠ 0) :
    fderiv ℝ (shellMap m Λ) p = dshellMap m Λ p :=
  (hasFDerivAt_shellMap (m := m) (Λ := Λ) (p := p) hm).fderiv

@[simp] theorem massShellParamDeriv_apply_succ (v : M3) (i : Fin 3) :
    massShellParamDeriv m p v i.succ = v i := by
  fin_cases i <;> simp

/-- Coordinate expansion of a Lorentz transformation in its standard-basis entries. -/
theorem lorentz_apply_eq_sum (q : M4) (μ : Fin 4) :
    ((Λ : M4 ≃L[ℝ] M4) q) μ =
      ∑ ν : Fin 4, lorentzEntry Λ μ ν * q ν := by
  have hq : q = ∑ ν : Fin 4, q ν • EuclideanSpace.single ν 1 := by
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.sum_repr q).symm
  conv_lhs => rw [hq, map_sum]
  simp_rw [map_smul]
  change (EuclideanSpace.proj μ : M4 →L[ℝ] ℝ)
      (∑ ν : Fin 4, q ν •
        (Λ : M4 ≃L[ℝ] M4) (EuclideanSpace.single ν 1)) =
      ∑ ν : Fin 4, lorentzEntry Λ μ ν * q ν
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, lorentzEntry]
  exact Finset.sum_congr rfl fun ν _ => mul_comm _ _

/-- **Derivative formula in coordinates**:
`D(shellMap)_p(v)ⱼ = Λʲ₀ ⟪p,v⟫/ω_p + ∑ᵢ Λʲᵢ vᵢ`. -/
theorem dshellMap_apply (v : M3) (j : Fin 3) :
    dshellMap m Λ p v j =
      lorentzEntry Λ j.succ 0 * (inner ℝ p v / physicalEnergy m p)
        + ∑ i : Fin 3, lorentzEntry Λ j.succ i.succ * v i := by
  simp only [dshellMap, ContinuousLinearMap.comp_apply, spatialOfCLM_apply,
    spatialOf_apply]
  change ((Λ : M4 ≃L[ℝ] M4) (massShellParamDeriv m p v)) j.succ =
    lorentzEntry Λ j.succ 0 * (inner ℝ p v / physicalEnergy m p)
      + ∑ i : Fin 3, lorentzEntry Λ j.succ i.succ * v i
  rw [lorentz_apply_eq_sum, Fin.sum_univ_succ, massShellParamDeriv_apply_zero]
  simp_rw [massShellParamDeriv_apply_succ]
  rw [div_eq_mul_inv]
  ring

/-- **Derivative-entry formula** in the standard spatial basis:
`∂(shellMap)ⱼ/∂pᵢ = Λʲᵢ + Λʲ₀ pᵢ/ω_p`. -/
theorem fderiv_shellMap_entry (hm : m ≠ 0) (j i : Fin 3) :
    (fderiv ℝ (shellMap m Λ) p) (EuclideanSpace.single i 1) j =
      lorentzEntry Λ j.succ i.succ
        + lorentzEntry Λ j.succ 0 * p i / physicalEnergy m p := by
  rw [fderiv_shellMap_eq (m := m) (Λ := Λ) (p := p) hm,
    dshellMap_apply]
  simp [PiLp.single_apply, EuclideanSpace.inner_single_right]
  ring

/-! ### The `Fin 3` Jacobian determinant -/

/-- Three-dimensional rank-one determinant expansion, proved by the explicit
`Matrix.det_fin_three` formula. -/
private theorem det_rankOne_fin_three (B : Matrix (Fin 3) (Fin 3) ℝ)
    (s v : Fin 3 → ℝ) :
    Matrix.det (fun j i => B j i + s j * v i) =
      Matrix.det B + ∑ j : Fin 3, s j * Matrix.det (B.updateRow j v) := by
  rw [Fin.sum_univ_three]
  simp_rw [Matrix.det_fin_three]
  simp [Matrix.updateRow]
  ring

/-- Cofactor contraction for `Fin 3`, again proved by
`Matrix.det_fin_three`: `adj(B) (B u) = det(B) u` written only in rows. -/
private theorem det_updateRow_cofPair (B : Matrix (Fin 3) (Fin 3) ℝ)
    (u v : Fin 3 → ℝ) :
    ∑ j : Fin 3, (∑ i : Fin 3, B j i * u i) * Matrix.det (B.updateRow j v) =
      Matrix.det B * ∑ i : Fin 3, u i * v i := by
  rw [Fin.sum_univ_three]
  simp_rw [Fin.sum_univ_three, Matrix.det_fin_three]
  simp [Matrix.updateRow]
  ring

private noncomputable def blockMatrix4 (γ : ℝ) (β c : Fin 3 → ℝ)
    (B : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![γ, β 0, β 1, β 2;
     c 0, B 0 0, B 0 1, B 0 2;
     c 1, B 1 0, B 1 1, B 1 2;
     c 2, B 2 0, B 2 1, B 2 2]

/-- Laplace expansion of a `1+3` block matrix, with all three minors evaluated by
`Matrix.det_fin_three`. -/
private theorem det_blockMatrix4 (γ : ℝ) (β c : Fin 3 → ℝ)
    (B : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.det (blockMatrix4 γ β c B) =
      γ * Matrix.det B - ∑ i : Fin 3, β i * Matrix.det (B.updateCol i c) := by
  have h0 : (blockMatrix4 γ β c B).submatrix Fin.succ (0 : Fin 4).succAbove = B := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [blockMatrix4]
  have h1 : (blockMatrix4 γ β c B).submatrix Fin.succ (1 : Fin 4).succAbove =
      !![c 0, B 0 1, B 0 2; c 1, B 1 1, B 1 2; c 2, B 2 1, B 2 2] := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [blockMatrix4, Fin.succAbove]
  have h2 : (blockMatrix4 γ β c B).submatrix Fin.succ (2 : Fin 4).succAbove =
      !![c 0, B 0 0, B 0 2; c 1, B 1 0, B 1 2; c 2, B 2 0, B 2 2] := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [blockMatrix4, Fin.succAbove]
  have h3 : (blockMatrix4 γ β c B).submatrix Fin.succ (3 : Fin 4).succAbove =
      !![c 0, B 0 0, B 0 1; c 1, B 1 0, B 1 1; c 2, B 2 0, B 2 1] := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [blockMatrix4, Fin.succAbove]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four, h0, h1, h2, h3,
    Fin.sum_univ_three]
  simp_rw [Matrix.det_fin_three]
  simp [blockMatrix4, Matrix.updateCol]
  ring

/-- Time-time entry, top spatial row, time spatial column, and spatial block of `Λ`. -/
noncomputable def lorentzGamma (Λ : RestrictedLorentzGroup) : ℝ := lorentzEntry Λ 0 0
noncomputable def lorentzBeta (Λ : RestrictedLorentzGroup) (i : Fin 3) : ℝ :=
  lorentzEntry Λ 0 i.succ
noncomputable def lorentzTimeColumn (Λ : RestrictedLorentzGroup) (j : Fin 3) : ℝ :=
  lorentzEntry Λ j.succ 0
noncomputable def lorentzSpatialBlock (Λ : RestrictedLorentzGroup) :
    Matrix (Fin 3) (Fin 3) ℝ := fun j i => lorentzEntry Λ j.succ i.succ

private theorem lorentzMat_eq_block :
    lorentzMat Λ = blockMatrix4 (lorentzGamma Λ) (lorentzBeta Λ)
      (lorentzTimeColumn Λ) (lorentzSpatialBlock Λ) := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [lorentzMat, blockMatrix4, lorentzGamma, lorentzBeta,
      lorentzTimeColumn, lorentzSpatialBlock]

private theorem det_updateCol_eq_updateRow_transpose
    (B : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (j : Fin 3) :
    Matrix.det (B.updateCol j c) = Matrix.det (Bᵀ.updateRow j c) := by
  rw [← Matrix.det_transpose]
  congr 1
  ext i k
  by_cases hij : i = j
  · subst i
    simp [Matrix.updateCol, Matrix.updateRow]
  · simp [Matrix.updateCol, Matrix.updateRow, hij]
/-- **Spatial-block determinant identity**: properness (`det Λ = 1`) fixes the sign left
undetermined by pseudo-orthogonality, giving `det B = Λ⁰₀`. -/
theorem det_lorentzSpatialBlock :
    Matrix.det (lorentzSpatialBlock Λ) = lorentzGamma Λ := by
  let γ := lorentzGamma Λ
  let β := lorentzBeta Λ
  let c := lorentzTimeColumn Λ
  let B := lorentzSpatialBlock Λ
  have hdet : γ * Matrix.det B - ∑ i : Fin 3, β i * Matrix.det (B.updateCol i c) = 1 := by
    rw [← det_blockMatrix4, ← lorentzMat_eq_block]
    exact lorentzMat_det_eq_one Λ
  have hcol (i : Fin 3) : ∑ r : Fin 3, B r i * c r = γ * β i := by
    simpa [B, c, γ, β, lorentzSpatialBlock, lorentzTimeColumn, lorentzGamma,
      lorentzBeta, mul_comm] using lorentzEntry_col_time Λ i
  have hcof := det_updateRow_cofPair Bᵀ c c
  have htail :
      γ * (∑ i : Fin 3, β i * Matrix.det (B.updateCol i c)) =
        Matrix.det B * ∑ i : Fin 3, c i ^ 2 := by
    calc
      γ * (∑ i : Fin 3, β i * Matrix.det (B.updateCol i c))
          = ∑ i : Fin 3, (∑ r : Fin 3, Bᵀ i r * c r) *
              Matrix.det (Bᵀ.updateRow i c) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun i _ => by
                  change γ * (β i * Matrix.det (B.updateCol i c)) =
                    (∑ r : Fin 3, B r i * c r) * Matrix.det (Bᵀ.updateRow i c)
                  rw [hcol, ← det_updateCol_eq_updateRow_transpose]
                  ring
      _ = Matrix.det Bᵀ * ∑ i : Fin 3, c i * c i := hcof
      _ = Matrix.det B * ∑ i : Fin 3, c i ^ 2 := by
        rw [Matrix.det_transpose]
        congr 1
        exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
  have hgamma : γ ^ 2 = 1 + ∑ i : Fin 3, c i ^ 2 := by
    simpa [γ, c, lorentzGamma, lorentzTimeColumn] using lorentzEntry_gamma_sq Λ
  have hmult : γ * (γ * Matrix.det B - ∑ i : Fin 3,
      β i * Matrix.det (B.updateCol i c)) = γ := by rw [hdet, mul_one]
  rw [mul_sub, ← mul_assoc γ γ (Matrix.det B),
    show γ * γ = γ ^ 2 by ring, hgamma, htail] at hmult
  ring_nf at hmult
  dsimp [B, γ] at hmult ⊢
  exact hmult

noncomputable def shellJacobianMatrix (m : ℝ) (Λ : RestrictedLorentzGroup) (p : M3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun j i => lorentzSpatialBlock Λ j i +
    lorentzTimeColumn Λ j * p i / physicalEnergy m p

theorem lorentzGamma_pos : 0 < lorentzGamma Λ := by
  simpa [lorentzGamma, lorentzEntry] using RestrictedLorentzGroup.orthochronous Λ

/-- Time component of the transformed four-momentum in block entries. -/
private theorem massShellParam_apply_succ (i : Fin 3) :
    massShellParam m p i.succ = p i := by
  fin_cases i <;> simp
theorem lorentz_time_massShellParam :
    ((Λ : M4 ≃L[ℝ] M4) (massShellParam m p)) 0 =
      lorentzGamma Λ * physicalEnergy m p +
        ∑ i : Fin 3, lorentzBeta Λ i * p i := by
  rw [lorentz_apply_eq_sum, Fin.sum_univ_succ]
  simp_rw [massShellParam_apply_succ]
  simp [lorentzGamma, lorentzBeta, lorentzEntry]

/-- Determinant of the physical-momentum Jacobian before taking absolute values. -/
theorem det_shellJacobianMatrix (hm : 0 < m) :
    Matrix.det (shellJacobianMatrix m Λ p) =
      physicalEnergy m (shellMap m Λ p) / physicalEnergy m p := by
  let γ := lorentzGamma Λ
  let β := lorentzBeta Λ
  let c := lorentzTimeColumn Λ
  let B := lorentzSpatialBlock Λ
  let ω := physicalEnergy m p
  have hrow (j : Fin 3) : ∑ i : Fin 3, B j i * β i = γ * c j := by
    simpa [B, β, γ, c, lorentzSpatialBlock, lorentzBeta, lorentzGamma,
      lorentzTimeColumn] using lorentzEntry_row_time Λ j
  have hcof := det_updateRow_cofPair B β p
  have hsum : ∑ j : Fin 3, c j * Matrix.det (B.updateRow j p) =
      ∑ i : Fin 3, β i * p i := by
    have hscaled :
        γ * (∑ j : Fin 3, c j * Matrix.det (B.updateRow j p)) =
          γ * ∑ i : Fin 3, β i * p i := by
      calc
        γ * (∑ j : Fin 3, c j * Matrix.det (B.updateRow j p))
            = ∑ j : Fin 3, (∑ i : Fin 3, B j i * β i) *
                Matrix.det (B.updateRow j p) := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun j _ => by
                    rw [hrow]
                    ring
        _ = Matrix.det B * ∑ i : Fin 3, β i * p i := hcof
        _ = γ * ∑ i : Fin 3, β i * p i := by
          rw [det_lorentzSpatialBlock (Λ := Λ)]
    have hγ : 0 < γ := by simpa [γ] using lorentzGamma_pos Λ
    nlinarith
  have hω : ω ≠ 0 := ne_of_gt (by simpa [ω] using physicalEnergy_pos m p hm)
  have hdet := det_rankOne_fin_three B (fun j => c j / ω) p
  have hmatrix : shellJacobianMatrix m Λ p =
      fun j i => B j i + (c j / ω) * p i := by
    ext j i
    simp [shellJacobianMatrix, B, c, ω, div_eq_mul_inv]
    ring
  have hdiv :
      ∑ j : Fin 3, (c j / ω) * Matrix.det (B.updateRow j p) =
        (∑ j : Fin 3, c j * Matrix.det (B.updateRow j p)) / ω := by
    rw [div_eq_mul_inv]
    calc
      ∑ j : Fin 3, c j * ω⁻¹ * Matrix.det (B.updateRow j p)
          = ∑ j : Fin 3, (c j * Matrix.det (B.updateRow j p)) * ω⁻¹ := by
              exact Finset.sum_congr rfl fun j _ => by ring
      _ = (∑ j : Fin 3, c j * Matrix.det (B.updateRow j p)) * ω⁻¹ :=
        by rw [Finset.sum_mul]
  rw [hmatrix, hdet, det_lorentzSpatialBlock (Λ := Λ), hdiv, hsum]
  rw [physicalEnergy_shellMap m Λ p hm, lorentz_time_massShellParam]
  have hω' : physicalEnergy m p ≠ 0 := by simpa [ω] using hω
  dsimp [β, ω]
  simp only [div_eq_mul_inv]
  rw [add_mul, mul_assoc (lorentzGamma Λ), mul_inv_cancel₀ hω', mul_one]

private theorem toMatrix_fderiv_shellMap (hm : m ≠ 0) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ |>.toBasis)
      (EuclideanSpace.basisFun (Fin 3) ℝ |>.toBasis)
      (fderiv ℝ (shellMap m Λ) p : M3 →ₗ[ℝ] M3) =
        shellJacobianMatrix m Λ p := by
  ext j i
  rw [LinearMap.toMatrix_apply]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr,
    shellJacobianMatrix, lorentzSpatialBlock, lorentzTimeColumn,
    fderiv_shellMap_entry (m := m) (Λ := Λ) (p := p) hm]

/-- **Absolute Jacobian identity** (Wigner 1939, §6, footnote 26):
`|det D(shellMap)_p| = ω_(shellMap p) / ω_p`. -/
theorem abs_det_fderiv_shellMap (hm : 0 < m) :
    |(fderiv ℝ (shellMap m Λ) p).det| =
      physicalEnergy m (shellMap m Λ p) / physicalEnergy m p := by
  change |LinearMap.det (fderiv ℝ (shellMap m Λ) p : M3 →ₗ[ℝ] M3)| = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ |>.toBasis)
    (fderiv ℝ (shellMap m Λ) p : M3 →ₗ[ℝ] M3)]
  rw [toMatrix_fderiv_shellMap (m := m) (Λ := Λ) (p := p) hm.ne',
    det_shellJacobianMatrix (m := m) (Λ := Λ) (p := p) hm]
  rw [abs_of_pos]
  exact div_pos (physicalEnergy_pos m _ hm) (physicalEnergy_pos m p hm)

/-! ### Weighted-measure invariance -/

/-- **Restricted-Lorentz invariance of the physical shell weight**:
pullback by `shellMap m Λ` preserves `d³p/(2ω_p)`. This is the direct
change-of-variables form of Wigner 1939, §6, eq. (59a), footnote 26. -/
theorem integral_weighted_massShell_invariance (hm : 0 < m) (ψ : M3 → ℝ) :
    ∫ q, ψ q / (2 * physicalEnergy m q) ∂volume =
      ∫ p, ψ (shellMap m Λ p) / (2 * physicalEnergy m p) ∂volume := by
  have hf' : ∀ x ∈ (Set.univ : Set M3),
      HasFDerivWithinAt (shellMap m Λ) (fderiv ℝ (shellMap m Λ) x) Set.univ x := by
    intro x hx
    have h := hasFDerivAt_shellMap (m := m) (Λ := Λ) (p := x) hm.ne'
    rw [← fderiv_shellMap_eq (m := m) (Λ := Λ) (p := x) hm.ne'] at h
    exact h.hasFDerivWithinAt
  have himage : shellMap m Λ '' Set.univ = Set.univ := by
    ext q
    constructor
    · intro h
      exact Set.mem_univ q
    · intro h
      obtain ⟨p, hp⟩ := surjective_shellMap m Λ hm q
      exact ⟨p, Set.mem_univ p, hp⟩
  have hpoint (x : M3) :
      |(fderiv ℝ (shellMap m Λ) x).det| •
          (ψ (shellMap m Λ x) / (2 * physicalEnergy m (shellMap m Λ x))) =
        ψ (shellMap m Λ x) / (2 * physicalEnergy m x) := by
    rw [abs_det_fderiv_shellMap (m := m) (Λ := Λ) (p := x) hm]
    simp only [smul_eq_mul]
    have hi : physicalEnergy m (shellMap m Λ x) ≠ 0 :=
      ne_of_gt (physicalEnergy_pos m _ hm)
    have hx : physicalEnergy m x ≠ 0 := ne_of_gt (physicalEnergy_pos m x hm)
    field_simp [hi, hx]
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul
    (μ := (volume : Measure M3)) (s := (Set.univ : Set M3))
    (f := shellMap m Λ) (f' := fun x => fderiv ℝ (shellMap m Λ) x)
    MeasurableSet.univ hf' (injective_shellMap m Λ hm).injOn
    (fun q : M3 => ψ q / (2 * physicalEnergy m q))
  rw [himage] at hcov
  simpa only [Measure.restrict_univ, hpoint] using hcov

end QFT.KleinGordon
