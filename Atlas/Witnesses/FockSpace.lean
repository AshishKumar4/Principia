import Atlas.Specs.QFT.FockSpace

/-!
# Witnesses — symmetric Fock space (P2.2, slice 1)

Non-vacuity witnesses for `Atlas/Specs/QFT/FockSpace.lean` on the concrete model
`E₂ = EuclideanSpace ℂ (Fin 2)`, whose standard basis gives *distinguishable* slots —
the only setting in which the symmetrizer has observable content.

* **Algebraic layer.** The degree-`2` symmetrizer in closed form
  (`symmetrizer_tprod_two`), evaluated on `e₀ ⊗ e₁`:
  `S(e₀ ⊗ e₁) = ½(e₀ ⊗ e₁ + e₁ ⊗ e₀)`, with the pairing `⟪e₀ ⊗ e₁, S(e₀ ⊗ e₁)⟫ = ½` and
  `‖S(e₀ ⊗ e₁)‖² = ½`. The latter pins the **projector, not isometry** convention of the
  spec: symmetrized pure tensors on distinguishable slots are not unit vectors, and the
  `√(n+1)` factors this trades off belong to the creation operators of the next slice.
  Expected-false: `symmetrizer ℂ E₂ 2 ≠ LinearMap.id`.
* **Completed layer.** `symmetrizerL` agreeing with the algebraic symmetrizer on the dense
  image, the symmetrized element lying in `SymTensorPower ℂ E₂ 2`, and the expected-false
  `e₀ ⊗ e₁ ∉ SymTensorPower ℂ E₂ 2` — the sector is a proper subspace, hence a real
  constraint. In degrees `n ≤ 1` it *is* the whole space
  (`symTensorPower_eq_top_of_le_one`), the sharp complement.
* **Fock layer.** Vacuum and one-particle states as `lp.single` vectors, their norms, their
  orthogonality, the two-sector Pythagorean norm `‖Ω + ψ‖² = 1 + ‖ψ‖²`, and finite-particle
  membership of both and of their sum.

Import discipline (spec module docstring, "Scope discipline"): this file opens the scoped
`PiTensorProduct.InnerNorm` instances and replicates the spec's `assert_not_exists` guard,
so it can never acquire Mathlib's projective-seminorm instances and form a norm diamond
against the ℓ² cross norm baked into `HilbertTensorPower`.

Note on the pairings: on `⨂[ℂ]^n E` the `Inner` instance found by elaboration is
`PiTensorProduct.instInner`, so the inner-product computations here go through
`PiTensorProduct.inner_def` and the bundled `innerAux`; the bridge to the norm of the
scoped inner-product-space structure is definitional (`inner_self_eq_norm_sq_to_K`
applies as a term).
-/

assert_not_exists PiTensorProduct.projectiveSeminorm

noncomputable section

namespace Atlas.Witnesses.FockSpace

open PiTensorProduct QFT UniformSpace
open scoped TensorProduct PiTensorProduct.InnerNorm ENNReal

/-- The model one-particle space: `ℂ²` with its Euclidean inner product. -/
abbrev E₂ : Type := EuclideanSpace ℂ (Fin 2)

/-- The standard basis vectors `e₀, e₁` of the model space. -/
def e (i : Fin 2) : E₂ := EuclideanSpace.single i (1 : ℂ)

@[simp] theorem norm_e (i : Fin 2) : ‖e i‖ = 1 := by simp [e]

/-- The model basis is orthonormal — the input to every pairing computation below. -/
theorem inner_e_e (i j : Fin 2) : inner ℂ (e i) (e j) = if i = j then (1 : ℂ) else 0 := by
  have h := (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal
  rw [orthonormal_iff_ite] at h
  simpa [e, EuclideanSpace.basisFun_apply] using h i j

/-- The distinguishable pure `2`-tensor `e₀ ⊗ e₁`. -/
def e₀₁ : ⨂[ℂ]^2 E₂ := tprod ℂ ![e 0, e 1]

/-- Its transpose `e₁ ⊗ e₀`. -/
def e₁₀ : ⨂[ℂ]^2 E₂ := tprod ℂ ![e 1, e 0]

@[simp] theorem inner_e₀₁_e₀₁ : inner ℂ e₀₁ e₀₁ = (1 : ℂ) := by
  simp [e₀₁, Fin.prod_univ_two]

@[simp] theorem inner_e₁₀_e₁₀ : inner ℂ e₁₀ e₁₀ = (1 : ℂ) := by
  simp [e₁₀, Fin.prod_univ_two]

/-- `e₀ ⊗ e₁` and `e₁ ⊗ e₀` are orthogonal: the tensor power sees the slot order. This is
what makes the model a genuine test of symmetrization. -/
@[simp] theorem inner_e₀₁_e₁₀ : inner ℂ e₀₁ e₁₀ = (0 : ℂ) := by
  simp [e₀₁, e₁₀, Fin.prod_univ_two, inner_e_e]

@[simp] theorem inner_e₁₀_e₀₁ : inner ℂ e₁₀ e₀₁ = (0 : ℂ) := by
  simp [e₀₁, e₁₀, Fin.prod_univ_two, inner_e_e]

@[simp] theorem norm_e₀₁ : ‖e₀₁‖ = 1 := by
  simp [e₀₁, Fin.prod_univ_two]

/-! ### The algebraic symmetrizer in degree 2 -/

/-- The degree-`2` symmetrizer in closed form: `S(x₀ ⊗ x₁) = ½(x₀ ⊗ x₁ + x₁ ⊗ x₀)`.
The sum over `S₂ = {1, (0 1)}` is enumerated by `decide`. -/
theorem symmetrizer_tprod_two (x : Fin 2 → E₂) :
    symmetrizer ℂ E₂ 2 (tprod ℂ x) = (2 : ℂ)⁻¹ • (tprod ℂ x + tprod ℂ ![x 1, x 0]) := by
  rw [symmetrizer_tprod]
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
  have h1 : (fun i => x ((1 : Equiv.Perm (Fin 2)) i)) = x := rfl
  have h2 : (fun i => x (Equiv.swap 0 1 i)) = ![x 1, x 0] := by
    funext i
    fin_cases i <;> simp
  rw [h1, h2]
  norm_num [Nat.factorial]

/-- The symmetrizer on distinguishable slots: `S(e₀ ⊗ e₁) = ½(e₀ ⊗ e₁ + e₁ ⊗ e₀)`. -/
theorem symmetrizer_e₀₁ : symmetrizer ℂ E₂ 2 e₀₁ = (2 : ℂ)⁻¹ • (e₀₁ + e₁₀) := by
  have h := symmetrizer_tprod_two ![e 0, e 1]
  simpa [e₀₁, e₁₀] using h

/-- **The pairing witness**: `⟪e₀ ⊗ e₁, S(e₀ ⊗ e₁)⟫ = ½`. Only the identity permutation
contributes, so the `(n!)⁻¹ = ½` normalization is read off directly. -/
theorem inner_e₀₁_symmetrizer_e₀₁ :
    inner ℂ e₀₁ (symmetrizer ℂ E₂ 2 e₀₁) = (1 / 2 : ℂ) := by
  rw [symmetrizer_e₀₁, inner_def, map_smul, map_add, ← inner_def, ← inner_def,
    inner_e₀₁_e₀₁, inner_e₀₁_e₁₀]
  norm_num

/-- **Expected-false**: in degree `2` the symmetrizer is not the identity. Contrast
`symmetrizer_eq_id` in degrees `n ≤ 1`. -/
theorem symmetrizer_two_ne_id : symmetrizer ℂ E₂ 2 ≠ LinearMap.id := by
  intro h
  have h2 := inner_e₀₁_symmetrizer_e₀₁
  rw [h, LinearMap.id_coe, id_eq, inner_e₀₁_e₀₁] at h2
  norm_num at h2

/-- The same expected-false, pointwise: the symmetrizer moves `e₀ ⊗ e₁`. -/
theorem symmetrizer_e₀₁_ne_self : symmetrizer ℂ E₂ 2 e₀₁ ≠ e₀₁ := by
  intro h
  have h2 := inner_e₀₁_symmetrizer_e₀₁
  rw [h, inner_e₀₁_e₀₁] at h2
  norm_num at h2

/-- Idempotency of the degree-`2` symmetrizer, instantiated on the model. -/
example : IsIdempotentElem (symmetrizer ℂ E₂ 2) := isIdempotentElem_symmetrizer ℂ E₂ 2

/-- Idempotency evaluated on the concrete tensor: symmetrizing twice changes nothing. -/
example : symmetrizer ℂ E₂ 2 (symmetrizer ℂ E₂ 2 e₀₁) = symmetrizer ℂ E₂ 2 e₀₁ := by
  have h := DFunLike.congr_fun (isIdempotentElem_symmetrizer ℂ E₂ 2) e₀₁
  rwa [Module.End.mul_apply] at h

/-- The self-pairing of the symmetrized tensor: `⟪S(e₀ ⊗ e₁), S(e₀ ⊗ e₁)⟫ = ½`. -/
theorem inner_symmetrizer_e₀₁_self :
    inner ℂ (symmetrizer ℂ E₂ 2 e₀₁) (symmetrizer ℂ E₂ 2 e₀₁) = (1 / 2 : ℂ) := by
  rw [symmetrizer_e₀₁, inner_def]
  simp only [map_smulₛₗ, map_add, LinearMap.smul_apply, LinearMap.add_apply, ← inner_def,
    inner_e₀₁_e₀₁, inner_e₀₁_e₁₀, inner_e₁₀_e₀₁, inner_e₁₀_e₁₀]
  norm_num [Complex.conj_ofNat]

/-- **The projector-not-isometry witness**: `‖S(e₀ ⊗ e₁)‖² = ½`, whereas `‖e₀ ⊗ e₁‖ = 1`.
With the orthogonal-projector normalization `(n!)⁻¹` of the spec, symmetrized pure tensors
on distinguishable slots are not unit vectors; the compensating `√(n+1)` factors appear in
the creation/annihilation operators, not here (spec docstring, "Symmetrizer
normalization"). -/
theorem norm_symmetrizer_e₀₁_sq : ‖symmetrizer ℂ E₂ 2 e₀₁‖ ^ 2 = 1 / 2 := by
  have h : ((‖symmetrizer ℂ E₂ 2 e₀₁‖ : ℂ)) ^ 2 = (1 / 2 : ℂ) :=
    (inner_self_eq_norm_sq_to_K (symmetrizer ℂ E₂ 2 e₀₁)).symm.trans inner_symmetrizer_e₀₁_self
  have h2 : ((‖symmetrizer ℂ E₂ 2 e₀₁‖ ^ 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    push_cast
    exact h
  exact_mod_cast h2

/-- **Expected-false**: the symmetrization of a unit pure tensor is not a unit vector. -/
theorem norm_symmetrizer_e₀₁_ne_one : ‖symmetrizer ℂ E₂ 2 e₀₁‖ ≠ 1 := by
  intro h
  have h2 := norm_symmetrizer_e₀₁_sq
  rw [h] at h2
  norm_num at h2

/-! ### The completed layer and the symmetric sectors -/

/-- `symmetrizerL` restricted to the dense algebraic image is the algebraic symmetrizer,
evaluated on the concrete element. -/
theorem symmetrizerL_e₀₁ :
    symmetrizerL ℂ E₂ 2 (e₀₁ : HilbertTensorPower ℂ E₂ 2) =
      (((2 : ℂ)⁻¹ • (e₀₁ + e₁₀) : ⨂[ℂ]^2 E₂) : HilbertTensorPower ℂ E₂ 2) := by
  rw [symmetrizerL_coe, symmetrizer_e₀₁]

/-- **The symmetrized element lies in the `2`-particle sector**: the range of
`symmetrizerL` is nontrivial. -/
theorem symmetrized_mem_symTensorPower :
    (((2 : ℂ)⁻¹ • (e₀₁ + e₁₀) : ⨂[ℂ]^2 E₂) : HilbertTensorPower ℂ E₂ 2) ∈
      SymTensorPower ℂ E₂ 2 :=
  LinearMap.mem_range.mpr ⟨(e₀₁ : HilbertTensorPower ℂ E₂ 2), symmetrizerL_e₀₁⟩

/-- The same membership read through the fixed-point characterization. -/
example :
    symmetrizerL ℂ E₂ 2 (((2 : ℂ)⁻¹ • (e₀₁ + e₁₀) : ⨂[ℂ]^2 E₂) : HilbertTensorPower ℂ E₂ 2) =
      (((2 : ℂ)⁻¹ • (e₀₁ + e₁₀) : ⨂[ℂ]^2 E₂) : HilbertTensorPower ℂ E₂ 2) :=
  (mem_symTensorPower_iff ℂ E₂ 2).mp symmetrized_mem_symTensorPower

/-- **Expected-false**: `e₀ ⊗ e₁` is *not* in the `2`-particle sector, so
`SymTensorPower ℂ E₂ 2` is a proper subspace of the ambient power — the sector is a real
constraint, not vacuously everything. -/
theorem e₀₁_not_mem_symTensorPower :
    (e₀₁ : HilbertTensorPower ℂ E₂ 2) ∉ SymTensorPower ℂ E₂ 2 := by
  rw [mem_symTensorPower_iff, symmetrizerL_coe, Completion.coe_inj]
  exact symmetrizer_e₀₁_ne_self

/-- The sharp complement: in degrees `n ≤ 1` the sector *is* everything, since there is
nothing to symmetrize (`symmetrizer_eq_id`), transported to the completion by density. -/
theorem symTensorPower_eq_top_of_le_one {n : ℕ} (hn : n ≤ 1) : SymTensorPower ℂ E₂ n = ⊤ := by
  have key : ∀ x : HilbertTensorPower ℂ E₂ n, symmetrizerL ℂ E₂ n x = x := by
    intro x
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (symmetrizerL ℂ E₂ n).continuous continuous_id
    | ih a => rw [symmetrizerL_coe, symmetrizer_eq_id ℂ E₂ n hn, LinearMap.id_coe, id_eq]
  exact eq_top_iff.mpr fun x _ => (mem_symTensorPower_iff ℂ E₂ n).mpr (key x)

example : SymTensorPower ℂ E₂ 0 = ⊤ := symTensorPower_eq_top_of_le_one (Nat.zero_le 1)
example : SymTensorPower ℂ E₂ 1 = ⊤ := symTensorPower_eq_top_of_le_one le_rfl

/-- The contraction bound, instantiated on the model. -/
example (y : HilbertTensorPower ℂ E₂ 2) : ‖symmetrizerL ℂ E₂ 2 y‖ ≤ ‖y‖ :=
  norm_symmetrizerL_apply_le ℂ E₂ 2 y

/-- Completed idempotency, instantiated on the model. -/
example (y : HilbertTensorPower ℂ E₂ 2) :
    symmetrizerL ℂ E₂ 2 (symmetrizerL ℂ E₂ 2 y) = symmetrizerL ℂ E₂ 2 y :=
  DFunLike.congr_fun (isIdempotentElem_symmetrizerL ℂ E₂ 2) y

/-! ### The boson Fock space over the model -/

/-- The one-particle sector vector carrying `ψ`. The membership proof is
`symmetrizer_eq_id`: in degree `1` every tensor is already symmetric. -/
def oneParticleVec (ψ : E₂) : SymTensorPower ℂ E₂ 1 :=
  ⟨((tprod ℂ ![ψ] : ⨂[ℂ]^1 E₂) : HilbertTensorPower ℂ E₂ 1), by
    rw [mem_symTensorPower_iff, symmetrizerL_coe, symmetrizer_eq_id ℂ E₂ 1 le_rfl,
      LinearMap.id_coe, id_eq]⟩

/-- The one-particle state `(0, ψ, 0, …)` of the boson Fock space (Reed & Simon II, §X.7). -/
def oneParticle (ψ : E₂) : BosonFock ℂ E₂ :=
  lp.single 2 1 (oneParticleVec ψ)

/-- The one-particle embedding is isometric: no normalization factor leaks into the
`n = 1` sector. -/
@[simp] theorem norm_oneParticle (ψ : E₂) : ‖oneParticle ψ‖ = ‖ψ‖ := by
  rw [oneParticle, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  show ‖((tprod ℂ ![ψ] : ⨂[ℂ]^1 E₂) : HilbertTensorPower ℂ E₂ 1)‖ = ‖ψ‖
  rw [Completion.norm_coe, PiTensorProduct.norm_tprod]
  simp

/-- **The sectors are orthogonal**: the vacuum is perpendicular to every one-particle
state, being supported at a different `lp` index. -/
theorem inner_vacuum_oneParticle (ψ : E₂) :
    inner ℂ (BosonFock.vacuum ℂ E₂) (oneParticle ψ) = 0 := by
  rw [BosonFock.vacuum, oneParticle, lp.inner_single_left,
    lp.single_apply_ne _ _ _ (by norm_num : (0 : ℕ) ≠ 1), inner_zero_right]

/-- **Two-sector norm**: `‖Ω + ψ‖² = 1 + ‖ψ‖²` — the Pythagorean identity across sectors.
Non-vacuity of the Hilbert-sum structure: the `lp` norm adds the sector norms in
quadrature. -/
theorem norm_vacuum_add_oneParticle_sq (ψ : E₂) :
    ‖BosonFock.vacuum ℂ E₂ + oneParticle ψ‖ ^ 2 = 1 + ‖ψ‖ ^ 2 := by
  rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (inner_vacuum_oneParticle ψ),
    BosonFock.norm_vacuum, norm_oneParticle, sq]
  norm_num

/-- One-particle states are finite-particle vectors. -/
theorem oneParticle_mem_finiteParticle (ψ : E₂) :
    oneParticle ψ ∈ BosonFock.finiteParticle ℂ E₂ :=
  le_iSup (fun N => LinearMap.range
      (lp.singleContinuousLinearMap ℂ (fun n => SymTensorPower ℂ E₂ n) 2 N).toLinearMap) 1
    ⟨oneParticleVec ψ, rfl⟩

/-- A genuinely two-sector finite-particle vector: `F₀` is more than the sectors
themselves. -/
example : BosonFock.vacuum ℂ E₂ + oneParticle (e 0) ∈ BosonFock.finiteParticle ℂ E₂ :=
  Submodule.add_mem _ (BosonFock.vacuum_mem_finiteParticle ℂ E₂)
    (oneParticle_mem_finiteParticle (e 0))

/-- Non-vacuity of the one-particle sector: `e₀` is a unit vector, hence so is its state. -/
example : ‖oneParticle (e 0)‖ = 1 := by simp

/-- **Expected-false**: a one-particle state is not the vacuum, so the Fock space is
strictly bigger than its `n = 0` sector. -/
example : oneParticle (e 0) ≠ BosonFock.vacuum ℂ E₂ := by
  intro h
  have h0 := inner_vacuum_oneParticle (e 0)
  rw [h, inner_self_eq_norm_sq_to_K, BosonFock.norm_vacuum] at h0
  norm_num at h0

/-- The degenerate point: the zero one-particle state is the zero vector, so the previous
witness is not an artifact of a badly chosen `ψ`. -/
example : oneParticle 0 = 0 := by
  rw [← norm_eq_zero, norm_oneParticle, norm_zero]

end Atlas.Witnesses.FockSpace

end
