import Atlas

/-!
# P2.2 slice-1 kernel probes — the degree-`2` symmetrizer arithmetic

* **Node**: P2.2 slice 1 (symmetric Fock space, algebraic layer),
  `Atlas/Specs/QFT/FockSpace.lean`.
* **Original review**: 2026-08-07 (BLUEPRINT P2.2: "Slice 1 `done` 2026-08-07, spec
  frozen 4a0b277 + witnesses landed"). The probe file of that review lived in a
  session-temporary scratchpad and was lost; this file is the X.3 backfill
  (`audits/README.md`), re-created 2026-08-23.
* **What it refutes**: the *identity impostor* — the reading under which the frozen
  `symmetrizer` is (or acts as) `LinearMap.id` in degree `2`, i.e. under which the
  symmetric sector is vacuously the whole tensor power and the `(n!)⁻¹` factor is
  cosmetic. It also refutes the *isometry* reading of the normalization
  (`‖S t‖ = 1` for a unit pure tensor `t`), which is the convention error that would
  silently move the `√(n+1)` factors of slice 2.

## What is checked, and how independently

Everything below is re-derived in this file from the frozen spec alone
(`QFT.symmetrizer`, `QFT.symmetrizer_tprod`, `QFT.isIdempotentElem_symmetrizer`,
`PiTensorProduct.inner_tprod`): the `S₂` closed form is re-enumerated over
`Equiv.Perm (Fin 2)` by `decide` rather than imported from
`Atlas/Witnesses/FockSpace.lean`, so a defect in the witness layer cannot hide here.

* `probe_symmetrizer_tprod_two` — `S(x₀ ⊗ x₁) = ½(x₀ ⊗ x₁ + x₁ ⊗ x₀)`;
* `probe_symmetrizer_e01` — the same on the distinguishable model tensor
  `e₀ ⊗ e₁ ∈ (ℂ²)^{⊗2}`;
* `probe_inner_e01_symmetrized`, `probe_inner_symmetrized_self` — the pairings
  `⟪e₀ ⊗ e₁, S(e₀ ⊗ e₁)⟫ = ½` and `⟪S(e₀ ⊗ e₁), S(e₀ ⊗ e₁)⟫ = ½`;
* `probe_norm_symmetrized_sq`, `probe_norm_symmetrized_ne_one` — `‖S(e₀ ⊗ e₁)‖² = ½`,
  hence not a unit vector (projector, not isometry);
* `probe_symmetrizer_two_ne_id`, `probe_symmetrizer_e01_ne_self` — the identity
  impostor, refuted at the operator level and pointwise;
* `probe_e01_not_mem_symTensorPower` — the `2`-particle sector is a *proper* subspace
  of the ambient power, so it is a real constraint.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*
  (1980), §II.4, Example 2 (symmetric tensors, the group-average projector `Sₙ` with
  its `(n!)⁻¹` normalization).
* O. Bratteli, D. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*
  (1981), §5.2 (boson Fock space over the symmetrized powers).

Theorem/section numbers are quoted from the source list of the frozen spec
`Atlas/Specs/QFT/FockSpace.lean`; they were not re-checked against the printed
editions in this backfill.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.2-slice1/` only;
compiles via `lake env lean audits/probes/P2.2-slice1/fock_symmetrizer_probe.lean`.
-/

assert_not_exists PiTensorProduct.projectiveSeminorm

noncomputable section

namespace P22Slice1Probe

open PiTensorProduct QFT UniformSpace
open scoped TensorProduct PiTensorProduct.InnerNorm

/-- The probe's one-particle space: `ℂ²`, whose standard basis gives distinguishable
slots — the only setting in which symmetrization has observable content. -/
abbrev E₂ : Type := EuclideanSpace ℂ (Fin 2)

/-- The standard basis vectors `e₀, e₁`. -/
def e (i : Fin 2) : E₂ := EuclideanSpace.single i (1 : ℂ)

@[simp] theorem probe_norm_e (i : Fin 2) : ‖e i‖ = 1 := by simp [e]

/-- Orthonormality of the probe basis: the input to every pairing below. -/
theorem probe_inner_e_e (i j : Fin 2) :
    inner ℂ (e i) (e j) = if i = j then (1 : ℂ) else 0 := by
  have h := (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal
  rw [orthonormal_iff_ite] at h
  simpa [e, EuclideanSpace.basisFun_apply] using h i j

/-- The distinguishable pure `2`-tensor `e₀ ⊗ e₁`. -/
def t01 : ⨂[ℂ]^2 E₂ := tprod ℂ ![e 0, e 1]

/-- Its transpose `e₁ ⊗ e₀`. -/
def t10 : ⨂[ℂ]^2 E₂ := tprod ℂ ![e 1, e 0]

theorem probe_inner_t01_t01 : inner ℂ t01 t01 = (1 : ℂ) := by
  simp [t01, Fin.prod_univ_two]

theorem probe_inner_t10_t10 : inner ℂ t10 t10 = (1 : ℂ) := by
  simp [t10, Fin.prod_univ_two]

/-- The tensor power sees the slot order: `e₀ ⊗ e₁ ⊥ e₁ ⊗ e₀`. -/
theorem probe_inner_t01_t10 : inner ℂ t01 t10 = (0 : ℂ) := by
  simp [t01, t10, Fin.prod_univ_two, probe_inner_e_e]

theorem probe_inner_t10_t01 : inner ℂ t10 t01 = (0 : ℂ) := by
  simp [t01, t10, Fin.prod_univ_two, probe_inner_e_e]

theorem probe_norm_t01 : ‖t01‖ = 1 := by
  simp [t01, Fin.prod_univ_two, e]

/-! ## The closed form of the degree-`2` symmetrizer -/

/-- The frozen `symmetrizer` in degree `2`, re-derived here from `symmetrizer_tprod` by
enumerating `S₂ = {1, (0 1)}` with `decide`: `S(x₀ ⊗ x₁) = ½(x₀ ⊗ x₁ + x₁ ⊗ x₀)`. -/
theorem probe_symmetrizer_tprod_two (x : Fin 2 → E₂) :
    symmetrizer ℂ E₂ 2 (tprod ℂ x) = (2 : ℂ)⁻¹ • (tprod ℂ x + tprod ℂ ![x 1, x 0]) := by
  rw [symmetrizer_tprod]
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
    decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
  have h1 : (fun i => x ((1 : Equiv.Perm (Fin 2)) i)) = x := rfl
  have h2 : (fun i => x (Equiv.swap 0 1 i)) = ![x 1, x 0] := by
    funext i
    fin_cases i <;> simp
  rw [h1, h2]
  norm_num [Nat.factorial]

/-- **The claimed arithmetic**: `S(e₀ ⊗ e₁) = ½(e₀ ⊗ e₁ + e₁ ⊗ e₀)`. -/
theorem probe_symmetrizer_e01 :
    symmetrizer ℂ E₂ 2 t01 = (2 : ℂ)⁻¹ • (t01 + t10) := by
  have h := probe_symmetrizer_tprod_two ![e 0, e 1]
  simpa [t01, t10] using h

/-! ## The pairings: where the `(2!)⁻¹ = ½` shows up -/

/-- `⟪e₀ ⊗ e₁, S(e₀ ⊗ e₁)⟫ = ½`: only the identity permutation contributes, so the
normalization is read off directly. -/
theorem probe_inner_e01_symmetrized :
    inner ℂ t01 (symmetrizer ℂ E₂ 2 t01) = (1 / 2 : ℂ) := by
  rw [probe_symmetrizer_e01, inner_def, map_smul, map_add, ← inner_def, ← inner_def,
    probe_inner_t01_t01, probe_inner_t01_t10]
  norm_num

/-- **`⟪S t, S t⟫ = ½`** for `t = e₀ ⊗ e₁`: the self-pairing of the symmetrized tensor.
Idempotency plus self-adjointness of a projector predicts exactly the value of
`probe_inner_e01_symmetrized`; here it is computed from the closed form instead. -/
theorem probe_inner_symmetrized_self :
    inner ℂ (symmetrizer ℂ E₂ 2 t01) (symmetrizer ℂ E₂ 2 t01) = (1 / 2 : ℂ) := by
  rw [probe_symmetrizer_e01, inner_def]
  simp only [map_smulₛₗ, map_add, LinearMap.smul_apply, LinearMap.add_apply, ← inner_def,
    probe_inner_t01_t01, probe_inner_t01_t10, probe_inner_t10_t01, probe_inner_t10_t10]
  norm_num [Complex.conj_ofNat]

/-- **Projector, not isometry**: `‖S(e₀ ⊗ e₁)‖² = ½` while `‖e₀ ⊗ e₁‖ = 1`. -/
theorem probe_norm_symmetrized_sq : ‖symmetrizer ℂ E₂ 2 t01‖ ^ 2 = 1 / 2 := by
  have h : ((‖symmetrizer ℂ E₂ 2 t01‖ : ℂ)) ^ 2 = (1 / 2 : ℂ) :=
    (inner_self_eq_norm_sq_to_K (symmetrizer ℂ E₂ 2 t01)).symm.trans
      probe_inner_symmetrized_self
  have h2 : ((‖symmetrizer ℂ E₂ 2 t01‖ ^ 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    push_cast
    exact h
  exact_mod_cast h2

/-- **Refutation of the isometry reading of the normalization**: the symmetrization of a
unit pure tensor on distinguishable slots is not a unit vector. -/
theorem probe_norm_symmetrized_ne_one : ‖symmetrizer ℂ E₂ 2 t01‖ ≠ 1 := by
  intro h
  have h2 := probe_norm_symmetrized_sq
  rw [h] at h2
  norm_num at h2

/-! ## The identity impostor, refuted -/

/-- **The identity impostor, at the operator level**: in degree `2` the frozen
symmetrizer is not `LinearMap.id`. Contrast `symmetrizer_eq_id` in degrees `n ≤ 1`,
which is the sharp complement. -/
theorem probe_symmetrizer_two_ne_id : symmetrizer ℂ E₂ 2 ≠ LinearMap.id := by
  intro h
  have h2 := probe_inner_e01_symmetrized
  rw [h, LinearMap.id_coe, id_eq, probe_inner_t01_t01] at h2
  norm_num at h2

/-- The same impostor, pointwise: the symmetrizer moves `e₀ ⊗ e₁`. -/
theorem probe_symmetrizer_e01_ne_self : symmetrizer ℂ E₂ 2 t01 ≠ t01 := by
  intro h
  have h2 := probe_inner_e01_symmetrized
  rw [h, probe_inner_t01_t01] at h2
  norm_num at h2

/-- The frozen symmetrizer *is* idempotent (the property the `(2!)⁻¹` factor exists
for), evaluated on the probe tensor — so the refutations above are not the trivial
observation that some scaling is wrong. -/
theorem probe_symmetrizer_idempotent_e01 :
    symmetrizer ℂ E₂ 2 (symmetrizer ℂ E₂ 2 t01) = symmetrizer ℂ E₂ 2 t01 := by
  have h := DFunLike.congr_fun (isIdempotentElem_symmetrizer ℂ E₂ 2) t01
  rwa [Module.End.mul_apply] at h

/-- **The sector is a proper subspace**: `e₀ ⊗ e₁ ∉ SymTensorPower ℂ E₂ 2`. With
`probe_symmetrizer_two_ne_id` this closes the vacuity question — the `2`-particle
sector constrains, rather than being all of the ambient tensor power. -/
theorem probe_e01_not_mem_symTensorPower :
    (t01 : HilbertTensorPower ℂ E₂ 2) ∉ SymTensorPower ℂ E₂ 2 := by
  rw [mem_symTensorPower_iff, symmetrizerL_coe, Completion.coe_inj]
  exact probe_symmetrizer_e01_ne_self

end P22Slice1Probe

end
