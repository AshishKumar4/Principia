import Atlas.Specs.OperatorTheory.Symmetric
import Atlas.Proofs.DeficiencyTheory

/-!
# Non-vacuity witnesses for symmetric operators and deficiency spaces (P2.3a/b)

Concrete models of the frozen spec `Atlas/Specs/OperatorTheory/Symmetric.lean`, all
built on the one-dimensional Hilbert space `ℂ` where multiplication-by-a-scalar operators
make every notion fully computable:

* `mulPMap z`: multiplication by `z : ℂ`, a total `LinearPMap` on `ℂ`. Its adjoint is
  multiplication by `conj z` (`adjoint_mulPMap_apply`), and its deficiency space at `c`
  is `⊤` if `c = z` and `⊥` otherwise (`deficiencySpace_mulPMap_self` /
  `deficiencySpace_mulPMap_of_ne`).
* **Real multiplier `r • id`** (`mulPMap (r : ℂ)`): the flagship *expected-true* witness —
  `IsSymmetric` (`isSymmetric_mulPMap_real`), `IsSelfAdjoint`
  (`isSelfAdjoint_mulPMap_real`), `IsEssentiallySelfAdjoint`
  (`isEssentiallySelfAdjoint_mulPMap_real`), and both deficiency spaces at `±i` vanish
  (`deficiencySpace_mulPMap_real_I` / `_neg_I`), exactly as the basic criterion demands
  of a (globally) self-adjoint operator.
* **Imaginary multiplier `i • id`** (`mulPMap Complex.I`): the *expected-false* witness —
  `¬ IsSymmetric` (`not_isSymmetric_mulPMap_I`), with the deficiency space at `I` equal to
  all of `ℂ` (`deficiencySpace_mulPMap_I_top`) and `⊥` at every other point.
* Norm-identity instantiations for the zero operator and for `r • id`
  (`norm_add_I_smul_sq`), both sides computed.
* A genuinely **partial** (non-total-domain) symmetric witness on `EuclideanSpace ℂ (Fin 2)`
  (`isSymmetric_idRestrict`), the identity restricted to a proper rank-one subspace.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I* (1980), §VIII.2
  (symmetric/self-adjoint/essentially self-adjoint operators; the basic criterion).
-/

open OperatorTheory
open scoped ComplexConjugate

noncomputable section

namespace OperatorTheory.Witnesses

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-! ### Multiplication-by-a-scalar operators on `ℂ` (the base models) -/

/-- Multiplication by `z : ℂ` on `ℂ`, as a total `LinearPMap`. -/
def mulPMap (z : ℂ) : ℂ →ₗ.[ℂ] ℂ := (z • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).toPMap ⊤

@[simp] theorem mulPMap_domain (z : ℂ) : (mulPMap z).domain = ⊤ := rfl

@[simp] theorem mulPMap_apply (z : ℂ) (x : (mulPMap z).domain) :
    mulPMap z x = z * (x : ℂ) := rfl

theorem mulPMap_dense (z : ℂ) : Dense ((mulPMap z).domain : Set ℂ) := by
  simp [dense_iff_closure_eq]

/-- Every `y` lies in the adjoint domain of multiplication-by-`z`. -/
theorem mem_adjointDomain_mulPMap (z : ℂ) (y : ℂ) : y ∈ (mulPMap z).adjoint.domain :=
  LinearPMap.mem_adjoint_domain_of_exists _
    ⟨conj z * y, fun x => by
      simp only [mulPMap_apply, RCLike.inner_apply, map_mul, Complex.conj_conj]
      ring⟩

/-- The adjoint of multiplication-by-`z` is multiplication by `conj z`. -/
theorem adjoint_mulPMap_apply (z : ℂ) (y : (mulPMap z).adjoint.domain) :
    (mulPMap z).adjoint y = conj z * (y : ℂ) := by
  refine LinearPMap.adjoint_apply_eq (mulPMap_dense z) y fun x => ?_
  simp only [mulPMap_apply, RCLike.inner_apply, map_mul, Complex.conj_conj]
  ring

/-- Deficiency space of multiplication-by-`z` at `c ≠ z` is `⊥`. -/
theorem deficiencySpace_mulPMap_of_ne {z c : ℂ} (h : c ≠ z) :
    LinearPMap.deficiencySpace (mulPMap z) c = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  rw [LinearPMap.mem_deficiencySpace_iff] at hy
  have h1 := hy ⟨1, trivial⟩
  simp only [mulPMap_apply, mul_one, smul_eq_mul, RCLike.inner_apply] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact h2
  · exact absurd (by simpa [sub_eq_zero] using congrArg conj h2 : z = c) (Ne.symm h)

/-- Deficiency space of multiplication-by-`z` at `c = z` is everything. -/
theorem deficiencySpace_mulPMap_self (z : ℂ) :
    LinearPMap.deficiencySpace (mulPMap z) z = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro y
  rw [LinearPMap.mem_deficiencySpace_iff]
  intro x
  simp [RCLike.inner_apply]

/-! ### Expected-true witness: real multiplier `r • id` -/

/-- **Expected-true**: multiplication by a real scalar is symmetric (Reed & Simon I,
§VIII.2). -/
theorem isSymmetric_mulPMap_real (r : ℝ) : LinearPMap.IsSymmetric (mulPMap (r : ℂ)) := by
  intro x y
  simp only [mulPMap_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- Multiplication by a real scalar is self-adjoint: its adjoint (multiplication by
`conj r = r`) is itself, with the full space as adjoint domain. -/
theorem isSelfAdjoint_mulPMap_real (r : ℝ) : IsSelfAdjoint (mulPMap (r : ℂ)) := by
  rw [LinearPMap.isSelfAdjoint_def]
  refine LinearPMap.ext ?_ ?_
  · rw [mulPMap_domain, Submodule.eq_top_iff']
    exact fun y => mem_adjointDomain_mulPMap _ y
  · intro x hf hg
    rw [adjoint_mulPMap_apply, mulPMap_apply, Complex.conj_ofReal]

/-- Multiplication by a real scalar is essentially self-adjoint (being self-adjoint, hence
closed, hence its own closure). -/
theorem isEssentiallySelfAdjoint_mulPMap_real (r : ℝ) :
    LinearPMap.IsEssentiallySelfAdjoint (mulPMap (r : ℂ)) :=
  LinearPMap.isEssentiallySelfAdjoint_of_isSelfAdjoint (isSelfAdjoint_mulPMap_real r)

theorem ofReal_ne_I (r : ℝ) : (r : ℂ) ≠ Complex.I := by
  intro h
  have := congrArg Complex.im h
  simp [Complex.ofReal_im, Complex.I_im] at this

theorem ofReal_ne_neg_I (r : ℝ) : (r : ℂ) ≠ -Complex.I := by
  intro h
  have := congrArg Complex.im h
  simp [Complex.ofReal_im] at this

/-- Both deficiency spaces of a self-adjoint `r • id` vanish (at `I`), matching the basic
criterion's characterization of essential self-adjointness. -/
theorem deficiencySpace_mulPMap_real_I (r : ℝ) :
    LinearPMap.deficiencySpace (mulPMap (r : ℂ)) Complex.I = ⊥ :=
  deficiencySpace_mulPMap_of_ne (ofReal_ne_I r).symm

theorem deficiencySpace_mulPMap_real_neg_I (r : ℝ) :
    LinearPMap.deficiencySpace (mulPMap (r : ℂ)) (-Complex.I) = ⊥ :=
  deficiencySpace_mulPMap_of_ne (ofReal_ne_neg_I r).symm

/-! ### Expected-false witness: imaginary multiplier `i • id` -/

/-- **Expected-false**: multiplication by `i` is not symmetric (Reed & Simon I, §VIII.2:
`⟪i·1, 1⟫ = i ≠ -i = ⟪1, i·1⟫`). -/
theorem not_isSymmetric_mulPMap_I : ¬ LinearPMap.IsSymmetric (mulPMap Complex.I) := by
  intro h
  have h1 := h ⟨1, trivial⟩ ⟨1, trivial⟩
  simp only [mulPMap_apply, mul_one, RCLike.inner_apply, Complex.conj_I, map_one,
    one_mul] at h1
  exact Complex.I_ne_zero (by linear_combination -h1 / 2)

/-- The deficiency space of `i • id` at `I` is all of `ℂ`: `ran (A - i) = {0}`, so its
orthogonal complement is everything. This is `K₋` (the concrete example from the spec's
`c = I` case). -/
theorem deficiencySpace_mulPMap_I_top :
    LinearPMap.deficiencySpace (mulPMap Complex.I) Complex.I = ⊤ :=
  deficiencySpace_mulPMap_self Complex.I

/-- The deficiency space of `i • id` at `-I` is `⊥` (`K₊ = ker (A† - i) = 0`): `-I ≠ I`.
Together with `deficiencySpace_mulPMap_I_top` this exhibits the asymmetry `K₋ = ℂ`,
`K₊ = 0` (deficiency indices `n₋ = 1`, `n₊ = 0`) that shows `i • id` is not essentially
self-adjoint. -/
theorem deficiencySpace_mulPMap_I_neg_I :
    LinearPMap.deficiencySpace (mulPMap Complex.I) (-Complex.I) = ⊥ :=
  deficiencySpace_mulPMap_of_ne (by
    intro h
    exact Complex.I_ne_zero (by linear_combination -h / 2))

/-! ### Norm-identity instantiations (both sides computed) -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The zero operator is symmetric. -/
theorem isSymmetric_zero : LinearPMap.IsSymmetric (0 : H →ₗ.[ℂ] H) := by
  intro x y
  simp

/-- Norm identity for `A = 0`: `‖0 + i • x‖² = ‖x‖²` (LHS reduces to `‖i • x‖² = ‖x‖²`,
RHS to `0 + ‖x‖²`). -/
theorem norm_add_I_smul_sq_zero (x : (0 : H →ₗ.[ℂ] H).domain) :
    ‖(0 : H →ₗ.[ℂ] H) x + Complex.I • (x : H)‖ ^ 2 = ‖(x : H)‖ ^ 2 := by
  have h := isSymmetric_zero.norm_add_I_smul_sq x
  simpa using h

/-- Norm identity for `A = r • id`: `‖r•x + i•x‖² = ‖r•x‖² + ‖x‖²`, both sides as the
operator delivers them. -/
theorem norm_add_I_smul_sq_mulPMap_real (r : ℝ) (x : (mulPMap (r : ℂ)).domain) :
    ‖(mulPMap (r : ℂ)) x + Complex.I • (x : ℂ)‖ ^ 2
      = ‖(mulPMap (r : ℂ)) x‖ ^ 2 + ‖(x : ℂ)‖ ^ 2 :=
  (isSymmetric_mulPMap_real r).norm_add_I_smul_sq x

/-- Concrete numeric instance for `A = 2 • id` at `x = 1`: both sides equal `5`. -/
theorem norm_add_I_smul_sq_two_one :
    ‖(mulPMap ((2 : ℝ) : ℂ)) ⟨1, trivial⟩ + Complex.I • (1 : ℂ)‖ ^ 2 = 5 := by
  have hval : (mulPMap ((2 : ℝ) : ℂ)) ⟨1, trivial⟩ + Complex.I • (1 : ℂ) = 2 + Complex.I := by
    rw [mulPMap_apply]; push_cast; ring
  rw [hval, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  norm_num

/-! ### A genuinely partial (non-total-domain) symmetric witness -/

/-- The identity operator on `EuclideanSpace ℂ (Fin 2)` restricted to the proper rank-one
subspace spanned by the first basis vector: a symmetric operator whose domain is **not**
the whole space. Symmetry of a restriction of a self-adjoint (indeed the identity) operator
is automatic; the point is that `IsSymmetric` genuinely applies to partially-defined
operators. -/
def idRestrict : EuclideanSpace ℂ (Fin 2) →ₗ.[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (LinearMap.id : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2)).toPMap
    (ℂ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℂ))

/-- The partial witness has a proper (non-total) domain: a rank-one subspace of the
two-dimensional space. -/
theorem idRestrict_domain_ne_top : idRestrict.domain ≠ ⊤ := by
  have hv : EuclideanSpace.single (0 : Fin 2) (1 : ℂ) ≠ 0 := by
    intro h0
    simpa using congrArg norm h0
  intro h
  have h1 : Module.finrank ℂ (idRestrict.domain : Submodule ℂ (EuclideanSpace ℂ (Fin 2))) = 1 := by
    rw [idRestrict, LinearMap.toPMap_domain]
    exact finrank_span_singleton hv
  rw [h, finrank_top, finrank_euclideanSpace_fin] at h1
  exact absurd h1 (by norm_num)

/-- **Partial symmetric witness**: the identity restricted to a proper subspace is
symmetric. -/
theorem isSymmetric_idRestrict : LinearPMap.IsSymmetric idRestrict := by
  intro x y
  simp only [idRestrict, LinearMap.toPMap_apply, LinearMap.id_coe, id_eq]

end OperatorTheory.Witnesses
