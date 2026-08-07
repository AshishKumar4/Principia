import Atlas.Proofs.PiTensorSemilinear
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# P2.1f — inner product space structure on finite tensor products

Blueprint node P2.1f, consuming the sesquilinear pairing `PiTensorProduct.innerAux` of
P2.1e (`Atlas/Proofs/PiTensorSemilinear.lean`). We prove that the pairing is positive
definite and package it as an `InnerProductSpace.Core`, then as (scoped, see below)
`NormedAddCommGroup` and `InnerProductSpace` instances on `⨂[𝕜] i, E i`, with
`‖⨂ₜ i, x i‖ = ∏ i, ‖x i‖`.

Definiteness mirrors the binary construction of
`Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` (M. Omar, PR #27228): any element
of the tensor product is a finite sum of pure tensors, hence lies in the range of
`mapIncl p` for finitely generated (so finite-dimensional) submodules `p i ≤ E i`
(`exists_fg_mapIncl_eq`, the `Pi` analog of `TensorProduct.exists_finite_submodule_of_setFinite`);
the pairing is invariant under `mapIncl` (`innerAux_map_map` applied to `(p i).subtypeₗᵢ`);
and on finite-dimensional factors, expanding along the `Basis.piTensorProduct` of
`stdOrthonormalBasis` bases makes the Gram matrix the identity, so
`⟪u, u⟫ = ∑ |coefficients|²` (`innerAux_self_eq_sum_sq`).

## DESIGN NOTE — why the norm instances are scoped

At our Mathlib pin, `Mathlib/Analysis/Normed/Module/PiTensorProduct/InjectiveSeminorm.lean`
already installs **global** `SeminormedAddCommGroup` and `NormedSpace` instances on
`⨂[𝕜] i, E i` (via `PiTensorProduct.projectiveSeminorm`) whenever `𝕜` is a normed field
and the `E i` are seminormed spaces — hypotheses our inner-product context satisfies. The
projective cross norm and the Hilbert (ℓ²) cross norm defined here agree on pure tensors
but differ on general elements, so a global `NormedAddCommGroup` instance derived from
this file's `InnerProductSpace.Core` would be a genuine, mathematically non-defeq diamond
against Mathlib for any file importing both hierarchies. (The binary
`TensorProduct.instNormedAddCommGroup` gets away with a global instance only because
binary `TensorProduct` carries no norm instance at the pin.)

We therefore expose:

* a **global** `Inner 𝕜 (⨂[𝕜] i, E i)` instance (no `Inner` instance exists upstream, and
  `Inner` alone forces no norm), plus the full `InnerProductSpace.Core` as the def
  `PiTensorProduct.innerCore`;
* the `NormedAddCommGroup`/`InnerProductSpace` instances **scoped** to the namespace
  `PiTensorProduct.InnerNorm`. Downstream files (P2.2 symmetrizer, Fock space) activate
  them with `open scoped PiTensorProduct.InnerNorm` and must not simultaneously import
  `Mathlib.Analysis.Normed.Module.PiTensorProduct.*`.

## Main definitions

* `PiTensorProduct.exists_fg_mapIncl_eq`: every element of `⨂[R] i, M i` comes from the
  tensor product of finitely generated submodules.
* `PiTensorProduct.instInner`, `PiTensorProduct.innerCore`: the inner product and its
  positive-definite core, with `inner_tprod : ⟪⨂ₜ x, ⨂ₜ y⟫ = ∏ i, ⟪x i, y i⟫`.
* `PiTensorProduct.InnerNorm.instNormedAddCommGroup`,
  `PiTensorProduct.InnerNorm.instInnerProductSpace`: the scoped instances.
* `PiTensorProduct.norm_tprod`: `‖⨂ₜ i, x i‖ = ∏ i, ‖x i‖`.
* `Orthonormal.piTensor`: pure tensors of orthonormal families are orthonormal.
* `PiTensorProduct.reindexIsometry`: `reindex` along `e : ι ≃ ι'` as a linear isometry
  equivalence — the input to the symmetrizer's `Equiv.Perm` action in P2.2.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised and enlarged edition (1980), §II.4: the inner product on finite tensor products
  of Hilbert spaces (Proposition preceding Theorem II.10) and its positive definiteness.
* M. Omar, Mathlib PR #27228, `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean`:
  the binary construction whose definiteness argument this file adapts.
-/

open scoped TensorProduct

namespace PiTensorProduct

/-! ### Reduction to finitely generated submodules -/

section Finiteness

variable {ι R : Type*} [CommSemiring R]
variable {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- `mapIncl` ranges grow with the submodules: the `Pi` analog of the monotonicity used by
`TensorProduct.exists_finite_submodule_of_setFinite`. -/
theorem range_mapIncl_mono {p q : Π i, Submodule R (M i)} (h : ∀ i, p i ≤ q i) :
    LinearMap.range (mapIncl p) ≤ LinearMap.range (mapIncl q) := by
  have hcomp : mapIncl p = mapIncl q ∘ₗ map fun i ↦ Submodule.inclusion (h i) := by
    simp only [mapIncl, ← map_comp]
    exact congrArg map (funext fun i ↦ (Submodule.subtype_comp_inclusion _ _ (h i)).symm)
  rw [hcomp]
  exact LinearMap.range_comp_le_range _ _

/-- Every element of `⨂[R] i, M i` lies in the image of the tensor product of finitely
generated submodules `p i ≤ M i`. This is the `Pi` analog of
`TensorProduct.exists_finite_submodule_of_setFinite`, and reduces statements about the
full tensor product to the finite-dimensional case. -/
theorem exists_fg_mapIncl_eq (x : ⨂[R] i, M i) :
    ∃ p : Π i, Submodule R (M i), (∀ i, (p i).FG) ∧ x ∈ LinearMap.range (mapIncl p) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c m =>
    refine ⟨fun i ↦ R ∙ m i, fun i ↦ Submodule.fg_span_singleton _,
      Submodule.smul_mem _ c ⟨tprod R fun i ↦ ⟨m i, Submodule.mem_span_singleton_self _⟩, ?_⟩⟩
    simp
  | add u v hu hv =>
    obtain ⟨p, hp, hup⟩ := hu
    obtain ⟨q, hq, hvq⟩ := hv
    exact ⟨fun i ↦ p i ⊔ q i, fun i ↦ (hp i).sup (hq i),
      Submodule.add_mem _ (range_mapIncl_mono (fun i ↦ le_sup_left) hup)
        (range_mapIncl_mono (fun i ↦ le_sup_right) hvq)⟩

end Finiteness

/-! ### Positivity and definiteness of `innerAux` -/

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]

/-- Specialization of `innerAux_map_map` to submodule inclusions: the pairing on
`⨂[𝕜] i, p i` agrees with the pairing on `⨂[𝕜] i, E i` under `mapIncl`. -/
theorem innerAux_mapIncl_mapIncl (p : Π i, Submodule 𝕜 (E i)) (x y : ⨂[𝕜] i, p i) :
    innerAux 𝕜 (mapIncl p x) (mapIncl p y) = innerAux 𝕜 x y :=
  innerAux_map_map (fun i ↦ (p i).subtypeₗᵢ) x y

/-- Pure tensors drawn from orthonormal families pair to `1` or `0`: the Gram matrix of
the induced family on the tensor product is the identity. -/
theorem innerAux_tprod_orthonormal {κ : ι → Type*} [DecidableEq (Π i, κ i)]
    {v : Π i, κ i → E i} (hv : ∀ i, Orthonormal 𝕜 (v i)) (a b : Π i, κ i) :
    innerAux 𝕜 (tprod 𝕜 fun i ↦ v i (a i)) (tprod 𝕜 fun i ↦ v i (b i)) =
      if a = b then 1 else 0 := by
  classical
  rw [innerAux_tprod,
    Finset.prod_congr rfl fun i _ ↦ orthonormal_iff_ite.mp (hv i) (a i) (b i),
    Fintype.prod_boole]
  simp [funext_iff]

/-- Expansion of `⟪x, x⟫` along componentwise orthonormal bases: the Gram matrix is the
identity, so the pairing of `x` with itself is the sum of its squared coefficients in the
`Basis.piTensorProduct` basis. The `Pi` analog of the binary `TensorProduct.inner_self`. -/
private theorem innerAux_self_eq_sum_sq [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (e : Π i, OrthonormalBasis (κ i) 𝕜 (E i)) (x : ⨂[𝕜] i, E i) :
    innerAux 𝕜 x x =
      ((∑ a : Π i, κ i,
        ‖(Basis.piTensorProduct fun i ↦ (e i).toBasis).repr x a‖ ^ 2 : ℝ) : 𝕜) := by
  classical
  set b := Basis.piTensorProduct fun i ↦ (e i).toBasis with hb
  have hgram (a c : Π i, κ i) : innerAux 𝕜 (b a) (b c) = if a = c then 1 else 0 := by
    simpa only [hb, Basis.piTensorProduct_apply, OrthonormalBasis.coe_toBasis] using
      innerAux_tprod_orthonormal (fun i ↦ (e i).orthonormal) a c
  have hx : x = ∑ a, b.repr x a • b a := (b.sum_repr x).symm
  conv_lhs => rw [hx]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply, hgram, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp [RCLike.mul_conj]

/-- The pairing is positive definite: `⟪x, x⟫ = 0` forces `x = 0`. Reduction to finitely
generated submodules, then the Gram computation `innerAux_self_eq_sum_sq`. -/
theorem innerAux_self_definite (x : ⨂[𝕜] i, E i) (hx : innerAux 𝕜 x x = 0) : x = 0 := by
  classical
  obtain ⟨p, hfg, y, rfl⟩ := exists_fg_mapIncl_eq x
  haveI : ∀ i, FiniteDimensional 𝕜 (p i) := fun i ↦ Module.Finite.of_fg (hfg i)
  set e := fun i ↦ stdOrthonormalBasis 𝕜 (p i)
  set b := Basis.piTensorProduct fun i ↦ (e i).toBasis with hb
  rw [innerAux_mapIncl_mapIncl, innerAux_self_eq_sum_sq e, RCLike.ofReal_eq_zero] at hx
  have hcoeff (a) : b.repr y a = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp hx a
      (Finset.mem_univ a)
    simpa [hb] using h
  have hy : y = 0 := by simp [b.ext_elem_iff, hcoeff]
  simp [hy]

/-- The pairing of `x` with itself has nonnegative real part, by the same reduction. -/
theorem re_innerAux_self_nonneg (x : ⨂[𝕜] i, E i) : 0 ≤ RCLike.re (innerAux 𝕜 x x) := by
  classical
  obtain ⟨p, hfg, y, rfl⟩ := exists_fg_mapIncl_eq x
  haveI : ∀ i, FiniteDimensional 𝕜 (p i) := fun i ↦ Module.Finite.of_fg (hfg i)
  rw [innerAux_mapIncl_mapIncl,
    innerAux_self_eq_sum_sq (fun i ↦ stdOrthonormalBasis 𝕜 (p i)), RCLike.ofReal_re]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-! ### The inner product and its core -/

instance instInner : Inner 𝕜 (⨂[𝕜] i, E i) :=
  ⟨fun x y ↦ innerAux 𝕜 x y⟩

lemma inner_def (x y : ⨂[𝕜] i, E i) : inner 𝕜 x y = innerAux 𝕜 x y := rfl

variable (𝕜) in
@[simp] theorem inner_tprod (x y : Π i, E i) :
    inner 𝕜 (tprod 𝕜 x) (tprod 𝕜 y) = ∏ i, inner 𝕜 (x i) (y i) :=
  innerAux_tprod x y

variable (𝕜 E) in
/-- The positive-definite core of the inner product on `⨂[𝕜] i, E i`: Hermitian symmetry
and sesquilinearity from the bundled `innerAux` (P2.1e), positivity and definiteness from
the Gram argument above. The associated norm satisfies `‖⨂ₜ i, x i‖ = ∏ i, ‖x i‖`.

The derived `NormedAddCommGroup`/`InnerProductSpace` instances are **scoped** in
`PiTensorProduct.InnerNorm`; see the design note in the module docstring. -/
@[reducible] def innerCore : InnerProductSpace.Core 𝕜 (⨂[𝕜] i, E i) where
  toInner := instInner
  conj_inner_symm x y := innerAux_conj_symm y x
  re_inner_nonneg := re_innerAux_self_nonneg
  add_left _ _ _ := LinearMap.map_add₂ _ _ _ _
  smul_left _ _ _ := LinearMap.map_smulₛₗ₂ _ _ _ _
  definite := innerAux_self_definite

namespace InnerNorm

/-- The Hilbert (ℓ²) cross norm on `⨂[𝕜] i, E i`, induced by the inner product. Scoped:
activating it alongside Mathlib's projective-seminorm instances would create a non-defeq
norm diamond (see the module docstring). -/
noncomputable scoped instance instNormedAddCommGroup : NormedAddCommGroup (⨂[𝕜] i, E i) :=
  (innerCore 𝕜 E).toNormedAddCommGroup

/-- The inner product space structure on `⨂[𝕜] i, E i`, relative to the scoped norm. -/
scoped instance instInnerProductSpace : InnerProductSpace 𝕜 (⨂[𝕜] i, E i) := .ofCore _

end InnerNorm

/-! ### API: norms of pure tensors, orthonormality, reindexing -/

section InnerNormAPI

open scoped InnerNorm

variable (𝕜) in
@[simp] theorem norm_tprod (x : Π i, E i) : ‖tprod 𝕜 x‖ = ∏ i, ‖x i‖ := by
  have h : inner 𝕜 (tprod 𝕜 x) (tprod 𝕜 x) = ((∏ i, ‖x i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [inner_tprod, RCLike.ofReal_prod]
    exact Finset.prod_congr rfl fun i _ ↦ by
      rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]
  rw [@norm_eq_sqrt_re_inner 𝕜, h, RCLike.ofReal_re, Finset.prod_pow,
    Real.sqrt_sq (by positivity)]

/-- Pure tensors of orthonormal families are orthonormal: the `Pi` analog of
`Orthonormal.tmul`. Applied to orthonormal bases this yields orthonormal bases of the
tensor product. -/
theorem _root_.Orthonormal.piTensor {κ : ι → Type*} {v : Π i, κ i → E i}
    (hv : ∀ i, Orthonormal 𝕜 (v i)) :
    Orthonormal 𝕜 fun a : Π i, κ i ↦ tprod 𝕜 fun i ↦ v i (a i) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  exact innerAux_tprod_orthonormal hv a b

variable {ι' : Type*} [Fintype ι']

/-- `reindex` preserves the pairing: the slotwise inner products are merely multiplied in
a different order. -/
theorem innerAux_reindex (e : ι ≃ ι') (u v : ⨂[𝕜] i, E i) :
    innerAux 𝕜 (reindex 𝕜 E e u) (reindex 𝕜 E e v) = innerAux 𝕜 u v := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    induction v using PiTensorProduct.induction_on with
    | smul_tprod d y =>
      simp only [map_smul, reindex_tprod, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        innerAux_tprod]
      rw [Equiv.prod_comp e.symm fun i ↦ inner 𝕜 (x i) (y i)]
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | add u₁ u₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

variable (𝕜 E) in
/-- Reindexing a finite tensor product of inner product spaces along `e : ι ≃ ι'` is a
linear isometry equivalence. This is the isometric upgrade of `PiTensorProduct.reindex`
feeding the symmetrizer's `Equiv.Perm` action (blueprint P2.2). -/
noncomputable def reindexIsometry (e : ι ≃ ι') :
    (⨂[𝕜] i, E i) ≃ₗᵢ[𝕜] ⨂[𝕜] i', E (e.symm i') :=
  (reindex 𝕜 E e).isometryOfInner fun u v ↦ innerAux_reindex e u v

@[simp] lemma reindexIsometry_apply (e : ι ≃ ι') (u : ⨂[𝕜] i, E i) :
    reindexIsometry 𝕜 E e u = reindex 𝕜 E e u := rfl

@[simp] lemma toLinearEquiv_reindexIsometry (e : ι ≃ ι') :
    (reindexIsometry 𝕜 E e).toLinearEquiv = reindex 𝕜 E e := rfl

lemma reindexIsometry_tprod (e : ι ≃ ι') (x : Π i, E i) :
    reindexIsometry 𝕜 E e (tprod 𝕜 x) = tprod 𝕜 fun i' ↦ x (e.symm i') :=
  reindex_tprod e x

@[simp] lemma norm_reindex (e : ι ≃ ι') (u : ⨂[𝕜] i, E i) :
    ‖reindex 𝕜 E e u‖ = ‖u‖ :=
  (reindexIsometry 𝕜 E e).norm_map u

@[simp] lemma inner_reindex_reindex (e : ι ≃ ι') (u v : ⨂[𝕜] i, E i) :
    inner 𝕜 (reindex 𝕜 E e u) (reindex 𝕜 E e v) = inner 𝕜 u v :=
  innerAux_reindex e u v

end InnerNormAPI

end PiTensorProduct
