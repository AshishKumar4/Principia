import Atlas.Specs.QFT.CreationAnnihilation

/-!
# P2.6a — the second-quantization functor Γ

Blueprint node P2.6a: the lift of a one-particle unitary `u : E ≃ₗᵢ[𝕜] F` to the boson
Fock space, `Γ(u) : BosonFock 𝕜 E ≃ₗᵢ[𝕜] BosonFock 𝕜 F`, with its functor laws, vacuum
and finite-particle preservation, and the conjugation laws
`Γ(u) a†(g) Γ(u)⁻¹ = a†(u g)` and `Γ(u) a(g) Γ(u)⁻¹ = a(u g)` on the finite-particle
domain — the engine the free-field covariance node (P2.6d) consumes.

## Proof architecture (four layers, mirroring `Atlas/Proofs/CCRTheory.lean`)

1. **Algebraic layer** (`PiTensorProduct.congrIsometry`): a family of linear isometry
   equivalences `f i : E i ≃ₗᵢ[𝕜] F i` induces an isometry equivalence of the algebraic
   tensor products for the P2.1e/f ℓ² inner product — the `Pi` analogue of the binary
   `TensorProduct.congrIsometry` consumed by the frozen P2.1b `congrₕ`. The inner-product
   computation (`innerAux_congr`) is the pure-tensor induction of
   `PiTensorProduct.innerAux_map_map`, with `LinearIsometryEquiv.inner_map_map` slotwise.
2. **Completed layer** (`QFT.tensorPowerCongr`): the completion of the constant-family
   congruence via the frozen `UniformSpace.Completion.congrₗᵢ` (P2.1b) acts on
   `QFT.HilbertTensorPower 𝕜 E n`. Equivariance facts transfer from the algebraic layer
   by `Completion.induction_on` (closed conditions among continuous maps, checked on the
   dense algebraic image through the `…_coe` pins).
3. **Sector layer** (`QFT.symTensorPowerCongr`): the congruence commutes with every
   permutation `reindex` (`map ∘ reindex = reindex ∘ map` on pure tensors), hence with
   the group-average symmetrizer, hence restricts to the boson sectors
   `QFT.SymTensorPower 𝕜 E n`. The creation/annihilation sector maps intertwine:
   insertion satisfies `u⊗⁽ⁿ⁺¹⁾ ∘ (g ⊗ ·) = (u g ⊗ ·) ∘ u⊗⁽ⁿ⁾` (postcomposition
   distributes over `Fin.cons`), and contraction satisfies
   `u⊗⁽ⁿ⁾ ∘ ⟪g, ·⟫₁ = ⟪u g, ·⟫₁ ∘ u⊗⁽ⁿ⁺¹⁾` because unitarity gives
   `⟪u g, u x₀⟫ = ⟪g, x₀⟫` — which is exactly why the conjugation law for the
   *antilinear-in-`g`* annihilation operator still reads `Γ(u) a(g) Γ(u)⁻¹ = a(u g)`
   with no conjugation on `u`. The frozen `√(n+1)` factors are scalars and pass through.
4. **`lp` layer** (`lp.congrₗᵢ`, `QFT.secondQuantization`): a family of isometric
   equivalences induces an isometric equivalence of `lp` spaces componentwise — absent
   from the pinned Mathlib, stated in upstream shape — and `Γ(u)` is the instance at
   the boson sectors. Functor laws, vacuum/one-particle images, finite-particle
   preservation, and the conjugation laws assemble componentwise (`lp.ext`).

Import discipline (spec module docstring, "Scope discipline"): this file opens the
scoped `PiTensorProduct.InnerNorm` instances and replicates the spec's
`assert_not_exists` guard.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised and enlarged edition (1980), §II.4, Example 2 (Fock spaces): the ambient
  construction. The second-quantization functor `Γ` of a one-particle operator appears
  in the self-adjointness material (§VIII.10, Example 2 — section number quoted from
  memory, not re-verified against a copy; the operative facts are proved per-lemma).
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II: Fourier Analysis,
  Self-Adjointness* (1975), §X.7 (the free quantum field): the covariance computation
  that consumes `Γ(u) a†(g) Γ(u)⁻¹ = a†(u g)`. Section-level citation.
* O. Bratteli, D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*,
  2nd edition (1997), §5.2: the unitary `Γ(U)` on the boson Fock space determined by
  `Γ(U) a†(f) Γ(U)⁻¹ = a†(U f)` and `Γ(U) Ω = Ω` (the Fock-implementation of a
  one-particle unitary). Section-level citation.
-/

assert_not_exists PiTensorProduct.projectiveSeminorm

noncomputable section

open scoped ENNReal

/-! ### Completion supplement: `congrₗᵢ` is functorial

The frozen P2.1b layer (`Atlas/Proofs/HilbertTensorMaps.lean`) provides `congrₗᵢ` with
its `refl` and `symm` laws; the composition law was not needed there and is added here,
upstream-shaped, without touching the frozen file. -/

namespace UniformSpace.Completion

variable {𝕜 X Y Z : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The completion functor respects composition of linear isometry equivalences. -/
theorem congrₗᵢ_trans (f : X ≃ₗᵢ[𝕜] Y) (g : Y ≃ₗᵢ[𝕜] Z) :
    congrₗᵢ (f.trans g) = (congrₗᵢ f).trans (congrₗᵢ g) := by
  refine LinearIsometryEquiv.ext fun x => ?_
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (LinearIsometryEquiv.continuous _) (LinearIsometryEquiv.continuous _)
  | ih a => simp

end UniformSpace.Completion

/-! ### The isometric congruence of finite tensor products

The `Pi` analogue of the binary `TensorProduct.congrIsometry` feeding the frozen P2.1b
`congrₕ`: a family of linear isometry equivalences induces a linear isometry equivalence
of the algebraic tensor products for the scoped ℓ² inner norm of P2.1f. Upstream-shaped
over the P2.1e/f layer. -/

namespace PiTensorProduct

open scoped TensorProduct PiTensorProduct.InnerNorm

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
variable {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)]

/-- The pairing is preserved by componentwise linear isometry equivalences: the
`PiTensorProduct.congr` of the underlying equivalences preserves `innerAux`. The equiv
counterpart of `PiTensorProduct.innerAux_map_map` (P2.1e). -/
theorem innerAux_congr (f : Π i, E i ≃ₗᵢ[𝕜] F i) (u v : ⨂[𝕜] i, E i) :
    innerAux 𝕜 (congr (fun i => (f i).toLinearEquiv) u)
        (congr (fun i => (f i).toLinearEquiv) v) =
      innerAux 𝕜 u v := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    induction v using PiTensorProduct.induction_on with
    | smul_tprod d y =>
      simp only [map_smul, congr_tprod, LinearIsometryEquiv.coe_toLinearEquiv,
        map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, innerAux_tprod,
        LinearIsometryEquiv.inner_map_map]
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | add u₁ u₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

/-- A family of linear isometry equivalences induces a linear isometry equivalence of
finite tensor products of inner product spaces, for the ℓ² cross norm of P2.1f. This is
the `Pi` analogue of the binary `TensorProduct.congrIsometry` (consumed by the frozen
P2.1b `congrₕ`), and the algebraic core of the second-quantization functor. -/
def congrIsometry (f : Π i, E i ≃ₗᵢ[𝕜] F i) : (⨂[𝕜] i, E i) ≃ₗᵢ[𝕜] ⨂[𝕜] i, F i :=
  (congr fun i => (f i).toLinearEquiv).isometryOfInner fun u v => innerAux_congr f u v

/-- **Action of the congruence on pure tensors**: slotwise application. -/
@[simp]
theorem congrIsometry_tprod (f : Π i, E i ≃ₗᵢ[𝕜] F i) (x : Π i, E i) :
    congrIsometry f (tprod 𝕜 x) = tprod 𝕜 fun i => f i (x i) := by
  simp only [congrIsometry, LinearEquiv.coe_isometryOfInner, congr_tprod,
    LinearIsometryEquiv.coe_toLinearEquiv]

/-- The congruence of the identity family is the identity. -/
theorem congrIsometry_refl :
    congrIsometry (fun i => LinearIsometryEquiv.refl 𝕜 (E i)) =
      LinearIsometryEquiv.refl 𝕜 (⨂[𝕜] i, E i) := by
  refine LinearIsometryEquiv.ext fun z => ?_
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    rw [map_smul, congrIsometry_tprod, LinearIsometryEquiv.coe_refl, id_eq]
    exact congrArg (c • ·)
      (congrArg (fun v : Π i, E i => tprod 𝕜 v) (funext fun i => rfl))
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The congruence respects composition of the component equivalences. -/
theorem congrIsometry_trans (f : Π i, E i ≃ₗᵢ[𝕜] F i) (g : Π i, F i ≃ₗᵢ[𝕜] G i) :
    congrIsometry (fun i => (f i).trans (g i)) =
      (congrIsometry f).trans (congrIsometry g) := by
  refine LinearIsometryEquiv.ext fun z => ?_
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    simp only [map_smul, congrIsometry_tprod, LinearIsometryEquiv.trans_apply]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The congruence respects inversion of the component equivalences. -/
theorem congrIsometry_symm (f : Π i, E i ≃ₗᵢ[𝕜] F i) :
    (congrIsometry f).symm = congrIsometry fun i => (f i).symm := by
  refine LinearIsometryEquiv.ext fun z => (congrIsometry f).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply]
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    rw [map_smul, map_smul, congrIsometry_tprod, congrIsometry_tprod]
    exact congrArg (c • ·) (congrArg (fun v : Π i, F i => tprod 𝕜 v)
      (funext fun i => ((f i).apply_symm_apply (y i)).symm))
  | add u v hu hv => rw [map_add, map_add, ← hu, ← hv]

end PiTensorProduct

/-! ### The `lp` family congruence

A family of linear isometry equivalences induces a linear isometry equivalence of `lp`
spaces componentwise. Absent from the pinned Mathlib; stated in upstream shape over the
instance context of the `lp` module structure. -/

/-- Membership in `Memℓp` only sees the componentwise norms, so it transfers across any
componentwise norm-preserving correspondence of families. -/
theorem Memℓp.of_norm_eq {α : Type*} {E F : α → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)] {p : ℝ≥0∞}
    {f : ∀ i, E i} {g : ∀ i, F i} (hf : Memℓp f p) (hfg : ∀ i, ‖g i‖ = ‖f i‖) :
    Memℓp g p := by
  rcases p.trichotomy with rfl | rfl | hp
  · rw [memℓp_zero_iff] at hf ⊢
    have hset : { i | g i ≠ 0 } = { i | f i ≠ 0 } :=
      Set.ext fun i => by
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← norm_ne_zero_iff, hfg i, norm_ne_zero_iff]
    rw [hset]
    exact hf
  · rw [memℓp_infty_iff] at hf ⊢
    have hfun : (fun i => ‖g i‖) = fun i => ‖f i‖ := funext hfg
    rw [hfun]
    exact hf
  · rw [memℓp_gen_iff hp] at hf ⊢
    have hfun : (fun i => ‖g i‖ ^ p.toReal) = fun i => ‖f i‖ ^ p.toReal :=
      funext fun i => by rw [hfg i]
    rw [hfun]
    exact hf

namespace lp

variable {α 𝕜 : Type*} {E F : α → Type*} {p : ℝ≥0∞} [NormedRing 𝕜]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, Module 𝕜 (F i)] [∀ i, IsBoundedSMul 𝕜 (F i)]

/-- A family of linear isometry equivalences `f i : E i ≃ₗᵢ[𝕜] F i` induces a linear
isometry equivalence `lp E p ≃ₗᵢ[𝕜] lp F p`, acting componentwise. Upstream candidate
(the `lp` counterpart of the finite-index `LinearIsometryEquiv.piLpCongrRight`). -/
protected def congrₗᵢ [Fact (1 ≤ p)] (f : ∀ i, E i ≃ₗᵢ[𝕜] F i) : lp E p ≃ₗᵢ[𝕜] lp F p where
  toFun x := ⟨fun i => f i (x i), (lp.memℓp x).of_norm_eq fun i => (f i).norm_map (x i)⟩
  invFun y :=
    ⟨fun i => (f i).symm (y i), (lp.memℓp y).of_norm_eq fun i => (f i).symm.norm_map (y i)⟩
  map_add' x y := lp.ext (funext fun i => by
    simp only [lp.coeFn_add, Pi.add_apply, map_add])
  map_smul' c x := lp.ext (funext fun i => by
    simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply])
  left_inv x := lp.ext (funext fun i => (f i).symm_apply_apply (x i))
  right_inv y := lp.ext (funext fun i => (f i).apply_symm_apply (y i))
  norm_map' x := by
    suffices h : ∀ y : lp F p, (∀ i, ‖y i‖ = ‖x i‖) → ‖y‖ = ‖x‖ from
      h _ fun i => (f i).norm_map (x i)
    intro y hy
    rcases p.trichotomy with rfl | rfl | hp
    · exact absurd (le_zero_iff.mp ‹Fact ((1 : ℝ≥0∞) ≤ 0)›.out) one_ne_zero
    · rw [lp.norm_eq_ciSup, lp.norm_eq_ciSup]
      exact congrArg iSup (funext hy)
    · rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
      exact congrArg (· ^ (1 / p.toReal)) (tsum_congr fun i => by rw [hy i])

/-- Component pin for the `lp` congruence. -/
@[simp]
protected theorem congrₗᵢ_apply [Fact (1 ≤ p)] (f : ∀ i, E i ≃ₗᵢ[𝕜] F i) (x : lp E p)
    (i : α) : lp.congrₗᵢ (p := p) f x i = f i (x i) :=
  rfl

/-- The inverse of the `lp` congruence is the congruence of the inverses. -/
protected theorem congrₗᵢ_symm [Fact (1 ≤ p)] (f : ∀ i, E i ≃ₗᵢ[𝕜] F i) :
    (lp.congrₗᵢ (p := p) f).symm = lp.congrₗᵢ fun i => (f i).symm :=
  rfl

end lp

/-! ### The completed tensor-power congruence and symmetrizer equivariance -/

namespace QFT

open PiTensorProduct UniformSpace Equiv
open scoped TensorProduct PiTensorProduct.InnerNorm Nat ENNReal

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- The lift of a one-particle unitary `u : E ≃ₗᵢ[𝕜] F` to the `n`-th Hilbert tensor
power: the completion (frozen P2.1b `Completion.congrₗᵢ`) of the constant-family
tensor-product congruence `u ⊗ ⋯ ⊗ u`. The `n`-particle piece of the
second-quantization functor (Reed & Simon I, §II.4; Bratteli & Robinson II, §5.2). -/
def tensorPowerCongr (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) :
    HilbertTensorPower 𝕜 E n ≃ₗᵢ[𝕜] HilbertTensorPower 𝕜 F n :=
  Completion.congrₗᵢ (congrIsometry fun _ : Fin n => u)

/-- Definitional pin: on the dense algebraic image, `tensorPowerCongr` is the algebraic
congruence. -/
@[simp]
theorem tensorPowerCongr_coe (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) (x : ⨂[𝕜]^n E) :
    tensorPowerCongr u n (x : HilbertTensorPower 𝕜 E n) =
      ((congrIsometry (fun _ : Fin n => u) x : ⨂[𝕜]^n F) : HilbertTensorPower 𝕜 F n) :=
  Completion.congrₗᵢ_coe _ x

/-- `tensorPowerCongr` of the identity is the identity. -/
theorem tensorPowerCongr_refl (n : ℕ) :
    tensorPowerCongr (LinearIsometryEquiv.refl 𝕜 E) n =
      LinearIsometryEquiv.refl 𝕜 (HilbertTensorPower 𝕜 E n) := by
  rw [tensorPowerCongr, congrIsometry_refl, Completion.congrₗᵢ_refl]

/-- `tensorPowerCongr` respects composition: the completed-power piece of
`Γ(u ∘ v) = Γ(u) ∘ Γ(v)`. -/
theorem tensorPowerCongr_trans (u : E ≃ₗᵢ[𝕜] F) (v : F ≃ₗᵢ[𝕜] G) (n : ℕ) :
    tensorPowerCongr (u.trans v) n =
      (tensorPowerCongr u n).trans (tensorPowerCongr v n) := by
  rw [tensorPowerCongr, tensorPowerCongr, tensorPowerCongr, congrIsometry_trans,
    Completion.congrₗᵢ_trans]

/-- `tensorPowerCongr` respects inversion. -/
theorem tensorPowerCongr_symm (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) :
    (tensorPowerCongr u n).symm = tensorPowerCongr u.symm n := by
  rw [tensorPowerCongr, tensorPowerCongr, Completion.congrₗᵢ_symm, congrIsometry_symm]

/-- **The congruence commutes with every permutation of the slots**:
`u⊗⁽ⁿ⁾ ∘ reindex σ = reindex σ ∘ u⊗⁽ⁿ⁾` — both send `⨂ₜ x` to
`⨂ₜ (u ∘ x ∘ σ⁻¹)`. The algebraic mechanism behind symmetrizer equivariance. -/
theorem congrIsometry_reindex (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) (σ : Perm (Fin n))
    (x : ⨂[𝕜]^n E) :
    congrIsometry (fun _ : Fin n => u) (reindex 𝕜 (fun _ ↦ E) σ x) =
      reindex 𝕜 (fun _ ↦ F) σ (congrIsometry (fun _ : Fin n => u) x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    simp only [map_smul]
    refine congrArg (c • ·) ?_
    simp only [reindex_tprod, congrIsometry_tprod]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **The congruence commutes with the algebraic symmetrizer**: averaging over the
permutation group commutes with `u⊗⁽ⁿ⁾` since each `reindex σ` does. -/
theorem symmetrizer_congrIsometry (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) (x : ⨂[𝕜]^n E) :
    symmetrizer 𝕜 F n (congrIsometry (fun _ : Fin n => u) x) =
      congrIsometry (fun _ : Fin n => u) (symmetrizer 𝕜 E n x) := by
  rw [symmetrizer_apply, symmetrizer_apply, map_smul, map_sum]
  refine congrArg ((n ! : 𝕜)⁻¹ • ·) ?_
  exact Finset.sum_congr rfl fun σ _ => (congrIsometry_reindex u n σ x).symm

/-- **The congruence commutes with the completed symmetrizer** — the density transfer
of `symmetrizer_congrIsometry`. -/
theorem symmetrizerL_tensorPowerCongr (u : E ≃ₗᵢ[𝕜] F) (n : ℕ)
    (x : HilbertTensorPower 𝕜 E n) :
    symmetrizerL 𝕜 F n (tensorPowerCongr u n x) =
      tensorPowerCongr u n (symmetrizerL 𝕜 E n x) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((symmetrizerL 𝕜 F n).continuous.comp (tensorPowerCongr u n).continuous)
      ((tensorPowerCongr u n).continuous.comp (symmetrizerL 𝕜 E n).continuous)
  | ih a =>
    rw [tensorPowerCongr_coe, symmetrizerL_coe, symmetrizerL_coe, tensorPowerCongr_coe,
      symmetrizer_congrIsometry]

/-! ### Restriction to the boson sectors -/

/-- The completed congruence maps the boson sector into the boson sector. -/
theorem tensorPowerCongr_mem_symTensorPower (u : E ≃ₗᵢ[𝕜] F) (n : ℕ)
    {x : HilbertTensorPower 𝕜 E n} (hx : x ∈ SymTensorPower 𝕜 E n) :
    tensorPowerCongr u n x ∈ SymTensorPower 𝕜 F n := by
  rw [mem_symTensorPower_iff] at hx ⊢
  rw [symmetrizerL_tensorPowerCongr, hx]

/-- The lift of a one-particle unitary to the `n`-particle boson sector: the restriction
of `tensorPowerCongr` to `SymTensorPower`, legitimate by symmetrizer equivariance. -/
def symTensorPowerCongr (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) :
    SymTensorPower 𝕜 E n ≃ₗᵢ[𝕜] SymTensorPower 𝕜 F n where
  toFun ψ := ⟨tensorPowerCongr u n ψ, tensorPowerCongr_mem_symTensorPower u n ψ.2⟩
  invFun w := ⟨(tensorPowerCongr u n).symm w, by
    rw [tensorPowerCongr_symm]
    exact tensorPowerCongr_mem_symTensorPower u.symm n w.2⟩
  map_add' ψ₁ ψ₂ := Subtype.ext (by
    simp only [Submodule.coe_add, map_add])
  map_smul' c ψ := Subtype.ext (by
    simp only [Submodule.coe_smul, map_smul, RingHom.id_apply])
  left_inv ψ := Subtype.ext ((tensorPowerCongr u n).symm_apply_apply _)
  right_inv w := Subtype.ext ((tensorPowerCongr u n).apply_symm_apply _)
  norm_map' ψ := (tensorPowerCongr u n).norm_map _

/-- Ambient-value pin for the sector congruence. -/
@[simp]
theorem symTensorPowerCongr_coe (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) (ψ : SymTensorPower 𝕜 E n) :
    (symTensorPowerCongr u n ψ : HilbertTensorPower 𝕜 F n) =
      tensorPowerCongr u n (ψ : HilbertTensorPower 𝕜 E n) :=
  rfl

/-- The sector congruence of the identity is the identity. -/
theorem symTensorPowerCongr_refl (n : ℕ) :
    symTensorPowerCongr (LinearIsometryEquiv.refl 𝕜 E) n =
      LinearIsometryEquiv.refl 𝕜 (SymTensorPower 𝕜 E n) := by
  refine LinearIsometryEquiv.ext fun ψ => Subtype.ext ?_
  rw [symTensorPowerCongr_coe, tensorPowerCongr_refl]
  rfl

/-- The sector congruence respects composition. -/
theorem symTensorPowerCongr_trans (u : E ≃ₗᵢ[𝕜] F) (v : F ≃ₗᵢ[𝕜] G) (n : ℕ) :
    symTensorPowerCongr (u.trans v) n =
      (symTensorPowerCongr u n).trans (symTensorPowerCongr v n) := by
  refine LinearIsometryEquiv.ext fun ψ => Subtype.ext ?_
  rw [symTensorPowerCongr_coe, tensorPowerCongr_trans, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply, symTensorPowerCongr_coe, symTensorPowerCongr_coe]

/-- The sector congruence respects inversion. -/
theorem symTensorPowerCongr_symm (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) :
    (symTensorPowerCongr u n).symm = symTensorPowerCongr u.symm n := by
  refine LinearIsometryEquiv.ext fun w => Subtype.ext ?_
  rw [symTensorPowerCongr_coe]
  show ((tensorPowerCongr u n).symm (w : HilbertTensorPower 𝕜 F n) :
    HilbertTensorPower 𝕜 E n) = tensorPowerCongr u.symm n (w : HilbertTensorPower 𝕜 F n)
  rw [tensorPowerCongr_symm]

/-! ### Equivariance of insertion and contraction

The sector-map mechanism of the conjugation laws. Insertion:
`u⊗⁽ⁿ⁺¹⁾ (g ⊗ ψ) = (u g) ⊗ u⊗⁽ⁿ⁾ ψ` (postcomposition distributes over `Fin.cons`).
Contraction: `u⊗⁽ⁿ⁾ (⟪g, ·⟫₁ w) = ⟪u g, ·⟫₁ (u⊗⁽ⁿ⁺¹⁾ w)`, because unitarity gives
`⟪u g, u x₀⟫ = ⟪g, x₀⟫` — this is why the annihilation conjugation law carries `u g`
with no conjugation despite the antilinearity of `a` in its argument. -/

/-- Insertion equivariance on the algebraic powers. -/
theorem congrIsometry_insertAux (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) (g : E) (x : ⨂[𝕜]^n E) :
    congrIsometry (fun _ : Fin (n + 1) => u) (insertAux 𝕜 E n g x) =
      insertAux 𝕜 F n (u g) (congrIsometry (fun _ : Fin n => u) x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    simp only [map_smul]
    refine congrArg (c • ·) ?_
    rw [insertAux_tprod, congrIsometry_tprod, congrIsometry_tprod, insertAux_tprod]
    refine congrArg (fun v : Fin (n + 1) → F => tprod 𝕜 v) (funext fun i => ?_)
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rw [Fin.cons_zero, Fin.cons_zero]
    · rw [Fin.cons_succ, Fin.cons_succ]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Contraction equivariance on the algebraic powers: the unitarity computation
`⟪u g, u x₀⟫ = ⟪g, x₀⟫` slotwise. -/
theorem congrIsometry_contractAux (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) (g : E)
    (y : ⨂[𝕜]^(n + 1) E) :
    congrIsometry (fun _ : Fin n => u) (contractAux 𝕜 E n g y) =
      contractAux 𝕜 F n (u g) (congrIsometry (fun _ : Fin (n + 1) => u) y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul]
    refine congrArg (c • ·) ?_
    rw [contractAux_tprod, map_smul, congrIsometry_tprod, congrIsometry_tprod,
      contractAux_tprod, LinearIsometryEquiv.inner_map_map]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Completed insertion equivariance:
`u⊗⁽ⁿ⁺¹⁾ ∘ insertL g = insertL (u g) ∘ u⊗⁽ⁿ⁾`. -/
theorem tensorPowerCongr_insertL (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) (g : E)
    (ψ : HilbertTensorPower 𝕜 E n) :
    tensorPowerCongr u (n + 1) (insertL 𝕜 E n g ψ) =
      insertL 𝕜 F n (u g) (tensorPowerCongr u n ψ) := by
  induction ψ using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((tensorPowerCongr u (n + 1)).continuous.comp (insertL 𝕜 E n g).continuous)
      ((insertL 𝕜 F n (u g)).continuous.comp (tensorPowerCongr u n).continuous)
  | ih a =>
    rw [insertL_coe, tensorPowerCongr_coe, tensorPowerCongr_coe, insertL_coe,
      congrIsometry_insertAux]

/-- Completed contraction equivariance:
`u⊗⁽ⁿ⁾ ∘ contractL g = contractL (u g) ∘ u⊗⁽ⁿ⁺¹⁾`. -/
theorem tensorPowerCongr_contractL (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) (g : E)
    (w : HilbertTensorPower 𝕜 E (n + 1)) :
    tensorPowerCongr u n (contractL 𝕜 E n g w) =
      contractL 𝕜 F n (u g) (tensorPowerCongr u (n + 1) w) := by
  induction w using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((tensorPowerCongr u n).continuous.comp (contractL 𝕜 E n g).continuous)
      ((contractL 𝕜 F n (u g)).continuous.comp (tensorPowerCongr u (n + 1)).continuous)
  | ih a =>
    rw [contractL_coe, tensorPowerCongr_coe, tensorPowerCongr_coe, contractL_coe,
      congrIsometry_contractAux]

/-- **Sector creation equivariance**: the sector congruence intertwines the creation
sector maps, `Γₙ₊₁(u) ∘ a†ₙ(g) = a†ₙ(u g) ∘ Γₙ(u)` — the frozen `√(n+1)` factor is a
scalar and passes through (Bratteli & Robinson II, §5.2). -/
theorem symTensorPowerCongr_creationSector (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) (g : E)
    (ψ : SymTensorPower 𝕜 E n) :
    symTensorPowerCongr u (n + 1) (creationSector 𝕜 E n g ψ) =
      creationSector 𝕜 F n (u g) (symTensorPowerCongr u n ψ) := by
  refine Subtype.ext ?_
  rw [symTensorPowerCongr_coe, creationSector_apply_coe, creationSector_apply_coe,
    symTensorPowerCongr_coe, map_smul, ← symmetrizerL_tensorPowerCongr,
    tensorPowerCongr_insertL]

/-- **Sector annihilation equivariance**: `Γₙ(u) ∘ aₙ(g) = aₙ(u g) ∘ Γₙ₊₁(u)`. -/
theorem symTensorPowerCongr_annihilationSector (u : E ≃ₗᵢ[𝕜] F) (n : ℕ) (g : E)
    (w : SymTensorPower 𝕜 E (n + 1)) :
    symTensorPowerCongr u n (annihilationSector 𝕜 E n g w) =
      annihilationSector 𝕜 F n (u g) (symTensorPowerCongr u (n + 1) w) := by
  refine Subtype.ext ?_
  rw [symTensorPowerCongr_coe, annihilationSector_apply_coe,
    annihilationSector_apply_coe, symTensorPowerCongr_coe, map_smul,
    ← symmetrizerL_tensorPowerCongr, tensorPowerCongr_contractL]

/-! ### The second-quantization functor Γ -/

/-- **The second-quantization functor** `Γ(u)`: the lift of a one-particle unitary
`u : E ≃ₗᵢ[𝕜] F` to a unitary of the boson Fock spaces, acting as `u ⊗ ⋯ ⊗ u` on each
boson sector (Reed & Simon I, §II.4; Reed & Simon II, §X.7; Bratteli & Robinson II,
§5.2 — the Fock implementation `Γ(U)`). -/
def secondQuantization (u : E ≃ₗᵢ[𝕜] F) : BosonFock 𝕜 E ≃ₗᵢ[𝕜] BosonFock 𝕜 F :=
  lp.congrₗᵢ fun n => symTensorPowerCongr u n

/-- Component pin: `Γ(u)` acts sector-wise. -/
@[simp]
theorem secondQuantization_apply (u : E ≃ₗᵢ[𝕜] F) (x : BosonFock 𝕜 E) (k : ℕ) :
    secondQuantization u x k = symTensorPowerCongr u k (x k) :=
  rfl

/-- **Γ is unital**: `Γ(1) = 1`. -/
theorem secondQuantization_refl :
    secondQuantization (LinearIsometryEquiv.refl 𝕜 E) =
      LinearIsometryEquiv.refl 𝕜 (BosonFock 𝕜 E) := by
  refine LinearIsometryEquiv.ext fun x => lp.ext (funext fun k => ?_)
  rw [secondQuantization_apply, symTensorPowerCongr_refl]
  rfl

/-- **Γ is multiplicative**: `Γ(u ∘ v) = Γ(u) ∘ Γ(v)` (in `trans` order: composing the
one-particle unitaries composes the second quantizations). With
`secondQuantization_refl`, `Γ` is a monoid homomorphism on unitaries of `E`. -/
theorem secondQuantization_trans (u : E ≃ₗᵢ[𝕜] F) (v : F ≃ₗᵢ[𝕜] G) :
    secondQuantization (u.trans v) =
      (secondQuantization u).trans (secondQuantization v) := by
  refine LinearIsometryEquiv.ext fun x => lp.ext (funext fun k => ?_)
  rw [secondQuantization_apply, symTensorPowerCongr_trans]
  rfl

/-- **Γ respects inversion**: `Γ(u)⁻¹ = Γ(u⁻¹)`. -/
theorem secondQuantization_symm (u : E ≃ₗᵢ[𝕜] F) :
    (secondQuantization u).symm = secondQuantization u.symm := by
  refine LinearIsometryEquiv.ext fun y => lp.ext (funext fun k => ?_)
  show (symTensorPowerCongr u k).symm (y k) = symTensorPowerCongr u.symm k (y k)
  rw [symTensorPowerCongr_symm]

/-- **Γ preserves the vacuum**: `Γ(u) Ω = Ω` (Bratteli & Robinson II, §5.2). -/
theorem secondQuantization_vacuum (u : E ≃ₗᵢ[𝕜] F) :
    secondQuantization u (BosonFock.vacuum 𝕜 E) = BosonFock.vacuum 𝕜 F := by
  refine lp.ext (funext fun k => ?_)
  match k with
  | 0 =>
    rw [secondQuantization_apply, BosonFock.vacuum_apply_zero, BosonFock.vacuum_apply_zero]
    refine Subtype.ext ?_
    rw [symTensorPowerCongr_coe, tensorPowerCongr_coe, congrIsometry_tprod]
    exact congrArg
      (fun v : Fin 0 → F => ((tprod 𝕜 v : ⨂[𝕜]^0 F) : HilbertTensorPower 𝕜 F 0))
      (funext fun i => i.elim0)
  | m + 1 =>
    rw [secondQuantization_apply, BosonFock.vacuum_apply_succ, map_zero,
      BosonFock.vacuum_apply_succ]

/-- **Γ on one-particle states**: `Γ(u) |ψ⟩ = |u ψ⟩` — `Γ` restricts to `u` itself on
the one-particle sector. -/
theorem secondQuantization_oneParticle (u : E ≃ₗᵢ[𝕜] F) (ψ : E) :
    secondQuantization u (BosonFock.oneParticle 𝕜 E ψ) =
      BosonFock.oneParticle 𝕜 F (u ψ) := by
  refine lp.ext (funext fun k => ?_)
  match k with
  | 1 =>
    rw [secondQuantization_apply, BosonFock.oneParticle_apply_one,
      BosonFock.oneParticle_apply_one]
    refine Subtype.ext ?_
    rw [symTensorPowerCongr_coe, tensorPowerCongr_coe, congrIsometry_tprod]
    refine congrArg
      (fun v : Fin 1 → F => ((tprod 𝕜 v : ⨂[𝕜]^1 F) : HilbertTensorPower 𝕜 F 1)) ?_
    funext i
    fin_cases i
    simp
  | 0 =>
    rw [secondQuantization_apply,
      BosonFock.oneParticle_apply_ne 𝕜 E ψ (by norm_num : (0 : ℕ) ≠ 1), map_zero,
      BosonFock.oneParticle_apply_ne 𝕜 F (u ψ) (by norm_num : (0 : ℕ) ≠ 1)]
  | m + 2 =>
    rw [secondQuantization_apply,
      BosonFock.oneParticle_apply_ne 𝕜 E ψ (by omega), map_zero,
      BosonFock.oneParticle_apply_ne 𝕜 F (u ψ) (by omega)]

/-- **Γ preserves the finite-particle subspace**: `Γ(u) F₀ ⊆ F₀`. -/
theorem secondQuantization_mem_finiteParticle (u : E ≃ₗᵢ[𝕜] F) {x : BosonFock 𝕜 E}
    (hx : x ∈ BosonFock.finiteParticle 𝕜 E) :
    secondQuantization u x ∈ BosonFock.finiteParticle 𝕜 F := by
  obtain ⟨N, hN⟩ := (BosonFock.mem_finiteParticle_iff 𝕜 E).mp hx
  refine (BosonFock.mem_finiteParticle_iff 𝕜 F).mpr ⟨N, fun k hk => ?_⟩
  rw [secondQuantization_apply, hN k hk, map_zero]

/-- `Γ(u)⁻¹` preserves the finite-particle subspace: the inverse-direction membership
witness for the conjugated form of the intertwining laws. -/
theorem secondQuantization_symm_mem_finiteParticle (u : E ≃ₗᵢ[𝕜] F) {y : BosonFock 𝕜 F}
    (hy : y ∈ BosonFock.finiteParticle 𝕜 F) :
    (secondQuantization u).symm y ∈ BosonFock.finiteParticle 𝕜 E := by
  rw [secondQuantization_symm]
  exact secondQuantization_mem_finiteParticle u.symm hy

/-! ### The conjugation laws (the P2.6d payoff)

Stated as intertwining relations on the finite-particle domain — the repo's
`LinearPMap`-composition-free form (spec docstring, "No `LinearPMap` composition") —
with the literal conjugated forms `Γ(u) a†(g) Γ(u)⁻¹ = a†(u g)` and
`Γ(u) a(g) Γ(u)⁻¹ = a(u g)` as corollaries. -/

/-- **Creation intertwining**: `Γ(u) a†(g) = a†(u g) Γ(u)` on `F₀`
(Reed & Simon II, §X.7; Bratteli & Robinson II, §5.2). -/
theorem secondQuantization_creationPMap (u : E ≃ₗᵢ[𝕜] F) (g : E)
    (x : BosonFock.finiteParticle 𝕜 E) :
    secondQuantization u (creationPMap 𝕜 E g x) =
      creationPMap 𝕜 F (u g)
        ⟨secondQuantization u x, secondQuantization_mem_finiteParticle u x.2⟩ := by
  refine lp.ext (funext fun k => ?_)
  match k with
  | 0 =>
    rw [secondQuantization_apply]
    rw [show (creationPMap 𝕜 E g x) 0 = 0 from creationPMap_apply_zero 𝕜 E g x, map_zero]
    exact (creationPMap_apply_zero 𝕜 F (u g) _).symm
  | m + 1 =>
    rw [secondQuantization_apply, creationPMap_apply_succ, creationPMap_apply_succ,
      symTensorPowerCongr_creationSector]
    rfl

/-- **Annihilation intertwining**: `Γ(u) a(g) = a(u g) Γ(u)` on `F₀`. The direction pin:
despite `a` being antilinear in its argument, the intertwined operator is `a(u g)` with
no conjugation, because the contraction pairs `⟪g, ·⟫` and unitarity gives
`⟪u g, u ·⟫ = ⟪g, ·⟫` (Reed & Simon II, §X.7). -/
theorem secondQuantization_annihilationPMap (u : E ≃ₗᵢ[𝕜] F) (g : E)
    (x : BosonFock.finiteParticle 𝕜 E) :
    secondQuantization u (annihilationPMap 𝕜 E g x) =
      annihilationPMap 𝕜 F (u g)
        ⟨secondQuantization u x, secondQuantization_mem_finiteParticle u x.2⟩ := by
  refine lp.ext (funext fun m => ?_)
  rw [secondQuantization_apply, annihilationPMap_apply, annihilationPMap_apply,
    symTensorPowerCongr_annihilationSector]
  rfl

/-- **The conjugation law for creation** (the P2.6d covariance engine):
`Γ(u) a†(g) Γ(u)⁻¹ = a†(u g)` on `F₀` (Bratteli & Robinson II, §5.2). -/
theorem secondQuantization_conj_creationPMap (u : E ≃ₗᵢ[𝕜] F) (g : E)
    (y : BosonFock.finiteParticle 𝕜 F) :
    secondQuantization u
        (creationPMap 𝕜 E g
          ⟨(secondQuantization u).symm y,
            secondQuantization_symm_mem_finiteParticle u y.2⟩) =
      creationPMap 𝕜 F (u g) y := by
  rw [secondQuantization_creationPMap]
  exact congrArg (creationPMap 𝕜 F (u g))
    (Subtype.ext ((secondQuantization u).apply_symm_apply (y : BosonFock 𝕜 F)))

/-- **The conjugation law for annihilation**: `Γ(u) a(g) Γ(u)⁻¹ = a(u g)` on `F₀`. -/
theorem secondQuantization_conj_annihilationPMap (u : E ≃ₗᵢ[𝕜] F) (g : E)
    (y : BosonFock.finiteParticle 𝕜 F) :
    secondQuantization u
        (annihilationPMap 𝕜 E g
          ⟨(secondQuantization u).symm y,
            secondQuantization_symm_mem_finiteParticle u y.2⟩) =
      annihilationPMap 𝕜 F (u g) y := by
  rw [secondQuantization_annihilationPMap]
  exact congrArg (annihilationPMap 𝕜 F (u g))
    (Subtype.ext ((secondQuantization u).apply_symm_apply (y : BosonFock 𝕜 F)))

/-! ### Regression anchors

The general laws reproduce the expected concrete actions on the anchor vectors of the
frozen slice-2 spec: `Γ(u) a†(g) Ω = |u g⟩` combines vacuum preservation, the creation
intertwining, and the frozen `creationPMap_vacuum`. -/

/-- `Γ(u) a†(g) Ω = a†(u g) Ω = |u g⟩`: the intertwining law at the vacuum reproduces
the one-particle image of `u`. -/
example (u : E ≃ₗᵢ[𝕜] E) (g : E) :
    secondQuantization u
        (creationPMap 𝕜 E g
          ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩) =
      BosonFock.oneParticle 𝕜 E (u g) := by
  rw [creationPMap_vacuum, secondQuantization_oneParticle]

/-- `Γ(u) a(g) |g'⟩ = ⟪g, g'⟫ Ω`: the annihilation intertwining is consistent with the
frozen inner-product pairing — `⟪u g, u g'⟫ = ⟪g, g'⟫`, so both routes agree. -/
example (u : E ≃ₗᵢ[𝕜] E) (g g' : E) :
    secondQuantization u
        (annihilationPMap 𝕜 E g
          ⟨BosonFock.oneParticle 𝕜 E g',
            BosonFock.oneParticle_mem_finiteParticle 𝕜 E g'⟩) =
      inner 𝕜 g g' • BosonFock.vacuum 𝕜 E := by
  rw [annihilationPMap_oneParticle, map_smul, secondQuantization_vacuum]

end QFT
