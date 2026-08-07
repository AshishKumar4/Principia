import Atlas.Specs.QFT.CreationAnnihilation

/-!
# P2.2 — the CCR theorem grind: adjointness, commutation relations, Segal-field symmetry

Proofs of the frozen `Prop`-valued targets of the slice-2 spec
`Atlas/Specs/QFT/CreationAnnihilation.lean` (blueprint node P2.2, proof slice):

* `QFT.creationAnnihilationAdjoint` : `CreationAnnihilationAdjoint 𝕜 E` —
  `⟪a†(f) x, y⟫ = ⟪x, a(f) y⟫` on the finite-particle domain (Reed & Simon II, §X.7).
* `QFT.ccrOnDomain` : `CCROnDomain 𝕜 E` — `[a(f), a†(g)] = ⟪f, g⟫ • 1` on `F₀`.
* `QFT.creationsCommute` / `QFT.annihilationsCommute` :
  `[a†(f), a†(g)] = [a(f), a(g)] = 0` on `F₀`.
* `QFT.segalField_isFormalAdjoint_self` / `QFT.segalField_isSymmetric` — the Segal
  field `Φ(f) = 2^{-1/2}(a(f) + a†(f))` is formally self-adjoint, hence a symmetric
  `LinearPMap` in the sense of the frozen P2.3a spec — the bridge toward the Nelson
  analytic-vector node for `SegalFieldEssentiallySelfAdjoint`.

## Proof architecture (three layers, mirroring the spec's construction)

1. **Algebraic combinatorial core** on `⨂[𝕜]^n E`: the engine is
   `symmetrizer_contractAux_symmetrizer_tprod`, evaluating `Sₙ ∘ ⟪f,·⟫₁ ∘ Sₙ₊₁` on a
   pure tensor as a `(n+1)⁻¹`-weighted sum over the slot the contraction eats — the
   permutation sum over `Sₙ₊₁` is reindexed by `Equiv.Perm.decomposeFin` (choice of
   image of slot `0` × permutation of the rest) and the inner `Sₙ`-average absorbs
   the residual permutation (`symmetrizer_tprod_comp_perm`). Specializing to inserted
   tensors gives the two sum-over-slots formulas (`symmetrizer_contract_insert_tprod`,
   `symmetrizer_insert_contract_symmetrizer_tprod`) whose difference telescopes to the
   CCR (`ccr_algebraic_succ`): `a(f)a†(g)` sees the inserted slot (the `⟪f,g⟫` term)
   plus `n+1` exchange terms, `a†(g)a(f)` sees exactly the same exchange terms.
   `symmetrizer_insertAux_symmetrizer` (the outer symmetrizer absorbs an inner one
   through an insertion) removes the Bratteli–Robinson compression redundancy.
2. **Completed layer**: each algebraic identity transfers to the Hilbert tensor
   powers by `Completion.induction_on` (the identity is a closed condition among
   continuous maps, checked on the dense algebraic image via the `…_coe` pins).
3. **Sector and `lp` layer**: the sector maps are `√·`-scalings of the completed
   composites (`creationSector_apply_coe`/`annihilationSector_apply_coe`); the `√`
   factors square to exactly the `(n+1)`/`(n+2)` weights of the algebraic layer
   (Reed & Simon II, §X.7 — "where the `√` factors live", spec docstring). The `lp`
   assembly is componentwise (`lp.ext`); for the adjointness the `lp` inner product
   is a finite sum on finite-particle vectors (`mem_finiteParticle_iff` caps the
   support), shifted across sectors by `Finset.sum_range_succ'`.
   `annihilationsCommute` is derived from `creationsCommute` by duality: both
   commutators have the same inner products against the dense `F₀`
   (`Dense.eq_of_inner_left`), using the proven adjointness twice.

Import discipline (spec module docstring, "Scope discipline"): this file opens the
scoped `PiTensorProduct.InnerNorm` instances and replicates the spec's
`assert_not_exists` guard.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II: Fourier Analysis,
  Self-Adjointness* (1975), §X.7: mutual adjointness of `a(f)`/`a†(f)` on `F₀`, the
  CCR `[a(f), a†(g)] = ⟪f, g⟫`, `[a(f), a(g)] = [a†(f), a†(g)] = 0`, and the symmetry
  of the Segal field `Φ_S(f)` (the first step of Thm X.41). Section-level citations.
* O. Bratteli, D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics
  2*, 2nd edition (1997), §5.2: the CCR over the boson Fock space in compressed form
  `P₊ (⋯) P₊`; the compression-redundancy lemmas here formalize why the compressed
  and uncompressed forms agree. Section-level citation.
-/

assert_not_exists PiTensorProduct.projectiveSeminorm

noncomputable section

namespace QFT

open PiTensorProduct UniformSpace Equiv
open scoped TensorProduct PiTensorProduct.InnerNorm Nat ENNReal

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (n : ℕ)

/-! ### Scalar bookkeeping helpers -/

private theorem factorial_succ_inv_mul :
    (((n + 1)! : ℕ) : 𝕜)⁻¹ * ((n ! : ℕ) : 𝕜) = ((n + 1 : ℕ) : 𝕜)⁻¹ := by
  have h1 : ((n ! : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv, mul_assoc, inv_mul_cancel₀ h1, mul_one]

private theorem ofReal_sqrt_succ_mul_self (m : ℕ) :
    ((Real.sqrt (m + 1) : ℝ) : 𝕜) * ((Real.sqrt (m + 1) : ℝ) : 𝕜) = ((m + 1 : ℕ) : 𝕜) := by
  rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  norm_cast

/-! ### The algebraic combinatorial core

Everything in this section lives on the algebraic tensor powers `⨂[𝕜]^n E` and is pure
finite `Perm`-sum combinatorics; no completion, no norms. -/

/-- The symmetrizer absorbs a permutation of the slots of a pure tensor: if
`w = z ∘ τ` slotwise, then `Sₙ (⨂ₜ w) = Sₙ (⨂ₜ z)`. This is `symmetrizer_reindex`
read on pure tensors, and the workhorse for every reindexed permutation sum below. -/
theorem symmetrizer_tprod_comp_perm (τ : Perm (Fin n)) {z w : Fin n → E}
    (h : ∀ i, w i = z (τ i)) :
    symmetrizer 𝕜 E n (tprod 𝕜 w) = symmetrizer 𝕜 E n (tprod 𝕜 z) := by
  have hw : (tprod 𝕜 w : ⨂[𝕜]^n E) = reindex 𝕜 (fun _ ↦ E) τ⁻¹ (tprod 𝕜 z) := by
    rw [reindex_tprod]
    exact congrArg (fun v : Fin n → E => tprod 𝕜 v) (funext fun i => h i)
  rw [hw, symmetrizer_reindex]

/-- **Contraction of a symmetrized pure tensor, sum-over-slots form**: the composite
`Sₙ ∘ ⟪f,·⟫₁ ∘ Sₙ₊₁` sends `⨂ₜ y` to the average over the slot `k` fed to the
contraction, with the remaining slots symmetrized. The permutation sum over `Sₙ₊₁` is
reindexed by `Equiv.Perm.decomposeFin` (the image of slot `0` times a permutation of
the remaining slots), and the residual permutation is absorbed by the outer
symmetrizer. This is the engine behind both Bratteli–Robinson sum-over-slots
formulas (BR II, §5.2). -/
theorem symmetrizer_contractAux_symmetrizer_tprod (f : E) (y : Fin (n + 1) → E) :
    symmetrizer 𝕜 E n (contractAux 𝕜 E n f (symmetrizer 𝕜 E (n + 1) (tprod 𝕜 y))) =
      ((n + 1 : ℕ) : 𝕜)⁻¹ • ∑ k : Fin (n + 1), inner 𝕜 f (y k) •
        symmetrizer 𝕜 E n (tprod 𝕜 fun i => y (Equiv.swap 0 k i.succ)) := by
  rw [symmetrizer_tprod, map_smul, map_smul, map_sum, map_sum]
  rw [Finset.sum_congr rfl fun (σ : Perm (Fin (n + 1))) _ => show
      symmetrizer 𝕜 E n (contractAux 𝕜 E n f (tprod 𝕜 fun i => y (σ i))) =
        inner 𝕜 f (y (σ 0)) • symmetrizer 𝕜 E n (tprod 𝕜 fun i => y (σ i.succ)) by
    rw [contractAux_tprod, map_smul]
    rfl]
  rw [← Equiv.sum_comp Perm.decomposeFin.symm
      (fun σ : Perm (Fin (n + 1)) =>
        inner 𝕜 f (y (σ 0)) • symmetrizer 𝕜 E n (tprod 𝕜 fun i => y (σ i.succ))),
    Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun (k : Fin (n + 1)) _ => Finset.sum_congr rfl
      fun (τ : Perm (Fin n)) _ => show
      inner 𝕜 f (y (Perm.decomposeFin.symm (k, τ) 0)) •
          symmetrizer 𝕜 E n (tprod 𝕜 fun i => y (Perm.decomposeFin.symm (k, τ) i.succ)) =
        inner 𝕜 f (y k) •
          symmetrizer 𝕜 E n (tprod 𝕜 fun i => y (Equiv.swap 0 k i.succ)) by
    rw [Perm.decomposeFin_symm_apply_zero]
    exact congrArg (inner 𝕜 f (y k) • ·)
      (symmetrizer_tprod_comp_perm 𝕜 E n τ fun i => by
        rw [Perm.decomposeFin_symm_apply_succ])]
  rw [Finset.sum_congr rfl fun (k : Fin (n + 1)) _ => show
      (∑ _τ : Perm (Fin n), inner 𝕜 f (y k) •
          symmetrizer 𝕜 E n (tprod 𝕜 fun i => y (Equiv.swap 0 k i.succ))) =
        ((n ! : ℕ) : 𝕜) • (inner 𝕜 f (y k) •
          symmetrizer 𝕜 E n (tprod 𝕜 fun i => y (Equiv.swap 0 k i.succ))) by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul 𝕜]]
  rw [← Finset.smul_sum, smul_smul, factorial_succ_inv_mul]

/-- **The symmetrizer absorbs an inner symmetrizer through an insertion**:
`Sₙ₊₁ (f ⊗ Sₙ ψ) = Sₙ₊₁ (f ⊗ ψ)`. This is the Bratteli–Robinson compression
redundancy on the creation side (BR II, §5.2): pre-symmetrizing the input costs
nothing once the output is symmetrized. -/
theorem symmetrizer_insertAux_symmetrizer (g : E) (ψ : ⨂[𝕜]^n E) :
    symmetrizer 𝕜 E (n + 1) (insertAux 𝕜 E n g (symmetrizer 𝕜 E n ψ)) =
      symmetrizer 𝕜 E (n + 1) (insertAux 𝕜 E n g ψ) := by
  induction ψ using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul]
    refine congrArg (c • ·) ?_
    rw [symmetrizer_tprod, map_smul, map_smul, map_sum, map_sum]
    rw [Finset.sum_congr rfl fun (τ : Perm (Fin n)) _ => show
        symmetrizer 𝕜 E (n + 1) (insertAux 𝕜 E n g (tprod 𝕜 fun i => x (τ i))) =
          symmetrizer 𝕜 E (n + 1) (insertAux 𝕜 E n g (tprod 𝕜 x)) by
      rw [insertAux_tprod, insertAux_tprod]
      refine symmetrizer_tprod_comp_perm 𝕜 E (n + 1) (Perm.decomposeFin.symm (0, τ))
        fun j => ?_
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
      · simp only [Fin.cons_zero, Perm.decomposeFin_symm_apply_zero]
      · simp only [Fin.cons_succ, Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
          Equiv.refl_apply]]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀
        (Nat.cast_ne_zero.mpr n.factorial_ne_zero : ((n ! : ℕ) : 𝕜) ≠ 0), one_smul]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- **The `a(f) a†(g)` sum-over-slots formula on pure tensors**: contracting after
inserting sees the inserted slot — the `⟪f, g⟫` term — plus each original slot with
`g` substituted in (the Bose exchange terms), all weighted `(n+1)⁻¹`
(Reed & Simon II, §X.7; BR II, §5.2). -/
theorem symmetrizer_contract_insert_tprod (f g : E) (x : Fin n → E) :
    symmetrizer 𝕜 E n (contractAux 𝕜 E n f
        (symmetrizer 𝕜 E (n + 1) (insertAux 𝕜 E n g (tprod 𝕜 x)))) =
      ((n + 1 : ℕ) : 𝕜)⁻¹ • (inner 𝕜 f g • symmetrizer 𝕜 E n (tprod 𝕜 x) +
        ∑ j : Fin n, inner 𝕜 f (x j) •
          symmetrizer 𝕜 E n (tprod 𝕜 (Function.update x j g))) := by
  rw [insertAux_tprod, symmetrizer_contractAux_symmetrizer_tprod, Fin.sum_univ_succ]
  refine congrArg (((n + 1 : ℕ) : 𝕜)⁻¹ • ·) (congrArg₂ (· + ·) ?_ ?_)
  · rw [Fin.cons_zero]
    refine congrArg (inner 𝕜 f g • ·) (congrArg (symmetrizer 𝕜 E n)
      (congrArg (fun v : Fin n → E => tprod 𝕜 v) (funext fun i => ?_)))
    simp only [Equiv.swap_self, Equiv.refl_apply, Fin.cons_succ]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.cons_succ]
    refine congrArg (inner 𝕜 f (x j) • ·) (congrArg (symmetrizer 𝕜 E n)
      (congrArg (fun v : Fin n → E => tprod 𝕜 v) (funext fun i => ?_)))
    rcases eq_or_ne i j with rfl | hij
    · rw [Equiv.swap_apply_right, Fin.cons_zero, Function.update_self]
    · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i)
          (fun hc => hij (Fin.succ_injective _ hc)),
        Fin.cons_succ, Function.update_of_ne hij]

/-- **The `a†(g) a(f)` sum-over-slots formula on pure tensors**: inserting after
contracting sees exactly the exchange terms of `symmetrizer_contract_insert_tprod` —
each slot `k` replaced by `g` — and nothing else. The difference of the two formulas
is the CCR. -/
theorem symmetrizer_insert_contract_symmetrizer_tprod (f g : E) (x : Fin (n + 1) → E) :
    symmetrizer 𝕜 E (n + 1) (insertAux 𝕜 E n g
        (contractAux 𝕜 E n f (symmetrizer 𝕜 E (n + 1) (tprod 𝕜 x)))) =
      ((n + 1 : ℕ) : 𝕜)⁻¹ • ∑ k : Fin (n + 1), inner 𝕜 f (x k) •
        symmetrizer 𝕜 E (n + 1) (tprod 𝕜 (Function.update x k g)) := by
  rw [symmetrizer_tprod, map_smul, map_smul, map_smul, map_sum, map_sum, map_sum]
  rw [Finset.sum_congr rfl fun (σ : Perm (Fin (n + 1))) _ => show
      symmetrizer 𝕜 E (n + 1) (insertAux 𝕜 E n g (contractAux 𝕜 E n f
          (tprod 𝕜 fun i => x (σ i)))) =
        inner 𝕜 f (x (σ 0)) • symmetrizer 𝕜 E (n + 1)
          (tprod 𝕜 (Fin.cons g fun i => x (σ i.succ))) by
    rw [contractAux_tprod, map_smul, map_smul, insertAux_tprod]
    rfl]
  rw [← Equiv.sum_comp Perm.decomposeFin.symm
      (fun σ : Perm (Fin (n + 1)) => inner 𝕜 f (x (σ 0)) •
        symmetrizer 𝕜 E (n + 1) (tprod 𝕜 (Fin.cons g fun i => x (σ i.succ)))),
    Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun (k : Fin (n + 1)) _ => Finset.sum_congr rfl
      fun (τ : Perm (Fin n)) _ => show
      inner 𝕜 f (x (Perm.decomposeFin.symm (k, τ) 0)) • symmetrizer 𝕜 E (n + 1)
          (tprod 𝕜 (Fin.cons g fun i => x (Perm.decomposeFin.symm (k, τ) i.succ))) =
        inner 𝕜 f (x k) • symmetrizer 𝕜 E (n + 1) (tprod 𝕜 (Function.update x k g)) by
    rw [Perm.decomposeFin_symm_apply_zero]
    refine congrArg (inner 𝕜 f (x k) • ·) ?_
    have hmid : symmetrizer 𝕜 E (n + 1)
        (tprod 𝕜 (Fin.cons g fun i => x (Perm.decomposeFin.symm (k, τ) i.succ))) =
        symmetrizer 𝕜 E (n + 1)
          (tprod 𝕜 (Fin.cons g fun i => x (Equiv.swap 0 k i.succ))) := by
      refine symmetrizer_tprod_comp_perm 𝕜 E (n + 1) (Perm.decomposeFin.symm (0, τ))
        fun j => ?_
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
      · simp only [Fin.cons_zero, Perm.decomposeFin_symm_apply_zero]
      · simp only [Fin.cons_succ, Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
          Equiv.refl_apply]
    have hupd : symmetrizer 𝕜 E (n + 1) (tprod 𝕜 (Function.update x k g)) =
        symmetrizer 𝕜 E (n + 1)
          (tprod 𝕜 (Fin.cons g fun i => x (Equiv.swap 0 k i.succ))) := by
      refine symmetrizer_tprod_comp_perm 𝕜 E (n + 1) (Equiv.swap 0 k) fun j => ?_
      rcases eq_or_ne j k with rfl | hjk
      · simp only [Equiv.swap_apply_right, Fin.cons_zero, Function.update_self]
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨m, rfl⟩
          · exact absurd rfl hjk
          · simp only [Function.update_of_ne hjk, Equiv.swap_apply_left, Fin.cons_succ,
              Equiv.swap_apply_right]
        · simp only [Function.update_of_ne hjk,
            Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i) hjk, Fin.cons_succ]
    rw [hmid, hupd]]
  rw [Finset.sum_congr rfl fun (k : Fin (n + 1)) _ => show
      (∑ _τ : Perm (Fin n), inner 𝕜 f (x k) •
          symmetrizer 𝕜 E (n + 1) (tprod 𝕜 (Function.update x k g))) =
        ((n ! : ℕ) : 𝕜) • (inner 𝕜 f (x k) •
          symmetrizer 𝕜 E (n + 1) (tprod 𝕜 (Function.update x k g))) by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul 𝕜]]
  rw [← Finset.smul_sum, smul_smul, factorial_succ_inv_mul]

/-- The algebraic CCR in the vacuum-adjacent sector: on `⨂[𝕜]^0 E` there is no
exchange term, and `a(f) a†(g)` is multiplication by `⟪f, g⟫` outright. -/
theorem ccr_algebraic_zero (f g : E) (z : ⨂[𝕜]^0 E) :
    symmetrizer 𝕜 E 0 (contractAux 𝕜 E 0 f
        (symmetrizer 𝕜 E 1 (insertAux 𝕜 E 0 g (symmetrizer 𝕜 E 0 z)))) =
      inner 𝕜 f g • symmetrizer 𝕜 E 0 z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul]
    rw [smul_comm (inner 𝕜 f g) c]
    refine congrArg (c • ·) ?_
    rw [symmetrizer_insertAux_symmetrizer, symmetrizer_contract_insert_tprod]
    simp
  | add u v hu hv => simp only [map_add, hu, hv, smul_add]

private theorem ccr_algebraic_succ_tprod (f g : E) (x : Fin (n + 1) → E) :
    ((n + 1 + 1 : ℕ) : 𝕜) • symmetrizer 𝕜 E (n + 1) (contractAux 𝕜 E (n + 1) f
        (symmetrizer 𝕜 E (n + 2) (insertAux 𝕜 E (n + 1) g
          (symmetrizer 𝕜 E (n + 1) (tprod 𝕜 x))))) -
      ((n + 1 : ℕ) : 𝕜) • symmetrizer 𝕜 E (n + 1) (insertAux 𝕜 E n g
        (symmetrizer 𝕜 E n (contractAux 𝕜 E n f
          (symmetrizer 𝕜 E (n + 1) (tprod 𝕜 x))))) =
      inner 𝕜 f g • symmetrizer 𝕜 E (n + 1) (tprod 𝕜 x) := by
  have h2 : ((n + 1 + 1 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have h1 : ((n + 1 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  rw [symmetrizer_insertAux_symmetrizer, symmetrizer_contract_insert_tprod,
    symmetrizer_insertAux_symmetrizer, symmetrizer_insert_contract_symmetrizer_tprod,
    smul_smul, smul_smul, mul_inv_cancel₀ h2, mul_inv_cancel₀ h1, one_smul, one_smul]
  exact add_sub_cancel_right _ _

/-- **The algebraic CCR in the higher sectors**: the difference of the two
sum-over-slots composites telescopes to `⟪f, g⟫` — the `n + 2` slot terms of
`a(f) a†(g)` are the inserted-slot term `⟪f, g⟫` plus the `n + 1` exchange terms of
`a†(g) a(f)` (Reed & Simon II, §X.7; BR II, §5.2). Everything is stated with the
symmetrizers of the Bratteli–Robinson compressions in place, so it applies verbatim
to the sector maps. -/
theorem ccr_algebraic_succ (f g : E) (z : ⨂[𝕜]^(n + 1) E) :
    ((n + 1 + 1 : ℕ) : 𝕜) • symmetrizer 𝕜 E (n + 1) (contractAux 𝕜 E (n + 1) f
        (symmetrizer 𝕜 E (n + 2) (insertAux 𝕜 E (n + 1) g
          (symmetrizer 𝕜 E (n + 1) z)))) -
      ((n + 1 : ℕ) : 𝕜) • symmetrizer 𝕜 E (n + 1) (insertAux 𝕜 E n g
        (symmetrizer 𝕜 E n (contractAux 𝕜 E n f (symmetrizer 𝕜 E (n + 1) z)))) =
      inner 𝕜 f g • symmetrizer 𝕜 E (n + 1) z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul]
    rw [smul_comm ((n + 1 + 1 : ℕ) : 𝕜) c, smul_comm ((n + 1 : ℕ) : 𝕜) c,
      smul_comm (inner 𝕜 f g) c, ← smul_sub]
    exact congrArg (c • ·) (ccr_algebraic_succ_tprod 𝕜 E n f g x)
  | add u v hu hv =>
    simp only [map_add, smul_add]
    rw [← hu, ← hv]
    abel

private theorem insert_insert_symmetrizer_tprod (f g : E) (x : Fin n → E) :
    symmetrizer 𝕜 E (n + 2) (insertAux 𝕜 E (n + 1) f (insertAux 𝕜 E n g (tprod 𝕜 x))) =
      symmetrizer 𝕜 E (n + 2) (insertAux 𝕜 E (n + 1) g
        (insertAux 𝕜 E n f (tprod 𝕜 x))) := by
  rw [insertAux_tprod, insertAux_tprod, insertAux_tprod, insertAux_tprod]
  refine symmetrizer_tprod_comp_perm 𝕜 E (n + 2)
    (Equiv.swap (0 : Fin (n + 2)) (Fin.succ 0)) fun j => ?_
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
  · rw [Equiv.swap_apply_left, Fin.cons_zero, Fin.cons_succ, Fin.cons_zero]
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨m, rfl⟩
    · rw [Equiv.swap_apply_right, Fin.cons_succ, Fin.cons_zero, Fin.cons_zero]
    · have h0 : (m.succ.succ : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero _
      have h1 : (m.succ.succ : Fin (n + 2)) ≠ Fin.succ 0 :=
        fun hc => Fin.succ_ne_zero m (Fin.succ_injective _ hc)
      rw [Equiv.swap_apply_of_ne_of_ne h0 h1, Fin.cons_succ, Fin.cons_succ,
        Fin.cons_succ, Fin.cons_succ]

/-- **Double insertions commute under the symmetrizer**:
`Sₙ₊₂ (f ⊗ g ⊗ ψ) = Sₙ₊₂ (g ⊗ f ⊗ ψ)` — the algebraic heart of
`[a†(f), a†(g)] = 0`, a single slot transposition absorbed by the group average. -/
theorem symmetrizer_insert_insert_comm (f g : E) (z : ⨂[𝕜]^n E) :
    symmetrizer 𝕜 E (n + 2) (insertAux 𝕜 E (n + 1) f (insertAux 𝕜 E n g z)) =
      symmetrizer 𝕜 E (n + 2) (insertAux 𝕜 E (n + 1) g (insertAux 𝕜 E n f z)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul]
    exact congrArg (c • ·) (insert_insert_symmetrizer_tprod 𝕜 E n f g x)
  | add u v hu hv => simp only [map_add, hu, hv]

/-! ### The completed layer

Each algebraic identity transfers to the Hilbert tensor powers by density: the
identity is a closed condition (equality of continuous maps), checked on the dense
algebraic image through the `…_coe` definitional pins. -/

/-- The completed symmetrizer absorbs an inner symmetrizer through an insertion
(the completed compression redundancy). -/
theorem symmetrizerL_insertL_symmetrizerL (g : E) (w : HilbertTensorPower 𝕜 E n) :
    symmetrizerL 𝕜 E (n + 1) (insertL 𝕜 E n g (symmetrizerL 𝕜 E n w)) =
      symmetrizerL 𝕜 E (n + 1) (insertL 𝕜 E n g w) := by
  induction w using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((symmetrizerL 𝕜 E (n + 1)).continuous.comp ((insertL 𝕜 E n g).continuous.comp
        (symmetrizerL 𝕜 E n).continuous))
      ((symmetrizerL 𝕜 E (n + 1)).continuous.comp (insertL 𝕜 E n g).continuous)
  | ih a =>
    rw [symmetrizerL_coe, insertL_coe, symmetrizerL_coe, insertL_coe, symmetrizerL_coe,
      symmetrizer_insertAux_symmetrizer]

/-- The completed CCR composite in the `0`-sector: `S₀ ⟪f,·⟫₁ S₁ (g ⊗ ·) S₀` is
multiplication by `⟪f, g⟫`. -/
theorem ccrL_zero (f g : E) (w : HilbertTensorPower 𝕜 E 0) :
    symmetrizerL 𝕜 E 0 (contractL 𝕜 E 0 f
        (symmetrizerL 𝕜 E 1 (insertL 𝕜 E 0 g (symmetrizerL 𝕜 E 0 w)))) =
      inner 𝕜 f g • symmetrizerL 𝕜 E 0 w := by
  induction w using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((symmetrizerL 𝕜 E 0).continuous.comp ((contractL 𝕜 E 0 f).continuous.comp
        ((symmetrizerL 𝕜 E 1).continuous.comp ((insertL 𝕜 E 0 g).continuous.comp
          (symmetrizerL 𝕜 E 0).continuous))))
      (((symmetrizerL 𝕜 E 0).continuous).const_smul (inner 𝕜 f g))
  | ih a =>
    simp only [symmetrizerL_coe, insertL_coe, contractL_coe, ← Completion.coe_smul]
    exact congrArg (fun t : ⨂[𝕜]^0 E => (t : HilbertTensorPower 𝕜 E 0))
      (ccr_algebraic_zero 𝕜 E f g a)

/-- The completed CCR difference in the higher sectors, weighted exactly as the
sector maps will weight it. -/
theorem ccrL_succ (f g : E) (w : HilbertTensorPower 𝕜 E (n + 1)) :
    ((n + 1 + 1 : ℕ) : 𝕜) • symmetrizerL 𝕜 E (n + 1) (contractL 𝕜 E (n + 1) f
        (symmetrizerL 𝕜 E (n + 2) (insertL 𝕜 E (n + 1) g
          (symmetrizerL 𝕜 E (n + 1) w)))) -
      ((n + 1 : ℕ) : 𝕜) • symmetrizerL 𝕜 E (n + 1) (insertL 𝕜 E n g
        (symmetrizerL 𝕜 E n (contractL 𝕜 E n f (symmetrizerL 𝕜 E (n + 1) w)))) =
      inner 𝕜 f g • symmetrizerL 𝕜 E (n + 1) w := by
  induction w using Completion.induction_on with
  | hp =>
    refine isClosed_eq (Continuous.sub ?_ ?_)
      (((symmetrizerL 𝕜 E (n + 1)).continuous).const_smul (inner 𝕜 f g))
    · exact (((symmetrizerL 𝕜 E (n + 1)).continuous.comp
        ((contractL 𝕜 E (n + 1) f).continuous.comp
          ((symmetrizerL 𝕜 E (n + 2)).continuous.comp
            ((insertL 𝕜 E (n + 1) g).continuous.comp
              (symmetrizerL 𝕜 E (n + 1)).continuous)))).const_smul _)
    · exact (((symmetrizerL 𝕜 E (n + 1)).continuous.comp
        ((insertL 𝕜 E n g).continuous.comp
          ((symmetrizerL 𝕜 E n).continuous.comp
            ((contractL 𝕜 E n f).continuous.comp
              (symmetrizerL 𝕜 E (n + 1)).continuous)))).const_smul _)
  | ih a =>
    simp only [symmetrizerL_coe, insertL_coe, contractL_coe, ← Completion.coe_smul,
      ← Completion.coe_sub]
    exact congrArg (fun t : ⨂[𝕜]^(n + 1) E => (t : HilbertTensorPower 𝕜 E (n + 1)))
      (ccr_algebraic_succ 𝕜 E n f g a)

/-- Completed double insertions commute under the completed symmetrizer. -/
theorem symmetrizerL_insertL_insertL_comm (f g : E) (w : HilbertTensorPower 𝕜 E n) :
    symmetrizerL 𝕜 E (n + 2) (insertL 𝕜 E (n + 1) f (insertL 𝕜 E n g w)) =
      symmetrizerL 𝕜 E (n + 2) (insertL 𝕜 E (n + 1) g (insertL 𝕜 E n f w)) := by
  induction w using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((symmetrizerL 𝕜 E (n + 2)).continuous.comp
        ((insertL 𝕜 E (n + 1) f).continuous.comp (insertL 𝕜 E n g).continuous))
      ((symmetrizerL 𝕜 E (n + 2)).continuous.comp
        ((insertL 𝕜 E (n + 1) g).continuous.comp (insertL 𝕜 E n f).continuous))
  | ih a =>
    simp only [insertL_coe, symmetrizerL_coe]
    exact congrArg (fun t : ⨂[𝕜]^(n + 2) E => (t : HilbertTensorPower 𝕜 E (n + 2)))
      (symmetrizer_insert_insert_comm 𝕜 E n f g a)

/-! ### The sector layer

The sector maps of the frozen spec are `√(n+1)`-scalings of the completed composites;
here the `√` factors square into exactly the natural-number weights of the completed
layer, and the symmetry of the sector inputs (`mem_symTensorPower_iff`) turns the
compressed composites into the identities above. -/

/-- **Sector-level mutual adjointness**: `⟪a†(f) ψ, w⟫ = ⟪ψ, a(f) w⟫` between the
`n`- and `(n+1)`-sectors (Reed & Simon II, §X.7). The completed adjointness
`inner_insertL_left` plus the symmetrizer self-adjointness of `FockBridge`, with the
`√(n+1)` factors — real, hence conjugation-invariant — matching on both sides. -/
theorem inner_creationSector_left (f : E) (ψ : SymTensorPower 𝕜 E n)
    (w : SymTensorPower 𝕜 E (n + 1)) :
    inner 𝕜 (creationSector 𝕜 E n f ψ) w = inner 𝕜 ψ (annihilationSector 𝕜 E n f w) := by
  rw [Submodule.coe_inner, Submodule.coe_inner, creationSector_apply_coe,
    annihilationSector_apply_coe, inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
    inner_symmetrizerL_left, (mem_symTensorPower_iff 𝕜 E (n + 1)).mp w.2,
    inner_insertL_left, ← inner_symmetrizerL_left, (mem_symTensorPower_iff 𝕜 E n).mp ψ.2]

/-- **The sector CCR at the vacuum-adjacent sector**: `a(f) a†(g) = ⟪f, g⟫ • 1` on
the `0`-sector — there is no annihilation back-channel, so no exchange term. -/
theorem annihilationSector_creationSector_zero (f g : E) (ψ : SymTensorPower 𝕜 E 0) :
    annihilationSector 𝕜 E 0 f (creationSector 𝕜 E 0 g ψ) = inner 𝕜 f g • ψ := by
  have hψ : symmetrizerL 𝕜 E 0 (ψ : HilbertTensorPower 𝕜 E 0) = (ψ : HilbertTensorPower 𝕜 E 0) :=
    (mem_symTensorPower_iff 𝕜 E 0).mp ψ.2
  refine Subtype.ext ?_
  rw [Submodule.coe_smul, annihilationSector_apply_coe, creationSector_apply_coe,
    map_smul, map_smul, smul_smul, ofReal_sqrt_succ_mul_self,
    show ((0 + 1 : ℕ) : 𝕜) = 1 by norm_num, one_smul, ← hψ]
  exact ccrL_zero 𝕜 E f g (ψ : HilbertTensorPower 𝕜 E 0)

/-- **The sector CCR in the higher sectors**:
`a(f) a†(g) - a†(g) a(f) = ⟪f, g⟫ • 1` on the `(n+1)`-sector — the `√(n+2)` and
`√(n+1)` pairs square to the weights of `ccrL_succ`, and the exchange terms cancel
between the two composites (Reed & Simon II, §X.7; BR II, §5.2). -/
theorem annihilationSector_creationSector_sub (f g : E) (w : SymTensorPower 𝕜 E (n + 1)) :
    annihilationSector 𝕜 E (n + 1) f (creationSector 𝕜 E (n + 1) g w) -
      creationSector 𝕜 E n g (annihilationSector 𝕜 E n f w) = inner 𝕜 f g • w := by
  have hw : symmetrizerL 𝕜 E (n + 1) (w : HilbertTensorPower 𝕜 E (n + 1)) =
      (w : HilbertTensorPower 𝕜 E (n + 1)) :=
    (mem_symTensorPower_iff 𝕜 E (n + 1)).mp w.2
  refine Subtype.ext ?_
  rw [Submodule.coe_sub, Submodule.coe_smul, annihilationSector_apply_coe,
    creationSector_apply_coe, creationSector_apply_coe, annihilationSector_apply_coe,
    map_smul, map_smul, map_smul, map_smul, smul_smul, smul_smul,
    ofReal_sqrt_succ_mul_self, ofReal_sqrt_succ_mul_self, ← hw]
  exact ccrL_succ 𝕜 E n f g (w : HilbertTensorPower 𝕜 E (n + 1))

/-- **Sector-level commutation of creations**: the `√` scalars are symmetric in the
two insertions, and the double insertion commutes under the symmetrizer. -/
theorem creationSector_creationSector_comm (f g : E) (ψ : SymTensorPower 𝕜 E n) :
    creationSector 𝕜 E (n + 1) f (creationSector 𝕜 E n g ψ) =
      creationSector 𝕜 E (n + 1) g (creationSector 𝕜 E n f ψ) := by
  refine Subtype.ext ?_
  rw [creationSector_apply_coe, creationSector_apply_coe, creationSector_apply_coe,
    creationSector_apply_coe]
  simp only [map_smul, smul_smul]
  congr 1
  rw [symmetrizerL_insertL_symmetrizerL, symmetrizerL_insertL_symmetrizerL]
  exact symmetrizerL_insertL_insertL_comm 𝕜 E n f g (ψ : HilbertTensorPower 𝕜 E n)

/-! ### The frozen targets -/

/-- **Mutual formal adjointness of `a†(f)` and `a(f)` on `F₀`** — the frozen
slice-2 target `CreationAnnihilationAdjoint` (Reed & Simon II, §X.7:
`a(f) = (a†(f))* |_{F₀}`). The `lp` inner product of finite-particle vectors is a
finite sum of sector pairings; `Finset.sum_range_succ'` shifts it across the sector
offset of `a†(f)`, and each term is the sector adjointness
`inner_creationSector_left`. -/
theorem creationAnnihilationAdjoint : CreationAnnihilationAdjoint 𝕜 E := by
  intro f x y
  obtain ⟨Nx, hNx⟩ := (BosonFock.mem_finiteParticle_iff 𝕜 E).mp x.2
  obtain ⟨Ny, hNy⟩ := (BosonFock.mem_finiteParticle_iff 𝕜 E).mp y.2
  have hM1 : ∀ k ∉ Finset.range (max (Nx + 1) Ny + 1),
      inner 𝕜 ((creationPMap 𝕜 E f x) k) ((y : BosonFock 𝕜 E) k) = 0 := by
    intro k hk
    rw [hNy k (by simp only [Finset.mem_range, not_lt] at hk; omega), inner_zero_right]
  have hM2 : ∀ m ∉ Finset.range (max (Nx + 1) Ny),
      inner 𝕜 ((x : BosonFock 𝕜 E) m) ((annihilationPMap 𝕜 E f y) m) = 0 := by
    intro m hm
    rw [hNx m (by simp only [Finset.mem_range, not_lt] at hm; omega), inner_zero_left]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, tsum_eq_sum hM1, tsum_eq_sum hM2,
    Finset.sum_range_succ',
    show inner 𝕜 ((creationPMap 𝕜 E f x) 0) ((y : BosonFock 𝕜 E) 0) = 0 by
      rw [creationPMap_apply_zero, inner_zero_left],
    add_zero]
  exact Finset.sum_congr rfl fun i _ =>
    inner_creationSector_left 𝕜 E i f ((x : BosonFock 𝕜 E) i) ((y : BosonFock 𝕜 E) (i + 1))

/-- **The canonical commutation relation on `F₀`** — the frozen slice-2 target
`CCROnDomain`: `a(f) a†(g) - a†(g) a(f) = ⟪f, g⟫ • 1` pointwise on the
finite-particle domain (Reed & Simon II, §X.7; Bratteli & Robinson II, §5.2).
Componentwise, sector `0` is `annihilationSector_creationSector_zero` and sector
`k + 1` is `annihilationSector_creationSector_sub`. -/
theorem ccrOnDomain : CCROnDomain 𝕜 E := by
  intro f g x
  refine lp.ext (funext fun m => ?_)
  rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply]
  match m with
  | 0 =>
    rw [show (creationPMap 𝕜 E g
        ⟨annihilationPMap 𝕜 E f x, annihilationPMap_apply_mem_finiteParticle 𝕜 E f x⟩) 0
        = 0 from creationPMap_apply_zero 𝕜 E g _, sub_zero]
    exact annihilationSector_creationSector_zero 𝕜 E f g ((x : BosonFock 𝕜 E) 0)
  | k + 1 =>
    exact annihilationSector_creationSector_sub 𝕜 E k f g ((x : BosonFock 𝕜 E) (k + 1))

/-- **Creation operators commute on `F₀`** — the frozen slice-2 target
`CreationsCommute`: `[a†(f), a†(g)] = 0` (Reed & Simon II, §X.7). Componentwise
from `creationSector_creationSector_comm`; the two lowest sectors vanish. -/
theorem creationsCommute : CreationsCommute 𝕜 E := by
  intro f g x
  refine lp.ext (funext fun k => ?_)
  match k with
  | 0 => rfl
  | 1 =>
    show creationSector 𝕜 E 0 f ((creationPMap 𝕜 E g x) 0) =
      creationSector 𝕜 E 0 g ((creationPMap 𝕜 E f x) 0)
    rw [creationPMap_apply_zero, creationPMap_apply_zero, map_zero, map_zero]
  | k + 2 =>
    exact creationSector_creationSector_comm 𝕜 E k f g ((x : BosonFock 𝕜 E) k)

/-- **Annihilation operators commute on `F₀`** — the frozen slice-2 target
`AnnihilationsCommute`: `[a(f), a(g)] = 0` (Reed & Simon II, §X.7). By duality from
`creationsCommute`: both composites have the same inner products against the dense
finite-particle subspace, via the proven adjointness applied twice. -/
theorem annihilationsCommute : AnnihilationsCommute 𝕜 E := by
  intro f g x
  refine (BosonFock.dense_finiteParticle 𝕜 E).eq_of_inner_left 𝕜 fun v hv => ?_
  have hadjf := (creationAnnihilationAdjoint 𝕜 E f).symm
  have hadjg := (creationAnnihilationAdjoint 𝕜 E g).symm
  have h1 : inner 𝕜 (annihilationPMap 𝕜 E f
        ⟨annihilationPMap 𝕜 E g x, annihilationPMap_apply_mem_finiteParticle 𝕜 E g x⟩) v =
      inner 𝕜 (x : BosonFock 𝕜 E) (creationPMap 𝕜 E g
        ⟨creationPMap 𝕜 E f ⟨v, hv⟩,
          creationPMap_apply_mem_finiteParticle 𝕜 E f ⟨v, hv⟩⟩) :=
    (hadjf ⟨annihilationPMap 𝕜 E g x,
        annihilationPMap_apply_mem_finiteParticle 𝕜 E g x⟩ ⟨v, hv⟩).trans
      (hadjg x ⟨creationPMap 𝕜 E f ⟨v, hv⟩,
        creationPMap_apply_mem_finiteParticle 𝕜 E f ⟨v, hv⟩⟩)
  have h2 : inner 𝕜 (annihilationPMap 𝕜 E g
        ⟨annihilationPMap 𝕜 E f x, annihilationPMap_apply_mem_finiteParticle 𝕜 E f x⟩) v =
      inner 𝕜 (x : BosonFock 𝕜 E) (creationPMap 𝕜 E f
        ⟨creationPMap 𝕜 E g ⟨v, hv⟩,
          creationPMap_apply_mem_finiteParticle 𝕜 E g ⟨v, hv⟩⟩) :=
    (hadjg ⟨annihilationPMap 𝕜 E f x,
        annihilationPMap_apply_mem_finiteParticle 𝕜 E f x⟩ ⟨v, hv⟩).trans
      (hadjf x ⟨creationPMap 𝕜 E g ⟨v, hv⟩,
        creationPMap_apply_mem_finiteParticle 𝕜 E g ⟨v, hv⟩⟩)
  rw [h1, h2]
  exact congrArg (fun t : BosonFock 𝕜 E => inner 𝕜 (x : BosonFock 𝕜 E) t)
    (creationsCommute 𝕜 E g f ⟨v, hv⟩)

/-! ### The Segal field is symmetric

The bridge toward the staged Nelson analytic-vector node for
`SegalFieldEssentiallySelfAdjoint`: a symmetric operator is the entry ticket to the
frozen P2.3a/b essential-self-adjointness layer. -/

/-- **The Segal field is formally self-adjoint on `F₀`**:
`⟪Φ(f) x, y⟫ = ⟪x, Φ(f) y⟫` (Reed & Simon II, §X.7 — the first step of Thm X.41).
Immediate from `creationAnnihilationAdjoint` used in both directions, since the
scalar `(√2)⁻¹` is real. -/
theorem segalField_isFormalAdjoint_self (f : E) :
    (segalField 𝕜 E f).IsFormalAdjoint (segalField 𝕜 E f) := by
  intro x y
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp x.2
  obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.mp y.2
  have h1 : inner 𝕜 ((annihilationPMap 𝕜 E f) ⟨(x : BosonFock 𝕜 E), hx1⟩)
        ((y : BosonFock 𝕜 E)) =
      inner 𝕜 ((x : BosonFock 𝕜 E)) ((creationPMap 𝕜 E f) ⟨(y : BosonFock 𝕜 E), hy2⟩) :=
    (creationAnnihilationAdjoint 𝕜 E f).symm ⟨(x : BosonFock 𝕜 E), hx1⟩
      ⟨(y : BosonFock 𝕜 E), hy2⟩
  have h2 : inner 𝕜 ((creationPMap 𝕜 E f) ⟨(x : BosonFock 𝕜 E), hx2⟩)
        ((y : BosonFock 𝕜 E)) =
      inner 𝕜 ((x : BosonFock 𝕜 E)) ((annihilationPMap 𝕜 E f) ⟨(y : BosonFock 𝕜 E), hy1⟩) :=
    creationAnnihilationAdjoint 𝕜 E f ⟨(x : BosonFock 𝕜 E), hx2⟩
      ⟨(y : BosonFock 𝕜 E), hy1⟩
  show inner 𝕜 (((Real.sqrt 2 : 𝕜))⁻¹ •
      ((annihilationPMap 𝕜 E f) ⟨(x : BosonFock 𝕜 E), hx1⟩ +
        (creationPMap 𝕜 E f) ⟨(x : BosonFock 𝕜 E), hx2⟩)) (y : BosonFock 𝕜 E) =
    inner 𝕜 (x : BosonFock 𝕜 E) (((Real.sqrt 2 : 𝕜))⁻¹ •
      ((annihilationPMap 𝕜 E f) ⟨(y : BosonFock 𝕜 E), hy1⟩ +
        (creationPMap 𝕜 E f) ⟨(y : BosonFock 𝕜 E), hy2⟩))
  rw [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, h1, h2,
    map_inv₀, RCLike.conj_ofReal]
  ring

/-- **The Segal field is a symmetric `LinearPMap`** in the sense of the frozen P2.3a
spec (`OperatorTheory.LinearPMap.IsSymmetric`): the formal self-adjointness of
`segalField_isFormalAdjoint_self` over `ℂ`, where the P2.3a operator layer lives. -/
theorem segalField_isSymmetric (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (f : E) :
    OperatorTheory.LinearPMap.IsSymmetric (segalField ℂ E f) :=
  OperatorTheory.LinearPMap.isSymmetric_iff_isFormalAdjoint.mpr
    (segalField_isFormalAdjoint_self ℂ E f)

/-! ### Regression anchors against the witness layer

The general theorems specialize to the kernel-checked witness identities of
`Atlas/Witnesses/CreationAnnihilation.lean` — same statements, now obtained from the
general proofs instead of sector-by-sector computation. -/

/-- `ccrOnDomain` at `x = Ω` reproduces the witness `ccr_vacuum`. -/
example (f g : E) :
    annihilationPMap 𝕜 E f
        ⟨creationPMap 𝕜 E g
            ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
          creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩ -
      creationPMap 𝕜 E g
        ⟨annihilationPMap 𝕜 E f
            ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
          annihilationPMap_apply_mem_finiteParticle 𝕜 E f _⟩ =
      inner 𝕜 f g • BosonFock.vacuum 𝕜 E :=
  ccrOnDomain 𝕜 E f g ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩

/-- `creationAnnihilationAdjoint` on the anchor vectors reproduces the witness
`inner_creation_vacuum_oneParticle`: `⟪a†(f) Ω, |g⟩⟫ = ⟪Ω, a(f) |g⟩⟫`. -/
example (f g : E) :
    inner 𝕜 ((creationPMap 𝕜 E f
        ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩ : BosonFock 𝕜 E))
        (BosonFock.oneParticle 𝕜 E g) =
      inner 𝕜 (BosonFock.vacuum 𝕜 E)
        ((annihilationPMap 𝕜 E f
          ⟨BosonFock.oneParticle 𝕜 E g,
            BosonFock.oneParticle_mem_finiteParticle 𝕜 E g⟩ : BosonFock 𝕜 E)) :=
  creationAnnihilationAdjoint 𝕜 E f
    ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩
    ⟨BosonFock.oneParticle 𝕜 E g, BosonFock.oneParticle_mem_finiteParticle 𝕜 E g⟩

/-- `ccrOnDomain` at `x = |h⟩` reproduces the witness `ccr_oneParticle`. -/
example (f g h : E) :
    annihilationPMap 𝕜 E f
        ⟨creationPMap 𝕜 E g ⟨BosonFock.oneParticle 𝕜 E h,
            BosonFock.oneParticle_mem_finiteParticle 𝕜 E h⟩,
          creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩ -
      creationPMap 𝕜 E g
        ⟨annihilationPMap 𝕜 E f ⟨BosonFock.oneParticle 𝕜 E h,
            BosonFock.oneParticle_mem_finiteParticle 𝕜 E h⟩,
          annihilationPMap_apply_mem_finiteParticle 𝕜 E f _⟩ =
      inner 𝕜 f g • BosonFock.oneParticle 𝕜 E h :=
  ccrOnDomain 𝕜 E f g
    ⟨BosonFock.oneParticle 𝕜 E h, BosonFock.oneParticle_mem_finiteParticle 𝕜 E h⟩

end QFT
