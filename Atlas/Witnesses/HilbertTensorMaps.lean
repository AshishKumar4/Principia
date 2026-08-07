import Atlas.Proofs.HilbertTensorBasis
import Atlas.Witnesses.HilbertTensorBasic

/-!
# Non-vacuity witnesses for the Hilbert tensor product functoriality (P2.1W)

Concrete models exercising `Atlas/Proofs/HilbertTensorMaps.lean` (node P2.1b) and
`Atlas/Proofs/HilbertTensorBasis.lean` (nodes P2.1c, P2.1d). The scalar and `ℂ²` models,
and the basis vectors `e`, are reused from `Atlas/Witnesses/HilbertTensorBasic.lean`
(node P2.1a) rather than redefined.

* **The action lemmas fire under bare `simp`** (expected-true): `congrₕ`, `commₕ`, `lidₕ`
  and `assocₕ` reduce a pure tensor to a pure tensor with no lemma hints, on `ℂ` and on
  `EuclideanSpace ℂ (Fin 2)`. This is the simp-normal-form design of P2.1b under test:
  the spec's `@[simp] tmulₕ_apply` rewrites a pure tensor to a completion coercion, and
  the `_coe_tmul` lemmas are stated in exactly that form.
* **Values computed through the isometries**: `‖assocₕ ((2 ⊗̂ 3) ⊗̂ 5)‖ = 30` and
  `lidₕ (2 ⊗̂ 3) = 6` — the maps carry the cross norm and the scalar action, and are not
  the zero map.
* **`congrₕ` at a genuinely non-identity pair**: `LinearIsometryEquiv.neg`, whose tensor
  square negates a pure tensor twice, i.e. acts trivially on it, while `congrₕ neg id`
  does not (kernel-checked refutation).
* **`commₕ` is an involution but not the identity** (expected-true round trip plus the
  expected-false `commₕ (e₀ ⊗̂ e₁) ≠ e₀ ⊗̂ e₁`): the symmetry is a nontrivial unitary.
* **`assocₕ` is injective on the models**: a unit pure tensor stays a unit vector, and
  orthogonal triples stay orthogonal.
* **Adjoints (P2.1c)**: `commₕ` is self-adjoint on `ℂ ⊗̂ ℂ`; `congrₕ`'s adjoint is the
  tensor of the inverses.
* **Hilbert bases (P2.1d)**: `ℂ² ⊗̂ ℂ²` gets the basis `eᵢ ⊗̂ eⱼ` indexed by
  `Fin 2 × Fin 2` with the expected coordinates, and the *infinite-dimensional* witness
  `ℓ²(ℕ, ℂ) ⊗̂ ℓ²(ℕ, ℂ) ≃ₗᵢ ℓ²(ℕ × ℕ, ℂ)` — the case where no Hamel-basis argument is
  available and the density argument is doing real work.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I* (1980), §II.4 and
  Theorem II.10.
-/

open OperatorTheory HilbertTensorProduct

open scoped lp

noncomputable section

namespace OperatorTheory.Witnesses

/-! ### The action lemmas fire under bare `simp` -/

/-- `congrₕ` of the identity pair acts as the identity on a pure tensor, by `simp` alone. -/
example : congrₕ (.refl ℂ ℂ) (.refl ℂ ℂ) (tmulₕ ℂ (2 : ℂ) (3 : ℂ)) = tmulₕ ℂ 2 3 := by simp

/-- `commₕ` swaps the factors of a pure tensor on `ℂ² ⊗̂ ℂ²`, by `simp` alone. -/
example : commₕ ℂ (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2))
    (tmulₕ ℂ (e 0) (e 1)) = tmulₕ ℂ (e 1) (e 0) := by simp

/-- `assocₕ` reassociates a pure tensor on `ℂ²`, by `simp` alone. -/
example : assocₕ ℂ (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2))
      (EuclideanSpace ℂ (Fin 2)) (tmulₕ ℂ (tmulₕ ℂ (e 0) (e 1)) (e 0)) =
    tmulₕ ℂ (e 0) (tmulₕ ℂ (e 1) (e 0)) := by simp

/-- `mapIsometryₕ` of the identity pair, by `simp` alone. -/
example : mapIsometryₕ (.id : ℂ →ₗᵢ[ℂ] ℂ) (.id : ℂ →ₗᵢ[ℂ] ℂ) (tmulₕ ℂ (2 : ℂ) (3 : ℂ)) =
    tmulₕ ℂ 2 3 := by simp

/-! ### Values computed through the isometries -/

/-- `‖assocₕ ((2 ⊗̂ 3) ⊗̂ 5)‖ = 2 * 3 * 5 = 30`: the associator carries the cross norm. -/
example : ‖assocₕ ℂ ℂ ℂ ℂ (tmulₕ ℂ (tmulₕ ℂ (2 : ℂ) (3 : ℂ)) (5 : ℂ))‖ = 30 := by
  rw [assocₕ_tmulₕ]
  simp
  norm_num

/-- `lidₕ (2 ⊗̂ 3) = 6`: the left unit isometry is scalar multiplication. -/
example : lidₕ ℂ ℂ (tmulₕ ℂ (2 : ℂ) (3 : ℂ)) = 6 := by
  rw [lidₕ_tmulₕ]
  norm_num

/-- `assocₕ` sends the unit pure tensor to a unit vector, in particular to a nonzero
vector: the associator is not degenerate. -/
example : ‖assocₕ ℂ ℂ ℂ ℂ (tmulₕ ℂ (tmulₕ ℂ (1 : ℂ) (1 : ℂ)) (1 : ℂ))‖ = 1 := by
  rw [assocₕ_tmulₕ]
  simp

example : assocₕ ℂ ℂ ℂ ℂ (tmulₕ ℂ (tmulₕ ℂ (1 : ℂ) (1 : ℂ)) (1 : ℂ)) ≠ 0 := by
  intro h
  have h1 : ‖assocₕ ℂ ℂ ℂ ℂ (tmulₕ ℂ (tmulₕ ℂ (1 : ℂ) (1 : ℂ)) (1 : ℂ))‖ = 1 := by
    rw [assocₕ_tmulₕ]; simp
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- `assocₕ` preserves orthogonality of triples of basis vectors: `e₀ ⊗̂ e₀ ⊗̂ e₀` and
`e₁ ⊗̂ e₁ ⊗̂ e₁` stay orthogonal after reassociation. -/
example :
    inner ℂ
        (assocₕ ℂ (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2))
          (EuclideanSpace ℂ (Fin 2)) (tmulₕ ℂ (tmulₕ ℂ (e 0) (e 0)) (e 0)))
        (assocₕ ℂ (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2))
          (EuclideanSpace ℂ (Fin 2)) (tmulₕ ℂ (tmulₕ ℂ (e 1) (e 1)) (e 1))) = 0 := by
  rw [assocₕ_tmulₕ, assocₕ_tmulₕ]
  simp [e, EuclideanSpace.inner_single_left]

/-! ### `congrₕ` at a genuinely non-identity pair -/

/-- `congrₕ (-1) (-1)` acts trivially on a pure tensor — the two sign changes cancel
inside the tensor, so this is a nontrivial identity, not a triviality. -/
example : congrₕ (LinearIsometryEquiv.neg ℂ (E := ℂ)) (LinearIsometryEquiv.neg ℂ (E := ℂ))
    (tmulₕ ℂ (1 : ℂ) (1 : ℂ)) = tmulₕ ℂ (1 : ℂ) (1 : ℂ) := by
  rw [congrₕ_tmulₕ]
  show tmulₕ ℂ (-1 : ℂ) (-1 : ℂ) = tmulₕ ℂ (1 : ℂ) (1 : ℂ)
  rw [map_neg, map_neg, neg_apply, neg_neg]

/-- **Expected-false**: `congrₕ (-1) id` is *not* the identity on `ℂ ⊗̂ ℂ`; it negates the
unit pure tensor, so pairing both sides against `1 ⊗̂ 1` would give `-1 = 1`. -/
example : congrₕ (LinearIsometryEquiv.neg ℂ (E := ℂ)) (.refl ℂ ℂ) (tmulₕ ℂ (1 : ℂ) (1 : ℂ)) ≠
    tmulₕ ℂ (1 : ℂ) (1 : ℂ) := by
  intro h
  have h1 := congrArg (fun t => inner ℂ (tmulₕ ℂ (1 : ℂ) (1 : ℂ)) t) h
  rw [congrₕ_tmulₕ, inner_tmulₕ, inner_tmulₕ] at h1
  norm_num at h1

/-! ### `commₕ` is an involution, but not the identity -/

/-- Round trip: `commₕ ∘ commₕ = id` on a pure tensor of `ℂ² ⊗̂ ℂ²`. -/
example : commₕ ℂ (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2))
      (commₕ ℂ (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2)) (tmulₕ ℂ (e 0) (e 1))) =
    tmulₕ ℂ (e 0) (e 1) := by simp

/-- **Expected-false**: `commₕ` is not the identity — it maps `e₀ ⊗̂ e₁` to the orthogonal
vector `e₁ ⊗̂ e₀`. Kernel-checked refutation that the symmetry isometry is nontrivial. -/
example : commₕ ℂ (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2))
    (tmulₕ ℂ (e 0) (e 1)) ≠ tmulₕ ℂ (e 0) (e 1) := by
  rw [commₕ_tmulₕ]
  intro h
  have h0 : inner ℂ (tmulₕ ℂ (e 1) (e 0)) (tmulₕ ℂ (e 0) (e 1)) = (0 : ℂ) := by
    simp [e, EuclideanSpace.inner_single_left]
  rw [h] at h0
  simp [e] at h0

/-! ### Adjoints (P2.1c) -/

/-- `commₕ` on `ℂ ⊗̂ ℂ` is self-adjoint: its adjoint is `commₕ` again. -/
example : ContinuousLinearMap.adjoint (commₕ ℂ ℂ ℂ : ℂ ⊗̂[ℂ] ℂ →L[ℂ] ℂ ⊗̂[ℂ] ℂ) =
    (commₕ ℂ ℂ ℂ : ℂ ⊗̂[ℂ] ℂ →L[ℂ] ℂ ⊗̂[ℂ] ℂ) := by simp

/-- The adjoint of `congrₕ (-1) (-1)` is `congrₕ (-1) (-1)`, since `neg` is its own
inverse. -/
example :
    ContinuousLinearMap.adjoint
        (congrₕ (LinearIsometryEquiv.neg ℂ (E := ℂ)) (LinearIsometryEquiv.neg ℂ (E := ℂ)) :
          ℂ ⊗̂[ℂ] ℂ →L[ℂ] ℂ ⊗̂[ℂ] ℂ) =
      (congrₕ (LinearIsometryEquiv.neg ℂ (E := ℂ)) (LinearIsometryEquiv.neg ℂ (E := ℂ)) :
        ℂ ⊗̂[ℂ] ℂ →L[ℂ] ℂ ⊗̂[ℂ] ℂ) := by
  rw [congrₕ_adjoint, LinearIsometryEquiv.symm_neg]

/-! ### Hilbert bases of the tensor product (P2.1d) -/

/-- The standard Hilbert basis of `EuclideanSpace ℂ (Fin 2)`. -/
def hb2 : HilbertBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (EuclideanSpace.basisFun (Fin 2) ℂ).toHilbertBasis

/-- The tensor Hilbert basis of `ℂ² ⊗̂ ℂ²` has the expected vectors `eᵢ ⊗̂ eⱼ`. -/
example : hb2.tensorProductₕ hb2 (0, 1) = tmulₕ ℂ (e 0) (e 1) := by
  rw [HilbertBasis.tensorProductₕ_apply]
  simp [hb2, e]

/-- It is orthonormal — the fence encloses an orthonormal family, not a degenerate one. -/
example : Orthonormal ℂ (hb2.tensorProductₕ hb2) := HilbertBasis.orthonormal _

/-- The `ℓ²` coordinates of a pure tensor factorize, and are nondegenerate:
`⟪e₀ ⊗̂ e₁, ·⟫` picks out the `(0, 1)` coefficient. -/
example : l2Equiv hb2 hb2 (tmulₕ ℂ (e 0) (e 1)) (0, 1) = 1 := by
  rw [l2Equiv_tmulₕ_apply]
  simp [hb2, e]

/-- **Expected-false**: the `(1, 0)` coefficient of `e₀ ⊗̂ e₁` is not `1` (it is `0`) —
the basis genuinely separates the two orderings. -/
example : ¬l2Equiv hb2 hb2 (tmulₕ ℂ (e 0) (e 1)) (1, 0) = 1 := by
  rw [l2Equiv_tmulₕ_apply]
  simp [hb2, e, EuclideanSpace.inner_single_left]

/-- **The infinite-dimensional witness**: `ℓ²(ℕ) ⊗̂ ℓ²(ℕ) ≃ₗᵢ ℓ²(ℕ × ℕ)`. No Hamel basis
of the algebraic tensor product is available here; this is the case the density argument
of `dense_span_tmulₕ_of_dense_span` exists for. -/
example : ℓ²(ℕ, ℂ) ⊗̂[ℂ] ℓ²(ℕ, ℂ) ≃ₗᵢ[ℂ] ℓ²(ℕ × ℕ, ℂ) := l2Equiv default default

/-- Its basis vectors are the pure tensors of the standard `ℓ²` basis vectors. -/
example (i j : ℕ) :
    (default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ)).tensorProductₕ default (i, j) =
      tmulₕ ℂ (lp.single (E := fun _ : ℕ => ℂ) 2 i 1)
        (lp.single (E := fun _ : ℕ => ℂ) 2 j 1) := by
  rw [HilbertBasis.tensorProductₕ_apply, ← HilbertBasis.repr_symm_single,
    ← HilbertBasis.repr_symm_single]
  rfl

end OperatorTheory.Witnesses
