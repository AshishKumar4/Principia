import Atlas.Proofs.PiTensorInner

/-!
# Witnesses — inner product on finite tensor products (P2.1f)

Non-vacuity witnesses for `Atlas/Proofs/PiTensorInner.lean` on the concrete model
`⨂[ℂ] (_ : Fin 2), ℂ`: inner-product computations, the pure-tensor norm formula, an
expected-false conjugation guard, and the reindex isometry under a transposition.
-/

open scoped TensorProduct
open PiTensorProduct
open scoped PiTensorProduct.InnerNorm

namespace Atlas.Witnesses.PiTensorInner

/-- Expected-true: the instance inner product multiplies slotwise inner products,
`⟪1 ⊗ 1, I ⊗ I⟫ = I * I = -1`. -/
example :
    inner ℂ (tprod ℂ fun _ : Fin 2 ↦ (1 : ℂ)) (tprod ℂ fun _ : Fin 2 ↦ Complex.I) = -1 := by
  simp [RCLike.inner_apply]

/-- Expected-false guard: the first slot is conjugated, so
`⟪I ⊗ I, 1 ⊗ 1⟫ = conj I * conj I = -1 ≠ 1`. -/
example :
    inner ℂ (tprod ℂ fun _ : Fin 2 ↦ Complex.I) (tprod ℂ fun _ : Fin 2 ↦ (1 : ℂ)) ≠ 1 := by
  simp [RCLike.inner_apply, Complex.conj_I]
  norm_num

/-- The norm of a pure tensor is the product of the slot norms: `‖2 ⊗ 2‖ = 4`. -/
example : ‖tprod ℂ fun _ : Fin 2 ↦ (2 : ℂ)‖ = 4 := by
  rw [norm_tprod]
  norm_num

/-- Non-vacuity of definiteness: the pure tensor of ones is nonzero because its norm
is `1`. -/
example : tprod ℂ (fun _ : Fin 2 ↦ (1 : ℂ)) ≠ 0 := by
  intro h
  have h1 : ‖tprod ℂ fun _ : Fin 2 ↦ (1 : ℂ)‖ = 1 := by rw [norm_tprod]; norm_num
  rw [h, norm_zero] at h1
  norm_num at h1

/-- The reindex isometry along the transposition of `Fin 2` swaps the slots of a pure
tensor. -/
example :
    reindexIsometry ℂ (fun _ : Fin 2 ↦ ℂ) (Equiv.swap 0 1) (tprod ℂ ![1, Complex.I]) =
      tprod ℂ ![Complex.I, 1] := by
  rw [reindexIsometry_tprod]
  congr 1
  funext i
  fin_cases i <;> simp

/-- Reindexing along the transposition preserves the norm — the isometry property on a
concrete non-symmetric tensor, `‖I ⊗ 2‖ = 2` either way around. -/
example :
    ‖reindexIsometry ℂ (fun _ : Fin 2 ↦ ℂ) (Equiv.swap 0 1) (tprod ℂ ![Complex.I, 2])‖ =
      ‖tprod ℂ ![Complex.I, 2]‖ :=
  (reindexIsometry ℂ (fun _ : Fin 2 ↦ ℂ) (Equiv.swap 0 1)).norm_map _

/-- The concrete value of that norm: `‖I ⊗ 2‖ = ‖I‖ * ‖2‖ = 2`. -/
example : ‖tprod ℂ ![Complex.I, 2]‖ = 2 := by
  rw [norm_tprod, Fin.prod_univ_two]
  simp

/-- The transposition preserves the inner product on non-pure elements as well:
`⟪u + v, u + v⟫` is invariant under `reindex`. -/
example
    (u v : ⨂[ℂ] _ : Fin 2, ℂ) :
    inner ℂ (reindex ℂ (fun _ : Fin 2 ↦ ℂ) (Equiv.swap 0 1) (u + v))
        (reindex ℂ (fun _ : Fin 2 ↦ ℂ) (Equiv.swap 0 1) (u + v)) =
      inner ℂ (u + v) (u + v) :=
  inner_reindex_reindex _ _ _

end Atlas.Witnesses.PiTensorInner
