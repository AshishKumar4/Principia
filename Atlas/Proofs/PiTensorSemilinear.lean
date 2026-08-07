import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.PiTensorProduct

/-!
# P2.1e — sesquilinear pairing on finite tensor products of inner product spaces

Blueprint node P2.1e. Mathlib's `PiTensorProduct.lift` is linear-only, while the inner
product `⟪⨂ₜ x, ⨂ₜ y⟫ = ∏ i, ⟪x i, y i⟫` is *conjugate*-multilinear in the first slot, so
it cannot be obtained from `lift` directly — this was flagged as the one uncertain
implementation point of the P2.1 design. This file closes the gap without any new
semilinear `PiTensorProduct` machinery:

Because the pairing takes values in the scalar field, where `starRingEnd 𝕜` lives, a
conjugate-multilinear map into `𝕜` is exactly `conj ∘ (honest multilinear map)`. Moreover
the space `(⨂[𝕜] i, E i) →ₛₗ[starRingEnd 𝕜] 𝕜` of conjugate-linear functionals is itself
a `𝕜`-module (scalars act on the codomain), and

`x ↦ (z ↦ conj (lift (y ↦ ∏ i, ⟪x i, y i⟫) z))`

is genuinely `𝕜`-multilinear in `x` *into that module*: scaling `x i` by `c` scales the
inner functional by `conj c`, and the outer `conj` flips it back to `c`. Two applications
of the existing linear `PiTensorProduct.lift` plus `LinearMap.flip` (which is already
fully semilinear in Mathlib) therefore produce the bundled pairing

`innerAux 𝕜 : (⨂[𝕜] i, E i) →ₛₗ[starRingEnd 𝕜] (⨂[𝕜] i, E i) →ₗ[𝕜] 𝕜`

in the same shape as Mathlib's `innerₛₗ`, together with the defining formula
`innerAux_tprod`. This mirrors, at the `Pi` level, how
`Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` (Omar, #27228) builds the binary
inner product from the semilinear binary `map (innerₛₗ 𝕜) (innerₛₗ 𝕜)` — the semilinear
binary `map` being exactly what `PiTensorProduct` lacks and what the `conj`-twisted
codomain trick replaces.

## Main definitions

* `PiTensorProduct.innerAux`: the sesquilinear pairing, conjugate-linear in the first
  argument and linear in the second.
* `PiTensorProduct.innerAux_tprod`: `innerAux 𝕜 (⨂ₜ x) (⨂ₜ y) = ∏ i, ⟪x i, y i⟫`.
* `PiTensorProduct.innerAux_conj_symm`: Hermitian symmetry of the pairing.
* `PiTensorProduct.innerAux_map_map`: invariance under componentwise linear isometries
  (in particular under `mapIncl` into finite-dimensional submodules).

## Consumption by P2.1f

Positivity and definiteness (the Gram argument) are node P2.1f, not this one. P2.1f can
set `Inner 𝕜 (⨂[𝕜] i, E i) := ⟨fun x y ↦ innerAux 𝕜 x y⟩` and build
`InnerProductSpace.Core` with: `conj_inner_symm := innerAux_conj_symm`;
`add_left`/`smul_left` free from the bundled semilinearity (`LinearMap.map_add₂`,
`LinearMap.map_smulₛₗ₂`, exactly as in the binary file); and definiteness by reducing to
finitely generated (hence finite-dimensional) submodules via `innerAux_map_map` applied to
`fun i ↦ (p i).subtypeₗᵢ`, then an orthonormal-basis Gram computation there.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised and enlarged edition (1980), §II.4: the inner product on finite tensor products
  of Hilbert spaces, `⟪φ₁ ⊗ ⋯ ⊗ φₙ, ψ₁ ⊗ ⋯ ⊗ ψₙ⟫ = ∏ₖ ⟪φₖ, ψₖ⟫`, is well defined
  (Proposition preceding Theorem II.10).
* M. Omar, Mathlib PR #27228, `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean`:
  the binary construction this file extends to finite families.
-/

open Function
open scoped TensorProduct ComplexConjugate

namespace PiTensorProduct

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
variable {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]

/-- For a fixed family `x`, the multilinear functional `y ↦ ∏ i, ⟪x i, y i⟫`. This is the
"second slot" of the pairing, where the inner product is honestly linear. -/
private def innerAuxRight (x : Π i, E i) : MultilinearMap 𝕜 E 𝕜 :=
  (MultilinearMap.mkPiAlgebra 𝕜 ι 𝕜).compLinearMap fun i ↦ innerₛₗ 𝕜 (x i)

private lemma innerAuxRight_apply (x y : Π i, E i) :
    innerAuxRight (𝕜 := 𝕜) x y = ∏ i, inner 𝕜 (x i) (y i) := by
  simp [innerAuxRight, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    innerₛₗ_apply_apply]

private lemma innerAuxRight_update_apply [DecidableEq ι] (x : Π i, E i) (i : ι) (a : E i)
    (y : Π i, E i) :
    innerAuxRight (𝕜 := 𝕜) (update x i a) y =
      inner 𝕜 a (y i) * ∏ j ∈ Finset.univ \ {i}, inner 𝕜 (x j) (y j) := by
  have h : ∀ j, inner 𝕜 (update x i a j) (y j) =
      update (fun j ↦ inner 𝕜 (x j) (y j)) i (inner 𝕜 a (y i)) j :=
    apply_update (fun j e ↦ inner 𝕜 e (y j)) x i a
  rw [innerAuxRight_apply, Finset.prod_congr rfl fun j _ ↦ h j,
    Finset.prod_update_of_mem (Finset.mem_univ i)]

/-- `innerAuxRight` is conjugate-multilinear in `x`: additivity in each slot. -/
private lemma innerAuxRight_update_add [DecidableEq ι] (x : Π i, E i) (i : ι) (a b : E i) :
    innerAuxRight (𝕜 := 𝕜) (update x i (a + b)) =
      innerAuxRight (update x i a) + innerAuxRight (update x i b) := by
  ext y
  simp only [MultilinearMap.add_apply, innerAuxRight_update_apply, inner_add_left, add_mul]

/-- `innerAuxRight` is conjugate-multilinear in `x`: scaling a slot by `c` scales the
functional by `conj c`. -/
private lemma innerAuxRight_update_smul [DecidableEq ι] (x : Π i, E i) (i : ι) (c : 𝕜)
    (a : E i) :
    innerAuxRight (𝕜 := 𝕜) (update x i (c • a)) = conj c • innerAuxRight (update x i a) := by
  ext y
  simp only [MultilinearMap.smul_apply, innerAuxRight_update_apply, inner_smul_left,
    smul_eq_mul, mul_assoc]

/-- The key object: `x ↦ conj ∘ lift (innerAuxRight x)` is an honest `𝕜`-multilinear map
into the `𝕜`-module of conjugate-linear functionals on `⨂[𝕜] i, E i`. The outer `conj`
cancels the conjugate-multilinearity of `innerAuxRight` in `x`. -/
private def innerAuxLeft : MultilinearMap 𝕜 E ((⨂[𝕜] i, E i) →ₛₗ[starRingEnd 𝕜] 𝕜) where
  toFun x := (starRingEnd 𝕜).toSemilinearMap.comp (lift (innerAuxRight x))
  map_update_add' x i a b := by
    ext z
    simp only [LinearMap.comp_apply, RingHom.coe_toSemilinearMap, LinearMap.add_apply,
      innerAuxRight_update_add, map_add]
  map_update_smul' x i c a := by
    ext z
    simp only [LinearMap.comp_apply, RingHom.coe_toSemilinearMap, LinearMap.smul_apply,
      innerAuxRight_update_smul, map_smul, smul_eq_mul, map_mul, RCLike.conj_conj]

private lemma innerAuxLeft_apply (x : Π i, E i) (z : ⨂[𝕜] i, E i) :
    innerAuxLeft (𝕜 := 𝕜) x z = conj (lift (innerAuxRight x) z) :=
  rfl

variable (𝕜) in
/-- The sesquilinear pairing on a finite tensor product of inner product spaces,
conjugate-linear in the first argument and linear in the second, with
`innerAux 𝕜 (⨂ₜ x) (⨂ₜ y) = ∏ i, ⟪x i, y i⟫` (`innerAux_tprod`).

This is the `PiTensorProduct` counterpart of `innerₛₗ`; positivity and definiteness (and
hence the `InnerProductSpace` instance) are established downstream (blueprint P2.1f). -/
def innerAux : (⨂[𝕜] i, E i) →ₛₗ[starRingEnd 𝕜] (⨂[𝕜] i, E i) →ₗ[𝕜] 𝕜 :=
  (lift innerAuxLeft).flip

@[simp] theorem innerAux_tprod (x y : Π i, E i) :
    innerAux 𝕜 (tprod 𝕜 x) (tprod 𝕜 y) = ∏ i, inner 𝕜 (x i) (y i) := by
  simp only [innerAux, LinearMap.flip_apply, lift.tprod, innerAuxLeft_apply,
    innerAuxRight_apply, map_prod, inner_conj_symm]

/-- Hermitian symmetry of the pairing; `conj_inner_symm` for the P2.1f core structure. -/
theorem innerAux_conj_symm (u v : ⨂[𝕜] i, E i) :
    conj (innerAux 𝕜 u v) = innerAux 𝕜 v u := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    induction v using PiTensorProduct.induction_on with
    | smul_tprod d y =>
      simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, map_mul,
        map_prod, RCLike.conj_conj, innerAux_tprod, inner_conj_symm]
      ring
    | add v₁ v₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | add u₁ u₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

/-- The pairing is preserved by componentwise linear isometries. Applied to
`fun i ↦ (p i).subtypeₗᵢ` this reduces definiteness on `⨂[𝕜] i, E i` to finitely
generated submodules — the P2.1f Gram argument, exactly as in the binary
`TensorProduct.inner_map_map`. -/
theorem innerAux_map_map (f : Π i, E i →ₗᵢ[𝕜] F i) (u v : ⨂[𝕜] i, E i) :
    innerAux 𝕜 (map (fun i ↦ (f i).toLinearMap) u) (map (fun i ↦ (f i).toLinearMap) v) =
      innerAux 𝕜 u v := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    induction v using PiTensorProduct.induction_on with
    | smul_tprod d y =>
      simp [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        LinearIsometry.inner_map_map]
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | add u₁ u₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

section Examples

/-- Expected-true: on `⨂ (_ : Fin 2), ℂ` the pairing multiplies slotwise inner products:
`⟪1 ⊗ 1, I ⊗ I⟫ = I * I = -1`. -/
example :
    innerAux ℂ (tprod ℂ fun _ : Fin 2 ↦ (1 : ℂ)) (tprod ℂ fun _ : Fin 2 ↦ Complex.I) =
      -1 := by
  simp [RCLike.inner_apply]

/-- Expected-false guard: conjugation of the *first* slot is real —
`⟪I ⊗ I, 1 ⊗ 1⟫ = conj I * conj I = -1`, not `I * I`-without-conjugation's naive `1`. -/
example :
    innerAux ℂ (tprod ℂ fun _ : Fin 2 ↦ Complex.I) (tprod ℂ fun _ : Fin 2 ↦ (1 : ℂ)) ≠
      1 := by
  simp [RCLike.inner_apply, Complex.conj_I]
  norm_num

end Examples

end PiTensorProduct
