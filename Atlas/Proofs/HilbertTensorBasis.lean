import Atlas.Proofs.HilbertTensorMaps
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# P2.1c/P2.1d — Hilbert bases and adjoints on the completed Hilbert tensor product

Blueprint nodes P2.1c and P2.1d, layered over the frozen spec
`Atlas/Specs/OperatorTheory/HilbertTensor.lean` (P2.1a) and the functoriality file
`Atlas/Proofs/HilbertTensorMaps.lean` (P2.1b), neither of which this file modifies.

## Contents

Density (`OperatorTheory.HilbertTensorProduct`, upstreamable as stated):

* `dense_span_tmulₕ_of_dense_span`: if `s ⊆ E` and `t ⊆ F` have dense spans, then the span
  of `{tmulₕ 𝕜 x y | x ∈ s, y ∈ t}` is dense in `E ⊗̂[𝕜] F`.

Orthonormality and bases:

* `Orthonormal.tmulₕ`: pure tensors of two orthonormal families form an orthonormal family
  indexed by the product — the completion-level counterpart of Mathlib's
  `Orthonormal.tmul`.
* `HilbertBasis.tensorProductₕ`: **the Hilbert basis of `E ⊗̂[𝕜] F` attached to Hilbert
  bases of `E` and `F`**, with vectors `tmulₕ 𝕜 (b₁ i) (b₂ j)` (`tensorProductₕ_apply`).
  Reed & Simon I, §II.4 Theorem II.10.
* `l2Equiv`: the resulting unitary `E ⊗̂[𝕜] F ≃ₗᵢ[𝕜] ℓ²(ι₁ × ι₂, 𝕜)`, with the
  coefficient formula `l2Equiv_tmulₕ_apply`.

Adjoints (P2.1c):

* `congrₕ_adjoint`, `commₕ_adjoint`: the monoidal isometries of P2.1b are unitaries, and
  the adjoint of a tensor of unitaries is the tensor of their adjoints.

## The density argument

The hard half of `HilbertBasis.tensorProductₕ` is totality: `Basis.tensorProduct` is
unavailable, because a `HilbertBasis` is not a Hamel basis — its span is merely dense, so
the family `tmulₕ 𝕜 (b₁ i) (b₂ j)` does *not* span the algebraic tensor product, let alone
the completion. What is proved instead, in `dense_span_tmulₕ_of_dense_span`, is that the
closed span `T` of the family already contains every pure tensor, in two steps, each a
"closed submodule containing a dense-span set is everything" argument transported along a
*continuous* map:

1. Fix `x ∈ s`. The preimage `T.comap (tmulₕ 𝕜 x)` is a closed submodule of `F`
   (continuity of `tmulₕ 𝕜 x`) containing `t`, hence contains the closure of `span 𝕜 t`,
   which is `⊤`. So `tmulₕ 𝕜 x y ∈ T` for *every* `y : F`, not only for `y ∈ t`.
2. Fix `y : F`. By step 1 the closed submodule `T.comap ((tmulₕ 𝕜).flip y)` of `E`
   contains `s`, hence is `⊤`. So `tmulₕ 𝕜 x y ∈ T` for every `x : E` and `y : F`.

Then `span 𝕜 {tmulₕ 𝕜 x y} ≤ T`, and the spec's `dense_span_tmulₕ` makes the smaller set
dense, so `T` is dense. Continuity of `tmulₕ` is what carries density across the two
completions; no summability or `HasSum` manipulation is needed.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised and enlarged edition (1980), §II.4, Theorem II.10: if `{φₖ}` and `{ψₗ}` are
  orthonormal bases of `H₁` and `H₂`, then `{φₖ ⊗ ψₗ}` is an orthonormal basis of
  `H₁ ⊗ H₂`.
* J. Weidmann, *Linear Operators in Hilbert Spaces*, GTM 68 (1980), §3.4.
* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*
  (1983), §2.6 (unitary implementation on the Hilbert tensor product).
-/

noncomputable section

open scoped TensorProduct lp

namespace OperatorTheory.HilbertTensorProduct

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ### Density of spans of pure tensors -/

/-- **Tensoring dense-span sets gives a dense span**: if the spans of `s : Set E` and
`t : Set F` are dense, then the span of the pure tensors `tmulₕ 𝕜 x y` with `x ∈ s`,
`y ∈ t` is dense in `E ⊗̂[𝕜] F`.

Both steps below say "a closed submodule containing a set of dense span is `⊤`", applied
to the preimage of the closed span of the pure tensors under a continuous partial
application of `tmulₕ`. -/
theorem dense_span_tmulₕ_of_dense_span {s : Set E} {t : Set F}
    (hs : Dense (Submodule.span 𝕜 s : Set E)) (ht : Dense (Submodule.span 𝕜 t : Set F)) :
    Dense (Submodule.span 𝕜 (Set.image2 (fun x y => tmulₕ 𝕜 x y) s t) :
      Set (E ⊗̂[𝕜] F)) := by
  set T := (Submodule.span 𝕜 (Set.image2 (fun x y => tmulₕ 𝕜 x y) s t)).topologicalClosure
  have hTclosed : IsClosed (T : Set (E ⊗̂[𝕜] F)) := Submodule.isClosed_topologicalClosure _
  have step₁ : ∀ x ∈ s, ∀ y : F, tmulₕ 𝕜 x y ∈ T := by
    intro x hx
    have hcomap : (⊤ : Submodule 𝕜 F) ≤ T.comap (tmulₕ 𝕜 x : F →L[𝕜] E ⊗̂[𝕜] F).toLinearMap := by
      rw [← Submodule.dense_iff_topologicalClosure_eq_top.mp ht]
      refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr fun y hy => ?_)
        (hTclosed.preimage (tmulₕ 𝕜 x).continuous)
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x, hx, y, hy, rfl⟩)
    exact fun y => hcomap (Submodule.mem_top (x := y))
  have step₂ : ∀ (x : E) (y : F), tmulₕ 𝕜 x y ∈ T := by
    intro x y
    have hcomap : (⊤ : Submodule 𝕜 E) ≤
        T.comap ((tmulₕ 𝕜).flip y : E →L[𝕜] E ⊗̂[𝕜] F).toLinearMap := by
      rw [← Submodule.dense_iff_topologicalClosure_eq_top.mp hs]
      exact Submodule.topologicalClosure_minimal _
        (Submodule.span_le.mpr fun x' hx' => step₁ x' hx' y)
        (hTclosed.preimage ((tmulₕ 𝕜).flip y).continuous)
    exact hcomap (Submodule.mem_top (x := x))
  rw [← dense_closure, ← Submodule.topologicalClosure_coe]
  refine (dense_span_tmulₕ 𝕜).mono (SetLike.coe_subset_coe.mpr ?_)
  exact Submodule.span_le.mpr (by rintro _ ⟨x, y, rfl⟩; exact step₂ x y)

/-! ### Orthonormal families and Hilbert bases -/

variable {ι₁ ι₂ : Type*}

/-- **Pure tensors of orthonormal families are orthonormal**: the completion-level
counterpart of Mathlib's `Orthonormal.tmul`, via the spec's `inner_tmulₕ`. -/
theorem _root_.Orthonormal.tmulₕ {v₁ : ι₁ → E} {v₂ : ι₂ → F}
    (h₁ : Orthonormal 𝕜 v₁) (h₂ : Orthonormal 𝕜 v₂) :
    Orthonormal 𝕜 fun i : ι₁ × ι₂ => tmulₕ 𝕜 (v₁ i.1) (v₂ i.2) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [orthonormal_iff_ite.mp, h₁, h₂, ← ite_and, Prod.ext_iff, and_comm]

/-- **The Hilbert basis of `E ⊗̂[𝕜] F` built from Hilbert bases of the factors**
(Reed & Simon I, §II.4, Theorem II.10): its vectors are the pure tensors
`tmulₕ 𝕜 (b₁ i) (b₂ j)`, indexed by `ι₁ × ι₂`.

The `ₕ` suffix marks the completed tensor product, matching `tmulₕ`, `congrₕ`, `assocₕ`;
there is no algebraic counterpart, since `E ⊗[𝕜] F` is not complete in general. -/
def _root_.HilbertBasis.tensorProductₕ (b₁ : HilbertBasis ι₁ 𝕜 E) (b₂ : HilbertBasis ι₂ 𝕜 F) :
    HilbertBasis (ι₁ × ι₂) 𝕜 (E ⊗̂[𝕜] F) :=
  HilbertBasis.mk (b₁.orthonormal.tmulₕ b₂.orthonormal) <| by
    have hrange : (Set.range fun i : ι₁ × ι₂ => tmulₕ 𝕜 (b₁ i.1) (b₂ i.2)) =
        Set.image2 (fun x y => tmulₕ 𝕜 x y) (Set.range b₁) (Set.range b₂) :=
      (Set.image2_range (fun x y => tmulₕ 𝕜 x y) (b₁ : ι₁ → E) (b₂ : ι₂ → F)).symm
    rw [top_le_iff, hrange, ← Submodule.dense_iff_topologicalClosure_eq_top]
    exact dense_span_tmulₕ_of_dense_span
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr b₁.dense_span)
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr b₂.dense_span)

@[simp]
theorem _root_.HilbertBasis.tensorProductₕ_apply (b₁ : HilbertBasis ι₁ 𝕜 E)
    (b₂ : HilbertBasis ι₂ 𝕜 F) (i : ι₁) (j : ι₂) :
    b₁.tensorProductₕ b₂ (i, j) = tmulₕ 𝕜 (b₁ i) (b₂ j) := by
  rw [HilbertBasis.tensorProductₕ, HilbertBasis.coe_mk]

/-- **The Hilbert tensor product is `ℓ²(ι₁ × ι₂)`** once Hilbert bases of the factors are
chosen: the unitary `E ⊗̂[𝕜] F ≃ₗᵢ[𝕜] ℓ²(ι₁ × ι₂, 𝕜)` given by the coordinates in the
pure-tensor Hilbert basis (Reed & Simon I, §II.4, Theorem II.10). -/
def l2Equiv (b₁ : HilbertBasis ι₁ 𝕜 E) (b₂ : HilbertBasis ι₂ 𝕜 F) :
    E ⊗̂[𝕜] F ≃ₗᵢ[𝕜] ℓ²(ι₁ × ι₂, 𝕜) :=
  (b₁.tensorProductₕ b₂).repr

/-- The coordinates of a pure tensor factorize: the `(i, j)` coefficient of
`tmulₕ 𝕜 x y` is `⟪b₁ i, x⟫ * ⟪b₂ j, y⟫`. -/
@[simp]
theorem l2Equiv_tmulₕ_apply (b₁ : HilbertBasis ι₁ 𝕜 E) (b₂ : HilbertBasis ι₂ 𝕜 F)
    (x : E) (y : F) (i : ι₁) (j : ι₂) :
    l2Equiv b₁ b₂ (tmulₕ 𝕜 x y) (i, j) = inner 𝕜 (b₁ i) x * inner 𝕜 (b₂ j) y := by
  rw [l2Equiv, HilbertBasis.repr_apply_apply, HilbertBasis.tensorProductₕ_apply, inner_tmulₕ]

/-! ### Adjoints: the monoidal isometries are unitaries

Every Hilbert tensor product is complete by construction, so `ContinuousLinearMap.adjoint`
applies to the P2.1b isometries with no completeness hypothesis at all — `lidₕ` carries the
one it already needs. Mathlib's `LinearIsometryEquiv.adjoint_eq_symm` then reduces each
adjoint to the inverse isometry; what the two lemmas below add is the identification of that
inverse with a map of the *same* family, which is the content of "the adjoint of a tensor of
unitaries is the tensor of the adjoints" (Kadison & Ringrose §2.6). For `lidₕ` and `assocₕ`
there is no such second name — their inverses are `lidₕ.symm` and `assocₕ.symm` — so
`LinearIsometryEquiv.adjoint_eq_symm` is already the whole statement and is used directly.

Neither lemma is `@[simp]`: `LinearIsometryEquiv.adjoint_eq_symm` is itself `@[simp]` with an
overlapping left-hand side, and two competing simp lemmas would make the normal form of
`adjoint ↑(congrₕ f g)` depend on which files are imported. -/

theorem congrₕ_adjoint (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    ContinuousLinearMap.adjoint (congrₕ f g : E ⊗̂[𝕜] F →L[𝕜] G ⊗̂[𝕜] H) =
      (congrₕ f.symm g.symm : G ⊗̂[𝕜] H →L[𝕜] E ⊗̂[𝕜] F) := by
  rw [LinearIsometryEquiv.adjoint_eq_symm, congrₕ_symm]

variable (𝕜 E F) in
theorem commₕ_adjoint :
    ContinuousLinearMap.adjoint (commₕ 𝕜 E F : E ⊗̂[𝕜] F →L[𝕜] F ⊗̂[𝕜] E) =
      (commₕ 𝕜 F E : F ⊗̂[𝕜] E →L[𝕜] E ⊗̂[𝕜] F) := by
  rw [LinearIsometryEquiv.adjoint_eq_symm, commₕ_symm]

end OperatorTheory.HilbertTensorProduct
