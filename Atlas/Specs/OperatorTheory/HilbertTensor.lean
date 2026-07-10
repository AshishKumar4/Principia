import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# P2.1a — The completed Hilbert tensor product

Frozen spec (blueprint node P2.1a): proof sessions must not edit this file; changes
require a spec review and a `[spec-review]` commit (see CLAUDE.md).

## Contents

* `HilbertTensorProduct 𝕜 E F` (scoped notation `E ⊗̂[𝕜] F`): the completed tensor
  product of two inner-product spaces, defined as the `UniformSpace.Completion` of the
  algebraic tensor product `E ⊗[𝕜] F` carrying Mathlib's cross inner product
  `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`. For complete `E`, `F` this is *the* Hilbert
  tensor product of the sources. Non-vacuity of the definition-by-`abbrev` is pinned
  by the `inferInstance` examples: `E ⊗̂[𝕜] F` is transparently a complete inner
  product space, i.e. a Hilbert space.
* `HilbertTensorProduct.tmulₕ 𝕜 : E →L[𝕜] F →L[𝕜] E ⊗̂[𝕜] F`: the canonical bounded
  bilinear map, sending `(x, y)` to the image of `x ⊗ₜ y` in the completion, with the
  definitional pin `tmulₕ_apply`.
* `HilbertTensorProduct.inner_tmulₕ` and `HilbertTensorProduct.norm_tmulₕ`: the
  characteristic identities `⟪tmulₕ 𝕜 x y, tmulₕ 𝕜 x' y'⟫ = ⟪x, x'⟫ * ⟪y, y'⟫` and
  `‖tmulₕ 𝕜 x y‖ = ‖x‖ * ‖y‖` — the defining property of the Hilbert tensor product
  in the sources, transferred through the completion coercion.
* `HilbertTensorProduct.dense_span_tmulₕ`: the span of the pure tensors `tmulₕ 𝕜 x y`
  is dense in `E ⊗̂[𝕜] F` — the totality clause of the construction.

## Conventions

* **`abbrev`, not `def`.** `HilbertTensorProduct` is a reducible synonym for
  `UniformSpace.Completion (E ⊗[𝕜] F)`, so every instance on completions of inner
  product spaces (`UniformSpace.Completion.instNormedAddCommGroup`,
  `UniformSpace.Completion.innerProductSpace`, `UniformSpace.Completion.completeSpace`)
  applies to `E ⊗̂[𝕜] F` with no copied instances and no drift. The `inferInstance`
  examples following the definition are frozen alongside it: they are the kernel-checked
  evidence that this transparency actually holds, and a change that breaks them is a
  spec change. The cost of `abbrev` is that `E ⊗̂[𝕜] F` and
  `UniformSpace.Completion (E ⊗[𝕜] F)` display interchangeably in goals; we accept
  this for instance transparency.
* **Generality `RCLike 𝕜`.** Mathlib's inner-product layer on `E ⊗[𝕜] F`
  (`Mathlib/Analysis/InnerProductSpace/TensorProduct.lean`) and on completions
  (`Mathlib/Analysis/InnerProductSpace/Completion.lean`) are both stated over
  `RCLike 𝕜`, so the whole file is; physics consumers instantiate `𝕜 = ℂ`.
* **Relation to the sources' construction.** Reed & Simon (I, §II.4) build the Hilbert
  tensor product as the completion of the *pre-Hilbert* span of formal pure tensors
  with `⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫⟪b, d⟫` extended sesquilinearly; Weidmann (§3.4) and
  Kadison & Ringrose (§2.6) do the same. Mathlib's algebraic `E ⊗[𝕜] F` with the
  cross inner product *is* that pre-Hilbert space (the inner product is definite —
  `TensorProduct.instNormedAddCommGroup` — which is RS's Proposition in §II.4 that
  the form is well defined and positive definite), so its uniform completion is the
  textbook object. No completeness of `E` or `F` is required for the definition, and
  none is assumed here.
* **`E` and `F` are not embedded in `E ⊗̂[𝕜] F`**; only the bilinear `tmulₕ` is
  canonical. `tmulₕ` is built by `LinearMap.mkContinuous₂` from the algebraic
  `TensorProduct.mk` composed with the completion coercion, with bound `1` from
  `‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖` (`TensorProduct.norm_tmul`). Its operator norm (equal to `1`
  for nontrivial `E`, `F`) and all mapping functoriality (`mapₕ`, `congrₕ`,
  associativity/commutativity/unit laws) are blueprint node P2.1b, not part of this
  spec.
* **Density spelling.** `dense_span_tmulₕ` states `Dense` of the coerced submodule
  `Submodule.span 𝕜 {t | ∃ x y, tmulₕ 𝕜 x y = t}`, mirroring the set-builder spelling
  of Mathlib's `TensorProduct.span_tmul_eq_top`. This is the sources' assertion that
  finite sums of pure tensors are dense (Reed & Simon I §II.4; Weidmann §3.4:
  "the linear hull of pure tensors is dense by construction").
* **Namespace.** The type and notation live in `OperatorTheory` (parallel to the P2.3
  specs); the API lives in `OperatorTheory.HilbertTensorProduct`. On upstreaming the
  type would move to root level alongside `TensorProduct`. The notation `⊗̂` is scoped
  to `OperatorTheory`; it does not collide with anything in Mathlib at our pin.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised and enlarged edition (1980), §II.4: definition of the tensor product of
  Hilbert spaces as the completion of the pre-Hilbert space of finite sums of pure
  tensors under `⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫⟪b, d⟫`.
* J. Weidmann, *Linear Operators in Hilbert Spaces*, GTM 68 (1980), §3.4 (tensor
  products of Hilbert spaces). Section-level citation.
* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*
  (1983), §2.6 (the Hilbert tensor product, unitary implementation of the universal
  property). Section-level citation.
-/

noncomputable section

namespace OperatorTheory

open scoped TensorProduct

variable (𝕜 E F : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The *Hilbert tensor product* `E ⊗̂[𝕜] F` of two inner-product spaces over
`𝕜 = ℝ, ℂ`: the uniform completion of the algebraic tensor product `E ⊗[𝕜] F`
equipped with the cross inner product `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`
(Reed & Simon I, §II.4; Weidmann §3.4; Kadison & Ringrose §2.6).

This is a reducible synonym (`abbrev`), so `E ⊗̂[𝕜] F` inherits the complete
inner-product-space structure of `UniformSpace.Completion` instance-by-instance —
see the `inferInstance` examples below, which are frozen with this definition. -/
abbrev HilbertTensorProduct : Type _ :=
  UniformSpace.Completion (E ⊗[𝕜] F)

@[inherit_doc] scoped notation:100 E " ⊗̂[" 𝕜 "] " F:100 => HilbertTensorProduct 𝕜 E F

/-! Non-vacuity of the `abbrev` design: the Hilbert-space structure of `E ⊗̂[𝕜] F` is
found by instance search alone. These examples are part of the frozen spec. -/

example : NormedAddCommGroup (E ⊗̂[𝕜] F) := inferInstance
example : InnerProductSpace 𝕜 (E ⊗̂[𝕜] F) := inferInstance
example : NormedSpace 𝕜 (E ⊗̂[𝕜] F) := inferInstance
example : CompleteSpace (E ⊗̂[𝕜] F) := inferInstance

namespace HilbertTensorProduct

variable {E F}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The canonical bilinear map `E × F → E ⊗̂[𝕜] F`, as a bounded bilinear map:
`tmulₕ 𝕜 x y` is the image of the algebraic pure tensor `x ⊗ₜ y` under the completion
coercion. Boundedness (with constant `1`) is `‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖`
(`TensorProduct.norm_tmul`); the exact norm identity for the resulting element is
`norm_tmulₕ`. -/
def tmulₕ : E →L[𝕜] F →L[𝕜] E ⊗̂[𝕜] F :=
  LinearMap.mkContinuous₂
    ((TensorProduct.mk 𝕜 E F).compr₂
      (UniformSpace.Completion.toComplₗᵢ (𝕜 := 𝕜) (E := E ⊗[𝕜] F)).toLinearMap)
    1 fun x y => by
      rw [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearIsometry.coe_toLinearMap,
        UniformSpace.Completion.coe_toComplₗᵢ, UniformSpace.Completion.norm_coe,
        TensorProduct.norm_tmul, one_mul]

/-- Definitional pin: `tmulₕ 𝕜 x y` is the completion coercion of `x ⊗ₜ y`. -/
@[simp]
theorem tmulₕ_apply (x : E) (y : F) :
    tmulₕ 𝕜 x y = ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : E ⊗̂[𝕜] F) :=
  rfl

/-- **The characteristic inner-product identity of the Hilbert tensor product**
(Reed & Simon I, §II.4; Weidmann §3.4; Kadison & Ringrose §2.6):
`⟪tmulₕ 𝕜 x y, tmulₕ 𝕜 x' y'⟫ = ⟪x, x'⟫ * ⟪y, y'⟫`. This is Mathlib's
`TensorProduct.inner_tmul` on the algebraic tensor product, transferred through
`UniformSpace.Completion.inner_coe`. -/
@[simp]
theorem inner_tmulₕ (x x' : E) (y y' : F) :
    ⟪tmulₕ 𝕜 x y, tmulₕ 𝕜 x' y'⟫ = ⟪x, x'⟫ * ⟪y, y'⟫ := by
  rw [tmulₕ_apply, tmulₕ_apply, UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]

/-- The cross-norm identity on pure tensors: `‖tmulₕ 𝕜 x y‖ = ‖x‖ * ‖y‖`
(Reed & Simon I, §II.4). -/
@[simp]
theorem norm_tmulₕ (x : E) (y : F) : ‖tmulₕ 𝕜 x y‖ = ‖x‖ * ‖y‖ := by
  rw [tmulₕ_apply, UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul]

/-- **Pure tensors span a dense subspace of the Hilbert tensor product**
(Reed & Simon I, §II.4; Weidmann §3.4): the `𝕜`-span of `{tmulₕ 𝕜 x y}` is dense in
`E ⊗̂[𝕜] F`. Composition of `TensorProduct.span_tmul_eq_top` (pure tensors span the
algebraic tensor product) with `UniformSpace.Completion.denseRange_coe` (the algebraic
tensor product is dense in its completion). -/
theorem dense_span_tmulₕ :
    Dense (Submodule.span 𝕜 {t : E ⊗̂[𝕜] F | ∃ x y, tmulₕ 𝕜 x y = t} :
      Set (E ⊗̂[𝕜] F)) := by
  have himg : {t : E ⊗̂[𝕜] F | ∃ x y, tmulₕ 𝕜 x y = t} =
      ⇑(UniformSpace.Completion.toComplₗᵢ (𝕜 := 𝕜) (E := E ⊗[𝕜] F)).toLinearMap ''
        {t : E ⊗[𝕜] F | ∃ x y, x ⊗ₜ[𝕜] y = t} := by
    ext t
    constructor
    · rintro ⟨x, y, rfl⟩
      exact ⟨x ⊗ₜ y, ⟨x, y, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, y, rfl⟩, rfl⟩
      exact ⟨x, y, rfl⟩
  rw [himg, ← Submodule.map_span, TensorProduct.span_tmul_eq_top, Submodule.map_top,
    LinearMap.coe_range, LinearIsometry.coe_toLinearMap,
    UniformSpace.Completion.coe_toComplₗᵢ]
  exact UniformSpace.Completion.denseRange_coe

end HilbertTensorProduct

end OperatorTheory
