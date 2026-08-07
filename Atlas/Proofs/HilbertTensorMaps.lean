import Atlas.Specs.OperatorTheory.HilbertTensor
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# P2.1b — functoriality of the completed Hilbert tensor product

Blueprint node P2.1b: the isometric functoriality layer over the frozen spec
`Atlas/Specs/OperatorTheory/HilbertTensor.lean` (node P2.1a), which this file consumes and
never modifies.

## Contents

Completion infrastructure (`UniformSpace.Completion`, upstreamable as stated):

* `mapₗᵢ`/`congrₗᵢ`: a linear isometry (equivalence) of normed spaces extends to their
  completions, with `mapₗᵢ_coe`, `congrₗᵢ_coe`, `congrₗᵢ_symm_coe`, `congrₗᵢ_symm`,
  `congrₗᵢ_refl`. Built from `LinearMap.extendOfNorm` / `LinearEquiv.extendOfIsometry`.

Algebraic tensor infrastructure (`TensorProduct`, upstreamable as stated):

* `TensorProduct.denseRange_map`: `map f g` has dense range as soon as `f` and `g`
  do. Pure tensors span (`span_tmul_eq_top`) and `⊗ₜ` is jointly continuous, so each
  `y ⊗ₜ w` lies in the closure of the range.

The Hilbert tensor product layer (`OperatorTheory.HilbertTensorProduct`):

* `mapIsometryₕ f g` and `congrₕ f g`: the isometry (equivalence) induced by a pair of
  isometries (equivalences), with the pure-tensor actions `mapIsometryₕ_tmulₕ`,
  `congrₕ_tmulₕ`, and `congrₕ_symm`, `congrₕ_refl`.
* `commₕ`, `lidₕ`, `assocₕ`: the symmetry, left unit and associativity isometries of the
  monoidal structure, each with its action on pure tensors.

## Scope: no general `mapₕ` for bounded operators

Deliberately absent is `mapₕ : (E →L[𝕜] G) → (F →L[𝕜] H) → (E ⊗̂[𝕜] F →L[𝕜] G ⊗̂[𝕜] H)`.
It needs the cross-norm bound `‖map f g‖ ≤ ‖f‖ * ‖g‖` on the *algebraic* tensor product,
which is not available at our Mathlib pin (v4.31.0): it arrives with the `mapL` material
of Mathlib PR #40074, merged upstream after the pin. Bumping the pin or vendoring that
proof is an owner-gated decision (BLUEPRINT.md P2.1b, `docs/OWNER-ACTIONS.md`), so this
file stops at the isometric case, which needs no cross-norm estimate — isometries are
handled by `TensorProduct.inner_map_map`, already in the pin.

## Design notes

* **`lidₕ` requires `[CompleteSpace E]`, and must.** `𝕜 ⊗̂[𝕜] E` is complete by
  construction, so an isometric equivalence with `E` forces `E` complete. This is the one
  place where the spec's "no completeness assumed" generality cannot be carried over.
* **`assocₕ` is not a completion of the algebraic associator.** Both
  `(E ⊗̂ F) ⊗̂ G = Completion ((E ⊗̂ F) ⊗ G)` and `E ⊗̂ (F ⊗̂ G)` are *double* completions,
  and neither is `Completion ((E ⊗ F) ⊗ G)`. The algebraic triple tensor product does sit
  densely and isometrically inside both, along
  `(E ⊗ F) ⊗ G → (E ⊗̂ F) ⊗ G → (E ⊗̂ F) ⊗̂ G` and
  `E ⊗ (F ⊗ G) → E ⊗ (F ⊗̂ G) → E ⊗̂ (F ⊗̂ G)`; density of the first leg of each is
  `TensorProduct.denseRange_map`, of the second `Completion.denseRange_coe`. The
  associator is then `LinearEquiv.extendOfIsometry` of `TensorProduct.assocIsometry` along
  those two embeddings.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised and enlarged edition (1980), §II.4: the tensor product of Hilbert spaces is
  commutative and associative up to unitary equivalence, and unitaries tensor.
* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*
  (1983), §2.6 (unitary implementation on the Hilbert tensor product).
-/

noncomputable section

open scoped TensorProduct

namespace UniformSpace.Completion

variable {𝕜 X Y : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A linear isometry equivalence of normed spaces extends to their completions. -/
def congrₗᵢ (f : X ≃ₗᵢ[𝕜] Y) : Completion X ≃ₗᵢ[𝕜] Completion Y :=
  f.toLinearEquiv.extendOfIsometry
    (toComplₗᵢ (𝕜 := 𝕜) (E := X)).toLinearMap (toComplₗᵢ (𝕜 := 𝕜) (E := Y)).toLinearMap
    (by simpa using denseRange_coe) (by simpa using denseRange_coe) (by simp)

@[simp]
theorem congrₗᵢ_coe (f : X ≃ₗᵢ[𝕜] Y) (x : X) :
    congrₗᵢ f (x : Completion X) = (f x : Completion Y) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

@[simp]
theorem congrₗᵢ_symm_coe (f : X ≃ₗᵢ[𝕜] Y) (y : Y) :
    (congrₗᵢ f).symm (y : Completion Y) = (f.symm y : Completion X) :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ y

theorem congrₗᵢ_symm (f : X ≃ₗᵢ[𝕜] Y) : (congrₗᵢ f).symm = congrₗᵢ f.symm := by
  refine LinearIsometryEquiv.ext fun y => ?_
  induction y using Completion.induction_on with
  | hp => exact isClosed_eq (LinearIsometryEquiv.continuous _) (LinearIsometryEquiv.continuous _)
  | ih a => simp

@[simp]
theorem congrₗᵢ_refl : congrₗᵢ (LinearIsometryEquiv.refl 𝕜 X) = .refl 𝕜 (Completion X) := by
  refine LinearIsometryEquiv.ext fun x => ?_
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (LinearIsometryEquiv.continuous _) (LinearIsometryEquiv.continuous _)
  | ih a => simp

/-- The extension of a linear isometry to the completions, before it is repackaged as a
linear isometry by `mapₗᵢ`. -/
private def mapCLM (f : X →ₗᵢ[𝕜] Y) : Completion X →L[𝕜] Completion Y :=
  ((toComplₗᵢ (𝕜 := 𝕜) (E := Y)).toLinearMap ∘ₗ f.toLinearMap).extendOfNorm
    (toComplₗᵢ (𝕜 := 𝕜) (E := X)).toLinearMap

private theorem mapCLM_coe (f : X →ₗᵢ[𝕜] Y) (x : X) :
    mapCLM f (x : Completion X) = (f x : Completion Y) :=
  LinearMap.extendOfNorm_eq (by simpa using denseRange_coe) ⟨1, by simp⟩ x

/-- A linear isometry of normed spaces extends to their completions. -/
def mapₗᵢ (f : X →ₗᵢ[𝕜] Y) : Completion X →ₗᵢ[𝕜] Completion Y where
  toLinearMap := mapCLM f
  norm_map' x := by
    simp only [ContinuousLinearMap.coe_coe]
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (continuous_norm.comp (mapCLM f).continuous) continuous_norm
    | ih a => rw [mapCLM_coe, norm_coe, norm_coe, f.norm_map]

@[simp]
theorem mapₗᵢ_coe (f : X →ₗᵢ[𝕜] Y) (x : X) :
    mapₗᵢ f (x : Completion X) = (f x : Completion Y) :=
  mapCLM_coe f x

end UniformSpace.Completion

namespace TensorProduct

variable {𝕜 X Y Z W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

variable (𝕜 Y W) in
/-- Forming pure tensors is jointly continuous, with `‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖` as the bound. -/
theorem continuous_uncurry_tmul :
    Continuous (Function.uncurry fun (a : Y) (b : W) => a ⊗ₜ[𝕜] b) :=
  (LinearMap.mkContinuous₂ (TensorProduct.mk 𝕜 Y W) 1 (by simp)).continuous₂

variable [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Z] [Module 𝕜 Z]

/-- Tensoring dense ranges gives a dense range: `TensorProduct.map f g` has dense range as
soon as `f` and `g` do. Pure tensors span (`span_tmul_eq_top`), and each pure tensor
`y ⊗ₜ w` is a limit of `f x ⊗ₜ g z` by joint continuity of `⊗ₜ`. -/
theorem denseRange_map (f : X →ₗ[𝕜] Y) (g : Z →ₗ[𝕜] W)
    (hf : DenseRange f) (hg : DenseRange g) : DenseRange (map f g) := by
  have key : Dense ((LinearMap.range (map f g) :
      Submodule 𝕜 (Y ⊗[𝕜] W)) : Set (Y ⊗[𝕜] W)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff, ← span_tmul_eq_top,
      Submodule.span_le]
    rintro _ ⟨y, w, rfl⟩
    have hmem := image_closure_subset_closure_image (continuous_uncurry_tmul 𝕜 Y W)
      (Set.mem_image_of_mem _ (hf.prodMap hg (y, w)))
    refine closure_mono ?_ hmem
    rintro _ ⟨_, ⟨⟨x, z⟩, rfl⟩, rfl⟩
    exact ⟨x ⊗ₜ z, rfl⟩
  simpa [DenseRange, LinearMap.coe_range] using key

end TensorProduct

namespace OperatorTheory.HilbertTensorProduct

open UniformSpace

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ### Functoriality for isometries

Each map below gets its action on pure tensors twice. The `_tmulₕ` form is the readable
statement, in the spec's named bilinear map `tmulₕ`. The `_coe_tmul` form is the same
identity after the spec's `@[simp] tmulₕ_apply` has rewritten `tmulₕ 𝕜 x y` to the
completion coercion of `x ⊗ₜ y`; that is the simp-normal form of a pure tensor, so it is
the form that has to carry `@[simp]` for these lemmas to fire inside a `simp` call. -/

/-- A pair of linear isometries induces a linear isometry of Hilbert tensor products. -/
def mapIsometryₕ (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) : E ⊗̂[𝕜] F →ₗᵢ[𝕜] G ⊗̂[𝕜] H :=
  Completion.mapₗᵢ (TensorProduct.mapIsometry f g)

theorem mapIsometryₕ_tmulₕ (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E) (y : F) :
    mapIsometryₕ f g (tmulₕ 𝕜 x y) = tmulₕ 𝕜 (f x) (g y) := by
  simp [mapIsometryₕ]

@[simp]
theorem mapIsometryₕ_coe_tmul (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E) (y : F) :
    mapIsometryₕ f g ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : E ⊗̂[𝕜] F) =
      ((f x ⊗ₜ[𝕜] g y : G ⊗[𝕜] H) : G ⊗̂[𝕜] H) :=
  mapIsometryₕ_tmulₕ f g x y

/-- A pair of linear isometry equivalences induces a linear isometry equivalence of
Hilbert tensor products (Kadison & Ringrose §2.6: unitaries tensor to a unitary). -/
def congrₕ (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) : E ⊗̂[𝕜] F ≃ₗᵢ[𝕜] G ⊗̂[𝕜] H :=
  Completion.congrₗᵢ (TensorProduct.congrIsometry f g)

theorem congrₕ_tmulₕ (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) (x : E) (y : F) :
    congrₕ f g (tmulₕ 𝕜 x y) = tmulₕ 𝕜 (f x) (g y) := by
  simp [congrₕ]

@[simp]
theorem congrₕ_coe_tmul (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) (x : E) (y : F) :
    congrₕ f g ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : E ⊗̂[𝕜] F) =
      ((f x ⊗ₜ[𝕜] g y : G ⊗[𝕜] H) : G ⊗̂[𝕜] H) :=
  congrₕ_tmulₕ f g x y

theorem congrₕ_symm (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (congrₕ f g).symm = congrₕ f.symm g.symm := by
  rw [congrₕ, Completion.congrₗᵢ_symm, TensorProduct.congrIsometry_symm, congrₕ]

@[simp]
theorem congrₕ_refl : congrₕ (.refl 𝕜 E) (.refl 𝕜 F) = .refl 𝕜 (E ⊗̂[𝕜] F) := by
  rw [congrₕ, TensorProduct.congrIsometry_refl_refl, Completion.congrₗᵢ_refl]

/-! ### The symmetry, unit and associativity isometries -/

variable (𝕜 E F) in
/-- **Commutativity of the Hilbert tensor product**: `E ⊗̂ F ≃ₗᵢ F ⊗̂ E`
(Reed & Simon I, §II.4). -/
def commₕ : E ⊗̂[𝕜] F ≃ₗᵢ[𝕜] F ⊗̂[𝕜] E :=
  Completion.congrₗᵢ (TensorProduct.commIsometry 𝕜 E F)

theorem commₕ_tmulₕ (x : E) (y : F) : commₕ 𝕜 E F (tmulₕ 𝕜 x y) = tmulₕ 𝕜 y x := by
  simp [commₕ]

@[simp]
theorem commₕ_coe_tmul (x : E) (y : F) :
    commₕ 𝕜 E F ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : E ⊗̂[𝕜] F) = ((y ⊗ₜ[𝕜] x : F ⊗[𝕜] E) : F ⊗̂[𝕜] E) :=
  commₕ_tmulₕ x y

@[simp]
theorem commₕ_symm : (commₕ 𝕜 E F).symm = commₕ 𝕜 F E := by
  rw [commₕ, Completion.congrₗᵢ_symm, TensorProduct.commIsometry_symm, commₕ]

variable (𝕜 E) in
/-- **The left unit law**: `𝕜 ⊗̂ E ≃ₗᵢ E` for a Hilbert space `E`. Completeness of `E`
is necessary, not incidental: the left-hand side is complete by construction. -/
def lidₕ [CompleteSpace E] : 𝕜 ⊗̂[𝕜] E ≃ₗᵢ[𝕜] E :=
  (TensorProduct.lidIsometry 𝕜 E).toLinearEquiv.extendOfIsometry
    (Completion.toComplₗᵢ (𝕜 := 𝕜) (E := 𝕜 ⊗[𝕜] E)).toLinearMap LinearMap.id
    (by simpa using Completion.denseRange_coe) (by simpa using denseRange_id) (by simp)

theorem lidₕ_tmulₕ [CompleteSpace E] (c : 𝕜) (x : E) : lidₕ 𝕜 E (tmulₕ 𝕜 c x) = c • x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ (c ⊗ₜ[𝕜] x)

@[simp]
theorem lidₕ_coe_tmul [CompleteSpace E] (c : 𝕜) (x : E) :
    lidₕ 𝕜 E ((c ⊗ₜ[𝕜] x : 𝕜 ⊗[𝕜] E) : 𝕜 ⊗̂[𝕜] E) = c • x :=
  lidₕ_tmulₕ c x

variable (𝕜 E F G) in
/-- **Associativity of the Hilbert tensor product**: `(E ⊗̂ F) ⊗̂ G ≃ₗᵢ E ⊗̂ (F ⊗̂ G)`
(Reed & Simon I, §II.4).

Both sides are *double* completions, so this is not a completion of the algebraic
associator: it is the extension of the algebraic `TensorProduct.assocIsometry` along the
two dense isometric embeddings of the algebraic triple tensor product
`(E ⊗ F) ⊗ G → (E ⊗̂ F) ⊗ G → (E ⊗̂ F) ⊗̂ G` and
`E ⊗ (F ⊗ G) → E ⊗ (F ⊗̂ G) → E ⊗̂ (F ⊗̂ G)`, whose density is
`TensorProduct.denseRange_map` composed with `Completion.denseRange_coe`. -/
def assocₕ : (E ⊗̂[𝕜] F) ⊗̂[𝕜] G ≃ₗᵢ[𝕜] E ⊗̂[𝕜] (F ⊗̂[𝕜] G) :=
  (TensorProduct.assocIsometry 𝕜 E F G).toLinearEquiv.extendOfIsometry
    ((Completion.toComplₗᵢ (𝕜 := 𝕜) (E := (E ⊗̂[𝕜] F) ⊗[𝕜] G)).toLinearMap ∘ₗ
      ((Completion.toComplₗᵢ (𝕜 := 𝕜) (E := E ⊗[𝕜] F)).rTensor G).toLinearMap)
    ((Completion.toComplₗᵢ (𝕜 := 𝕜) (E := E ⊗[𝕜] (F ⊗̂[𝕜] G))).toLinearMap ∘ₗ
      ((Completion.toComplₗᵢ (𝕜 := 𝕜) (E := F ⊗[𝕜] G)).lTensor E).toLinearMap)
    (by
      rw [LinearMap.coe_comp]
      refine Completion.denseRange_coe.comp ?_ (Completion.continuous_coe _)
      exact TensorProduct.denseRange_map _ _
        (by simpa using Completion.denseRange_coe) (by simpa using denseRange_id))
    (by
      rw [LinearMap.coe_comp]
      refine Completion.denseRange_coe.comp ?_ (Completion.continuous_coe _)
      exact TensorProduct.denseRange_map _ _
        (by simpa using denseRange_id) (by simpa using Completion.denseRange_coe))
    (fun x => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearIsometry.coe_toLinearMap,
        Completion.coe_toComplₗᵢ, Completion.norm_coe, LinearIsometry.norm_map,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map])

theorem assocₕ_tmulₕ (x : E) (y : F) (z : G) :
    assocₕ 𝕜 E F G (tmulₕ 𝕜 (tmulₕ 𝕜 x y) z) = tmulₕ 𝕜 x (tmulₕ 𝕜 y z) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ ((x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] z)

@[simp]
theorem assocₕ_coe_tmul (x : E) (y : F) (z : G) :
    assocₕ 𝕜 E F G (((((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : E ⊗̂[𝕜] F) ⊗ₜ[𝕜] z :
        (E ⊗̂[𝕜] F) ⊗[𝕜] G) : (E ⊗̂[𝕜] F) ⊗̂[𝕜] G)) =
      ((x ⊗ₜ[𝕜] ((y ⊗ₜ[𝕜] z : F ⊗[𝕜] G) : F ⊗̂[𝕜] G) : E ⊗[𝕜] (F ⊗̂[𝕜] G)) :
        E ⊗̂[𝕜] (F ⊗̂[𝕜] G)) :=
  assocₕ_tmulₕ x y z

end OperatorTheory.HilbertTensorProduct
