import Atlas.Proofs.PiTensorInner
import Atlas.Proofs.HilbertTensorMaps
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# P2.2 — symmetric tensor powers and the boson Fock space

Frozen spec (blueprint node P2.2, first spec slice): proof sessions must not edit this
file; changes require a spec review and a `[spec-review]` commit (see CLAUDE.md).

## Contents

* `QFT.symmetrizer 𝕜 E n : ⨂[𝕜]^n E →ₗ[𝕜] ⨂[𝕜]^n E`: the symmetrization operator
  `(n!)⁻¹ ∑ σ ∈ Sₙ, σ` on the algebraic `n`-th tensor power, with its action on pure
  tensors (`symmetrizer_tprod`), its `Sₙ`-invariance (`symmetrizer_reindex`), and its
  idempotency (`isIdempotentElem_symmetrizer`), all kernel-checked here since they pin
  the definition.
* `QFT.HilbertTensorPower 𝕜 E n`: the completed `n`-th Hilbert tensor power — the
  `UniformSpace.Completion` of `⨂[𝕜]^n E` under the ℓ²/Hilbert cross norm of P2.1e/f
  (scoped in `PiTensorProduct.InnerNorm`). The `inferInstance` examples pinning its
  Hilbert-space structure are frozen with the definition.
* `QFT.symmetrizerL 𝕜 E n`: the symmetrizer on the completed power, defined as the same
  group average taken over the *completed* reindexing isometries — hence bounded by
  construction (`norm_symmetrizerL_apply_le`: it is a contraction), restricting to the
  algebraic symmetrizer on the dense image (`symmetrizerL_coe`), and idempotent
  (`isIdempotentElem_symmetrizerL`).
* `QFT.SymTensorPower 𝕜 E n : Submodule 𝕜 (HilbertTensorPower 𝕜 E n)`: the `n`-particle
  boson sector — the range of `symmetrizerL`, equivalently its fixed-point space
  (`mem_symTensorPower_iff`), a closed subspace (`isClosed_symTensorPower`) and hence a
  Hilbert space (the `CompleteSpace` instance plus `inferInstance` examples).
* `QFT.BosonFock 𝕜 E := lp (fun n => SymTensorPower 𝕜 E n) 2`: the symmetric (boson)
  Fock space over `E`, the Hilbert sum of the sectors, with its Hilbert-space instance
  witnesses.
* `QFT.BosonFock.vacuum`: the vacuum vector `Ω` — the unit of the `n = 0` sector — with
  `norm_vacuum : ‖Ω‖ = 1`.
* `QFT.BosonFock.finiteParticle`: the finite-particle subspace `F₀` (the algebraic sum
  of the sectors inside the Hilbert sum), with `dense_finiteParticle` — the common core
  on which the whole P2.2 operator layer will live.

## Conventions

* **Symmetrizer normalization: the orthogonal-projector convention.**
  `symmetrizer 𝕜 E n = (n!)⁻¹ • ∑ σ : Equiv.Perm (Fin n), reindex σ`, following
  Reed & Simon (I, §II.4, Example 2: `Sₙ = (n!)⁻¹ ∑_{σ ∈ 𝒫ₙ} σ`) and
  Bratteli & Robinson (II, §5.2, the symmetrization projector `P₊` on Fock space).
  With this normalization the symmetrizer is idempotent and fixes symmetric tensors;
  the alternative `(n!)^(-1/2)` normalizations found in symmetric-product constructions
  (e.g. for the product `f₁ ∨ ⋯ ∨ fₙ` and its inner product) are *not* used here — the
  `√(n+1)`-type factors those conventions trade off will instead appear explicitly in
  the creation/annihilation operators of the next spec slice.
* **How the `Equiv.Perm` action is encoded** (the subtle spot flagged in BLUEPRINT.md):
  `σ : Equiv.Perm (Fin n)` acts by `PiTensorProduct.reindex 𝕜 (fun _ ↦ E) σ`, whose
  codomain `⨂[𝕜] i, (fun _ ↦ E) (σ.symm i)` is *definitionally* (by beta reduction of
  the constant family) the tensor power `⨂[𝕜]^n E` again — so no cast or transport
  appears anywhere; the definitions elaborating without casts is the kernel-checked
  evidence. On pure tensors, `reindex σ (⨂ₜ x) = ⨂ₜ (x ∘ σ.symm)` (slot `i` of the
  result holds `x (σ⁻¹ i)`), and `reindex σ ∘ reindex τ = reindex (σ * τ)` by
  `PiTensorProduct.reindex_trans` with `Equiv.Perm.mul_def` — a genuine left monoid
  action. The symmetrizer only consumes the translation invariance of the group sum,
  so the action is not bundled as a `MonoidHom`; bundling it is a candidate upstream
  lemma, not part of this spec. Since the sum runs over all of `Sₙ`, the choice of
  `σ` versus `σ⁻¹` in the action is immaterial for the symmetrizer (the two sums are
  equal by `σ ↦ σ⁻¹`); `symmetrizer_tprod` is stated with the sum over `⨂ₜ (x ∘ σ)`.
* **Complete-then-symmetrize** (design adjudication for the P2.2 grind). We complete
  the algebraic tensor power first and symmetrize the completion, rather than
  completing the algebraic symmetric range:
  1. it is the textbook construction — Reed & Simon and Bratteli & Robinson both apply
     `Sₙ` to the *completed* `n`-fold tensor product `H⁽ⁿ⁾`;
  2. the extension of the symmetrizer to the completion is free of any operator-norm
     machinery: it is the average of the completed reindexing *isometries*
     (`Completion.congrₗᵢ` of P2.1b applied to `reindexIsometry` of P2.1f), bounded by
     construction;
  3. each sector becomes a closed subspace of an ambient Hilbert space, so
     completeness is inherited (`IsClosed.completeSpace_coe`) instead of re-proved,
     and all sectors live in one ambient chain `HilbertTensorPower 𝕜 E n` — which is
     what the creation/annihilation grind needs, since `a†(f)` maps sector `n` into
     the ambient power `n + 1` by `f ⊗ₜ ·` before re-symmetrizing. Under
     symmetrize-then-complete every cross-sector identity would instead thread through
     the completion functor applied to isometric embeddings.
  The identification of `SymTensorPower 𝕜 E n` with the closure of the image of the
  *algebraic* symmetric range (equivalently, with its abstract completion) is a
  candidate future lemma; the Fock construction does not need it.
* **Scope discipline (inherited from P2.1f, mechanically guarded).** The norm on
  `⨂[𝕜]^n E` used throughout is the scoped Hilbert (ℓ²) cross norm
  `PiTensorProduct.InnerNorm`; Mathlib's projective-seminorm instances on
  `PiTensorProduct` would form a non-defeq diamond against it. This file therefore
  must never (transitively) import `Mathlib.Analysis.Normed.Module.PiTensorProduct.*`;
  the `assert_not_exists PiTensorProduct.projectiveSeminorm` below enforces this at
  compile time and is frozen with the spec. Downstream consumers of this file must
  `open scoped PiTensorProduct.InnerNorm` and obey the same import discipline. The
  scoped instances are baked into the *definitions* here (the completion is taken with
  respect to the ℓ² uniformity), so the meaning of `HilbertTensorPower` cannot drift
  even if a consumer's instance context differs — such a consumer either fails to elaborate or receives the baked ℓ² structure by
  unification; drift is impossible either way (probe-verified at review).
* **Spec-load-bearing imports.** This spec consumes three Proofs files:
  `Atlas.Proofs.PiTensorSemilinear` (P2.1e: `innerAux` itself — the pairing whose
  values give every norm below its meaning), `Atlas.Proofs.PiTensorInner` (P2.1f:
  the scoped `InnerNorm` instances, `reindexIsometry`, with anchor lemmas
  `inner_tprod`/`norm_tprod`/`reindexIsometry_apply`), and
  `Atlas.Proofs.HilbertTensorMaps` (P2.1b: `UniformSpace.Completion.congrₗᵢ`,
  anchor `congrₗᵢ_coe`). Those
  definitions are hereby load-bearing for a frozen spec: changing them changes the
  meaning of this file, so they are de facto frozen and any edit to them requires the
  same `[spec-review]` scrutiny (mechanically enforced: the commit-msg hook covers
  these three files by name).
* **`abbrev` for `HilbertTensorPower` and `BosonFock`** (P2.1a precedent): both are
  reducible synonyms so that the completion/`lp` instances apply with no copied
  instances and no drift; the `inferInstance` examples are frozen with the
  definitions as the kernel-checked evidence of this transparency. `SymTensorPower`
  is a `def` (a `Submodule`, not a type synonym); its Hilbert structure flows through
  Mathlib's submodule instances plus the `CompleteSpace` instance proved here.
* **Hilbert sum via `lp`.** `BosonFock` is `lp _ 2` — Mathlib's canonical countable
  Hilbert sum, with `lp.instInnerProductSpace`/`lp.completeSpace` and the
  `IsHilbertSum` API available downstream. `DirectSum` is not used: it carries no
  norm. No completeness of `E` is assumed anywhere in this file (P2.1a precedent);
  physics consumers instantiate complete `E` (and `𝕜 = ℂ`).
* **Generality `RCLike 𝕜`.** The completed layer needs the P2.1f inner-norm instances,
  which are stated over `RCLike 𝕜`; the algebraic `symmetrizer` alone would make sense
  over any field with `n!` invertible (`RCLike` supplies characteristic zero, so
  `(n! : 𝕜)⁻¹` is legitimate), but we do not introduce a second generality track.
* **Namespace.** Everything lives in `QFT` — the atlas's first QFT-named spec — with
  the vacuum and the finite-particle subspace under `QFT.BosonFock`. On upstreaming,
  `symmetrizer` belongs near `TensorPower`, the Fock layer in a physics library.

## Future spec items (next slices — named here, deliberately not defined)

The following are blueprint node P2.2 material staged for the next spec slice, after
review of this one; naming them here fixes the interfaces they will attach to:

* the symmetrizer is *self-adjoint* for the P2.1f inner product
  (`⟪symmetrizerL x, y⟫ = ⟪x, symmetrizerL y⟫`), upgrading `SymTensorPower` from
  "range of a bounded idempotent" to "range of an orthogonal projection";
* `creation`/`annihilation` operators `a†(f), a(f)` as `LinearPMap`s on
  `BosonFock 𝕜 E` with domain `BosonFock.finiteParticle 𝕜 E`, and their sector maps
  (`a†(f)` on the `n`-sector: `√(n+1) · symmetrizerL (f ⊗ₜ ·)`);
* mutual formal adjointness of `a(f)` and `a†(f)` (`LinearPMap.IsFormalAdjoint`) and
  the CCR `[a(f), a†(g)] = ⟪f, g⟫ • 1` on the finite-particle domain;
* the Segal field `Φ(f) = (a(f) + a†(f))/√2` and its essential self-adjointness on
  the finite-particle domain via a new Nelson analytic-vector node (Reed & Simon II,
  Thm X.39) feeding the proven P2.3b criterion
  (`OperatorTheory.EssentialSelfAdjointnessCriterion`).

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised and enlarged edition (1980), §II.4, Example 2 (Fock spaces): the full Fock
  space `F(H) = ⊕_{n≥0} H⁽ⁿ⁾` over the completed powers, the symmetrization operator
  `Sₙ = (n!)⁻¹ ∑_{σ ∈ 𝒫ₙ} σ`, and the boson (symmetric) Fock space
  `F_s(H) = ⊕_{n≥0} Sₙ H⁽ⁿ⁾`. The example label ("Example 2") is quoted from memory
  and not re-verified against a copy; the section citation is authoritative.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II: Fourier Analysis,
  Self-Adjointness* (1975), §X.7 (the free quantum field): the vacuum `Ω`, the set
  `F₀` of finite-particle vectors as the common dense domain, and the operator layer
  (creation/annihilation, Segal field) staged above as future slices.
* O. Bratteli, D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*,
  2nd edition (1997), §5.2 (the CCR algebra over Fock space): the symmetrization
  projector `P₊` on Fock space, obtained by averaging the permutation unitaries and
  extending by continuity — the construction `symmetrizerL` formalizes. Section-level
  citation.
-/

assert_not_exists PiTensorProduct.projectiveSeminorm

noncomputable section

namespace QFT

open PiTensorProduct UniformSpace Equiv
open scoped TensorProduct PiTensorProduct.InnerNorm Nat ENNReal

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (n : ℕ)

/-! ### The symmetrizer on the algebraic tensor power -/

/-- The *symmetrization operator* on the `n`-th tensor power: the average
`(n!)⁻¹ • ∑ σ ∈ Sₙ, σ` of the permutation actions `PiTensorProduct.reindex 𝕜 (fun _ ↦ E) σ`
(Reed & Simon I, §II.4, Example 2; Bratteli & Robinson II, §5.2). For the constant family
`fun _ ↦ E` each reindexing is definitionally an endomorphism of `⨂[𝕜]^n E`, so no cast
appears. This is the orthogonal-projector normalization; see the module docstring. -/
def symmetrizer : ⨂[𝕜]^n E →ₗ[𝕜] ⨂[𝕜]^n E :=
  (n ! : 𝕜)⁻¹ • ∑ σ : Perm (Fin n),
    ((reindex 𝕜 (fun _ ↦ E) σ).toLinearMap : ⨂[𝕜]^n E →ₗ[𝕜] ⨂[𝕜]^n E)

/-- Unfolding pin for the symmetrizer: the pointwise group average. -/
theorem symmetrizer_apply (x : ⨂[𝕜]^n E) :
    symmetrizer 𝕜 E n x = (n ! : 𝕜)⁻¹ • ∑ σ : Perm (Fin n), reindex 𝕜 (fun _ ↦ E) σ x := by
  simp [symmetrizer]

/-- **Action of the symmetrizer on pure tensors**: `⨂ₜ x` is sent to the average of the
pure tensors `⨂ₜ (x ∘ σ)` over all permutations `σ` (Reed & Simon I, §II.4, Example 2). -/
theorem symmetrizer_tprod (x : Fin n → E) :
    symmetrizer 𝕜 E n (tprod 𝕜 x) =
      (n ! : 𝕜)⁻¹ • ∑ σ : Perm (Fin n), tprod 𝕜 fun i => x (σ i) := by
  rw [symmetrizer_apply]
  refine congrArg (fun t => (n ! : 𝕜)⁻¹ • t) ?_
  calc
    ∑ σ : Perm (Fin n), reindex 𝕜 (fun _ ↦ E) σ (tprod 𝕜 x)
        = ∑ σ : Perm (Fin n), tprod 𝕜 fun i => x (σ⁻¹ i) :=
          Finset.sum_congr rfl fun σ _ => reindex_tprod σ x
    _ = ∑ σ : Perm (Fin n), tprod 𝕜 fun i => x (σ i) :=
          Equiv.sum_comp (Equiv.inv (Perm (Fin n))) fun σ => tprod 𝕜 fun i => x (σ i)

/-- The symmetrizer is invariant under precomposition with any permutation: averaging
over the group absorbs a translation. This is the engine behind idempotency. -/
theorem symmetrizer_reindex (τ : Perm (Fin n)) (x : ⨂[𝕜]^n E) :
    symmetrizer 𝕜 E n (reindex 𝕜 (fun _ ↦ E) τ x) = symmetrizer 𝕜 E n x := by
  rw [symmetrizer_apply, symmetrizer_apply]
  refine congrArg (fun t => (n ! : 𝕜)⁻¹ • t) ?_
  calc
    ∑ σ : Perm (Fin n), reindex 𝕜 (fun _ ↦ E) σ (reindex 𝕜 (fun _ ↦ E) τ x)
        = ∑ σ : Perm (Fin n), reindex 𝕜 (fun _ ↦ E) (σ * τ) x :=
          Finset.sum_congr rfl fun σ _ => by
            rw [← LinearEquiv.trans_apply, reindex_trans, ← Perm.mul_def]
    _ = ∑ σ : Perm (Fin n), reindex 𝕜 (fun _ ↦ E) σ x :=
          Equiv.sum_comp (Equiv.mulRight τ) fun σ => reindex 𝕜 (fun _ ↦ E) σ x

/-- **The symmetrizer is idempotent** (Reed & Simon I, §II.4, Example 2: `Sₙ² = Sₙ`):
averaging a group action is a projection. Kernel-checked here since it pins the
`(n!)⁻¹` normalization — any other scaling would fail it. -/
theorem isIdempotentElem_symmetrizer : IsIdempotentElem (symmetrizer 𝕜 E n) := by
  have hfac : (n ! : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply]
  calc
    symmetrizer 𝕜 E n (symmetrizer 𝕜 E n x)
        = (n ! : 𝕜)⁻¹ • ∑ τ : Perm (Fin n),
            symmetrizer 𝕜 E n (reindex 𝕜 (fun _ ↦ E) τ x) := by
          rw [symmetrizer_apply 𝕜 E n x, map_smul, map_sum]
    _ = (n ! : 𝕜)⁻¹ • ∑ _τ : Perm (Fin n), symmetrizer 𝕜 E n x :=
          congrArg (fun t => (n ! : 𝕜)⁻¹ • t)
            (Finset.sum_congr rfl fun τ _ => symmetrizer_reindex 𝕜 E n τ x)
    _ = symmetrizer 𝕜 E n x := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀ hfac, one_smul]

/-- In degrees `n ≤ 1` there is nothing to symmetrize: the symmetrizer is the identity.
Pins the `n = 0` and `n = 1` sectors (vacuum and one-particle space). -/
theorem symmetrizer_eq_id (hn : n ≤ 1) : symmetrizer 𝕜 E n = LinearMap.id := by
  haveI : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
  have hone : (n ! : 𝕜) = 1 := by rw [Nat.factorial_eq_one.mpr hn, Nat.cast_one]
  refine LinearMap.ext fun x => ?_
  rw [symmetrizer_apply,
    Fintype.sum_subsingleton (fun σ : Perm (Fin n) => reindex 𝕜 (fun _ ↦ E) σ x)
      (Equiv.refl (Fin n)),
    reindex_refl, hone, inv_one, one_smul]
  rfl

/-! ### The completed Hilbert tensor power -/

/-- The *`n`-th Hilbert tensor power* of an inner-product space `E`: the uniform
completion of the algebraic tensor power `⨂[𝕜]^n E` under the Hilbert (ℓ²) cross norm
of P2.1e/f, `‖⨂ₜ i, x i‖ = ∏ i, ‖x i‖`. For complete `E` this is the space `H⁽ⁿ⁾` of
Reed & Simon I, §II.4, Example 2. A reducible synonym (P2.1a precedent), so the
completion's Hilbert-space structure applies instance-by-instance — the `inferInstance`
examples below are frozen with this definition. -/
abbrev HilbertTensorPower : Type _ :=
  Completion (⨂[𝕜]^n E)

/-! Non-vacuity of the `abbrev` design: the Hilbert-space structure of
`HilbertTensorPower 𝕜 E n` is found by instance search alone (with the
`PiTensorProduct.InnerNorm` scope open). These examples are part of the frozen spec. -/

example : NormedAddCommGroup (HilbertTensorPower 𝕜 E n) := inferInstance
example : InnerProductSpace 𝕜 (HilbertTensorPower 𝕜 E n) := inferInstance
example : CompleteSpace (HilbertTensorPower 𝕜 E n) := inferInstance

/-- The symmetrizer on the completed tensor power: the average of the *completed*
permutation isometries — `Completion.congrₗᵢ` (P2.1b) applied to
`PiTensorProduct.reindexIsometry` (P2.1f) — so it is a continuous linear map bounded by
construction, with no extension-of-bounded-operators machinery. This is the projector
`P₊` restricted to the `n`-particle subspace in Bratteli & Robinson II, §5.2, there
likewise obtained by averaging the permutation unitaries and extending by continuity. -/
def symmetrizerL : HilbertTensorPower 𝕜 E n →L[𝕜] HilbertTensorPower 𝕜 E n :=
  (n ! : 𝕜)⁻¹ • ∑ σ : Perm (Fin n),
    ((Completion.congrₗᵢ
        (reindexIsometry 𝕜 (fun _ ↦ E) σ)).toLinearIsometry.toContinuousLinearMap :
      HilbertTensorPower 𝕜 E n →L[𝕜] HilbertTensorPower 𝕜 E n)

/-- Definitional pin: on the dense image of the algebraic tensor power, `symmetrizerL`
is the algebraic `symmetrizer`. -/
@[simp]
theorem symmetrizerL_coe (x : ⨂[𝕜]^n E) :
    symmetrizerL 𝕜 E n (x : HilbertTensorPower 𝕜 E n) =
      (symmetrizer 𝕜 E n x : HilbertTensorPower 𝕜 E n) := by
  calc
    symmetrizerL 𝕜 E n (x : HilbertTensorPower 𝕜 E n)
        = (n ! : 𝕜)⁻¹ • ∑ σ : Perm (Fin n),
            ((reindex 𝕜 (fun _ ↦ E) σ x : ⨂[𝕜]^n E) : HilbertTensorPower 𝕜 E n) := by
          rw [symmetrizerL, smul_apply, sum_apply]
          exact congrArg (fun t => (n ! : 𝕜)⁻¹ • t)
            (Finset.sum_congr rfl fun σ _ =>
              Completion.congrₗᵢ_coe (reindexIsometry 𝕜 (fun _ ↦ E) σ) x)
    _ = (symmetrizer 𝕜 E n x : HilbertTensorPower 𝕜 E n) := by
          rw [symmetrizer_apply, Completion.coe_smul]
          exact congrArg (fun t => (n ! : 𝕜)⁻¹ • t)
            (map_sum (Completion.toComplₗᵢ (𝕜 := 𝕜)
              (E := ⨂[𝕜]^n E)).toLinearMap _ _).symm

/-- The completed symmetrizer is a contraction: `‖symmetrizerL x‖ ≤ ‖x‖`, since it
averages `n!` isometries. Pins the operator-norm content of the average-of-unitaries
construction (Bratteli & Robinson II, §5.2). -/
theorem norm_symmetrizerL_apply_le (x : HilbertTensorPower 𝕜 E n) :
    ‖symmetrizerL 𝕜 E n x‖ ≤ ‖x‖ := by
  have hfac : (0 : ℝ) < (n ! : ℝ) := by positivity
  rw [symmetrizerL, smul_apply, sum_apply, norm_smul, norm_inv, RCLike.norm_natCast]
  calc
    (n ! : ℝ)⁻¹ * ‖∑ σ : Perm (Fin n),
        (Completion.congrₗᵢ
          (reindexIsometry 𝕜 (fun _ ↦ E) σ)).toLinearIsometry.toContinuousLinearMap x‖
        ≤ (n ! : ℝ)⁻¹ * ∑ σ : Perm (Fin n), ‖x‖ := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => le_of_eq ?_)
          exact (Completion.congrₗᵢ (reindexIsometry 𝕜 (fun _ ↦ E) σ)).norm_map x
    _ = ‖x‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hfac.ne', one_mul]

/-- **The completed symmetrizer is idempotent**: idempotency transfers from the dense
algebraic image (`isIdempotentElem_symmetrizer`) by continuity. -/
theorem isIdempotentElem_symmetrizerL : IsIdempotentElem (symmetrizerL 𝕜 E n) := by
  refine ContinuousLinearMap.ext fun x => ?_
  show symmetrizerL 𝕜 E n (symmetrizerL 𝕜 E n x) = symmetrizerL 𝕜 E n x
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((symmetrizerL 𝕜 E n).continuous.comp (symmetrizerL 𝕜 E n).continuous)
      (symmetrizerL 𝕜 E n).continuous
  | ih a =>
    simp only [symmetrizerL_coe]
    exact congrArg _ ((Module.End.mul_apply _ _ _).symm.trans
      (DFunLike.congr_fun (isIdempotentElem_symmetrizer 𝕜 E n) a))

/-! ### The symmetric sectors -/

/-- The *`n`-particle boson sector* `Sₙ H⁽ⁿ⁾`: the range of the completed symmetrizer,
as a submodule of the `n`-th Hilbert tensor power (Reed & Simon I, §II.4, Example 2;
Bratteli & Robinson II, §5.2). Equivalently the fixed-point space of `symmetrizerL`
(`mem_symTensorPower_iff`); closed (`isClosed_symTensorPower`), hence itself a Hilbert
space — see the instances below. -/
def SymTensorPower : Submodule 𝕜 (HilbertTensorPower 𝕜 E n) :=
  LinearMap.range (symmetrizerL 𝕜 E n).toLinearMap

/-- Membership in the sector is being fixed by the symmetrizer — the "symmetric
tensors" description of the range, via idempotency. -/
theorem mem_symTensorPower_iff {x : HilbertTensorPower 𝕜 E n} :
    x ∈ SymTensorPower 𝕜 E n ↔ symmetrizerL 𝕜 E n x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact DFunLike.congr_fun (isIdempotentElem_symmetrizerL 𝕜 E n) y
  · exact fun h => ⟨x, h⟩

/-- The boson sector is closed: it is the equalizer of `symmetrizerL` and the
identity. This is what makes complete-then-symmetrize deliver complete sectors. -/
theorem isClosed_symTensorPower :
    IsClosed (SymTensorPower 𝕜 E n : Set (HilbertTensorPower 𝕜 E n)) := by
  have h : (SymTensorPower 𝕜 E n : Set (HilbertTensorPower 𝕜 E n)) =
      {x | symmetrizerL 𝕜 E n x = x} :=
    Set.ext fun _ => mem_symTensorPower_iff 𝕜 E n
  rw [h]
  exact isClosed_eq (symmetrizerL 𝕜 E n).continuous continuous_id

instance : CompleteSpace (SymTensorPower 𝕜 E n) :=
  (isClosed_symTensorPower 𝕜 E n).completeSpace_coe

/-! Non-vacuity: each sector is transparently a Hilbert space (submodule instances plus
the `CompleteSpace` instance above). Frozen with the definition. -/

example : NormedAddCommGroup (SymTensorPower 𝕜 E n) := inferInstance
example : InnerProductSpace 𝕜 (SymTensorPower 𝕜 E n) := inferInstance
example : CompleteSpace (SymTensorPower 𝕜 E n) := inferInstance

/-! ### The boson Fock space -/

/-- The *symmetric (boson) Fock space* over `E`: the Hilbert sum
`F_s(E) = ⊕_{n≥0} Sₙ E⁽ⁿ⁾` of the boson sectors, realized as `lp _ 2`
(Reed & Simon I, §II.4, Example 2; Reed & Simon II, §X.7; Bratteli & Robinson II,
§5.2). A reducible synonym, so Mathlib's `lp`-instances give its Hilbert-space
structure directly — the `inferInstance` examples below are frozen with it. -/
abbrev BosonFock : Type _ :=
  lp (fun n => SymTensorPower 𝕜 E n) 2

example : NormedAddCommGroup (BosonFock 𝕜 E) := inferInstance
example : InnerProductSpace 𝕜 (BosonFock 𝕜 E) := inferInstance
example : CompleteSpace (BosonFock 𝕜 E) := inferInstance

namespace BosonFock

/-- The *vacuum vector* `Ω`: the image of the empty pure tensor — the unit of the
scalar `n = 0` sector — under `lp.single` (Reed & Simon II, §X.7: `Ω = (1, 0, 0, …)`).
The membership proof is `symmetrizer_eq_id`: in degree `0` the symmetrizer is the
identity, so the vector is symmetric. -/
def vacuum : BosonFock 𝕜 E :=
  lp.single 2 0
    ⟨((tprod 𝕜 Fin.elim0 : ⨂[𝕜]^0 E) : HilbertTensorPower 𝕜 E 0), by
      rw [mem_symTensorPower_iff, symmetrizerL_coe, symmetrizer_eq_id 𝕜 E 0 (Nat.zero_le 1),
        LinearMap.id_coe, id_eq]⟩

/-- **The vacuum is a unit vector** (Reed & Simon II, §X.7): the empty tensor has norm
`∏ i ∈ (∅ : Finset _), ‖·‖ = 1`, and `lp.single` is isometric. Non-vacuity witness:
the `n = 0` sector, hence the Fock space, is nontrivial. -/
@[simp]
theorem norm_vacuum : ‖vacuum 𝕜 E‖ = 1 := by
  rw [vacuum, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  show ‖((tprod 𝕜 Fin.elim0 : ⨂[𝕜]^0 E) : HilbertTensorPower 𝕜 E 0)‖ = 1
  rw [Completion.norm_coe, PiTensorProduct.norm_tprod]
  simp

/-- Expected-true guard: the vacuum is not the zero vector. -/
example : vacuum 𝕜 E ≠ 0 := by
  intro h
  simpa [h] using (norm_vacuum 𝕜 E).symm

/-- The *finite-particle subspace* `F₀`: the algebraic (non-closed) sum of the sectors
inside the Hilbert sum — elements with only finitely many nonzero components (Reed &
Simon II, §X.7). This is the common dense domain on which the whole P2.2 operator layer
(creation/annihilation, CCR, Segal fields) will be defined as `LinearPMap`s. -/
def finiteParticle : Submodule 𝕜 (BosonFock 𝕜 E) :=
  ⨆ N, LinearMap.range
    (lp.singleContinuousLinearMap 𝕜 (fun n => SymTensorPower 𝕜 E n) 2 N).toLinearMap

/-- The vacuum is a finite-particle vector. -/
theorem vacuum_mem_finiteParticle : vacuum 𝕜 E ∈ finiteParticle 𝕜 E :=
  le_iSup (fun N => LinearMap.range
      (lp.singleContinuousLinearMap 𝕜 (fun n => SymTensorPower 𝕜 E n) 2 N).toLinearMap) 0
    ⟨_, rfl⟩

/-- **The finite-particle subspace is dense** in the boson Fock space (Reed & Simon II,
§X.7: `F₀` is dense in `F_s`): every `lp`-element is the sum of its single-sector
components, and the partial sums are finite-particle vectors. This density is what will
make the finite-particle domain a legitimate common core. -/
theorem dense_finiteParticle : Dense (finiteParticle 𝕜 E : Set (BosonFock 𝕜 E)) := by
  intro f
  refine mem_closure_of_tendsto
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) f)
    (Filter.Eventually.of_forall fun s => Submodule.sum_mem _ fun N _ => ?_)
  exact le_iSup (fun N => LinearMap.range
      (lp.singleContinuousLinearMap 𝕜 (fun n => SymTensorPower 𝕜 E n) 2 N).toLinearMap) N
    ⟨f N, rfl⟩

end BosonFock

end QFT
