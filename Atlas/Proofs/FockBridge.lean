-- FROZEN-BY-IMPORT (P2.2 slice 2 spec draft, 2026-08-07): this file is imported by
-- Atlas/Specs/QFT/CreationAnnihilation.lean, so its definitions carry frozen spec
-- meaning. Grind sessions must not edit it; changes require [spec-review].
-- NOTE for the orchestrator: the commit-msg hook's frozen-by-import list does not yet
-- name this file; extend it (guard-file change) when freezing the slice-2 spec.
import Atlas.Specs.QFT.FockSpace

/-!
# Fock-space bridge API (P2.2 support layer)

General-purpose, kernel-checked API over the *frozen* slice-1 spec
`Atlas/Specs/QFT/FockSpace.lean`. No spec content: everything here is provable
convenience API about the frozen definitions, recorded outside the spec file so that
spec slices stay pure statements-plus-definition-pinning. Three groups:

* **Instance-friction bridges.** On `⨂[𝕜]^n E` the globally-found `Inner` instance is
  `PiTensorProduct.instInner` while the norm comes from the scoped
  `PiTensorProduct.InnerNorm` core (see the design note in
  `Atlas/Proofs/PiTensorInner.lean` and §"fragility" of the slice-1 witness file);
  on the completion the inner product is the extension provided by
  `UniformSpace.Completion.innerProductSpace`. `inner_hilbertTensorPower_coe` pins the
  round trip: the completed inner product restricted to the dense algebraic image *is*
  the bundled `innerAux` pairing. Downstream computations should rewrite with it (or
  with `UniformSpace.Completion.inner_coe` + `PiTensorProduct.inner_def`) instead of
  unfolding instances.
* **Self-adjointness of the symmetrizer** (`inner_symmetrizer_left`,
  `inner_symmetrizerL_left`): the group average `(n!)⁻¹ ∑ σ` is self-adjoint for the
  P2.1f inner product, since each `reindex σ` is unitary with adjoint `reindex σ⁻¹` and
  the sum over the group absorbs inversion. This upgrades `SymTensorPower` from "range
  of a bounded idempotent" to "range of an orthogonal projection" — the first item on
  the slice-1 "future spec items" list — and is what makes the Bratteli–Robinson
  compressed form of the annihilation operator (P2.2 slice 2) formally adjoint to the
  creation operator.
* **The finite-particle characterization** (`BosonFock.mem_finiteParticle_iff`):
  membership in the slice-1 `⨆ N, range (lp.single N)` definition is equivalent to
  "all components vanish beyond some `N`". This is the working form used by the
  slice-2 operator layer to build `LinearPMap`s on the finite-particle domain and to
  prove that creation/annihilation preserve it.

Import discipline (slice-1 spec module docstring, "Scope discipline"): this file opens
the scoped `PiTensorProduct.InnerNorm` instances and replicates the spec's
`assert_not_exists` guard, so it can never acquire Mathlib's projective-seminorm
instances and form a norm diamond against the ℓ² cross norm baked into
`HilbertTensorPower`.
-/

assert_not_exists PiTensorProduct.projectiveSeminorm

noncomputable section

namespace QFT

open PiTensorProduct UniformSpace Equiv
open scoped TensorProduct PiTensorProduct.InnerNorm Nat ENNReal

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (n : ℕ)

/-! ### Instance-friction bridge -/

/-- **Bridge lemma**: the inner product of the completed Hilbert tensor power,
restricted to the dense algebraic image, is the bundled `PiTensorProduct.innerAux`
pairing of P2.1e. This is the one identity connecting the three faces of the same
pairing — the global `PiTensorProduct.instInner`, the scoped `InnerNorm` core, and the
completion's extended inner product — so computations never unfold instances. -/
theorem inner_hilbertTensorPower_coe (x y : ⨂[𝕜]^n E) :
    inner 𝕜 (x : HilbertTensorPower 𝕜 E n) (y : HilbertTensorPower 𝕜 E n) =
      innerAux 𝕜 x y := by
  rw [Completion.inner_coe, inner_def]

/-! ### The symmetrizer is self-adjoint -/

/-- Each permutation acts unitarily with inverse `σ⁻¹`:
`⟪reindex σ x, y⟫ = ⟪x, reindex σ⁻¹ y⟫`. -/
theorem inner_reindex_left (σ : Perm (Fin n)) (x y : ⨂[𝕜]^n E) :
    inner 𝕜 (reindex 𝕜 (fun _ ↦ E) σ x) y =
      inner 𝕜 x (reindex 𝕜 (fun _ ↦ E) σ⁻¹ y) := by
  conv_lhs => rw [← inner_reindex_reindex σ⁻¹ (reindex 𝕜 (fun _ ↦ E) σ x) y]
  congr 1
  rw [← LinearEquiv.trans_apply, reindex_trans, ← Perm.mul_def, inv_mul_cancel,
    Perm.one_def, reindex_refl]
  rfl

/-- **The algebraic symmetrizer is self-adjoint** for the P2.1f inner product:
`⟪Sₙ x, y⟫ = ⟪x, Sₙ y⟫`. Averaging the unitaries `reindex σ` over the group absorbs
the inversion `σ ↦ σ⁻¹` coming from taking adjoints (Reed & Simon I, §II.4, Example 2:
`Sₙ` is an orthogonal projection; Bratteli & Robinson II, §5.2, the projector `P₊`). -/
theorem inner_symmetrizer_left (x y : ⨂[𝕜]^n E) :
    inner 𝕜 (symmetrizer 𝕜 E n x) y = inner 𝕜 x (symmetrizer 𝕜 E n y) := by
  rw [symmetrizer_apply, symmetrizer_apply, inner_smul_left, inner_smul_right,
    sum_inner, inner_sum, map_inv₀, map_natCast]
  refine congrArg (fun t => ((n ! : 𝕜))⁻¹ * t) ?_
  rw [Finset.sum_congr rfl fun σ _ => inner_reindex_left 𝕜 E n σ x y]
  exact Equiv.sum_comp (Equiv.inv (Perm (Fin n)))
    fun σ => inner 𝕜 x (reindex 𝕜 (fun _ ↦ E) σ y)

/-- **The completed symmetrizer is self-adjoint**: `SymTensorPower 𝕜 E n` is the range
of an orthogonal projection, not merely of a bounded idempotent. Transfer of
`inner_symmetrizer_left` to the completion by density. -/
theorem inner_symmetrizerL_left (x y : HilbertTensorPower 𝕜 E n) :
    inner 𝕜 (symmetrizerL 𝕜 E n x) y = inner 𝕜 x (symmetrizerL 𝕜 E n y) := by
  induction x, y using Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq
      (Continuous.inner ((symmetrizerL 𝕜 E n).continuous.comp continuous_fst)
        continuous_snd)
      (Continuous.inner continuous_fst
        ((symmetrizerL 𝕜 E n).continuous.comp continuous_snd))
  | ih a b =>
    rw [symmetrizerL_coe, symmetrizerL_coe, Completion.inner_coe, Completion.inner_coe,
      inner_symmetrizer_left]

/-! ### The finite-particle characterization -/

namespace BosonFock

/-- **Membership in the finite-particle subspace** is having only finitely many
nonzero sectors: `x ∈ F₀` iff all components of `x` vanish beyond some `N` (Reed &
Simon II, §X.7: `F₀ = {ψ : ψ⁽ⁿ⁾ = 0 for all but finitely many n}`). The working form
of the slice-1 definition `⨆ N, range (lp.single N)` for the P2.2 operator layer. -/
theorem mem_finiteParticle_iff {x : BosonFock 𝕜 E} :
    x ∈ finiteParticle 𝕜 E ↔ ∃ N, ∀ n, N < n → x n = 0 := by
  constructor
  · intro hx
    refine Submodule.iSup_induction
      (motive := fun y : BosonFock 𝕜 E => ∃ N, ∀ n, N < n → y n = 0) _ hx
      (fun N y hy => ?_) ⟨0, fun n _ => rfl⟩ ?_
    · obtain ⟨ψ, rfl⟩ := hy
      exact ⟨N, fun n hn => by
        simp [lp.singleContinuousLinearMap_apply, lp.single_apply,
          Pi.single_eq_of_ne (Nat.ne_of_gt hn)]⟩
    · rintro y z ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
      refine ⟨max N₁ N₂, fun n hn => ?_⟩
      rw [lp.coeFn_add, Pi.add_apply, h₁ n (lt_of_le_of_lt (le_max_left _ _) hn),
        h₂ n (lt_of_le_of_lt (le_max_right _ _) hn), add_zero]
  · rintro ⟨N, hN⟩
    have hsum : x = ∑ k ∈ Finset.range (N + 1), lp.single 2 k (x k) := by
      refine lp.ext (funext fun m => ?_)
      rw [lp.coeFn_sum, Finset.sum_apply]
      simp only [lp.single_apply]
      rw [Finset.sum_pi_single]
      by_cases hm : m ∈ Finset.range (N + 1)
      · rw [if_pos hm]
      · rw [if_neg hm]
        exact hN m (by simpa [Nat.lt_succ_iff, not_le] using hm)
    rw [hsum]
    exact Submodule.sum_mem _ fun k _ =>
      le_iSup (fun N => LinearMap.range
          (lp.singleContinuousLinearMap 𝕜 (fun n => SymTensorPower 𝕜 E n) 2 N).toLinearMap)
        k ⟨x k, rfl⟩

end BosonFock

end QFT

end
