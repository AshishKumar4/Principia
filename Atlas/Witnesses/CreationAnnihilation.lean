import Atlas.Specs.QFT.CreationAnnihilation
import Atlas.Witnesses.FockSpace

/-!
# Witnesses — creation and annihilation operators (P2.2, slice 2)

Non-vacuity witnesses for `Atlas/Specs/QFT/CreationAnnihilation.lean`. The frozen spec's
target statements `CreationAnnihilationAdjoint`, `CCROnDomain`, … are `Prop`s whose proofs
are future blueprint nodes; what is checked here is that the *definitions they are about*
compute the values the sources predict, so that those targets are not statements about a
degenerate operator.

The one thing that can silently go wrong in this construction is the placement of the `√`
factors (spec docstring, "Where the `√` factors live — THE trap"). Every witness below is
chosen to be sensitive to it.

* **Roundtrips.** `a(f) a†(g) Ω = ⟪f, g⟫ Ω` (`annihilation_creation_vacuum`, sector
  `0 → 1 → 0`) and the decisive `a(f) a†(g) |h⟩ = ⟪f, g⟫ |h⟩ + ⟪f, h⟫ |g⟩`
  (`annihilation_creation_oneParticle`, sector `1 → 2 → 1`). The second one multiplies
  `√2` (creation, `1 → 2`), `√2` (annihilation, `2 → 1`) and the symmetrizer's `(2!)⁻¹`
  into exactly `1`; any other convention for the `√`s changes the answer.
* **CCR instances.** The body of the frozen `CCROnDomain` at `x = Ω` (`ccr_vacuum`) and at
  `x = |h⟩` (`ccr_oneParticle`), verbatim in the spec's shape — so the target statement has
  kernel-checked instances beyond the trivial sector, pinning operator order, sign, and the
  side the conjugation falls on. Expected-false: `not_ccr_sign_reversed` refutes the
  sign-flipped commutator, so the frozen statement is not one of a pair of interchangeable
  conventions.
* **Adjointness anchor.** `⟪|f⟩, |g⟩⟫ = ⟪f, g⟫` and `⟪a†(f) Ω, |g⟩⟫ = ⟪Ω, a(f) |g⟩⟫` — the
  `IsFormalAdjoint` relation of the frozen `CreationAnnihilationAdjoint` on the anchor
  vectors, with no stray conjugate.
* **Bose enhancement — the physical signature.** `‖a†(f) a†(f) Ω‖² = 2 ‖f‖⁴` for a repeated
  mode against `‖a†(e₀) a†(e₁) Ω‖² = 1` for two orthogonal modes: the factor `2 = 2!` that
  distinguishes bosons from distinguishable particles, obtained end-to-end from the frozen
  definitions. This is the `n = 2` case of the `√(n!)` normalization of occupation-number
  states (Reed & Simon II, §X.7).
* **Numerology on `E₂`.** `a(e₀) a†(e₀) |e₁⟩ = |e₁⟩` versus `a(e₀) a†(e₀) |e₀⟩ = 2 |e₀⟩` —
  the `n̂ + 1` eigenvalue seen concretely, with the expected-false that the parallel case is
  *not* the orthogonal one. And `a(f) a†(f) Ω = 2 Ω ≠ Ω` for `‖f‖² = 2`, which pins the
  inner-product factor against any scaling convention.

Import discipline (spec module docstring, "Scope discipline"): this file opens the scoped
`PiTensorProduct.InnerNorm` instances and replicates the spec's `assert_not_exists` guard,
so it can never acquire Mathlib's projective-seminorm instances and form a norm diamond
against the ℓ² cross norm baked into `HilbertTensorPower`.

Domain bookkeeping: the operators are `LinearPMap`s, so each application carries its
finite-particle membership witness (spec docstring, "No `LinearPMap` composition"). The
statements below are written with those witnesses inline rather than behind abbreviations,
so that they can be read against the frozen spec without unfolding anything.
-/

assert_not_exists PiTensorProduct.projectiveSeminorm

noncomputable section

namespace Atlas.Witnesses.CreationAnnihilation

open PiTensorProduct QFT UniformSpace Equiv
open scoped TensorProduct PiTensorProduct.InnerNorm Nat ENNReal

/-! ### Roundtrips: where the `√` factors have to cancel -/

section General

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The `0 → 1 → 0` roundtrip**: `a(f) a†(g) Ω = ⟪f, g⟫ Ω` (Reed & Simon II, §X.7).
Chains the spec's two vacuum anchors `creationPMap_vacuum` and
`annihilationPMap_oneParticle`; the `n = 0` sanity check advertised in the spec's
"Where the `√` factors live" note. -/
theorem annihilation_creation_vacuum (f g : E) :
    annihilationPMap 𝕜 E f
      ⟨creationPMap 𝕜 E g ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
        creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩ =
      inner 𝕜 f g • BosonFock.vacuum 𝕜 E :=
  (congrArg (fun x : BosonFock.finiteParticle 𝕜 E => annihilationPMap 𝕜 E f x)
      (Subtype.ext (creationPMap_vacuum 𝕜 E g))).trans
    (annihilationPMap_oneParticle 𝕜 E f g)

/-- `a†(g) a(f) Ω = 0`: the vacuum is annihilated, and creation cannot resurrect it. The
second term of the `x = Ω` instance of `CCROnDomain`. -/
theorem creation_annihilation_vacuum (f g : E) :
    creationPMap 𝕜 E g
      ⟨annihilationPMap 𝕜 E f
          ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
        annihilationPMap_apply_mem_finiteParticle 𝕜 E f _⟩ = 0 :=
  (congrArg (fun x : BosonFock.finiteParticle 𝕜 E => creationPMap 𝕜 E g x)
      (Subtype.ext (annihilationPMap_vacuum 𝕜 E f))).trans
    (creationPMap 𝕜 E g).map_zero

/-- **The `1 → 2 → 1` roundtrip — the decisive one**:
`a(f) a†(g) |h⟩ = ⟪f, g⟫ |h⟩ + ⟪f, h⟫ |g⟩` (Reed & Simon II, §X.7). Exercises `√2`
(creation, `1 → 2`), `√2` (annihilation, `2 → 1`) and the symmetrizer's `(2!)⁻¹`
normalization at once: the scalar `√2 · √2 · ½ = 1` is exactly where a wrong convention
for the `√` factors fails to cancel. The second summand is the exchange term that makes
the state bosonic. -/
theorem annihilation_creation_oneParticle (f g h : E) :
    annihilationPMap 𝕜 E f
      ⟨creationPMap 𝕜 E g ⟨BosonFock.oneParticle 𝕜 E h,
          BosonFock.oneParticle_mem_finiteParticle 𝕜 E h⟩,
        creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩ =
      inner 𝕜 f g • BosonFock.oneParticle 𝕜 E h +
        inner 𝕜 f h • BosonFock.oneParticle 𝕜 E g := by
  have hcr := creationPMap_oneParticle 𝕜 E g h
  have hsym : symmetrizer 𝕜 E 2 (tprod 𝕜 ![g, h]) =
      (2 : 𝕜)⁻¹ • (tprod 𝕜 ![g, h] + tprod 𝕜 ![h, g]) := by
    simpa using FockSpace.symmetrizer_tprod_two 𝕜 E ![g, h]
  have ht1 : Fin.tail ![g, h] = ![h] := by
    funext i
    fin_cases i
    rfl
  have ht2 : Fin.tail ![h, g] = ![g] := by
    funext i
    fin_cases i
    rfl
  have hc1 : contractAux 𝕜 E 1 f (tprod 𝕜 ![g, h]) = inner 𝕜 f g • tprod 𝕜 ![h] := by
    rw [contractAux_tprod]
    simp only [Matrix.cons_val_zero]
    rw [ht1]
  have hc2 : contractAux 𝕜 E 1 f (tprod 𝕜 ![h, g]) = inner 𝕜 f h • tprod 𝕜 ![g] := by
    rw [contractAux_tprod]
    simp only [Matrix.cons_val_zero]
    rw [ht2]
  have hS1 : ∀ y : ⨂[𝕜]^1 E,
      symmetrizerL 𝕜 E 1 (y : HilbertTensorPower 𝕜 E 1) =
        (y : HilbertTensorPower 𝕜 E 1) := fun y => by
    rw [symmetrizerL_coe, symmetrizer_eq_id 𝕜 E 1 le_rfl, LinearMap.id_coe, id_eq]
  refine lp.ext (funext fun m => ?_)
  rw [annihilationPMap_apply]
  have hcomp : ∀ k, ((⟨creationPMap 𝕜 E g ⟨BosonFock.oneParticle 𝕜 E h,
      BosonFock.oneParticle_mem_finiteParticle 𝕜 E h⟩,
        creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩ :
          BosonFock.finiteParticle 𝕜 E) : BosonFock 𝕜 E) k =
      (lp.single 2 2
        ⟨(Real.sqrt 2 : 𝕜) • symmetrizerL 𝕜 E 2
            ((tprod 𝕜 ![g, h] : ⨂[𝕜]^2 E) : HilbertTensorPower 𝕜 E 2),
          Submodule.smul_mem _ _ ⟨_, rfl⟩⟩ : BosonFock 𝕜 E) k := by
    intro k
    exact congrFun (congrArg _ hcr) k
  rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, lp.coeFn_smul, Pi.smul_apply,
    Pi.smul_apply]
  match m with
  | 0 =>
    rw [hcomp (0 + 1), lp.single_apply_ne 2 2 _ (by omega : (0 + 1 : ℕ) ≠ 2), map_zero,
      BosonFock.oneParticle_apply_ne 𝕜 E h (by omega : (0 : ℕ) ≠ 1),
      BosonFock.oneParticle_apply_ne 𝕜 E g (by omega : (0 : ℕ) ≠ 1),
      smul_zero, smul_zero, add_zero]
  | 1 =>
    rw [hcomp (1 + 1),
      show ((lp.single 2 2 (⟨(Real.sqrt 2 : 𝕜) • symmetrizerL 𝕜 E 2
          ((tprod 𝕜 ![g, h] : ⨂[𝕜]^2 E) : HilbertTensorPower 𝕜 E 2),
            Submodule.smul_mem _ _ ⟨_, rfl⟩⟩) : BosonFock 𝕜 E)) (1 + 1) = _ from
        lp.single_apply_self 2 2 _,
      BosonFock.oneParticle_apply_one, BosonFock.oneParticle_apply_one]
    refine Subtype.ext ?_
    rw [annihilationSector_apply_coe]
    simp only [Nat.cast_one, Submodule.coe_smul, Submodule.coe_add, map_smul, map_add,
      symmetrizerL_coe, hsym, Completion.coe_smul, Completion.coe_add, contractL_coe,
      hc1, hc2, hS1, smul_add]
    have hkey : ((Real.sqrt (1 + 1) : ℝ) : 𝕜) * ((Real.sqrt 2 : ℝ) : 𝕜) = 2 := by
      rw [← RCLike.ofReal_mul, show Real.sqrt (1 + 1) = Real.sqrt 2 by norm_num,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_cast
    match_scalars
    · linear_combination ((2 : 𝕜)⁻¹ * inner 𝕜 f g) * hkey
    · linear_combination ((2 : 𝕜)⁻¹ * inner 𝕜 f h) * hkey
  | m + 2 =>
    rw [hcomp (m + 2 + 1), lp.single_apply_ne 2 2 _ (by omega : (m + 2 + 1 : ℕ) ≠ 2),
      map_zero,
      BosonFock.oneParticle_apply_ne 𝕜 E h (by omega : (m + 2 : ℕ) ≠ 1),
      BosonFock.oneParticle_apply_ne 𝕜 E g (by omega : (m + 2 : ℕ) ≠ 1),
      smul_zero, smul_zero, add_zero]

/-- `a†(g) a(f) |h⟩ = ⟪f, h⟫ |g⟩`: annihilating the one particle and creating another.
The second term of the `x = |h⟩` instance of `CCROnDomain`. -/
theorem creation_annihilation_oneParticle (f g h : E) :
    creationPMap 𝕜 E g
      ⟨annihilationPMap 𝕜 E f ⟨BosonFock.oneParticle 𝕜 E h,
          BosonFock.oneParticle_mem_finiteParticle 𝕜 E h⟩,
        annihilationPMap_apply_mem_finiteParticle 𝕜 E f _⟩ =
      inner 𝕜 f h • BosonFock.oneParticle 𝕜 E g := by
  have hx : (⟨annihilationPMap 𝕜 E f ⟨BosonFock.oneParticle 𝕜 E h,
      BosonFock.oneParticle_mem_finiteParticle 𝕜 E h⟩,
        annihilationPMap_apply_mem_finiteParticle 𝕜 E f _⟩ :
          BosonFock.finiteParticle 𝕜 E) =
      inner 𝕜 f h • ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩ :=
    Subtype.ext (annihilationPMap_oneParticle 𝕜 E f h)
  exact (congrArg (fun x : BosonFock.finiteParticle 𝕜 E => creationPMap 𝕜 E g x) hx).trans
    (((creationPMap 𝕜 E g).toFun.map_smul _ _).trans
      (congrArg (fun z => inner 𝕜 f h • z) (creationPMap_vacuum 𝕜 E g)))

/-! ### Instances of the frozen `CCROnDomain` target

The two statements below are the body of `QFT.CCROnDomain` at `x = Ω` and at `x = |h⟩`,
written out verbatim in the spec's shape. -/

/-- **The CCR at the vacuum**: `a(f) a†(g) Ω - a†(g) a(f) Ω = ⟪f, g⟫ Ω`. -/
theorem ccr_vacuum (f g : E) :
    annihilationPMap 𝕜 E f
        ⟨creationPMap 𝕜 E g
            ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
          creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩ -
      creationPMap 𝕜 E g
        ⟨annihilationPMap 𝕜 E f
            ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
          annihilationPMap_apply_mem_finiteParticle 𝕜 E f _⟩ =
      inner 𝕜 f g • BosonFock.vacuum 𝕜 E := by
  rw [annihilation_creation_vacuum, creation_annihilation_vacuum, sub_zero]

/-- The commutator with the two orders exchanged evaluates to `-⟪f, g⟫ Ω` at the vacuum —
the value the sign-flipped CCR would have to reproduce (see `not_ccr_sign_reversed`). -/
theorem ccr_vacuum_reversed (f g : E) :
    creationPMap 𝕜 E g
        ⟨annihilationPMap 𝕜 E f
            ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
          annihilationPMap_apply_mem_finiteParticle 𝕜 E f _⟩ -
      annihilationPMap 𝕜 E f
        ⟨creationPMap 𝕜 E g
            ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
          creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩ =
      -(inner 𝕜 f g • BosonFock.vacuum 𝕜 E) := by
  rw [annihilation_creation_vacuum, creation_annihilation_vacuum, zero_sub]

/-- **The CCR on a one-particle state**: `a(f) a†(g) |h⟩ - a†(g) a(f) |h⟩ = ⟪f, g⟫ |h⟩`.
The exchange terms `⟪f, h⟫ |g⟩` cancel between the two orders — the first instance of the
frozen `CCROnDomain` that sees the `√2`s, so it pins the operator order, the sign, and the
slot the conjugation falls on. -/
theorem ccr_oneParticle (f g h : E) :
    annihilationPMap 𝕜 E f
        ⟨creationPMap 𝕜 E g ⟨BosonFock.oneParticle 𝕜 E h,
            BosonFock.oneParticle_mem_finiteParticle 𝕜 E h⟩,
          creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩ -
      creationPMap 𝕜 E g
        ⟨annihilationPMap 𝕜 E f ⟨BosonFock.oneParticle 𝕜 E h,
            BosonFock.oneParticle_mem_finiteParticle 𝕜 E h⟩,
          annihilationPMap_apply_mem_finiteParticle 𝕜 E f _⟩ =
      inner 𝕜 f g • BosonFock.oneParticle 𝕜 E h := by
  rw [annihilation_creation_oneParticle, creation_annihilation_oneParticle]
  abel

/-! ### The adjointness anchor -/

/-- The one-particle embedding is isometric on inner products: `⟪|f⟩, |g⟩⟫ = ⟪f, g⟫`. -/
theorem inner_oneParticle_oneParticle (f g : E) :
    inner 𝕜 (BosonFock.oneParticle 𝕜 E f) (BosonFock.oneParticle 𝕜 E g) =
      inner 𝕜 f g := by
  rw [BosonFock.oneParticle, BosonFock.oneParticle, lp.inner_single_left,
    lp.single_apply_self]
  show inner 𝕜 ((tprod 𝕜 ![f] : ⨂[𝕜]^1 E) : HilbertTensorPower 𝕜 E 1)
      ((tprod 𝕜 ![g] : ⨂[𝕜]^1 E) : HilbertTensorPower 𝕜 E 1) = inner 𝕜 f g
  rw [Completion.inner_coe, PiTensorProduct.inner_tprod]
  simp

/-- **The adjointness anchor**: `⟪a†(f) Ω, |g⟩⟫ = ⟪Ω, a(f) |g⟩⟫`, i.e. the
`IsFormalAdjoint` relation of the frozen `CreationAnnihilationAdjoint` holds on the anchor
vectors — with no stray conjugate on either side. -/
theorem inner_creation_vacuum_oneParticle (f g : E) :
    inner 𝕜 ((creationPMap 𝕜 E f
        ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩ : BosonFock 𝕜 E))
        (BosonFock.oneParticle 𝕜 E g) =
      inner 𝕜 (BosonFock.vacuum 𝕜 E)
        ((annihilationPMap 𝕜 E f
          ⟨BosonFock.oneParticle 𝕜 E g,
            BosonFock.oneParticle_mem_finiteParticle 𝕜 E g⟩ : BosonFock 𝕜 E)) := by
  rw [creationPMap_vacuum, annihilationPMap_oneParticle, inner_oneParticle_oneParticle,
    inner_smul_right, @inner_self_eq_norm_sq_to_K 𝕜, BosonFock.norm_vacuum]
  norm_num

/-! ### Two-particle states and the Bose enhancement factor -/

/-- The two-particle state built from the vacuum: `a†(f) a†(g) Ω = √2 S₂(f ⊗ g)` in
sector `2`. -/
theorem creation_creation_vacuum (f g : E) :
    creationPMap 𝕜 E f
      ⟨creationPMap 𝕜 E g ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
        creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩ =
      lp.single 2 2
        ⟨(Real.sqrt 2 : 𝕜) • symmetrizerL 𝕜 E 2
            ((tprod 𝕜 ![f, g] : ⨂[𝕜]^2 E) : HilbertTensorPower 𝕜 E 2),
          Submodule.smul_mem _ _ ⟨_, rfl⟩⟩ :=
  (congrArg (fun x : BosonFock.finiteParticle 𝕜 E => creationPMap 𝕜 E f x)
      (Subtype.ext (creationPMap_vacuum 𝕜 E g))).trans
    (creationPMap_oneParticle 𝕜 E f g)

/-- The norm of a two-particle state, reduced to the norm of the symmetrized tensor:
`‖a†(f) a†(g) Ω‖ = √2 ‖S₂(f ⊗ g)‖`. -/
theorem norm_creation_creation_vacuum (f g : E) :
    ‖creationPMap 𝕜 E f
      ⟨creationPMap 𝕜 E g ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
        creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩‖ =
      Real.sqrt 2 *
        ‖symmetrizerL 𝕜 E 2 ((tprod 𝕜 ![f, g] : ⨂[𝕜]^2 E) : HilbertTensorPower 𝕜 E 2)‖ := by
  rw [creation_creation_vacuum, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  show ‖(Real.sqrt 2 : 𝕜) •
      symmetrizerL 𝕜 E 2 ((tprod 𝕜 ![f, g] : ⨂[𝕜]^2 E) : HilbertTensorPower 𝕜 E 2)‖ = _
  rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg 2)]

/-- The squared norm of a two-particle state: `‖a†(f) a†(g) Ω‖² = 2 ‖S₂(f ⊗ g)‖²`. The
factor `2` is the creation operators' `√1 · √2`; what varies with `f` and `g` is the
symmetrized tensor, and that is where the Bose enhancement sits. -/
theorem norm_creation_creation_vacuum_sq (f g : E) :
    ‖creationPMap 𝕜 E f
      ⟨creationPMap 𝕜 E g ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
        creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩‖ ^ 2 =
      2 * ‖symmetrizerL 𝕜 E 2
          ((tprod 𝕜 ![f, g] : ⨂[𝕜]^2 E) : HilbertTensorPower 𝕜 E 2)‖ ^ 2 := by
  rw [norm_creation_creation_vacuum, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- A repeated pure tensor is already symmetric: `S₂(f ⊗ f) = f ⊗ f`. -/
theorem symmetrizer_tprod_two_diag (f : E) :
    symmetrizer 𝕜 E 2 (tprod 𝕜 ![f, f]) = tprod 𝕜 ![f, f] := by
  rw [FockSpace.symmetrizer_tprod_two]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  match_scalars
  norm_num

/-- **The Bose enhancement factor** — the physical signature of the whole construction:
putting two quanta into the *same* mode gives `‖a†(f) a†(f) Ω‖² = 2 ‖f‖⁴`, not `‖f‖⁴`. The
`2 = 2!` is the `n = 2` case of the `√(n!)` normalization of occupation-number states
(Reed & Simon II, §X.7); compare `norm_two_boson_distinct_sq` below, where two *different*
modes give `1`. Nothing here assumes any unproven target statement: the value is computed
from the frozen `creationPMap` alone. -/
theorem norm_creation_creation_vacuum_diag_sq (f : E) :
    ‖creationPMap 𝕜 E f
      ⟨creationPMap 𝕜 E f ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
        creationPMap_apply_mem_finiteParticle 𝕜 E f _⟩‖ ^ 2 = 2 * ‖f‖ ^ 4 := by
  rw [norm_creation_creation_vacuum_sq, symmetrizerL_coe, symmetrizer_tprod_two_diag,
    Completion.norm_coe, PiTensorProduct.norm_tprod]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end General

/-! ### Concrete numerology on `E₂ = ℂ²`

The general statements above are instantiated on the slice-1 model, where the standard
basis gives genuinely distinguishable modes. -/

section E₂

open Atlas.Witnesses.FockSpace

/-- **Orthogonal modes**: `a(e₀) a†(e₀) |e₁⟩ = |e₁⟩` — the prediction
`⟪e₀, e₀⟫ |e₁⟩ + ⟪e₀, e₁⟫ |e₀⟩` with the exchange term switched off. -/
example :
    annihilationPMap ℂ E₂ (e 0)
      ⟨creationPMap ℂ E₂ (e 0) ⟨BosonFock.oneParticle ℂ E₂ (e 1),
          BosonFock.oneParticle_mem_finiteParticle ℂ E₂ (e 1)⟩,
        creationPMap_apply_mem_finiteParticle ℂ E₂ (e 0) _⟩ =
      BosonFock.oneParticle ℂ E₂ (e 1) := by
  rw [annihilation_creation_oneParticle, inner_e_e, inner_e_e]
  norm_num

/-- **Parallel modes**: `a(e₀) a†(e₀) |e₀⟩ = 2 |e₀⟩` — the `n̂ + 1` eigenvalue, with the
exchange term switched on. -/
theorem annihilation_creation_oneParticle_diag :
    annihilationPMap ℂ E₂ (e 0)
      ⟨creationPMap ℂ E₂ (e 0) ⟨BosonFock.oneParticle ℂ E₂ (e 0),
          BosonFock.oneParticle_mem_finiteParticle ℂ E₂ (e 0)⟩,
        creationPMap_apply_mem_finiteParticle ℂ E₂ (e 0) _⟩ =
      (2 : ℂ) • BosonFock.oneParticle ℂ E₂ (e 0) := by
  rw [annihilation_creation_oneParticle, inner_e_e]
  norm_num [two_smul]

/-- **Expected-false**: the parallel case does *not* reproduce the orthogonal one — the
eigenvalue is `2`, not `1`. If the exchange term of `annihilation_creation_oneParticle`
were dropped (or the `√`s mis-assigned so that it cancelled), this would be an equality. -/
theorem annihilation_creation_oneParticle_diag_ne :
    annihilationPMap ℂ E₂ (e 0)
      ⟨creationPMap ℂ E₂ (e 0) ⟨BosonFock.oneParticle ℂ E₂ (e 0),
          BosonFock.oneParticle_mem_finiteParticle ℂ E₂ (e 0)⟩,
        creationPMap_apply_mem_finiteParticle ℂ E₂ (e 0) _⟩ ≠
      BosonFock.oneParticle ℂ E₂ (e 0) := by
  rw [annihilation_creation_oneParticle_diag]
  intro hcon
  have hnorm := congrArg norm hcon
  rw [norm_smul, BosonFock.norm_oneParticle, norm_e] at hnorm
  norm_num at hnorm

/-- `⟪e₀ + e₁, e₀ + e₁⟫ = 2`: the model's non-unit vector, used to pin the inner-product
factor of the roundtrip against rescaling. -/
theorem inner_eSum_eSum : inner ℂ (e 0 + e 1) (e 0 + e 1) = (2 : ℂ) := by
  simp only [inner_add_left, inner_add_right, inner_e_e]
  norm_num

/-- **Expected-false — the roundtrip factor is the inner product, not `1`**: for
`‖f‖² = 2` the vacuum roundtrip returns `2 Ω`, so `a(f) a†(f) Ω ≠ Ω`. Any convention that
normalized the `√` factors against `‖f‖` rather than against the sector index would make
this an equality. -/
theorem annihilation_creation_vacuum_ne :
    annihilationPMap ℂ E₂ (e 0 + e 1)
      ⟨creationPMap ℂ E₂ (e 0 + e 1)
          ⟨BosonFock.vacuum ℂ E₂, BosonFock.vacuum_mem_finiteParticle ℂ E₂⟩,
        creationPMap_apply_mem_finiteParticle ℂ E₂ (e 0 + e 1) _⟩ ≠
      BosonFock.vacuum ℂ E₂ := by
  rw [annihilation_creation_vacuum, inner_eSum_eSum]
  intro hcon
  have hnorm := congrArg norm hcon
  rw [norm_smul, BosonFock.norm_vacuum] at hnorm
  norm_num at hnorm

/-- **Expected-false — the CCR sign is not a convention**: the commutator with the two
orders exchanged, `[a†(g), a(f)] = ⟪f, g⟫ • 1`, is refutable already at the vacuum, where
it would give `-⟪f, g⟫ Ω = ⟪f, g⟫ Ω`. So the frozen `CCROnDomain` picks out one of two
genuinely different statements. -/
theorem not_ccr_sign_reversed :
    ¬ ∀ (f g : E₂) (x : BosonFock.finiteParticle ℂ E₂),
        creationPMap ℂ E₂ g
            ⟨annihilationPMap ℂ E₂ f x,
              annihilationPMap_apply_mem_finiteParticle ℂ E₂ f x⟩ -
          annihilationPMap ℂ E₂ f
            ⟨creationPMap ℂ E₂ g x, creationPMap_apply_mem_finiteParticle ℂ E₂ g x⟩ =
        inner ℂ f g • (x : BosonFock ℂ E₂) := by
  intro hccr
  have he : inner ℂ (e 0) (e 0) = (1 : ℂ) := by rw [inner_e_e]; simp
  have h0 : BosonFock.vacuum ℂ E₂ = -BosonFock.vacuum ℂ E₂ := by
    have h := (hccr (e 0) (e 0)
      ⟨BosonFock.vacuum ℂ E₂, BosonFock.vacuum_mem_finiteParticle ℂ E₂⟩).symm.trans
        (ccr_vacuum_reversed ℂ E₂ (e 0) (e 0))
    rwa [he, one_smul] at h
  have h1 : inner ℂ (BosonFock.vacuum ℂ E₂) (BosonFock.vacuum ℂ E₂) =
      inner ℂ (BosonFock.vacuum ℂ E₂) (-BosonFock.vacuum ℂ E₂) := by rw [← h0]
  rw [inner_neg_right, @inner_self_eq_norm_sq_to_K ℂ, BosonFock.norm_vacuum] at h1
  norm_num at h1

/-! #### The Bose enhancement, concretely -/

/-- The symmetrized tensor of two distinct modes has squared norm `½` (slice-1 witness
`norm_symmetrizer_e₀₁_sq`), read on the completed layer. -/
theorem norm_symmetrizerL_e₀₁_sq :
    ‖symmetrizerL ℂ E₂ 2
        ((tprod ℂ ![e 0, e 1] : ⨂[ℂ]^2 E₂) : HilbertTensorPower ℂ E₂ 2)‖ ^ 2 = 1 / 2 := by
  rw [show (tprod ℂ ![e 0, e 1] : ⨂[ℂ]^2 E₂) = e₀₁ from rfl, symmetrizerL_coe,
    Completion.norm_coe]
  exact norm_symmetrizer_e₀₁_sq

/-- **Two quanta in the same mode**: `‖a†(e₀) a†(e₀) Ω‖² = 2`. -/
theorem norm_two_boson_same_sq :
    ‖creationPMap ℂ E₂ (e 0)
      ⟨creationPMap ℂ E₂ (e 0)
          ⟨BosonFock.vacuum ℂ E₂, BosonFock.vacuum_mem_finiteParticle ℂ E₂⟩,
        creationPMap_apply_mem_finiteParticle ℂ E₂ (e 0) _⟩‖ ^ 2 = 2 := by
  rw [norm_creation_creation_vacuum_diag_sq, norm_e]
  norm_num

/-- **Two quanta in distinct modes**: `‖a†(e₀) a†(e₁) Ω‖² = 1`. Against
`norm_two_boson_same_sq` this is the Bose enhancement factor `2 = 2!` — the same two
creation operators, differing only in whether the modes coincide. Here the `√2` of the
creation operator and the `½` of the symmetrizer cancel; in the repeated-mode case they do
not, and that surviving `2` is the physics. -/
theorem norm_two_boson_distinct_sq :
    ‖creationPMap ℂ E₂ (e 0)
      ⟨creationPMap ℂ E₂ (e 1)
          ⟨BosonFock.vacuum ℂ E₂, BosonFock.vacuum_mem_finiteParticle ℂ E₂⟩,
        creationPMap_apply_mem_finiteParticle ℂ E₂ (e 1) _⟩‖ ^ 2 = 1 := by
  rw [norm_creation_creation_vacuum_sq, norm_symmetrizerL_e₀₁_sq]
  norm_num

/-- **Expected-false**: the two are not equal, so the enhancement is a real effect of the
frozen definitions and not an artifact of how the norm was computed. -/
example :
    ‖creationPMap ℂ E₂ (e 0)
        ⟨creationPMap ℂ E₂ (e 0)
            ⟨BosonFock.vacuum ℂ E₂, BosonFock.vacuum_mem_finiteParticle ℂ E₂⟩,
          creationPMap_apply_mem_finiteParticle ℂ E₂ (e 0) _⟩‖ ^ 2 ≠
      ‖creationPMap ℂ E₂ (e 0)
        ⟨creationPMap ℂ E₂ (e 1)
            ⟨BosonFock.vacuum ℂ E₂, BosonFock.vacuum_mem_finiteParticle ℂ E₂⟩,
          creationPMap_apply_mem_finiteParticle ℂ E₂ (e 1) _⟩‖ ^ 2 := by
  rw [norm_two_boson_same_sq, norm_two_boson_distinct_sq]
  norm_num

end E₂

end Atlas.Witnesses.CreationAnnihilation

end
