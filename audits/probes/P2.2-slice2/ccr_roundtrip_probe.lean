import Atlas

/-!
# P2.2 slice-2 kernel probes — the CCR `√`-roundtrip and its normalization

* **Node**: P2.2 slice 2 (creation/annihilation operators),
  `Atlas/Specs/QFT/CreationAnnihilation.lean`.
* **Original review**: 2026-08-07 (BLUEPRINT P2.2: "Slice 2 spec FROZEN 2026-08-07
  51f2ce3, a/a† as `LinearPMap`s with kernel-verified sqrt/CCR roundtrip"). The probe
  file of that review lived in a session-temporary scratchpad and was lost; this file
  is the X.3 backfill (`audits/README.md`), re-created 2026-08-23.
* **What it refutes**:
  1. the *sign-reversed CCR* — the commutator `[a†(g), a(f)] = ⟪f, g⟫ · 1`, i.e. the
     reading under which the frozen `CCROnDomain` is one of two interchangeable
     conventions (`probe_not_ccr_sign_reversed`);
  2. every *misplacement of the `√` factors* that would let the creation operators'
     `√1 · √2 = 2` cancel against the symmetrizer's `(2!)⁻¹ = ½` in the wrong place:
     the two-boson norms `2` (same mode) and `1` (distinct modes) are computed
     end-to-end, and they differ (`probe_bose_enhancement`);
  3. the *rescaled roundtrip* — a convention normalizing `a(f) a†(f)` against `‖f‖`
     rather than against the sector index, which would make `a(f) a†(f) Ω = Ω` for
     `‖f‖² = 2` (`probe_vacuum_roundtrip_ne`).

## What is checked, and how independently

Every statement is derived in this file from the frozen spec only
(`QFT.creationPMap_vacuum`, `QFT.annihilationPMap_vacuum`,
`QFT.annihilationPMap_oneParticle`, `QFT.creationPMap_oneParticle`,
`QFT.symmetrizer_tprod`, `QFT.BosonFock.norm_vacuum`); nothing is taken from
`Atlas/Witnesses/CreationAnnihilation.lean`, including the degree-`2` symmetrizer
closed form, which is re-enumerated here.

* `probe_annihilation_creation_vacuum` — the `0 → 1 → 0` roundtrip
  `a(f) a†(g) Ω = ⟪f, g⟫ Ω`;
* `probe_ccr_vacuum` / `probe_ccr_vacuum_reversed` — the frozen commutator at the
  vacuum, and the value the sign-flipped statement would need;
* `probe_norm_two_boson_distinct_sq` — **the `2 · ½ = 1` normalization pin**:
  `‖a†(e₀) a†(e₁) Ω‖² = 2 · ‖S₂(e₀ ⊗ e₁)‖² = 2 · ½ = 1`, with both factors computed
  here (the `2` from `√1 · √2` of the creation operators, the `½` from the
  symmetrizer);
* `probe_norm_two_boson_same_sq` — `‖a†(e₀) a†(e₀) Ω‖² = 2`, the Bose factor `2 = 2!`
  surviving when the modes coincide.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II: Fourier Analysis,
  Self-Adjointness* (1975), §X.7 (creation/annihilation operators on symmetric Fock
  space, the `√(n+1)` normalization, the CCR on the finite-particle domain).
* O. Bratteli, D. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*
  (1981), §5.2 (the same construction, CCR half `[a(f), a(g)] = 0`).

Theorem/section numbers are quoted from the source list of the frozen spec
`Atlas/Specs/QFT/CreationAnnihilation.lean`; they were not re-checked against the
printed editions in this backfill.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.2-slice2/` only;
compiles via `lake env lean audits/probes/P2.2-slice2/ccr_roundtrip_probe.lean`.
-/

assert_not_exists PiTensorProduct.projectiveSeminorm

noncomputable section

namespace P22Slice2Probe

open PiTensorProduct QFT UniformSpace
open scoped TensorProduct PiTensorProduct.InnerNorm ENNReal

/-! ## The roundtrips at the vacuum -/

section General

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The `0 → 1 → 0` roundtrip**: `a(f) a†(g) Ω = ⟪f, g⟫ Ω`. Chains the two frozen
vacuum anchors; the sector walk `0 → 1 → 0` carries `√1` twice, so the value is the
bare inner product. -/
theorem probe_annihilation_creation_vacuum (f g : E) :
    annihilationPMap 𝕜 E f
      ⟨creationPMap 𝕜 E g ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
        creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩ =
      inner 𝕜 f g • BosonFock.vacuum 𝕜 E :=
  (congrArg (fun x : BosonFock.finiteParticle 𝕜 E => annihilationPMap 𝕜 E f x)
      (Subtype.ext (creationPMap_vacuum 𝕜 E g))).trans
    (annihilationPMap_oneParticle 𝕜 E f g)

/-- `a†(g) a(f) Ω = 0`: the vacuum is annihilated, and creation cannot resurrect it. -/
theorem probe_creation_annihilation_vacuum (f g : E) :
    creationPMap 𝕜 E g
      ⟨annihilationPMap 𝕜 E f
          ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
        annihilationPMap_apply_mem_finiteParticle 𝕜 E f _⟩ = 0 :=
  (congrArg (fun x : BosonFock.finiteParticle 𝕜 E => creationPMap 𝕜 E g x)
      (Subtype.ext (annihilationPMap_vacuum 𝕜 E f))).trans
    (creationPMap 𝕜 E g).map_zero

/-- The body of the frozen `CCROnDomain` at `x = Ω`:
`a(f) a†(g) Ω - a†(g) a(f) Ω = ⟪f, g⟫ Ω`. -/
theorem probe_ccr_vacuum (f g : E) :
    annihilationPMap 𝕜 E f
        ⟨creationPMap 𝕜 E g
            ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
          creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩ -
      creationPMap 𝕜 E g
        ⟨annihilationPMap 𝕜 E f
            ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
          annihilationPMap_apply_mem_finiteParticle 𝕜 E f _⟩ =
      inner 𝕜 f g • BosonFock.vacuum 𝕜 E := by
  rw [probe_annihilation_creation_vacuum, probe_creation_annihilation_vacuum, sub_zero]

/-- The two orders exchanged give `-⟪f, g⟫ Ω` — the value a sign-flipped CCR would have
to reproduce. -/
theorem probe_ccr_vacuum_reversed (f g : E) :
    creationPMap 𝕜 E g
        ⟨annihilationPMap 𝕜 E f
            ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
          annihilationPMap_apply_mem_finiteParticle 𝕜 E f _⟩ -
      annihilationPMap 𝕜 E f
        ⟨creationPMap 𝕜 E g
            ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
          creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩ =
      -(inner 𝕜 f g • BosonFock.vacuum 𝕜 E) := by
  rw [probe_annihilation_creation_vacuum, probe_creation_annihilation_vacuum, zero_sub]

/-! ## Two-particle states: where the `√`s meet the symmetrizer -/

/-- `a†(f) a†(g) Ω = √2 · S₂(f ⊗ g)` in sector `2`, from the frozen vacuum and
one-particle anchors. -/
theorem probe_creation_creation_vacuum (f g : E) :
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

/-- `‖a†(f) a†(g) Ω‖ = √2 ‖S₂(f ⊗ g)‖`: the `ℓ²` norm of a single-sector vector. -/
theorem probe_norm_creation_creation_vacuum (f g : E) :
    ‖creationPMap 𝕜 E f
      ⟨creationPMap 𝕜 E g ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
        creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩‖ =
      Real.sqrt 2 *
        ‖symmetrizerL 𝕜 E 2 ((tprod 𝕜 ![f, g] : ⨂[𝕜]^2 E) : HilbertTensorPower 𝕜 E 2)‖ := by
  rw [probe_creation_creation_vacuum, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  show ‖(Real.sqrt 2 : 𝕜) •
      symmetrizerL 𝕜 E 2 ((tprod 𝕜 ![f, g] : ⨂[𝕜]^2 E) : HilbertTensorPower 𝕜 E 2)‖ = _
  rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg 2)]

/-- **The creation operators contribute exactly `2 = √1 · √2` to the squared norm**:
`‖a†(f) a†(g) Ω‖² = 2 ‖S₂(f ⊗ g)‖²`. Everything mode-dependent now sits in the
symmetrized tensor. -/
theorem probe_norm_creation_creation_vacuum_sq (f g : E) :
    ‖creationPMap 𝕜 E f
      ⟨creationPMap 𝕜 E g ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
        creationPMap_apply_mem_finiteParticle 𝕜 E g _⟩‖ ^ 2 =
      2 * ‖symmetrizerL 𝕜 E 2
          ((tprod 𝕜 ![f, g] : ⨂[𝕜]^2 E) : HilbertTensorPower 𝕜 E 2)‖ ^ 2 := by
  rw [probe_norm_creation_creation_vacuum, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The degree-`2` symmetrizer closed form, re-enumerated over `S₂` here (not imported
from the slice-1 witness): `S(x₀ ⊗ x₁) = ½(x₀ ⊗ x₁ + x₁ ⊗ x₀)`. -/
theorem probe_symmetrizer_tprod_two (x : Fin 2 → E) :
    symmetrizer 𝕜 E 2 (tprod 𝕜 x) = (2 : 𝕜)⁻¹ • (tprod 𝕜 x + tprod 𝕜 ![x 1, x 0]) := by
  rw [symmetrizer_tprod]
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
    decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
  have h1 : (fun i => x ((1 : Equiv.Perm (Fin 2)) i)) = x := rfl
  have h2 : (fun i => x (Equiv.swap 0 1 i)) = ![x 1, x 0] := by
    funext i
    fin_cases i <;> simp
  rw [h1, h2]
  norm_num [Nat.factorial]

/-- A repeated pure tensor is already symmetric: `S₂(f ⊗ f) = f ⊗ f`. Here the `½`
cancels against the two identical summands, so *nothing* offsets the creation
operators' `2`. -/
theorem probe_symmetrizer_tprod_two_diag (f : E) :
    symmetrizer 𝕜 E 2 (tprod 𝕜 ![f, f]) = tprod 𝕜 ![f, f] := by
  rw [probe_symmetrizer_tprod_two]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  match_scalars
  norm_num

/-- **Two quanta in the same mode**: `‖a†(f) a†(f) Ω‖² = 2 ‖f‖⁴`, the Bose factor
`2 = 2!` (Reed & Simon II, §X.7: the `√(n!)` normalization of occupation-number
states). -/
theorem probe_norm_creation_creation_vacuum_diag_sq (f : E) :
    ‖creationPMap 𝕜 E f
      ⟨creationPMap 𝕜 E f ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩,
        creationPMap_apply_mem_finiteParticle 𝕜 E f _⟩‖ ^ 2 = 2 * ‖f‖ ^ 4 := by
  rw [probe_norm_creation_creation_vacuum_sq, symmetrizerL_coe,
    probe_symmetrizer_tprod_two_diag, Completion.norm_coe, PiTensorProduct.norm_tprod]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end General

/-! ## The concrete model `E₂ = ℂ²` -/

section Model

/-- The probe's one-particle space: `ℂ²`, whose standard basis gives distinguishable
modes. -/
abbrev E₂ : Type := EuclideanSpace ℂ (Fin 2)

/-- The standard basis vectors `e₀, e₁`. -/
def e (i : Fin 2) : E₂ := EuclideanSpace.single i (1 : ℂ)

@[simp] theorem probe_norm_e (i : Fin 2) : ‖e i‖ = 1 := by simp [e]

theorem probe_inner_e_e (i j : Fin 2) :
    inner ℂ (e i) (e j) = if i = j then (1 : ℂ) else 0 := by
  have h := (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal
  rw [orthonormal_iff_ite] at h
  simpa [e, EuclideanSpace.basisFun_apply] using h i j

def t01 : ⨂[ℂ]^2 E₂ := tprod ℂ ![e 0, e 1]

def t10 : ⨂[ℂ]^2 E₂ := tprod ℂ ![e 1, e 0]

theorem probe_inner_t01_t01 : inner ℂ t01 t01 = (1 : ℂ) := by
  simp [t01, Fin.prod_univ_two]

theorem probe_inner_t10_t10 : inner ℂ t10 t10 = (1 : ℂ) := by
  simp [t10, Fin.prod_univ_two]

theorem probe_inner_t01_t10 : inner ℂ t01 t10 = (0 : ℂ) := by
  simp [t01, t10, Fin.prod_univ_two, probe_inner_e_e]

theorem probe_inner_t10_t01 : inner ℂ t10 t01 = (0 : ℂ) := by
  simp [t01, t10, Fin.prod_univ_two, probe_inner_e_e]

/-- `S₂(e₀ ⊗ e₁) = ½(e₀ ⊗ e₁ + e₁ ⊗ e₀)` on the model. -/
theorem probe_symmetrizer_t01 :
    symmetrizer ℂ E₂ 2 t01 = (2 : ℂ)⁻¹ • (t01 + t10) := by
  have h := probe_symmetrizer_tprod_two ℂ E₂ ![e 0, e 1]
  simpa [t01, t10] using h

/-- `⟪S₂(e₀ ⊗ e₁), S₂(e₀ ⊗ e₁)⟫ = ½` — the symmetrizer's half of the `2 · ½ = 1`
arithmetic. -/
theorem probe_inner_symmetrized_self :
    inner ℂ (symmetrizer ℂ E₂ 2 t01) (symmetrizer ℂ E₂ 2 t01) = (1 / 2 : ℂ) := by
  rw [probe_symmetrizer_t01, inner_def]
  simp only [map_smulₛₗ, map_add, LinearMap.smul_apply, LinearMap.add_apply, ← inner_def,
    probe_inner_t01_t01, probe_inner_t01_t10, probe_inner_t10_t01, probe_inner_t10_t10]
  norm_num [Complex.conj_ofNat]

theorem probe_norm_symmetrized_sq : ‖symmetrizer ℂ E₂ 2 t01‖ ^ 2 = 1 / 2 := by
  have h : ((‖symmetrizer ℂ E₂ 2 t01‖ : ℂ)) ^ 2 = (1 / 2 : ℂ) :=
    (inner_self_eq_norm_sq_to_K (symmetrizer ℂ E₂ 2 t01)).symm.trans
      probe_inner_symmetrized_self
  have h2 : ((‖symmetrizer ℂ E₂ 2 t01‖ ^ 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    push_cast
    exact h
  exact_mod_cast h2

/-- The same `½`, read on the completed layer where the creation operators live. -/
theorem probe_norm_symmetrizerL_t01_sq :
    ‖symmetrizerL ℂ E₂ 2
        ((tprod ℂ ![e 0, e 1] : ⨂[ℂ]^2 E₂) : HilbertTensorPower ℂ E₂ 2)‖ ^ 2 = 1 / 2 := by
  rw [show (tprod ℂ ![e 0, e 1] : ⨂[ℂ]^2 E₂) = t01 from rfl, symmetrizerL_coe,
    Completion.norm_coe]
  exact probe_norm_symmetrized_sq

/-- **THE `2 · ½ = 1` NORMALIZATION PIN**: `‖a†(e₀) a†(e₁) Ω‖² = 1`. The `2` is
`√1 · √2` from the two creation operators (`probe_norm_creation_creation_vacuum_sq`),
the `½` is the symmetrizer's `(2!)⁻¹` (`probe_norm_symmetrizerL_t01_sq`); they cancel
exactly. Any other placement of the `√` factors changes this number. -/
theorem probe_norm_two_boson_distinct_sq :
    ‖creationPMap ℂ E₂ (e 0)
      ⟨creationPMap ℂ E₂ (e 1)
          ⟨BosonFock.vacuum ℂ E₂, BosonFock.vacuum_mem_finiteParticle ℂ E₂⟩,
        creationPMap_apply_mem_finiteParticle ℂ E₂ (e 1) _⟩‖ ^ 2 = 1 := by
  rw [probe_norm_creation_creation_vacuum_sq, probe_norm_symmetrizerL_t01_sq]
  norm_num

/-- **Two quanta in the same mode**: `‖a†(e₀) a†(e₀) Ω‖² = 2`. Here the symmetrizer
contributes `1`, not `½`, so the creation operators' `2` survives. -/
theorem probe_norm_two_boson_same_sq :
    ‖creationPMap ℂ E₂ (e 0)
      ⟨creationPMap ℂ E₂ (e 0)
          ⟨BosonFock.vacuum ℂ E₂, BosonFock.vacuum_mem_finiteParticle ℂ E₂⟩,
        creationPMap_apply_mem_finiteParticle ℂ E₂ (e 0) _⟩‖ ^ 2 = 2 := by
  rw [probe_norm_creation_creation_vacuum_diag_sq, probe_norm_e]
  norm_num

/-- **The Bose enhancement is a real effect of the frozen definitions**: the same two
creation operators, differing only in whether the modes coincide, give `2` and `1`. A
`√`-convention under which the sector factors cancelled uniformly would equate them. -/
theorem probe_bose_enhancement :
    ‖creationPMap ℂ E₂ (e 0)
        ⟨creationPMap ℂ E₂ (e 0)
            ⟨BosonFock.vacuum ℂ E₂, BosonFock.vacuum_mem_finiteParticle ℂ E₂⟩,
          creationPMap_apply_mem_finiteParticle ℂ E₂ (e 0) _⟩‖ ^ 2 ≠
      ‖creationPMap ℂ E₂ (e 0)
        ⟨creationPMap ℂ E₂ (e 1)
            ⟨BosonFock.vacuum ℂ E₂, BosonFock.vacuum_mem_finiteParticle ℂ E₂⟩,
          creationPMap_apply_mem_finiteParticle ℂ E₂ (e 1) _⟩‖ ^ 2 := by
  rw [probe_norm_two_boson_same_sq, probe_norm_two_boson_distinct_sq]
  norm_num

/-! ## Refutations -/

theorem probe_inner_eSum_eSum : inner ℂ (e 0 + e 1) (e 0 + e 1) = (2 : ℂ) := by
  simp only [inner_add_left, inner_add_right, probe_inner_e_e]
  norm_num

/-- **The roundtrip factor is the inner product, not `1`**: for `‖f‖² = 2` the vacuum
roundtrip returns `2 Ω`, so `a(f) a†(f) Ω ≠ Ω`. A convention normalizing the `√`
factors against `‖f‖` instead of the sector index would make this an equality. -/
theorem probe_vacuum_roundtrip_ne :
    annihilationPMap ℂ E₂ (e 0 + e 1)
      ⟨creationPMap ℂ E₂ (e 0 + e 1)
          ⟨BosonFock.vacuum ℂ E₂, BosonFock.vacuum_mem_finiteParticle ℂ E₂⟩,
        creationPMap_apply_mem_finiteParticle ℂ E₂ (e 0 + e 1) _⟩ ≠
      BosonFock.vacuum ℂ E₂ := by
  rw [probe_annihilation_creation_vacuum, probe_inner_eSum_eSum]
  intro hcon
  have hnorm := congrArg norm hcon
  rw [norm_smul, BosonFock.norm_vacuum] at hnorm
  norm_num at hnorm

/-- **The CCR sign is not a convention**: the commutator with the two orders exchanged,
`[a†(g), a(f)] = ⟪f, g⟫ · 1`, is already refuted at the vacuum, where it would force
`Ω = -Ω`. So the frozen `CCROnDomain` picks out one of two genuinely different
statements. -/
theorem probe_not_ccr_sign_reversed :
    ¬ ∀ (f g : E₂) (x : BosonFock.finiteParticle ℂ E₂),
        creationPMap ℂ E₂ g
            ⟨annihilationPMap ℂ E₂ f x,
              annihilationPMap_apply_mem_finiteParticle ℂ E₂ f x⟩ -
          annihilationPMap ℂ E₂ f
            ⟨creationPMap ℂ E₂ g x, creationPMap_apply_mem_finiteParticle ℂ E₂ g x⟩ =
        inner ℂ f g • (x : BosonFock ℂ E₂) := by
  intro hccr
  have he : inner ℂ (e 0) (e 0) = (1 : ℂ) := by rw [probe_inner_e_e]; simp
  have h0 : BosonFock.vacuum ℂ E₂ = -BosonFock.vacuum ℂ E₂ := by
    have h := (hccr (e 0) (e 0)
      ⟨BosonFock.vacuum ℂ E₂, BosonFock.vacuum_mem_finiteParticle ℂ E₂⟩).symm.trans
        (probe_ccr_vacuum_reversed ℂ E₂ (e 0) (e 0))
    rwa [he, one_smul] at h
  have h1 : inner ℂ (BosonFock.vacuum ℂ E₂) (BosonFock.vacuum ℂ E₂) =
      inner ℂ (BosonFock.vacuum ℂ E₂) (-BosonFock.vacuum ℂ E₂) := by rw [← h0]
  rw [inner_neg_right, @inner_self_eq_norm_sq_to_K ℂ, BosonFock.norm_vacuum] at h1
  norm_num at h1

end Model

end P22Slice2Probe

end
