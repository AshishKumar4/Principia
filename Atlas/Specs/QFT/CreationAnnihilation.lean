import Atlas.Proofs.FockBridge
import Atlas.Specs.OperatorTheory.Symmetric
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# P2.2 — creation and annihilation operators on the boson Fock space

Frozen spec (blueprint node P2.2, second spec slice): proof sessions must not edit this
file; changes require a spec review and a `[spec-review]` commit (see CLAUDE.md).
Builds on the frozen slice-1 spec `Atlas/Specs/QFT/FockSpace.lean` and the bridge API
`Atlas/Proofs/FockBridge.lean` (frozen by import).

## Contents

* Algebraic layer: `QFT.insertAux 𝕜 E n : E →ₗ[𝕜] ⨂[𝕜]^n E →ₗ[𝕜] ⨂[𝕜]^(n+1) E`, the
  front-slot insertion `f ⊗ (x₁ ⊗ ⋯ ⊗ xₙ)` realized directly on tensor powers, and
  `QFT.contractAux 𝕜 E n : E →ₛₗ[starRingEnd 𝕜] ⨂[𝕜]^(n+1) E →ₗ[𝕜] ⨂[𝕜]^n E`, the
  front-slot contraction `x₀ ⊗ ⋯ ⊗ xₙ ↦ ⟪f, x₀⟫ (x₁ ⊗ ⋯ ⊗ xₙ)`; their pure-tensor
  actions, the norm identity `‖f ⊗ ψ‖ = ‖f‖ ‖ψ‖` (`norm_insertAux`, via
  `inner_insertAux_insertAux`), the mutual-adjointness identity
  `⟪f ⊗ ψ, w⟫ = ⟪ψ, contract_f w⟫` (`inner_insertAux_left`), and the contraction bound
  `‖contract_f w‖ ≤ ‖f‖ ‖w‖` — all kernel-checked here since they pin the definitions.
* Completed layer: `QFT.insertL`/`QFT.contractL`, the extensions to the Hilbert tensor
  powers by density (`LinearMap.extendOfNorm`), restricting to the algebraic maps on
  the dense image (`insertL_coe`/`contractL_coe`), with the norm identity, the bound,
  the completed adjointness identity (`inner_insertL_left`), and the (anti)linearity
  in `f` pinned (`insertL_add_left`, `insertL_smul_left`, `contractL_add_left`,
  `contractL_smul_left`).
* Sector maps: `QFT.creationSector 𝕜 E n f : SymTensorPower 𝕜 E n →L[𝕜]
  SymTensorPower 𝕜 E (n+1)`, `ψ ↦ √(n+1) • Sₙ₊₁ (f ⊗ ψ)`, and
  `QFT.annihilationSector 𝕜 E n f : SymTensorPower 𝕜 E (n+1) →L[𝕜] SymTensorPower 𝕜 E n`,
  `w ↦ √(n+1) • Sₙ (contract_f w)` (Reed & Simon II, §X.7; Bratteli & Robinson II,
  §5.2), with their ambient-value pins and (anti)linearity in `f`.
* The operators: `QFT.creationPMap 𝕜 E f` (`a†(f)`) and `QFT.annihilationPMap 𝕜 E f`
  (`a(f)`) as `LinearPMap`s on `BosonFock 𝕜 E` with domain the frozen slice-1
  `BosonFock.finiteParticle` (Reed & Simon II, §X.7: all operators live on `F₀`),
  acting sector-wise; `BosonFock.oneParticle`; kernel-checked statement pins: the
  component formulas, preservation of the finite-particle domain, the vacuum actions
  `a(f) Ω = 0` and `a†(f) Ω = |f⟩`, the one-particle actions
  `a(f) |g⟩ = ⟪f, g⟫ Ω` and `a†(f) |g⟩ = √2 S₂(f ⊗ g)` in sector 2, and the
  linearity of `f ↦ a†(f)` / antilinearity of `f ↦ a(f)`.
* `Prop`-valued target statements (proofs are future blueprint nodes, never to be
  weakened): `CreationAnnihilationAdjoint` (mutual formal adjointness on `F₀`, via
  Mathlib's `LinearPMap.IsFormalAdjoint` — the relation the frozen P2.3a spec
  connects to symmetry), `CCROnDomain` (`[a(f), a†(g)] = ⟪f, g⟫ • 1` on `F₀`),
  `AnnihilationsCommute`/`CreationsCommute` (`[a(f), a(g)] = [a†(f), a†(g)] = 0`),
  and — with the Segal field `QFT.segalField f = (a(f) + a†(f))/√2` —
  `SegalFieldEssentiallySelfAdjoint` via the frozen P2.3a
  `OperatorTheory.LinearPMap.IsEssentiallySelfAdjoint` (the future proof node is the
  Nelson analytic-vector route, Reed & Simon II, Thm X.39, feeding the proven P2.3b
  criterion).

## Conventions

* **Where the `√` factors live — THE trap** (Reed & Simon II, §X.7; cf. the slice-1
  witness `norm_symmetrizer_e₀₁_sq`). With the slice-1 *orthogonal-projector*
  symmetrizer (idempotent `Sₙ`, `(n!)⁻¹` normalization), the factors making
  `a(f)`/`a†(f)` mutually adjoint with `[a(f), a†(g)] = ⟪f, g⟫` are:
  `a†(f) : sector n → sector (n+1)` carries `√(n+1)`, and
  `a(f) : sector (n+1) → sector n` carries `√(n+1)` — the *same* factor, indexed by
  the higher sector, as mutual adjointness forces. Equivalently, acting from sector
  `n`, `a(f)` carries `√n` (Reed & Simon II, §X.7 writes
  `(a(f)ψ)⁽ⁿ⁾ = √(n+1) ⟨f, ψ⁽ⁿ⁺¹⁾⟩₁`). Texts that instead build the symmetric Fock
  space with `(n!)`-weighted inner products on symmetric tensors (exponential-vector
  constructions, e.g. Guichardet) absorb these factors into the norm; we do not — the
  slice-1 witness pins `‖S₂(e₀ ⊗ e₁)‖² = ½`, and the `√`s stay in the operators.
  Sanity anchor, kernel-checked below: `a(f) a†(g) Ω = ⟪f, g⟫ Ω` with no stray factor
  (`annihilationPMap_oneParticle` + `creationPMap_vacuum`).
* **Bratteli–Robinson's sum-over-slots form is the same operator.** BR II §5.2 write
  `(a†(f)ψ)⁽ⁿ⁾ = n^{-1/2} ∑ᵢ f(xᵢ) ψ⁽ⁿ⁻¹⁾(… x̂ᵢ …)`; since our `Sₙ` averages over the
  full permutation group, `n^{-1/2} ∑ᵢ (insert at slot i) = √n Sₙ ∘ (insert at slot 0)`
  on symmetric input, which is this file's `√(n+1) Sₙ₊₁ (f ⊗ ·)` re-indexed by the
  source sector. Their formulas are cited section-level (numbers not re-verified
  against a copy).
* **Compression convention (Bratteli–Robinson).** Both sector maps are defined as
  compressions `P₊ (⋯) P₊`: the creation map post-symmetrizes (necessary — `f ⊗ ψ` is
  not symmetric), and the annihilation map also post-symmetrizes (redundant —
  front-slot contraction of a symmetric tensor is already symmetric, but making that a
  *definition-level* fact would cost a lemma where BR's compression gives
  well-definedness by construction; the redundancy statement
  `Sₙ (contract_f w) = contract_f w` for symmetric `w` is a candidate future node,
  not needed by any planned proof). This is exactly BR II §5.2's definition of the
  Fock representation on `F₊(H)` by compressing the full-Fock operators.
* **`a(f)` is antilinear in `f`; `a†(f)` is linear in `f`** (Reed & Simon II, §X.7;
  Bratteli & Robinson II, §5.2 — both sources agree; the alternative "linear `a(f)`
  over the conjugate Hilbert space" bookkeeping found elsewhere is not used).
  Mechanically: `contractAux` is a bundled `→ₛₗ[starRingEnd 𝕜]` in `f`, `insertAux` a
  bundled `→ₗ[𝕜]`, and the operator-level pins are `annihilationPMap_smul_left`
  (`a(c • f) = c̄ • a(f)` pointwise) and `creationPMap_smul_left`. Consistency check:
  in `[a(f), a†(g)] = ⟪f, g⟫ • 1`, Mathlib's inner product is conjugate-linear in its
  *first* slot, matching antilinearity in `f` through `a(f)` — the physicists'
  convention, verbatim.
* **The one-step multiplication, not the full `mulEquiv` (P2.1f.ii adjudication).**
  The blueprint sketch `a†(f) = √(n+1) Sₙ₊₁ (f ⊗ₜ ·)` suggests routing through a
  completed multiplication `E ⊗̂ (⨂̂ⁿE) ≃ ⨂̂ⁿ⁺¹E` (the completed
  `TensorPower.mulEquiv`, split off as blueprint todo P2.1f.ii). The operators only
  ever consume the *partial application* `f ⊗ ·` at fixed `f`, so this file builds
  that map directly on tensor powers — `insertAux` via `MultilinearMap.curryLeft` of
  `tprod`, extended to `insertL` by density — and kernel-checks the exact
  partial-application shadow of the `mulEquiv`-isometry claim:
  `‖f ⊗ ψ‖ = ‖f‖ ‖ψ‖` (`norm_insertAux`/`norm_insertL_apply`, the ℓ² cross-norm
  factorization on the first slot). The full binary statement (that the ℓ² norms make
  `mulEquiv 1 n` an isometry `E ⊗̂ ⨂̂ⁿE ≃ₗᵢ ⨂̂ⁿ⁺¹E`) remains open as P2.1f.ii; nothing
  in this slice depends on it.
* **No `LinearPMap` composition.** Mathlib's `LinearPMap` has no composition, and a
  composition-shaped CCR would bury the statement under domain bookkeeping. Instead
  the kernel-checked lemmas `creationPMap_apply_mem_finiteParticle` /
  `annihilationPMap_apply_mem_finiteParticle` show both operators map `F₀` into `F₀`,
  and `CCROnDomain` is stated pointwise on `F₀` with those membership witnesses — the
  literal form "for all `ψ ∈ F₀`, `a(f) a†(g) ψ - a†(g) a(f) ψ = ⟪f, g⟫ ψ`" of the
  sources. `segalField` uses Mathlib's `LinearPMap` `+`/`•` (domain
  `F₀ ⊓ F₀ = F₀`, pinned by `segalField_domain`).
* **Scope discipline** (inherited from slice 1, mechanically guarded): the
  `assert_not_exists` below keeps Mathlib's projective-seminorm instances out; this
  file opens `PiTensorProduct.InnerNorm` and consumers must do the same.
* **Generality.** Everything is stated over `RCLike 𝕜` except
  `SegalFieldEssentiallySelfAdjoint`, which lives over `ℂ` because the frozen P2.3a
  operator layer (`IsEssentiallySelfAdjoint`, deficiency spaces) is complex — as is
  the physics. No completeness of `E` is assumed anywhere (slice-1 precedent).

## Target statements (not theorems here)

`CreationAnnihilationAdjoint`, `CCROnDomain`, `AnnihilationsCommute`,
`CreationsCommute`, `SegalFieldEssentiallySelfAdjoint` are `Prop`-valued definitions:
their proofs are future blueprint nodes (adjointness/CCR grind; a new Nelson
analytic-vector node for the last). A stuck proof node decomposes into sub-lemmas; it
never weakens these statements.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II: Fourier Analysis,
  Self-Adjointness* (1975), §X.7 (the free quantum field): `a(f)`, `a†(f)` on the
  dense domain `F₀` with the `√(n+1)` factors, antilinearity of `f ↦ a(f)`, the CCR
  `[a(f), a†(g)] = ⟪f, g⟫`, the Segal field `Φ_S(f) = 2^{-1/2}(a(f) + a†(f))`, and
  Thm X.41 (its essential self-adjointness on `F₀`); Thm X.39 (Nelson's analytic
  vector theorem — the staged proof route). Section-level citations; in-section
  display numbers quoted from memory are flagged where used.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised and enlarged edition (1980), §II.4, Example 2 (Fock spaces): the ambient
  construction this slice's sector maps live in.
* O. Bratteli, D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*,
  2nd edition (1997), §5.2: `a(f)`/`a*(f)` on the boson Fock space as compressions by
  the symmetrization projector `P₊`, their sum-over-slots component formulas, and the
  CCR over `F₊(H)`. Section-level citation.
-/

assert_not_exists PiTensorProduct.projectiveSeminorm

noncomputable section

namespace QFT

open PiTensorProduct UniformSpace Equiv
open scoped TensorProduct PiTensorProduct.InnerNorm Nat ENNReal

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (n : ℕ)

/-! ### Insertion and contraction on the algebraic tensor powers -/

/-- *Front-slot insertion* `f ⊗ ·` on tensor powers: the linear-in-`f` bundle of the
maps `⨂[𝕜]^n E →ₗ[𝕜] ⨂[𝕜]^(n+1) E` sending `x₁ ⊗ ⋯ ⊗ xₙ` to `f ⊗ x₁ ⊗ ⋯ ⊗ xₙ`
(`insertAux_tprod`). This is the partial application of the tensor-power
multiplication that the creation operator consumes (see the module docstring for the
P2.1f.ii adjudication); built from `MultilinearMap.curryLeft` of `tprod`, so no cast
appears. -/
def insertAux : E →ₗ[𝕜] ⨂[𝕜]^n E →ₗ[𝕜] ⨂[𝕜]^(n + 1) E :=
  (PiTensorProduct.lift.toLinearMap).comp
    (tprod 𝕜 (s := fun _ : Fin (n + 1) => E)).curryLeft

/-- **Action of insertion on pure tensors**: `insertAux f (⨂ₜ x) = ⨂ₜ (f, x)`. -/
@[simp]
theorem insertAux_tprod (f : E) (x : Fin n → E) :
    insertAux 𝕜 E n f (tprod 𝕜 x) = tprod 𝕜 (Fin.cons f x) := by
  simp [insertAux, MultilinearMap.curryLeft_apply]

/-- *Front-slot contraction* `⟪f, ·⟫₁` on tensor powers: the antilinear-in-`f` bundle
of the maps `⨂[𝕜]^(n+1) E →ₗ[𝕜] ⨂[𝕜]^n E` sending `x₀ ⊗ x₁ ⊗ ⋯ ⊗ xₙ` to
`⟪f, x₀⟫ (x₁ ⊗ ⋯ ⊗ xₙ)` (`contractAux_tprod`) — the algebraic core of the
annihilation operator (Reed & Simon II, §X.7). The `→ₛₗ[starRingEnd 𝕜]` bundling *is*
the antilinearity convention for `a(f)`, pinned at the definition. -/
def contractAux : E →ₛₗ[starRingEnd 𝕜] ⨂[𝕜]^(n + 1) E →ₗ[𝕜] ⨂[𝕜]^n E where
  toFun f := PiTensorProduct.lift
    (LinearMap.uncurryLeft (M := fun _ : Fin (n + 1) => E)
      ((innerₛₗ 𝕜 f).smulRight (tprod 𝕜 (s := fun _ : Fin n => E))))
  map_add' f g := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp [add_smul]
  map_smul' c f := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp [mul_smul]

/-- **Action of contraction on pure tensors**:
`contractAux f (⨂ₜ x) = ⟪f, x 0⟫ • ⨂ₜ (tail x)`. -/
@[simp]
theorem contractAux_tprod (f : E) (x : Fin (n + 1) → E) :
    contractAux 𝕜 E n f (tprod 𝕜 x) = inner 𝕜 f (x 0) • tprod 𝕜 (Fin.tail x) := by
  simp [contractAux]

/-- The pairing of two insertions factorizes on the front slot:
`⟪f ⊗ ψ, g ⊗ w⟫ = ⟪f, g⟫ ⟪ψ, w⟫`. This is the partial-application form of the ℓ²
cross-norm factorization (Reed & Simon I, §II.4) and the engine behind
`norm_insertAux`. -/
theorem inner_insertAux_insertAux (f g : E) (x y : ⨂[𝕜]^n E) :
    inner 𝕜 (insertAux 𝕜 E n f x) (insertAux 𝕜 E n g y) =
      inner 𝕜 f g * inner 𝕜 x y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod d b =>
      simp only [map_smul, insertAux_tprod, inner_smul_left, inner_smul_right,
        inner_tprod, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, inner_add_right, h₁, h₂, mul_add]
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, inner_add_left, h₁, h₂, mul_add]

/-- **Insertion scales norms exactly**: `‖f ⊗ ψ‖ = ‖f‖ ‖ψ‖` — the kernel-checked
partial-application shadow of the "`mulEquiv` is an ℓ²-isometry" claim (P2.1f.ii; see
the module docstring). -/
theorem norm_insertAux (f : E) (x : ⨂[𝕜]^n E) :
    ‖insertAux 𝕜 E n f x‖ = ‖f‖ * ‖x‖ := by
  have h : inner 𝕜 (insertAux 𝕜 E n f x) (insertAux 𝕜 E n f x) =
      ((‖f‖ ^ 2 * ‖x‖ ^ 2 : ℝ) : 𝕜) := by
    rw [inner_insertAux_insertAux, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K]
    push_cast
    ring
  rw [@norm_eq_sqrt_re_inner 𝕜, h, RCLike.ofReal_re,
    show ‖f‖ ^ 2 * ‖x‖ ^ 2 = (‖f‖ * ‖x‖) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

/-- **Insertion and contraction are formally adjoint** on the algebraic layer:
`⟪f ⊗ ψ, w⟫ = ⟪ψ, ⟪f, ·⟫₁ w⟫` (Reed & Simon II, §X.7: `a(f) = (a†(f))*` on `F₀`).
This identity is what `CreationAnnihilationAdjoint` will amplify sector-by-sector. -/
theorem inner_insertAux_left (f : E) (x : ⨂[𝕜]^n E) (y : ⨂[𝕜]^(n + 1) E) :
    inner 𝕜 (insertAux 𝕜 E n f x) y = inner 𝕜 x (contractAux 𝕜 E n f y) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod d b =>
      simp only [map_smul, insertAux_tprod, contractAux_tprod, inner_smul_left,
        inner_smul_right, inner_tprod, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ, Fin.tail]
      ring
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, inner_add_right, h₁, h₂]
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, inner_add_left, h₁, h₂]

/-- The contraction bound `‖⟪f, ·⟫₁ w‖ ≤ ‖f‖ ‖w‖`, by the adjoint identity and
Cauchy–Schwarz; the operator-norm content making `contractL` well defined. -/
theorem norm_contractAux_apply_le (f : E) (y : ⨂[𝕜]^(n + 1) E) :
    ‖contractAux 𝕜 E n f y‖ ≤ ‖f‖ * ‖y‖ := by
  set c := contractAux 𝕜 E n f y with hc
  have hkey : ‖c‖ * ‖c‖ ≤ ‖f‖ * ‖y‖ * ‖c‖ :=
    calc ‖c‖ * ‖c‖
        = RCLike.re (inner 𝕜 (insertAux 𝕜 E n f c) y) := by
          rw [inner_insertAux_left, ← hc, inner_self_eq_norm_mul_norm]
      _ ≤ ‖inner 𝕜 (insertAux 𝕜 E n f c) y‖ := RCLike.re_le_norm _
      _ ≤ ‖insertAux 𝕜 E n f c‖ * ‖y‖ := norm_inner_le_norm _ _
      _ = ‖f‖ * ‖y‖ * ‖c‖ := by rw [norm_insertAux]; ring
  rcases (norm_nonneg c).eq_or_lt with h0 | h0
  · rw [← h0]
    positivity
  · exact le_of_mul_le_mul_right hkey h0

/-! ### Insertion and contraction on the completed powers -/

/-- Front-slot insertion on the completed Hilbert tensor powers: the extension of
`insertAux f` by density (`LinearMap.extendOfNorm` along `toComplₗᵢ`, bounded by
`‖f‖`). Restricts to the algebraic insertion on the dense image (`insertL_coe`). -/
def insertL (f : E) : HilbertTensorPower 𝕜 E n →L[𝕜] HilbertTensorPower 𝕜 E (n + 1) :=
  ((Completion.toComplₗᵢ (𝕜 := 𝕜) (E := ⨂[𝕜]^(n + 1) E)).toLinearMap ∘ₗ
      insertAux 𝕜 E n f).extendOfNorm
    (Completion.toComplₗᵢ (𝕜 := 𝕜) (E := ⨂[𝕜]^n E)).toLinearMap

/-- Definitional pin: on the dense algebraic image, `insertL` is `insertAux`. -/
@[simp]
theorem insertL_coe (f : E) (x : ⨂[𝕜]^n E) :
    insertL 𝕜 E n f (x : HilbertTensorPower 𝕜 E n) =
      (insertAux 𝕜 E n f x : HilbertTensorPower 𝕜 E (n + 1)) :=
  LinearMap.extendOfNorm_eq (by simpa using Completion.denseRange_coe)
    ⟨‖f‖, fun z => by
      simp only [LinearMap.coe_comp, Function.comp_apply,
        LinearIsometry.coe_toLinearMap, Completion.coe_toComplₗᵢ,
        Completion.norm_coe, norm_insertAux, le_refl]⟩ x

/-- The completed insertion scales norms exactly: `‖f ⊗ ψ‖ = ‖f‖ ‖ψ‖`. -/
theorem norm_insertL_apply (f : E) (ψ : HilbertTensorPower 𝕜 E n) :
    ‖insertL 𝕜 E n f ψ‖ = ‖f‖ * ‖ψ‖ := by
  induction ψ using Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_norm.comp (insertL 𝕜 E n f).continuous)
      (continuous_const.mul continuous_norm)
  | ih a => rw [insertL_coe, Completion.norm_coe, Completion.norm_coe, norm_insertAux]

/-- Linearity of `f ↦ f ⊗ ·` on the completion: additivity. -/
theorem insertL_add_left (f g : E) :
    insertL 𝕜 E n (f + g) = insertL 𝕜 E n f + insertL 𝕜 E n g := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  induction ψ using Completion.induction_on with
  | hp =>
    exact isClosed_eq (insertL 𝕜 E n (f + g)).continuous
      (insertL 𝕜 E n f + insertL 𝕜 E n g).continuous
  | ih a =>
    rw [add_apply, insertL_coe, insertL_coe, insertL_coe,
      map_add, LinearMap.add_apply, Completion.coe_add]

/-- Linearity of `f ↦ f ⊗ ·` on the completion: homogeneity — `a†` will be *linear*
in `f` (Reed & Simon II, §X.7). -/
theorem insertL_smul_left (c : 𝕜) (f : E) :
    insertL 𝕜 E n (c • f) = c • insertL 𝕜 E n f := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  induction ψ using Completion.induction_on with
  | hp =>
    exact isClosed_eq (insertL 𝕜 E n (c • f)).continuous
      (c • insertL 𝕜 E n f).continuous
  | ih a =>
    rw [smul_apply, insertL_coe, insertL_coe, map_smul,
      LinearMap.smul_apply, Completion.coe_smul]

/-- Front-slot contraction on the completed Hilbert tensor powers: the extension of
`contractAux f` by density, bounded by `‖f‖` (`norm_contractAux_apply_le`). -/
def contractL (f : E) :
    HilbertTensorPower 𝕜 E (n + 1) →L[𝕜] HilbertTensorPower 𝕜 E n :=
  ((Completion.toComplₗᵢ (𝕜 := 𝕜) (E := ⨂[𝕜]^n E)).toLinearMap ∘ₗ
      contractAux 𝕜 E n f).extendOfNorm
    (Completion.toComplₗᵢ (𝕜 := 𝕜) (E := ⨂[𝕜]^(n + 1) E)).toLinearMap

/-- Definitional pin: on the dense algebraic image, `contractL` is `contractAux`. -/
@[simp]
theorem contractL_coe (f : E) (y : ⨂[𝕜]^(n + 1) E) :
    contractL 𝕜 E n f (y : HilbertTensorPower 𝕜 E (n + 1)) =
      (contractAux 𝕜 E n f y : HilbertTensorPower 𝕜 E n) :=
  LinearMap.extendOfNorm_eq (by simpa using Completion.denseRange_coe)
    ⟨‖f‖, fun z => by
      simpa only [LinearMap.coe_comp, Function.comp_apply,
        LinearIsometry.coe_toLinearMap, Completion.coe_toComplₗᵢ,
        Completion.norm_coe] using norm_contractAux_apply_le 𝕜 E n f z⟩ y

/-- The completed contraction bound `‖contractL f w‖ ≤ ‖f‖ ‖w‖`. -/
theorem norm_contractL_apply_le (f : E) (w : HilbertTensorPower 𝕜 E (n + 1)) :
    ‖contractL 𝕜 E n f w‖ ≤ ‖f‖ * ‖w‖ := by
  induction w using Completion.induction_on with
  | hp =>
    exact isClosed_le (continuous_norm.comp (contractL 𝕜 E n f).continuous)
      (continuous_const.mul continuous_norm)
  | ih a =>
    rw [contractL_coe, Completion.norm_coe, Completion.norm_coe]
    exact norm_contractAux_apply_le 𝕜 E n f a

/-- Antilinearity of `f ↦ ⟪f, ·⟫₁` on the completion: additivity. -/
theorem contractL_add_left (f g : E) :
    contractL 𝕜 E n (f + g) = contractL 𝕜 E n f + contractL 𝕜 E n g := by
  refine ContinuousLinearMap.ext fun w => ?_
  induction w using Completion.induction_on with
  | hp =>
    exact isClosed_eq (contractL 𝕜 E n (f + g)).continuous
      (contractL 𝕜 E n f + contractL 𝕜 E n g).continuous
  | ih a =>
    rw [add_apply, contractL_coe, contractL_coe, contractL_coe,
      map_add, LinearMap.add_apply, Completion.coe_add]

/-- Antilinearity of `f ↦ ⟪f, ·⟫₁` on the completion: conjugate homogeneity — `a`
will be *antilinear* in `f` (Reed & Simon II, §X.7; the convention pin). -/
theorem contractL_smul_left (c : 𝕜) (f : E) :
    contractL 𝕜 E n (c • f) = (starRingEnd 𝕜) c • contractL 𝕜 E n f := by
  refine ContinuousLinearMap.ext fun w => ?_
  induction w using Completion.induction_on with
  | hp =>
    exact isClosed_eq (contractL 𝕜 E n (c • f)).continuous
      ((starRingEnd 𝕜) c • contractL 𝕜 E n f).continuous
  | ih a =>
    rw [smul_apply, contractL_coe, contractL_coe, map_smulₛₗ,
      LinearMap.smul_apply, Completion.coe_smul]

/-- **Completed insertion and contraction are formally adjoint**:
`⟪insertL f ψ, w⟫ = ⟪ψ, contractL f w⟫`, by density from `inner_insertAux_left`.
This is the whole analytic content of the future `CreationAnnihilationAdjoint`
proof node; what remains there is sector bookkeeping. -/
theorem inner_insertL_left (f : E) (ψ : HilbertTensorPower 𝕜 E n)
    (w : HilbertTensorPower 𝕜 E (n + 1)) :
    inner 𝕜 (insertL 𝕜 E n f ψ) w = inner 𝕜 ψ (contractL 𝕜 E n f w) := by
  induction ψ, w using Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq
      (Continuous.inner ((insertL 𝕜 E n f).continuous.comp continuous_fst)
        continuous_snd)
      (Continuous.inner continuous_fst
        ((contractL 𝕜 E n f).continuous.comp continuous_snd))
  | ih a b =>
    rw [insertL_coe, contractL_coe, Completion.inner_coe, Completion.inner_coe,
      inner_insertAux_left]

/-! ### The sector maps -/

/-- The *creation sector map* `a†(f) : Sₙ E⁽ⁿ⁾ → Sₙ₊₁ E⁽ⁿ⁺¹⁾`,
`ψ ↦ √(n+1) • Sₙ₊₁ (f ⊗ ψ)` (Reed & Simon II, §X.7, with the projector-normalized
symmetrizer of slice 1; Bratteli & Robinson II, §5.2, the compression `P₊ a†(f) P₊`).
Codomain-restricted to the `(n+1)`-sector, which it lands in by construction. -/
def creationSector (f : E) :
    SymTensorPower 𝕜 E n →L[𝕜] SymTensorPower 𝕜 E (n + 1) :=
  ContinuousLinearMap.codRestrict
    ((Real.sqrt (n + 1) : 𝕜) • ((symmetrizerL 𝕜 E (n + 1)).comp
      ((insertL 𝕜 E n f).comp (SymTensorPower 𝕜 E n).subtypeL)))
    (SymTensorPower 𝕜 E (n + 1))
    (fun _ => Submodule.smul_mem _ _ ⟨_, rfl⟩)

/-- Ambient-value pin for the creation sector map:
`a†(f) ψ = √(n+1) • Sₙ₊₁ (f ⊗ ψ)` in `E⁽ⁿ⁺¹⁾`. -/
theorem creationSector_apply_coe (f : E) (ψ : SymTensorPower 𝕜 E n) :
    (creationSector 𝕜 E n f ψ : HilbertTensorPower 𝕜 E (n + 1)) =
      (Real.sqrt (n + 1) : 𝕜) •
        symmetrizerL 𝕜 E (n + 1)
          (insertL 𝕜 E n f (ψ : HilbertTensorPower 𝕜 E n)) := by
  simp [creationSector]

/-- The *annihilation sector map* `a(f) : Sₙ₊₁ E⁽ⁿ⁺¹⁾ → Sₙ E⁽ⁿ⁾`,
`w ↦ √(n+1) • Sₙ (⟪f, ·⟫₁ w)` (Reed & Simon II, §X.7:
`(a(f)ψ)⁽ⁿ⁾ = √(n+1) ⟨f, ψ⁽ⁿ⁺¹⁾⟩₁`; Bratteli & Robinson II, §5.2). The
post-symmetrization is the BR compression — redundant on symmetric input but giving
well-definedness by construction (module docstring, "Compression convention"). -/
def annihilationSector (f : E) :
    SymTensorPower 𝕜 E (n + 1) →L[𝕜] SymTensorPower 𝕜 E n :=
  ContinuousLinearMap.codRestrict
    ((Real.sqrt (n + 1) : 𝕜) • ((symmetrizerL 𝕜 E n).comp
      ((contractL 𝕜 E n f).comp (SymTensorPower 𝕜 E (n + 1)).subtypeL)))
    (SymTensorPower 𝕜 E n)
    (fun _ => Submodule.smul_mem _ _ ⟨_, rfl⟩)

/-- Ambient-value pin for the annihilation sector map:
`a(f) w = √(n+1) • Sₙ (⟪f, ·⟫₁ w)` in `E⁽ⁿ⁾`. -/
theorem annihilationSector_apply_coe (f : E) (w : SymTensorPower 𝕜 E (n + 1)) :
    (annihilationSector 𝕜 E n f w : HilbertTensorPower 𝕜 E n) =
      (Real.sqrt (n + 1) : 𝕜) •
        symmetrizerL 𝕜 E n
          (contractL 𝕜 E n f (w : HilbertTensorPower 𝕜 E (n + 1))) := by
  simp [annihilationSector]

/-- The creation sector map is additive in `f`. -/
theorem creationSector_add_left (f g : E) :
    creationSector 𝕜 E n (f + g) =
      creationSector 𝕜 E n f + creationSector 𝕜 E n g := by
  refine ContinuousLinearMap.ext fun ψ => Subtype.ext ?_
  simp only [add_apply, Submodule.coe_add,
    creationSector_apply_coe, insertL_add_left, add_apply,
    map_add, smul_add]

/-- The creation sector map is homogeneous in `f`. -/
theorem creationSector_smul_left (c : 𝕜) (f : E) :
    creationSector 𝕜 E n (c • f) = c • creationSector 𝕜 E n f := by
  refine ContinuousLinearMap.ext fun ψ => Subtype.ext ?_
  simp only [smul_apply, Submodule.coe_smul,
    creationSector_apply_coe, insertL_smul_left, map_smul, smul_smul]
  rw [mul_comm]

/-- The annihilation sector map is additive in `f`. -/
theorem annihilationSector_add_left (f g : E) :
    annihilationSector 𝕜 E n (f + g) =
      annihilationSector 𝕜 E n f + annihilationSector 𝕜 E n g := by
  refine ContinuousLinearMap.ext fun w => Subtype.ext ?_
  simp only [add_apply, Submodule.coe_add,
    annihilationSector_apply_coe, contractL_add_left, add_apply,
    map_add, smul_add]

/-- The annihilation sector map is *conjugate*-homogeneous in `f`: the antilinearity
convention, at sector level. -/
theorem annihilationSector_smul_left (c : 𝕜) (f : E) :
    annihilationSector 𝕜 E n (c • f) =
      (starRingEnd 𝕜) c • annihilationSector 𝕜 E n f := by
  refine ContinuousLinearMap.ext fun w => Subtype.ext ?_
  simp only [smul_apply, Submodule.coe_smul,
    annihilationSector_apply_coe, contractL_smul_left, map_smul, smul_smul]
  rw [mul_comm]

/-! ### One-particle states -/

namespace BosonFock

/-- The *one-particle state* `|ψ⟩ = (0, ψ, 0, …)` of the boson Fock space (Reed &
Simon II, §X.7). Membership in the `1`-sector is `symmetrizer_eq_id`: in degree `1`
every tensor is symmetric. -/
def oneParticle (ψ : E) : BosonFock 𝕜 E :=
  lp.single 2 1
    ⟨((tprod 𝕜 ![ψ] : ⨂[𝕜]^1 E) : HilbertTensorPower 𝕜 E 1), by
      rw [mem_symTensorPower_iff, symmetrizerL_coe, symmetrizer_eq_id 𝕜 E 1 le_rfl,
        LinearMap.id_coe, id_eq]⟩

/-- The one-particle embedding is isometric: no normalization factor leaks into the
`n = 1` sector. -/
@[simp]
theorem norm_oneParticle (ψ : E) : ‖oneParticle 𝕜 E ψ‖ = ‖ψ‖ := by
  rw [oneParticle, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  show ‖((tprod 𝕜 ![ψ] : ⨂[𝕜]^1 E) : HilbertTensorPower 𝕜 E 1)‖ = ‖ψ‖
  rw [Completion.norm_coe, PiTensorProduct.norm_tprod]
  simp

/-- One-particle states are finite-particle vectors. -/
theorem oneParticle_mem_finiteParticle (ψ : E) :
    oneParticle 𝕜 E ψ ∈ finiteParticle 𝕜 E :=
  le_iSup (fun N => LinearMap.range
      (lp.singleContinuousLinearMap 𝕜 (fun n => SymTensorPower 𝕜 E n) 2 N).toLinearMap)
    1 ⟨_, rfl⟩

/-- Component pin for the vacuum: sector `0` carries the empty tensor. -/
theorem vacuum_apply_zero :
    (vacuum 𝕜 E) 0 =
      ⟨((tprod 𝕜 Fin.elim0 : ⨂[𝕜]^0 E) : HilbertTensorPower 𝕜 E 0), by
        rw [mem_symTensorPower_iff, symmetrizerL_coe,
          symmetrizer_eq_id 𝕜 E 0 (Nat.zero_le 1), LinearMap.id_coe, id_eq]⟩ := by
  rw [vacuum, lp.single_apply]
  exact Pi.single_eq_same _ _

/-- Component pin for the vacuum: all higher sectors vanish. -/
theorem vacuum_apply_succ (m : ℕ) : (vacuum 𝕜 E) (m + 1) = 0 := by
  rw [vacuum, lp.single_apply]
  exact Pi.single_eq_of_ne (Nat.succ_ne_zero m) _

/-- Component pin for one-particle states: sector `1` carries `ψ`. -/
theorem oneParticle_apply_one (ψ : E) :
    (oneParticle 𝕜 E ψ) 1 =
      ⟨((tprod 𝕜 ![ψ] : ⨂[𝕜]^1 E) : HilbertTensorPower 𝕜 E 1), by
        rw [mem_symTensorPower_iff, symmetrizerL_coe, symmetrizer_eq_id 𝕜 E 1 le_rfl,
          LinearMap.id_coe, id_eq]⟩ := by
  rw [oneParticle, lp.single_apply]
  exact Pi.single_eq_same _ _

/-- Component pin for one-particle states: all other sectors vanish. -/
theorem oneParticle_apply_ne (ψ : E) {k : ℕ} (hk : k ≠ 1) :
    (oneParticle 𝕜 E ψ) k = 0 := by
  rw [oneParticle]
  exact lp.single_apply_ne 2 1 _ hk

end BosonFock

/-! ### The creation and annihilation operators -/

/-- The *creation operator* `a†(f)` on the boson Fock space, as an unbounded
`LinearPMap` with domain the finite-particle subspace `F₀` (Reed & Simon II, §X.7;
Bratteli & Robinson II, §5.2): sector-wise,
`(a†(f) ψ)⁽ⁿ⁺¹⁾ = √(n+1) • Sₙ₊₁ (f ⊗ ψ⁽ⁿ⁾)` and `(a†(f) ψ)⁽⁰⁾ = 0`. Linear in `f`
(`creationPMap_smul_left`). -/
def creationPMap (f : E) : BosonFock 𝕜 E →ₗ.[𝕜] BosonFock 𝕜 E where
  domain := BosonFock.finiteParticle 𝕜 E
  toFun :=
    { toFun := fun x =>
        ⟨fun k =>
          match k with
          | 0 => 0
          | m + 1 => creationSector 𝕜 E m f ((x : BosonFock 𝕜 E) m),
        by
          obtain ⟨N, hN⟩ := (BosonFock.mem_finiteParticle_iff 𝕜 E).mp x.2
          refine memℓp_gen (summable_of_ne_finset_zero
            (s := Finset.range (N + 2)) fun k hk => ?_)
          have hk' : N + 2 ≤ k := by simpa [Finset.mem_range, not_lt] using hk
          obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
          show ‖creationSector 𝕜 E m f ((x : BosonFock 𝕜 E) m)‖ ^ (2 : ℝ≥0∞).toReal = 0
          rw [hN m (by omega), map_zero, norm_zero]
          simp⟩,
      map_add' := fun x y => by
        refine lp.ext (funext fun k => ?_)
        match k with
        | 0 => simp
        | m + 1 =>
          show creationSector 𝕜 E m f (((x + y : _) : BosonFock 𝕜 E) m) = _
          simp
      map_smul' := fun c x => by
        refine lp.ext (funext fun k => ?_)
        match k with
        | 0 => simp
        | m + 1 =>
          show creationSector 𝕜 E m f (((c • x : _) : BosonFock 𝕜 E) m) = _
          simp [lp.coeFn_smul] }

/-- The *annihilation operator* `a(f)` on the boson Fock space, as an unbounded
`LinearPMap` with domain `F₀` (Reed & Simon II, §X.7:
`(a(f) ψ)⁽ⁿ⁾ = √(n+1) ⟨f, ψ⁽ⁿ⁺¹⁾⟩₁`; Bratteli & Robinson II, §5.2). Antilinear in
`f` (`annihilationPMap_smul_left`). -/
def annihilationPMap (f : E) : BosonFock 𝕜 E →ₗ.[𝕜] BosonFock 𝕜 E where
  domain := BosonFock.finiteParticle 𝕜 E
  toFun :=
    { toFun := fun x =>
        ⟨fun m => annihilationSector 𝕜 E m f ((x : BosonFock 𝕜 E) (m + 1)),
        by
          obtain ⟨N, hN⟩ := (BosonFock.mem_finiteParticle_iff 𝕜 E).mp x.2
          refine memℓp_gen (summable_of_ne_finset_zero
            (s := Finset.range (N + 1)) fun m hm => ?_)
          have hm' : N + 1 ≤ m := by simpa [Finset.mem_range, not_lt] using hm
          show ‖annihilationSector 𝕜 E m f ((x : BosonFock 𝕜 E) (m + 1))‖ ^
            (2 : ℝ≥0∞).toReal = 0
          rw [hN (m + 1) (by omega), map_zero, norm_zero]
          simp⟩,
      map_add' := fun x y => by
        refine lp.ext (funext fun m => ?_)
        show annihilationSector 𝕜 E m f (((x + y : _) : BosonFock 𝕜 E) (m + 1)) = _
        simp
      map_smul' := fun c x => by
        refine lp.ext (funext fun m => ?_)
        show annihilationSector 𝕜 E m f (((c • x : _) : BosonFock 𝕜 E) (m + 1)) = _
        simp [lp.coeFn_smul] }

/-- Domain pin: `a†(f)` lives on the finite-particle subspace. -/
@[simp]
theorem creationPMap_domain (f : E) :
    (creationPMap 𝕜 E f).domain = BosonFock.finiteParticle 𝕜 E := rfl

/-- Domain pin: `a(f)` lives on the finite-particle subspace. -/
@[simp]
theorem annihilationPMap_domain (f : E) :
    (annihilationPMap 𝕜 E f).domain = BosonFock.finiteParticle 𝕜 E := rfl

/-- Component pin: `a†(f)` has no vacuum component. -/
@[simp]
theorem creationPMap_apply_zero (f : E) (x : BosonFock.finiteParticle 𝕜 E) :
    (creationPMap 𝕜 E f x) 0 = 0 := rfl

/-- Component pin: `(a†(f) ψ)⁽ᵐ⁺¹⁾ = √(m+1) • Sₘ₊₁ (f ⊗ ψ⁽ᵐ⁾)`, via the sector map. -/
@[simp]
theorem creationPMap_apply_succ (f : E) (x : BosonFock.finiteParticle 𝕜 E) (m : ℕ) :
    (creationPMap 𝕜 E f x) (m + 1) =
      creationSector 𝕜 E m f ((x : BosonFock 𝕜 E) m) := rfl

/-- Component pin: `(a(f) ψ)⁽ᵐ⁾ = √(m+1) • Sₘ (⟪f, ·⟫₁ ψ⁽ᵐ⁺¹⁾)`, via the sector
map. -/
@[simp]
theorem annihilationPMap_apply (f : E) (x : BosonFock.finiteParticle 𝕜 E) (m : ℕ) :
    (annihilationPMap 𝕜 E f x) m =
      annihilationSector 𝕜 E m f ((x : BosonFock 𝕜 E) (m + 1)) := rfl

/-- **`a†(f)` preserves the finite-particle subspace** — the membership witness that
lets `CCROnDomain` be stated without `LinearPMap` composition. -/
theorem creationPMap_apply_mem_finiteParticle (f : E)
    (x : BosonFock.finiteParticle 𝕜 E) :
    creationPMap 𝕜 E f x ∈ BosonFock.finiteParticle 𝕜 E := by
  obtain ⟨N, hN⟩ := (BosonFock.mem_finiteParticle_iff 𝕜 E).mp x.2
  refine (BosonFock.mem_finiteParticle_iff 𝕜 E).mpr ⟨N + 1, fun k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [creationPMap_apply_succ, hN m (by omega), map_zero]

/-- **`a(f)` preserves the finite-particle subspace.** -/
theorem annihilationPMap_apply_mem_finiteParticle (f : E)
    (x : BosonFock.finiteParticle 𝕜 E) :
    annihilationPMap 𝕜 E f x ∈ BosonFock.finiteParticle 𝕜 E := by
  obtain ⟨N, hN⟩ := (BosonFock.mem_finiteParticle_iff 𝕜 E).mp x.2
  refine (BosonFock.mem_finiteParticle_iff 𝕜 E).mpr ⟨N, fun m hm => ?_⟩
  rw [annihilationPMap_apply, hN (m + 1) (by omega), map_zero]

/-- `f ↦ a†(f)` is additive (pointwise on `F₀`). -/
theorem creationPMap_add_left (f g : E) (x : BosonFock.finiteParticle 𝕜 E) :
    creationPMap 𝕜 E (f + g) x = creationPMap 𝕜 E f x + creationPMap 𝕜 E g x := by
  refine lp.ext (funext fun k => ?_)
  match k with
  | 0 => simp
  | m + 1 =>
    simp [creationSector_add_left]

/-- **`f ↦ a†(f)` is linear** (Reed & Simon II, §X.7): homogeneity, pointwise on
`F₀`. Contrast `annihilationPMap_smul_left`. -/
theorem creationPMap_smul_left (c : 𝕜) (f : E) (x : BosonFock.finiteParticle 𝕜 E) :
    creationPMap 𝕜 E (c • f) x = c • creationPMap 𝕜 E f x := by
  refine lp.ext (funext fun k => ?_)
  match k with
  | 0 => simp
  | m + 1 =>
    simp [creationSector_smul_left, lp.coeFn_smul]

/-- `f ↦ a(f)` is additive (pointwise on `F₀`). -/
theorem annihilationPMap_add_left (f g : E) (x : BosonFock.finiteParticle 𝕜 E) :
    annihilationPMap 𝕜 E (f + g) x =
      annihilationPMap 𝕜 E f x + annihilationPMap 𝕜 E g x := by
  refine lp.ext (funext fun m => ?_)
  simp [annihilationSector_add_left]

/-- **`f ↦ a(f)` is antilinear** (Reed & Simon II, §X.7; Bratteli & Robinson II,
§5.2): conjugate homogeneity, pointwise on `F₀` — the convention pin at operator
level. -/
theorem annihilationPMap_smul_left (c : 𝕜) (f : E)
    (x : BosonFock.finiteParticle 𝕜 E) :
    annihilationPMap 𝕜 E (c • f) x =
      (starRingEnd 𝕜) c • annihilationPMap 𝕜 E f x := by
  refine lp.ext (funext fun m => ?_)
  simp [annihilationSector_smul_left, lp.coeFn_smul]

/-! ### Actions on the vacuum and the one-particle states

The kernel-checked anchor computations pinning the `√` and inner-product conventions
(Reed & Simon II, §X.7): `a(f) Ω = 0`, `a†(f) Ω = |f⟩`, `a(f) |g⟩ = ⟪f, g⟫ Ω`, and
`a†(f) |g⟩ = √2 S₂(f ⊗ g)`. Together they witness `a(f) a†(g) Ω = ⟪f, g⟫ Ω` — the
`n = 0` instance of the CCR — so the frozen `CCROnDomain` target is not vacuous. -/

/-- **The vacuum is annihilated**: `a(f) Ω = 0` (Reed & Simon II, §X.7). -/
theorem annihilationPMap_vacuum (f : E) :
    annihilationPMap 𝕜 E f
      ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩ = 0 := by
  refine lp.ext (funext fun m => ?_)
  rw [annihilationPMap_apply]
  show annihilationSector 𝕜 E m f ((BosonFock.vacuum 𝕜 E) (m + 1)) = _
  rw [BosonFock.vacuum_apply_succ, map_zero, lp.coeFn_zero, Pi.zero_apply]

/-- **Creation from the vacuum**: `a†(f) Ω = |f⟩`, the one-particle state — with no
stray normalization, since `√1 = 1` and `S₁ = id` (Reed & Simon II, §X.7). -/
theorem creationPMap_vacuum (f : E) :
    creationPMap 𝕜 E f
      ⟨BosonFock.vacuum 𝕜 E, BosonFock.vacuum_mem_finiteParticle 𝕜 E⟩ =
      BosonFock.oneParticle 𝕜 E f := by
  refine lp.ext (funext fun k => ?_)
  match k with
  | 0 =>
    rw [BosonFock.oneParticle_apply_ne 𝕜 E f (by norm_num : (0 : ℕ) ≠ 1)]
    rfl
  | 1 =>
    rw [creationPMap_apply_succ, BosonFock.oneParticle_apply_one]
    refine Subtype.ext ?_
    rw [creationSector_apply_coe, BosonFock.vacuum_apply_zero]
    have harg : Fin.cons f Fin.elim0 = ![f] :=
      funext fun i => Fin.cases rfl (fun j => j.elim0) i
    simp only [Nat.cast_zero, zero_add, Real.sqrt_one, RCLike.ofReal_one, one_smul]
    rw [insertL_coe, insertAux_tprod, symmetrizerL_coe,
      symmetrizer_eq_id 𝕜 E 1 le_rfl, LinearMap.id_coe, id_eq, harg]
  | (m + 2) =>
    rw [creationPMap_apply_succ, BosonFock.oneParticle_apply_ne 𝕜 E f (by omega),
      BosonFock.vacuum_apply_succ, map_zero]

/-- **Annihilation of a one-particle state**: `a(f) |g⟩ = ⟪f, g⟫ Ω` — the
kernel-checked pin of both the inner-product pairing (conjugate-linear in `f`) and
the `√1` normalization (Reed & Simon II, §X.7). -/
theorem annihilationPMap_oneParticle (f g : E) :
    annihilationPMap 𝕜 E f
      ⟨BosonFock.oneParticle 𝕜 E g, BosonFock.oneParticle_mem_finiteParticle 𝕜 E g⟩ =
      inner 𝕜 f g • BosonFock.vacuum 𝕜 E := by
  refine lp.ext (funext fun m => ?_)
  rw [annihilationPMap_apply, lp.coeFn_smul, Pi.smul_apply]
  match m with
  | 0 =>
    rw [BosonFock.oneParticle_apply_one, BosonFock.vacuum_apply_zero]
    refine Subtype.ext ?_
    rw [annihilationSector_apply_coe]
    have harg : Fin.tail ![g] = Fin.elim0 := funext fun i => i.elim0
    simp only [Nat.cast_zero, zero_add, Real.sqrt_one, RCLike.ofReal_one, one_smul]
    conv_lhs => rw [contractL_coe, contractAux_tprod, harg, Completion.coe_smul,
      map_smul, symmetrizerL_coe, symmetrizer_eq_id 𝕜 E 0 (Nat.zero_le 1),
      LinearMap.id_coe, id_eq]
    simp
  | m + 1 =>
    rw [BosonFock.oneParticle_apply_ne 𝕜 E g (by omega), map_zero,
      BosonFock.vacuum_apply_succ, smul_zero]

/-- **Creation on a one-particle state**: `a†(f) |g⟩` is the two-particle state
`√2 S₂(f ⊗ g)` in sector `2` — the kernel-checked pin of the `√(n+1)` factor beyond
the trivial `n = 0` case (Reed & Simon II, §X.7). -/
theorem creationPMap_oneParticle (f g : E) :
    creationPMap 𝕜 E f
      ⟨BosonFock.oneParticle 𝕜 E g, BosonFock.oneParticle_mem_finiteParticle 𝕜 E g⟩ =
      lp.single 2 2
        ⟨(Real.sqrt 2 : 𝕜) • symmetrizerL 𝕜 E 2
            ((tprod 𝕜 ![f, g] : ⨂[𝕜]^2 E) : HilbertTensorPower 𝕜 E 2),
          Submodule.smul_mem _ _ ⟨_, rfl⟩⟩ := by
  refine lp.ext (funext fun k => ?_)
  match k with
  | 0 =>
    rw [show ((lp.single 2 2 _ : BosonFock 𝕜 E)) 0 = 0 from
      lp.single_apply_ne 2 2 _ (by omega)]
    rfl
  | 1 =>
    rw [creationPMap_apply_succ, BosonFock.oneParticle_apply_ne 𝕜 E g (by omega),
      map_zero, show ((lp.single 2 2 _ : BosonFock 𝕜 E)) 1 = 0 from
        lp.single_apply_ne 2 2 _ (by omega)]
  | 2 =>
    rw [creationPMap_apply_succ, BosonFock.oneParticle_apply_one,
      show ((lp.single 2 2 _ : BosonFock 𝕜 E)) 2 = _ from lp.single_apply_self 2 2 _]
    refine Subtype.ext ?_
    rw [creationSector_apply_coe]
    have harg : Fin.cons f ![g] = ![f, g] := by
      funext i
      fin_cases i <;> simp
    rw [insertL_coe, insertAux_tprod, harg]
    norm_num
  | (m + 3) =>
    rw [creationPMap_apply_succ, BosonFock.oneParticle_apply_ne 𝕜 E g (by omega),
      map_zero, show ((lp.single 2 2 _ : BosonFock 𝕜 E)) (m + 3) = 0 from
        lp.single_apply_ne 2 2 _ (by omega)]

/-! ### Target statements (proofs are future blueprint nodes) -/

/-- **Target statement — mutual formal adjointness** (blueprint node P2.2, proof
staged): `⟪a†(f) x, y⟫ = ⟪x, a(f) y⟫` on the finite-particle domain, i.e.
`(a†(f)).IsFormalAdjoint (a(f))` in Mathlib's sense (Reed & Simon II, §X.7:
`a(f) = (a†(f))* |_{F₀}`; the frozen P2.3a spec connects `IsFormalAdjoint` to
symmetry and adjoint containment). The reversed relation
`(a(f)).IsFormalAdjoint (a†(f))` follows by `LinearPMap.IsFormalAdjoint.symm`, so
only one direction is frozen. The analytic content is already kernel-checked as
`inner_insertL_left` plus the symmetrizer self-adjointness of
`Atlas/Proofs/FockBridge.lean`; the proof node is sector bookkeeping. -/
def CreationAnnihilationAdjoint : Prop :=
  ∀ f : E, (creationPMap 𝕜 E f).IsFormalAdjoint (annihilationPMap 𝕜 E f)

/-- **Target statement — the canonical commutation relation on `F₀`** (blueprint node
P2.2, proof staged): `[a(f), a†(g)] = ⟪f, g⟫ • 1` pointwise on the finite-particle
domain (Reed & Simon II, §X.7; Bratteli & Robinson II, §5.2), stated via the
kernel-checked membership witnesses instead of a `LinearPMap` composition (module
docstring, "No `LinearPMap` composition"). Note the sides: antilinear in `f` through
`a(f)`, matching Mathlib's inner product, conjugate-linear in its first slot. -/
def CCROnDomain : Prop :=
  ∀ (f g : E) (x : BosonFock.finiteParticle 𝕜 E),
    annihilationPMap 𝕜 E f
        ⟨creationPMap 𝕜 E g x, creationPMap_apply_mem_finiteParticle 𝕜 E g x⟩ -
      creationPMap 𝕜 E g
        ⟨annihilationPMap 𝕜 E f x, annihilationPMap_apply_mem_finiteParticle 𝕜 E f x⟩ =
      inner 𝕜 f g • (x : BosonFock 𝕜 E)

/-- **Target statement — annihilators commute**: `[a(f), a(g)] = 0` on `F₀` (Reed &
Simon II, §X.7; Bratteli & Robinson II, §5.2 — the other half of the CCR). -/
def AnnihilationsCommute : Prop :=
  ∀ (f g : E) (x : BosonFock.finiteParticle 𝕜 E),
    annihilationPMap 𝕜 E f
        ⟨annihilationPMap 𝕜 E g x, annihilationPMap_apply_mem_finiteParticle 𝕜 E g x⟩ =
      annihilationPMap 𝕜 E g
        ⟨annihilationPMap 𝕜 E f x, annihilationPMap_apply_mem_finiteParticle 𝕜 E f x⟩

/-- **Target statement — creators commute**: `[a†(f), a†(g)] = 0` on `F₀`. -/
def CreationsCommute : Prop :=
  ∀ (f g : E) (x : BosonFock.finiteParticle 𝕜 E),
    creationPMap 𝕜 E f
        ⟨creationPMap 𝕜 E g x, creationPMap_apply_mem_finiteParticle 𝕜 E g x⟩ =
      creationPMap 𝕜 E g
        ⟨creationPMap 𝕜 E f x, creationPMap_apply_mem_finiteParticle 𝕜 E f x⟩

/-- The *Segal field operator* `Φ(f) = 2^{-1/2} (a(f) + a†(f))` on the
finite-particle domain (Reed & Simon II, §X.7, `Φ_S(f)`; Bratteli & Robinson II,
§5.2). Built with Mathlib's `LinearPMap` addition and scalar action; the domain stays
`F₀` (`segalField_domain`). Real-linear but not complex-linear in `f` — `a` is
antilinear and `a†` linear — which is why the Weyl/CCR *algebra* over a real
subspace is the eventual home of these operators. -/
def segalField (f : E) : BosonFock 𝕜 E →ₗ.[𝕜] BosonFock 𝕜 E :=
  ((Real.sqrt 2 : 𝕜))⁻¹ • (annihilationPMap 𝕜 E f + creationPMap 𝕜 E f)

/-- Domain pin: the Segal field lives on the finite-particle subspace
(`F₀ ⊓ F₀ = F₀`). -/
@[simp]
theorem segalField_domain (f : E) :
    (segalField 𝕜 E f).domain = BosonFock.finiteParticle 𝕜 E := by
  rw [segalField, LinearPMap.smul_domain, LinearPMap.add_domain]
  exact inf_idem _

/-- **Target statement — essential self-adjointness of the Segal field** (blueprint
node P2.2, proof staged behind a new Nelson analytic-vector node): each `Φ(f)` is
essentially self-adjoint on the finite-particle domain, in the sense of the frozen
P2.3a `OperatorTheory.LinearPMap.IsEssentiallySelfAdjoint` (Reed & Simon II, §X.7,
Thm X.41(a); the staged proof route is Nelson's analytic vector theorem, Reed & Simon
II, Thm X.39, feeding the proven P2.3b criterion
`EssentialSelfAdjointnessCriterion`). Stated over `ℂ`, where the P2.3a operator
layer lives. -/
def SegalFieldEssentiallySelfAdjoint (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : Prop :=
  ∀ f : E, OperatorTheory.LinearPMap.IsEssentiallySelfAdjoint (segalField ℂ E f)

end QFT
