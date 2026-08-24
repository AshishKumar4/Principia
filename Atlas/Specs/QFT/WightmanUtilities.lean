import Atlas.Specs.Spacetime.Poincare
import Atlas.Specs.Spacetime.Minkowski
import Mathlib.Analysis.Distribution.Support

/-!
# P2.5a — Wightman utilities: the Minkowski Fourier transform, the closed forward cone,
and the spectrum-condition support hypothesis

**Frozen spec (blueprint node P2.5a, 2026-08-24).** Fable and independent Codex
adversarial reviews approved this surface after a four-defect review/fix/re-review
loop. Changes require `[spec-review]` and new evidence under `audits/reviews/P2.5a*`.

## Contents

* `Spacetime.Minkowski.timeReflectionCLM` / `timeReflection` — the time reflection
  `T(x⁰, x⃗) = (-x⁰, x⃗)` of `M4`, as a continuous linear map and as the continuous
  linear equivalence it is (`T` is an involution). Its reason for existing is
  `inner_timeReflection_right : ⟪v, T w⟫ = η(v, w)`: post-composing with `T` turns the
  Euclidean pairing that Mathlib's Fourier transform uses into the Minkowski pairing.
* `Spacetime.Minkowski.timeReflectionSchwartzCLM` / `timeReflectionSchwartzCLE` — the
  same reflection acting on `𝓢(M4, ℂ)` by composition, again an involutive
  equivalence.
* `Spacetime.Minkowski.fourierMinkowskiCLE` (notation `𝓕η`) — the **Minkowski Fourier
  transform** on `𝓢(M4, ℂ)`: Mathlib's Schwartz Fourier equivalence followed by the
  Schwartz-level time reflection, i.e. `𝓕η f = (𝓕 f) ∘ T`. The convention anchor is
  `fourierMinkowski_apply_eq_integral`:
  `𝓕η f p = ∫ a, 𝐞 (-η(a, p)) • f a`.
  The composition-of-continuous-linear-map lemmas P2.5b consumes are
  `fourierMinkowski_apply`, `fourierMinkowski_apply_apply`,
  `fourierMinkowskiCLE_coe_eq_comp` and `fourierMinkowskiCLE_symm_apply`.
* `Spacetime.Minkowski.closedForwardCone` — the closed forward cone `V̄₊ ⊆ M4`, defined
  as `insert 0 {v | InFutureCausalCone v}` (the frozen P2.4a cone is punctured at the
  origin), with its coordinate and bilinear-form characterizations, its closedness, and
  closure under addition and nonnegative scaling.
* `Spacetime.Minkowski.IsVanishingNearClosedForwardCone` — the spectrum-condition
  support hypothesis on a tempered distribution: it vanishes on a neighbourhood of
  `closedForwardCone`, phrased with `Distribution.IsVanishingOn`, with the `dsupport`
  consequence `IsVanishingNearClosedForwardCone.disjoint_dsupport`.
* `Spacetime.Minkowski.FourierVanishesNearClosedForwardCone` — the same hypothesis for
  a test function `f`, imposed pointwise on `𝓕η f`; this is the form a concrete model
  supplies. `FourierVanishesNearClosedForwardCone.isVanishingNear` is the bridge to the
  distributional form.
* `Spacetime.Minkowski.integrable_smul_of_bounded` — the integrability lemma that makes
  the smeared translation `∫ f(a) • U(a)Ψ da` of the spectrum condition a definite
  Bochner integral in the complete codomain `H` (complete as it is for the frozen
  `PoincareRep`).
* `Spacetime.Minkowski.PoincareGroup.schwartzActionCLM` /
  `schwartzActionCLE` / `schwartzActionHom` — the **Poincaré action on Schwartz space**:
  the pullback by the inverse affine action, `(g ▷ f)(x) = f (g⁻¹ • x)` for
  `g ∈ P↑₊`, with its pointwise formula, group laws, and monoid-hom packaging into the
  endomorphism monoid of `𝓢(M4, ℂ)`. This is the action deferred to P2.5a by the frozen
  P2.4a spec (`Atlas/Specs/Spacetime/Poincare.lean`) and consumed by the P2.5b covariance
  axiom.

## What this file deliberately does not define

* **`SpacelikeSeparated`.** It is already frozen, in
  `Atlas/Specs/Spacetime/Minkowski.lean`, together with `IsSpacelike` and the cone
  trichotomy `isSpacelike_iff_not_inFutureCausalCone`. P2.5's microcausality axiom
  consumes that definition directly; nothing is aliased or restated here. The
  kernel-checked anchor tying it to the frozen P1.2 causal relations,
  `IsSpacelike (x - y) ↔ ¬ x ⤳ y ∧ ¬ y ⤳ x`, is
  `Spacetime.Minkowski.isSpacelike_sub_iff_not_causallyPrecedes` in
  `Atlas/Witnesses/MinkowskiCausal.lean`. That file is *not* imported here: it is a
  witness, and a spec must not depend on the witness layer. The single new fact this
  file adds on the spacelike side is `IsSpacelike.notMem_closedForwardCone`, which is
  what separates the microcausality support condition from the spectrum cone.
* **The spectrum condition itself, and any `WightmanField` structure.** Those are P2.5b.
  Everything here is a utility that P2.5b quantifies over or applies.

## Conventions

* **Signature.** Mostly-plus `(-, +, +, +)`, inherited from the frozen P2.4a spec: `η`
  is `Spacetime.Minkowski.minkowskiForm`, coordinate `0` is time, and the future time
  direction is `EuclideanSpace.single 0 1`.
* **Which reflection.** `T` flips the *time* coordinate, not the spatial ones. This is
  forced, not chosen: `⟪v, T w⟫ = η(v, w)`, whereas the space reflection `-T` gives
  `-η(v, w)`. See `audits/probes/P2.5a/time_flip_sign_probe.lean`.
* **Which pullback.** The Poincaré action on `𝓢(M4, ℂ)` pulls back by the INVERSE
  affine action: `(g ▷ f)(x) = f (g⁻¹ • x)` — never by `g • x`. The inverse convention
  is what makes `g ↦ ▷g` multiplicative for the frozen semidirect multiplication
  (`PoincareGroup.schwartzActionCLM_mul`), the Schwartz-space counterpart of the frozen
  `PoincareRep` bundling; the forward pullback is an antihomomorphism and a different
  operator. See `audits/probes/P2.5a/poincare_schwartz_action_probe.lean`.
* **Fourier normalization.** Mathlib supplies the forward-transform normalization: its
  `𝓕` on `𝓢(V, E)` is `𝓕 g ξ = ∫ v, 𝐞 (-⟪v, ξ⟫) • g v` with `𝐞 t = exp (2 π i t)`, so
  `𝓕η f p = ∫ a, 𝐞 (-η(a, p)) • f a`, and the `2π` is Mathlib's, not a textbook's.
  Reed & Simon II §IX.1 states the symmetric `(2π)^(-n/2) exp(-i λ·x)` convention;
  relative to it, `𝓕η` is a rescaled *inverse* transform, not their stated forward
  normalization. The sign matches Wightman (2000), pp. 210–211, whose reconstruction
  formula uses the kernel `exp(+i p·ξ)` with support in the forward cone. The `2π`
  makes the Fourier variable `p` the physical four-momentum divided by `2π`: a mass-`m`
  shell reads `4 π² (−η(p, p)) = m²`, i.e. `Ω(k) = √(4 π² ‖k‖² + m²)` in the P2.6c
  convention. This rescaling is invisible to the spectrum condition, because
  `closedForwardCone` is invariant under positive scaling
  (`closedForwardCone.smul_mem`). See
  `audits/probes/P2.5a/fourier_normalization_probe.lean`.
* **Closed, not punctured, and not open.** `V̄₊` contains the origin (zero four-momentum
  — the vacuum) and the null boundary. The frozen `InFutureCausalCone` excludes the
  origin and `InFutureTimeCone` excludes the whole boundary; using either in the
  spectrum condition changes the axiom. See
  `audits/probes/P2.5a/cone_closure_probe.lean` and
  `audits/probes/P2.5a/vanishing_cone_probe.lean`.
* **"Vanishes near".** The support hypothesis is vanishing on a *neighbourhood* of
  `V̄₊` (`𝓝ˢ closedForwardCone`), which is the form the tube-analyticity argument of
  P2.7 needs; `dsupport` disjointness is the weaker consequence recorded here.

## Sources

* Streater & Wightman, *PCT, Spin and Statistics, and All That* (1964; Princeton
  Landmarks in Mathematics and Physics ed. 2000), Ch. 3 — the Wightman axioms, and in
  particular the spectrum condition in the form "the Fourier transform of the smearing
  function vanishes near `V̄₊`" together with the cones `V̄±` of Ch. 1; §1-1 — the
  affine action `(a, Λ) • x = Λx + a` whose pullback
  `PoincareGroup.schwartzActionCLM` is. Cited at chapter/section level on purpose: the
  numbering inside those chapters differs between the editions and the secondary
  presentations available online, so no display number is asserted here.
* Reed & Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis,
  Self-Adjointness* (1975), §IX.1 — the Schwartz space `𝓢` and the Fourier transform as
  a bijection of `𝓢` onto itself; §IX.2 — tempered distributions, their support, and the
  pairing of a Schwartz function with a tempered distribution. Its stated normalization
  is the symmetric `(2π)^(-n/2) exp(-i λ·x)` one; the `2π` normalization used here is
  Mathlib's and is not attributed to Reed–Simon. Cited at section level; no display
  number is asserted here.
* A. S. Wightman, "The spin-statistics connection: Some pedagogical remarks in response
  to Neuenschwander's question", *Mathematical Physics and Quantum Field Theory*,
  Electron. J. Differential Equations, Conf. 04 (2000), pp. 207–213 — pp. 210–211: the
  reconstruction formula `F_n = ∫ exp(i Σ p_j·ξ_j) G_n` with `G_n` supported in the
  forward cone `V₊`, the sign orientation `fourierMinkowski_apply_eq_integral` pins.
* Weinberg, *The Quantum Theory of Fields*, Vol. I (1995), §2.3 — Poincaré group
  conventions and the transformation law underlying the pullback action on test
  functions (section level; no display number asserted here).
* O'Neill, *Semi-Riemannian Geometry with Applications to Relativity* (1983), Ch. 5,
  pp. 143–146 — the time cones of a Lorentz vector space, which the frozen P2.4a cone
  toolkit reused here formalizes.
-/

open MeasureTheory RealInnerProductSpace
open scoped FourierTransform SchwartzMap Topology

namespace Spacetime.Minkowski

variable {v w : M4}

/-! ### Time reflection on `M4` -/

/-- Time reflection `T(x⁰, x⃗) = (-x⁰, x⃗)` of Minkowski space, as a continuous linear
map: subtracting twice the time component of `v` along the future time direction flips
the sign of the time coordinate and fixes the spatial ones. Written the same way as
`minkowskiForm`, whose sign flip it implements: `⟪v, T w⟫ = η(v, w)`
(`inner_timeReflection_right`).

Streater & Wightman, *PCT, Spin and Statistics, and All That* (Princeton Landmarks ed.
2000), Ch. 1 (the Minkowski pairing whose Fourier kernel this reflection produces). -/
noncomputable def timeReflectionCLM : M4 →L[ℝ] M4 :=
  ContinuousLinearMap.id ℝ M4 -
    (2 : ℝ) • (EuclideanSpace.proj 0).smulRight (EuclideanSpace.single 0 1 : M4)

theorem timeReflectionCLM_apply (v : M4) :
    timeReflectionCLM v = v - (2 * v 0) • (EuclideanSpace.single 0 1 : M4) := by
  have h : timeReflectionCLM v
      = v - (2 : ℝ) • ((v 0) • (EuclideanSpace.single 0 1 : M4)) := rfl
  rw [h, smul_smul]

theorem timeReflectionCLM_apply_apply (v : M4) (i : Fin 4) :
    timeReflectionCLM v i = v i - 2 * v 0 * (if i = 0 then 1 else 0) := by
  rw [timeReflectionCLM_apply]
  simp [PiLp.single_apply]

@[simp]
theorem timeReflectionCLM_apply_zero (v : M4) : timeReflectionCLM v 0 = -(v 0) := by
  rw [timeReflectionCLM_apply_apply, if_pos rfl]; ring

theorem timeReflectionCLM_apply_of_ne (v : M4) {i : Fin 4} (hi : i ≠ 0) :
    timeReflectionCLM v i = v i := by
  rw [timeReflectionCLM_apply_apply, if_neg hi]; ring

theorem timeReflectionCLM_involutive : Function.Involutive timeReflectionCLM := by
  intro v
  ext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [timeReflectionCLM_apply_zero, timeReflectionCLM_apply_zero, neg_neg]
  · rw [timeReflectionCLM_apply_of_ne _ hi, timeReflectionCLM_apply_of_ne _ hi]

/-- Time reflection as a continuous linear equivalence of `M4`: `timeReflectionCLM` is
its own inverse. This is the equivalence Mathlib's Schwartz-space composition operator
`SchwartzMap.compCLMOfContinuousLinearEquiv` consumes. -/
noncomputable def timeReflection : M4 ≃L[ℝ] M4 :=
  ContinuousLinearEquiv.equivOfInverse timeReflectionCLM timeReflectionCLM
    timeReflectionCLM_involutive timeReflectionCLM_involutive

@[simp]
theorem timeReflection_apply (v : M4) : timeReflection v = timeReflectionCLM v := rfl

@[simp]
theorem timeReflection_symm : timeReflection.symm = timeReflection := rfl

theorem timeReflection_involutive : Function.Involutive timeReflection :=
  timeReflectionCLM_involutive

/-- **The reason time reflection appears at all.** Pairing against the reflected vector
is the Minkowski form: `⟪v, T w⟫ = η(v, w)`. Mathlib's Fourier transform on
`𝓢(V, E)` uses the Euclidean pairing `⟪v, ξ⟫` in its kernel, so precomposing the
frequency variable with `T` — equivalently, post-composing the transform with `T` — is
exactly what turns it into the Minkowski-pairing transform of the Wightman axioms
(Streater & Wightman, *PCT, Spin and Statistics, and All That*, Princeton Landmarks ed.
2000, Ch. 3). -/
theorem inner_timeReflection_right (v w : M4) :
    ⟪v, timeReflection w⟫ = minkowskiForm v w := by
  rw [timeReflection_apply, timeReflectionCLM_apply, inner_sub_right, real_inner_smul_right,
    minkowskiForm_apply]
  simp [EuclideanSpace.inner_single_right]
  ring

theorem inner_timeReflection_left (v w : M4) :
    ⟪timeReflection v, w⟫ = minkowskiForm v w := by
  rw [real_inner_comm, inner_timeReflection_right, minkowskiForm_symm]

/-! ### Time reflection on Schwartz space -/

/-- Time reflection acting on `𝓢(M4, ℂ)` by composition: `f ↦ f ∘ T`. Mathlib's
`SchwartzMap.compCLMOfContinuousLinearEquiv` supplies continuity and linearity, since
`T` is a continuous linear equivalence. -/
noncomputable def timeReflectionSchwartzCLM : 𝓢(M4, ℂ) →L[ℂ] 𝓢(M4, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ timeReflection

@[simp]
theorem timeReflectionSchwartzCLM_apply (f : 𝓢(M4, ℂ)) :
    (timeReflectionSchwartzCLM f : M4 → ℂ) = f ∘ timeReflection := rfl

theorem timeReflectionSchwartzCLM_apply_apply (f : 𝓢(M4, ℂ)) (x : M4) :
    timeReflectionSchwartzCLM f x = f (timeReflection x) := rfl

theorem timeReflectionSchwartzCLM_involutive :
    Function.Involutive timeReflectionSchwartzCLM := by
  intro f
  ext x
  rw [timeReflectionSchwartzCLM_apply_apply, timeReflectionSchwartzCLM_apply_apply,
    timeReflection_involutive x]

/-- Time reflection on `𝓢(M4, ℂ)` as a continuous linear equivalence. -/
noncomputable def timeReflectionSchwartzCLE : 𝓢(M4, ℂ) ≃L[ℂ] 𝓢(M4, ℂ) :=
  ContinuousLinearEquiv.equivOfInverse timeReflectionSchwartzCLM timeReflectionSchwartzCLM
    timeReflectionSchwartzCLM_involutive timeReflectionSchwartzCLM_involutive

@[simp]
theorem timeReflectionSchwartzCLE_apply (f : 𝓢(M4, ℂ)) :
    timeReflectionSchwartzCLE f = timeReflectionSchwartzCLM f := rfl

@[simp]
theorem timeReflectionSchwartzCLE_symm : timeReflectionSchwartzCLE.symm =
    timeReflectionSchwartzCLE := rfl

/-! ### The Minkowski Fourier transform `𝓕η` -/

/-- The **Minkowski Fourier transform** on `𝓢(M4, ℂ)`: Mathlib's Schwartz Fourier
equivalence followed by the time reflection of the frequency variable, so that the
kernel pairs with `η` instead of the Euclidean inner product
(`fourierMinkowski_apply_eq_integral`). It is a continuous linear equivalence because
both factors are.

This is the transform the Wightman spectrum condition is stated with (Streater &
Wightman, *PCT, Spin and Statistics, and All That*, Princeton Landmarks ed. 2000,
Ch. 3); that the Fourier transform is a bijection of `𝓢` onto `𝓢` is Reed & Simon,
*Methods of Modern Mathematical Physics II*, §IX.1. -/
noncomputable def fourierMinkowskiCLE : 𝓢(M4, ℂ) ≃L[ℂ] 𝓢(M4, ℂ) :=
  (FourierTransform.fourierCLE ℂ 𝓢(M4, ℂ)).trans timeReflectionSchwartzCLE

@[inherit_doc fourierMinkowskiCLE]
scoped notation "𝓕η" => fourierMinkowskiCLE

@[simp]
theorem fourierMinkowski_apply (f : 𝓢(M4, ℂ)) :
    𝓕η f = timeReflectionSchwartzCLM (𝓕 f) := rfl

theorem fourierMinkowski_apply_apply (f : 𝓢(M4, ℂ)) (p : M4) :
    𝓕η f p = 𝓕 f (timeReflection p) := rfl

/-- `𝓕η` as a composition of continuous linear maps. This is the form the P2.5b
covariance and spectrum arguments compose against. -/
theorem fourierMinkowskiCLE_coe_eq_comp :
    (fourierMinkowskiCLE : 𝓢(M4, ℂ) →L[ℂ] 𝓢(M4, ℂ)) =
      timeReflectionSchwartzCLM ∘L FourierTransform.fourierCLM ℂ 𝓢(M4, ℂ) :=
  rfl

theorem fourierMinkowskiCLE_symm_apply (f : 𝓢(M4, ℂ)) :
    fourierMinkowskiCLE.symm f = 𝓕⁻ (timeReflectionSchwartzCLM f) := rfl

/-- **The convention anchor.** `𝓕η f p = ∫ a, 𝐞 (-η(a, p)) • f a`, with
`𝐞 t = exp (2 π i t)` Mathlib's `Real.fourierChar`: the `2π` forward-transform
normalization is Mathlib's, and the exponent is the Minkowski pairing. Mostly-plus `η`
makes this the physics kernel `exp (2 π i (a⁰p⁰ - a⃗ · p⃗))`, i.e. the Fourier variable
`p` is the physical four-momentum divided by `2π`. The sign matches Wightman (2000),
pp. 210–211, whose reconstruction formula uses `exp(+i p·ξ)` with support in the
forward cone.

Reed & Simon, *Methods of Modern Mathematical Physics II*, §IX.1 states the symmetric
`(2π)^(-n/2) exp(-i λ·x)` normalization instead; relative to it this transform is a
rescaled inverse transform, not their stated forward normalization. -/
theorem fourierMinkowski_apply_eq_integral (f : 𝓢(M4, ℂ)) (p : M4) :
    𝓕η f p = ∫ a : M4, Real.fourierChar (-(minkowskiForm a p)) • f a := by
  rw [fourierMinkowski_apply_apply, SchwartzMap.fourier_coe, Real.fourier_eq]
  simp only [inner_timeReflection_right]

/-! ### The closed forward cone -/

/-- The **closed forward cone** `V̄₊` of Minkowski space: the frozen (punctured) future
causal cone `InFutureCausalCone` of P2.4a together with the origin. Equivalently, in
coordinates, `‖v⃗‖² ≤ (v⁰)²` and `0 ≤ v⁰` (`mem_closedForwardCone_iff`).

The origin has to be there: it is the four-momentum of the vacuum, and the spectrum
condition of the Wightman axioms is stated with the *closed* cone (Streater & Wightman,
*PCT, Spin and Statistics, and All That*, Princeton Landmarks ed. 2000, Ch. 1 for `V̄±`,
Ch. 3 for the axiom). O'Neill, *Semi-Riemannian Geometry*, Ch. 5, pp. 143–146 is the
geometry. -/
def closedForwardCone : Set M4 :=
  insert 0 {v | InFutureCausalCone v}

@[simp]
theorem zero_mem_closedForwardCone : (0 : M4) ∈ closedForwardCone :=
  Set.mem_insert _ _

theorem InFutureCausalCone.mem_closedForwardCone (h : InFutureCausalCone v) :
    v ∈ closedForwardCone :=
  Set.mem_insert_of_mem _ h

theorem InFutureTimeCone.mem_closedForwardCone (h : InFutureTimeCone v) :
    v ∈ closedForwardCone :=
  h.inFutureCausalCone.mem_closedForwardCone

/-- The closed forward cone in coordinates: `(v¹)² + (v²)² + (v³)² ≤ (v⁰)²` and
`0 ≤ v⁰`. Adjoining the origin to the punctured cone is exactly relaxing `0 < v⁰` to
`0 ≤ v⁰`, because a causal vector with vanishing time component vanishes. -/
theorem mem_closedForwardCone_iff (v : M4) :
    v ∈ closedForwardCone ↔ v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 ≤ v 0 ^ 2 ∧ 0 ≤ v 0 := by
  rw [closedForwardCone, Set.mem_insert_iff]
  constructor
  · rintro (rfl | ⟨h1, h0⟩)
    · simp
    · exact ⟨h1, h0.le⟩
  · rintro ⟨h1, h0⟩
    rcases h0.lt_or_eq with h0 | h0
    · exact Or.inr ⟨h1, h0⟩
    · refine Or.inl ?_
      have hv0 : v 0 ^ 2 = 0 := by rw [← h0]; ring
      have key : ∀ i : Fin 4, v i ^ 2 ≤ 0 → v i = 0 := fun i hi =>
        pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hi (sq_nonneg _))
      ext i
      fin_cases i
      · simpa using h0.symm
      · simpa using key 1 (by nlinarith [sq_nonneg (v 2), sq_nonneg (v 3)])
      · simpa using key 2 (by nlinarith [sq_nonneg (v 1), sq_nonneg (v 3)])
      · simpa using key 3 (by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)])

/-- The closed forward cone against the bilinear form: `η(v, v) ≤ 0` and `0 ≤ v⁰`. -/
theorem mem_closedForwardCone_iff_form (v : M4) :
    v ∈ closedForwardCone ↔ minkowskiForm v v ≤ 0 ∧ 0 ≤ v 0 := by
  rw [mem_closedForwardCone_iff, minkowskiForm_eq]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by nlinarith, h2⟩

/-- `V̄₊` is closed — the point of adjoining the origin. In coordinates it is cut out by
two non-strict inequalities between continuous functions. -/
theorem isClosed_closedForwardCone : IsClosed closedForwardCone := by
  have hset : closedForwardCone =
      {v : M4 | v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 ≤ v 0 ^ 2} ∩ {v : M4 | 0 ≤ v 0} := by
    ext v; simpa using mem_closedForwardCone_iff v
  rw [hset]
  have hproj : ∀ i : Fin 4, Continuous fun v : M4 => v i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  exact (isClosed_le (by fun_prop) (by fun_prop)).inter (isClosed_le continuous_const (hproj 0))

/-- `V̄₊` is closed under addition: it is a convex cone. Reuses the frozen P2.4a
`InFutureCausalCone.add`. -/
theorem closedForwardCone.add_mem (hv : v ∈ closedForwardCone) (hw : w ∈ closedForwardCone) :
    v + w ∈ closedForwardCone := by
  rw [closedForwardCone, Set.mem_insert_iff] at hv hw
  rcases hv with rfl | hv
  · rcases hw with rfl | hw
    · simp
    · simpa using hw.mem_closedForwardCone
  · rcases hw with rfl | hw
    · simpa using hv.mem_closedForwardCone
    · exact (hv.add hw).mem_closedForwardCone

/-- `V̄₊` is a cone: it is stable under nonnegative scaling. This is why the `2π` in
Mathlib's Fourier normalization is invisible to the spectrum condition — rescaling the
frequency variable by a positive constant does not move the cone. -/
theorem closedForwardCone.smul_mem {c : ℝ} (hc : 0 ≤ c) (hv : v ∈ closedForwardCone) :
    c • v ∈ closedForwardCone := by
  rw [mem_closedForwardCone_iff] at hv ⊢
  obtain ⟨h1, h0⟩ := hv
  simp only [PiLp.smul_apply, smul_eq_mul]
  refine ⟨by nlinarith [sq_nonneg c], mul_nonneg hc h0⟩

/-- A spacelike vector is outside the closed forward cone. With
`isSpacelike_iff_not_inFutureCausalCone` (frozen P2.4a) this is what keeps the
microcausality support condition and the spectrum cone apart. -/
theorem IsSpacelike.notMem_closedForwardCone (h : IsSpacelike v) :
    v ∉ closedForwardCone := by
  rw [isSpacelike_iff] at h
  rw [mem_closedForwardCone_iff]
  exact fun hv => absurd hv.1 (not_le.2 h)

/-! ### The spectrum-condition support hypothesis -/

/-- A tempered distribution **vanishes near the closed forward cone** when it vanishes,
in the sense of `Distribution.IsVanishingOn`, on some neighbourhood of `V̄₊`.

This is the support hypothesis of the Wightman spectrum condition in its distributional
form (Streater & Wightman, *PCT, Spin and Statistics, and All That*, Princeton Landmarks
ed. 2000, Ch. 3): the spectrum condition says that a smeared translation vanishes as
soon as the Minkowski Fourier transform of the smearing function vanishes near `V̄₊`.
`Distribution.IsVanishingOn` and `Distribution.dsupport` are Mathlib's notions (Reed &
Simon, *Methods of Modern Mathematical Physics II*, §IX.2 for the classical account of
tempered-distribution support). -/
def IsVanishingNearClosedForwardCone (u : 𝓢'(M4, ℂ)) : Prop :=
  ∃ s ∈ 𝓝ˢ closedForwardCone, Distribution.IsVanishingOn u s

/-- Vanishing near `V̄₊` implies that the distributional support misses `V̄₊`. The
converse needs a partition of unity and is not claimed: "vanishes on a neighbourhood"
is the stronger, primitive hypothesis, which is why it is the one imposed. -/
theorem IsVanishingNearClosedForwardCone.disjoint_dsupport {u : 𝓢'(M4, ℂ)}
    (hu : IsVanishingNearClosedForwardCone u) :
    Disjoint closedForwardCone (Distribution.dsupport u) := by
  obtain ⟨s, hs, hvan⟩ := hu
  obtain ⟨t, ht_open, hKt, hts⟩ := mem_nhdsSet_iff_exists.1 hs
  exact Disjoint.mono_left hKt ((hvan.mono hts).disjoint_dsupport ht_open)

/-- A test function `f` satisfies the spectrum-condition support hypothesis when its
Minkowski Fourier transform vanishes pointwise on a neighbourhood of `V̄₊`. This is the
form a concrete model supplies (P2.6: the free-field sector computation); the
distributional form `IsVanishingNearClosedForwardCone` follows by
`FourierVanishesNearClosedForwardCone.isVanishingNear`.

Streater & Wightman, *PCT, Spin and Statistics, and All That* (Princeton Landmarks ed.
2000), Ch. 3. -/
def FourierVanishesNearClosedForwardCone (f : 𝓢(M4, ℂ)) : Prop :=
  ∃ s ∈ 𝓝ˢ closedForwardCone, Set.EqOn (𝓕η f : M4 → ℂ) 0 s

/-- A Schwartz function vanishing pointwise on a set induces a tempered distribution
vanishing on that set: for a test function supported in the set, the integrand
`x ↦ φ x • g x` is identically zero. (The converse direction, recovering pointwise
vanishing from distributional vanishing, is Reed & Simon, *Methods of Modern
Mathematical Physics II*, §IX.2, and is not needed here.) -/
theorem isVanishingOn_toTemperedDistribution {g : 𝓢(M4, ℂ)} {s : Set M4}
    (hg : Set.EqOn (g : M4 → ℂ) 0 s) :
    Distribution.IsVanishingOn (SchwartzMap.toTemperedDistributionCLM M4 ℂ volume g) s := by
  intro φ hφ
  simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply, smul_eq_mul]
  have hzero : ∀ x : M4, φ x * g x = 0 := by
    intro x
    by_cases hx : x ∈ s
    · simp [hg hx]
    · simp [image_eq_zero_of_notMem_tsupport (fun hmem => hx (hφ hmem))]
  simp [hzero]

/-- Bridge from the pointwise hypothesis to the distributional one. -/
theorem FourierVanishesNearClosedForwardCone.isVanishingNear {f : 𝓢(M4, ℂ)}
    (hf : FourierVanishesNearClosedForwardCone f) :
    IsVanishingNearClosedForwardCone
      (SchwartzMap.toTemperedDistributionCLM M4 ℂ volume (𝓕η f)) := by
  obtain ⟨s, hs, hvan⟩ := hf
  exact ⟨s, hs, isVanishingOn_toTemperedDistribution hvan⟩

/-- The integrability lemma behind the smeared translations of the spectrum condition:
for `f : 𝓢(M4, ℂ)` and a bounded continuous vector-valued map `Ψ`, `a ↦ f a • Ψ a` is
Bochner integrable, and because the codomain `H` is complete, `∫ a, f a • Ψ a` is a
definite vector of `H` (Mathlib defines the Bochner integral as junk `0` on
noncomplete codomains, so completeness is what backs the definite-integral promise).
The spectrum condition applies this with `Ψ a = U a ψ` for a strongly continuous unitary
representation `U`, where `‖U a ψ‖ = ‖ψ‖` supplies the bound; the frozen `PoincareRep`
carries exactly this completeness instance.

Reed & Simon, *Methods of Modern Mathematical Physics II*, §IX.1 (Schwartz functions are
integrable); Streater & Wightman, *PCT, Spin and Statistics, and All That* (Princeton
Landmarks ed. 2000), Ch. 3 (the smeared translations of the spectrum condition). -/
theorem integrable_smul_of_bounded {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (f : 𝓢(M4, ℂ)) {Ψ : M4 → H} (hΨ : Continuous Ψ) {C : ℝ}
    (hC : ∀ a, ‖Ψ a‖ ≤ C) :
    Integrable (fun a : M4 => f a • Ψ a) volume := by
  refine Integrable.mono' (f.integrable.norm.const_mul C)
    (f.continuous.smul hΨ).aestronglyMeasurable (Filter.Eventually.of_forall fun a => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC a) (norm_nonneg _)


/-! ### The Poincaré action on Schwartz space

The action on test functions deferred to this node by the frozen P2.4a spec: the
restricted Poincaré group acts on `𝓢(M4, ℂ)` by pullback along the inverse affine
action, `(g ▷ f)(x) = f (g⁻¹ • x)`. For `g = (a, Λ)` the point reads `Λ⁻¹ (x - a)`, so
Mathlib's Schwartz-space composition operators supply continuity and temperateness:
translation by `a` (`SchwartzMap.compSubConstCLM`) followed by composition with the
linear automorphism `Λ⁻¹` (`SchwartzMap.compCLMOfContinuousLinearEquiv`). No
temperate-growth estimate is reproved here.
-/

/-- The inverse affine action spelled out: `g⁻¹ • x = Λ⁻¹ (x - a)` for `g = (a, Λ)`.
This is the display form of the pullback argument in
`PoincareGroup.schwartzActionCLM_apply_apply`. -/
theorem PoincareGroup.inv_smul_def (g : PoincareGroup) (x : M4) :
    g⁻¹ • x = ((g.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4)
      (x - g.translation) := by
  rw [smul_def, inv_lorentz, inv_translation, map_sub, sub_eq_add_neg]
/-- **The Poincaré action on Schwartz space**: the pullback `(g ▷ f)(x) = f (g⁻¹ • x)`
for `g = (a, Λ) ∈ P↑₊`, i.e. `f ↦ f ∘ Λ⁻¹ ∘ (· - a)`, built from Mathlib's
`SchwartzMap.compSubConstCLM` and `SchwartzMap.compCLMOfContinuousLinearEquiv`.

Streater & Wightman, *PCT, Spin and Statistics, and All That* (Princeton Landmarks ed.
2000), §1-1 (the affine action whose pullback this is) and Ch. 3 (covariance of Wightman
functions under the induced action on test functions); Weinberg, *The Quantum Theory of
Fields*, Vol. I (1995), §2.3. -/
noncomputable def PoincareGroup.schwartzActionCLM (g : PoincareGroup) :
    𝓢(M4, ℂ) →L[ℂ] 𝓢(M4, ℂ) :=
  (SchwartzMap.compSubConstCLM ℂ g.translation).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((g.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4))

@[simp]
theorem PoincareGroup.schwartzActionCLM_apply_apply (g : PoincareGroup)
    (f : 𝓢(M4, ℂ)) (x : M4) :
    schwartzActionCLM g f x = f (g⁻¹ • x) := by
  simp only [schwartzActionCLM, ContinuousLinearMap.coe_comp, Function.comp_apply,
    SchwartzMap.compSubConstCLM_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    inv_smul_def]

/-- The exact display formula: `(g ▷ f)(x) = f (Λ⁻¹ (x - a))` for `g = (a, Λ)`. -/
theorem PoincareGroup.schwartzActionCLM_apply' (g : PoincareGroup) (f : 𝓢(M4, ℂ)) (x : M4) :
    schwartzActionCLM g f x
      = f (((g.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4)
        (x - g.translation)) := by
  rw [schwartzActionCLM_apply_apply, inv_smul_def]

/-- **Identity law**: the identity group element acts as the identity operator. -/
@[simp]
theorem PoincareGroup.schwartzActionCLM_one :
    schwartzActionCLM (1 : PoincareGroup) = ContinuousLinearMap.id ℂ (𝓢(M4, ℂ)) := by
  ext f x
  simp

/-- **Multiplication law — the group-law orientation**: the pullback is covariant,
`▷(g₁ * g₂) = ▷g₁ ∘L ▷g₂` for the frozen semidirect product. This is what makes the
action packageable as the monoid homomorphism `schwartzActionHom`; pulling back by the
forward affine action would compose the other way round. -/
@[simp]
theorem PoincareGroup.schwartzActionCLM_mul (g₁ g₂ : PoincareGroup) :
    schwartzActionCLM (g₁ * g₂) = (schwartzActionCLM g₁).comp (schwartzActionCLM g₂) := by
  ext f x
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    schwartzActionCLM_apply_apply]
  rw [mul_inv_rev, mul_smul]

/-- Inverse law, one side: `▷g⁻¹ ∘ ▷g = id`. -/
theorem PoincareGroup.schwartzActionCLM_mul_inv (g : PoincareGroup) :
    (schwartzActionCLM g⁻¹).comp (schwartzActionCLM g) =
      ContinuousLinearMap.id ℂ (𝓢(M4, ℂ)) := by
  rw [← schwartzActionCLM_mul, inv_mul_cancel, schwartzActionCLM_one]

/-- Inverse law, the other side: `▷g ∘ ▷g⁻¹ = id`. -/
theorem PoincareGroup.schwartzActionCLM_inv_mul (g : PoincareGroup) :
    (schwartzActionCLM g).comp (schwartzActionCLM g⁻¹) =
      ContinuousLinearMap.id ℂ (𝓢(M4, ℂ)) := by
  rw [← schwartzActionCLM_mul, mul_inv_cancel, schwartzActionCLM_one]

/-- Pointwise consequence of `schwartzActionCLM_mul_inv`: `▷g⁻¹` undoes `▷g`. -/
theorem PoincareGroup.schwartzActionCLM_apply_comp_inv (g : PoincareGroup)
    (f : 𝓢(M4, ℂ)) :
    schwartzActionCLM g⁻¹ (schwartzActionCLM g f) = f :=
  DFunLike.congr_fun (schwartzActionCLM_mul_inv g) f

/-- Pointwise consequence of `schwartzActionCLM_inv_mul`: `▷g` undoes `▷g⁻¹`. -/
theorem PoincareGroup.schwartzActionCLM_apply_inv_mul (g : PoincareGroup)
    (f : 𝓢(M4, ℂ)) :
    schwartzActionCLM g (schwartzActionCLM g⁻¹ f) = f :=
  DFunLike.congr_fun (schwartzActionCLM_inv_mul g) f

/-- **The Poincaré action as a continuous linear equivalence**; its inverse is the
action of `g⁻¹`. -/
noncomputable def PoincareGroup.schwartzActionCLE (g : PoincareGroup) :
    𝓢(M4, ℂ) ≃L[ℂ] 𝓢(M4, ℂ) :=
  ContinuousLinearEquiv.equivOfInverse (schwartzActionCLM g) (schwartzActionCLM g⁻¹)
    (schwartzActionCLM_apply_comp_inv g) (schwartzActionCLM_apply_inv_mul g)

@[simp]
theorem PoincareGroup.schwartzActionCLE_apply (g : PoincareGroup) (f : 𝓢(M4, ℂ)) :
    schwartzActionCLE g f = schwartzActionCLM g f := rfl

/-- The inverse of the equivalence is the action of the inverted group element. -/
@[simp]
theorem PoincareGroup.schwartzActionCLE_symm_apply (g : PoincareGroup)
    (f : 𝓢(M4, ℂ)) :
    (schwartzActionCLE g).symm f = schwartzActionCLM g⁻¹ f := rfl

/-- **The laws packaged**: `g ↦ ▷g` is a monoid homomorphism from the restricted
Poincaré group into the endomorphism monoid of `𝓢(M4, ℂ)` under composition — the
Schwartz-space counterpart of the frozen `PoincareRep` bundling
(`PoincareGroup →* unitary (H →L[ℂ] H)`). -/
noncomputable def PoincareGroup.schwartzActionHom :
    PoincareGroup →* (𝓢(M4, ℂ) →L[ℂ] 𝓢(M4, ℂ)) where
  toFun := schwartzActionCLM
  map_one' := schwartzActionCLM_one
  map_mul' := schwartzActionCLM_mul

end Spacetime.Minkowski
