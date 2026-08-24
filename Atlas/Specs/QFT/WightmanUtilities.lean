import Atlas.Specs.Spacetime.Minkowski
import Mathlib.Analysis.Distribution.Support

/-!
# P2.5a — Wightman utilities: the Minkowski Fourier transform, the closed forward cone,
and the spectrum-condition support hypothesis

**DRAFT spec (blueprint node P2.5a).** This file is written to the frozen-spec standard,
but it is *not* frozen: the freeze is blocked on the owner's cross-model review
(Workflow v2, CLAUDE.md — two model families must independently fail to break a spec
surface). Until that review lands, treat every statement here as a review target.

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
  Bochner integral.

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
* **Fourier normalization.** Mathlib's `𝓕` on `𝓢(V, E)` is
  `𝓕 g ξ = ∫ v, 𝐞 (-⟪v, ξ⟫) • g v` with `𝐞 t = exp (2 π i t)`, so
  `𝓕η f p = ∫ a, 𝐞 (-η(a, p)) • f a`. The `2π` sits in the exponent, so the Fourier
  variable `p` is the physical four-momentum divided by `2π`: a mass-`m` shell reads
  `4 π² (−η(p, p)) = m²`, i.e. `Ω(k) = √(4 π² ‖k‖² + m²)` in the P2.6c convention.
  This rescaling is invisible to the spectrum condition, because
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
  function vanishes near `V̄₊`" together with the cones `V̄±` of Ch. 1. Cited at chapter
  level on purpose: the numbering of the axioms inside that chapter differs between the
  editions and the secondary presentations available online, so no display number is
  asserted here.
* Reed & Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis,
  Self-Adjointness* (1975), §IX.1 — the Schwartz space `𝓢`, the Fourier transform as a
  bijection of `𝓢` onto itself, and the `e^{i p x}` versus `e^{2 π i p x}`
  normalization bookkeeping; §IX.2 — tempered distributions, their support, and the
  pairing of a Schwartz function with a tempered distribution. Cited at section level;
  no display number is asserted here.
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
`𝐞 t = exp (2 π i t)` Mathlib's `Real.fourierChar`: the exponent is the Minkowski
pairing, and the `2π` sits inside the character. Mostly-plus `η` makes this the physics
kernel `exp (2 π i (a⁰p⁰ - a⃗ · p⃗))`, i.e. the Fourier variable `p` is the physical
four-momentum divided by `2π`.

Reed & Simon, *Methods of Modern Mathematical Physics II*, §IX.1 (the `e^{2 π i p x}`
normalization of the Fourier transform on `𝓢`). -/
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
Bochner integrable, so `∫ a, f a • Ψ a` is a definite vector. The spectrum condition
applies this with `Ψ a = U a ψ` for a strongly continuous unitary representation `U`,
where `‖U a ψ‖ = ‖ψ‖` supplies the bound.

Reed & Simon, *Methods of Modern Mathematical Physics II*, §IX.1 (Schwartz functions are
integrable); Streater & Wightman, *PCT, Spin and Statistics, and All That* (Princeton
Landmarks ed. 2000), Ch. 3 (the smeared translations of the spectrum condition). -/
theorem integrable_smul_of_bounded {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (f : 𝓢(M4, ℂ)) {Ψ : M4 → H} (hΨ : Continuous Ψ) {C : ℝ} (hC : ∀ a, ‖Ψ a‖ ≤ C) :
    Integrable (fun a : M4 => f a • Ψ a) volume := by
  refine Integrable.mono' (f.integrable.norm.const_mul C)
    (f.continuous.smul hΨ).aestronglyMeasurable (Filter.Eventually.of_forall fun a => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC a) (norm_nonneg _)

end Spacetime.Minkowski
