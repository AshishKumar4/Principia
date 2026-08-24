import Atlas.Specs.QFT.WightmanUtilities
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# P2.5a witnesses — the Minkowski Fourier transform, the closed forward cone, and the
spectrum-condition support hypothesis are non-vacuous

Non-vacuity witnesses for the frozen spec `Atlas/Specs/QFT/WightmanUtilities.lean`
(blueprint node P2.5a): a concrete Schwartz test function on `M4`, concrete cone
points, and expected-true / expected-false `example`s for every definition,
including its Poincaré action on Schwartz space, exercised on the pure translation
`translateTimeUnit`.

## The concrete test functions

`Spacetime.Minkowski.testFn` and `Spacetime.Minkowski.pastFn` are `ContDiffBump`s on
`M4` pushed into `ℂ` and packaged as Schwartz functions by
`HasCompactSupport.toSchwartzMap`. `testFn` is centred on the future unit time vector
`∂₀` and `pastFn` on `-2 ∂₀`, both with radii `rIn = 1/2`, `rOut = 1`; the two centres
lie on opposite sides of the closed forward cone, which is what makes the
expected-true / expected-false pairs below decidable by kernel arithmetic:
`testFn ∂₀ = 1` and `testFn (-∂₀) = 0`, so `testFn` is genuinely not time-symmetric,
and `pastFn` vanishes on the whole half space `{v⁰ > -1}`, which contains `V̄₊`.

**Deviation from the P2.5a assignment, recorded deliberately.** The assignment asked for
the time flip to be exercised on an explicit Schwartz *Gaussian*. The pinned Mathlib has
no Gaussian packaged as a `SchwartzMap`, and the only way to build an element of
`𝓢(E, F)` from a bare function is the raw structure or `HasCompactSupport.toSchwartzMap`
(everything else maps Schwartz spaces to Schwartz spaces), so a Gaussian witness would
require proving the full seminorm decay estimates by hand. A compactly supported bump is
explicit in the same sense, has kernel-computable values at the points that matter (a
Gaussian is nowhere zero, so the expected-false pairs would need `Real.exp` injectivity
instead of a plain `0 ≠ 1`), and exercises exactly the same definitions.

## Sources

* Streater & Wightman, *PCT, Spin and Statistics, and All That* (1964; Princeton
  Landmarks in Mathematics and Physics ed. 2000), Ch. 1 (the cones `V̄±`), Ch. 3 (the
  Wightman axioms and the spectrum condition). Cited at chapter level; no display number
  is asserted here, since the numbering inside that chapter differs between the editions
  and the secondary presentations available online.
* Reed & Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis,
  Self-Adjointness* (1975), §IX.1 (the Fourier transform is a bijection of `𝓢` onto
  itself — the fact that lets the witnesses below name a preimage `testFnPre`).
-/

open MeasureTheory Metric RealInnerProductSpace
open scoped FourierTransform SchwartzMap Topology ContDiff

namespace Spacetime.Minkowski

/-! ### Time reflection on `M4` -/

/-- The future unit time vector `∂₀`, the point every cone witness below is built from
(it is the same vector the P1.W1/P1.W2 witnesses use). -/
noncomputable abbrev timeUnit : M4 := EuclideanSpace.single 0 1

/-- The unit `x¹` direction `∂₁`, the spacelike reference vector of the P1.W2
witnesses. -/
noncomputable abbrev spaceUnit : M4 := EuclideanSpace.single 1 1

@[simp]
theorem timeUnit_apply_zero : timeUnit 0 = 1 := by simp

@[simp]
theorem spaceUnit_apply_zero : spaceUnit 0 = 0 := by simp

-- Expected-true: time reflection flips the time direction.
theorem timeReflection_timeUnit : timeReflection timeUnit = -timeUnit := by
  rw [timeReflection_apply, timeReflectionCLM_apply, timeUnit_apply_zero]
  module

-- Expected-true: time reflection fixes the spatial directions.
theorem timeReflection_spaceUnit : timeReflection spaceUnit = spaceUnit := by
  rw [timeReflection_apply, timeReflectionCLM_apply, spaceUnit_apply_zero]
  simp

theorem timeReflection_neg_timeUnit : timeReflection (-timeUnit) = timeUnit := by
  rw [← timeReflection_timeUnit, timeReflection_involutive]

-- Expected-false: time reflection is not the identity.
example : timeReflection timeUnit ≠ timeUnit := by
  rw [timeReflection_timeUnit]
  intro h
  have h0 : (-timeUnit : M4) 0 = timeUnit 0 := by rw [h]
  norm_num at h0

-- Expected-true: the reflected pairing is the Minkowski form — `η(∂₀, ∂₀) = -1`.
example : ⟪timeUnit, timeReflection timeUnit⟫ = -1 := by
  rw [inner_timeReflection_right, minkowskiForm_eq]
  simp [Fin.ext_iff]

-- Expected-false: the *unreflected* (Euclidean) pairing has the opposite sign, so
-- dropping the time reflection would change the Fourier kernel. This is the whole
-- reason `timeReflection` exists.
example : ⟪timeUnit, timeUnit⟫ ≠ minkowskiForm timeUnit timeUnit := by
  rw [minkowskiForm_eq]
  simp [Fin.ext_iff]
  norm_num

/-! ### A concrete Schwartz function on `M4` -/

/-- A bump function centred on the future unit time vector `∂₀`, with radii
`1/2 < 1`. -/
noncomputable def bumpFuture : ContDiffBump (timeUnit : M4) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- A bump function centred on the past point `-2 ∂₀`, with radii `1/2 < 1`. -/
noncomputable def bumpPast : ContDiffBump (EuclideanSpace.single (0 : Fin 4) (-2 : ℝ) : M4) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The witness test function: `bumpFuture` viewed in `ℂ`, as a Schwartz function. It is
smooth and compactly supported, hence Schwartz. -/
noncomputable def testFn : 𝓢(M4, ℂ) :=
  HasCompactSupport.toSchwartzMap
    (f := fun x : M4 => ((bumpFuture x : ℝ) : ℂ))
    (bumpFuture.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp bumpFuture.contDiff)

/-- The past-supported witness test function. -/
noncomputable def pastFn : 𝓢(M4, ℂ) :=
  HasCompactSupport.toSchwartzMap
    (f := fun x : M4 => ((bumpPast x : ℝ) : ℂ))
    (bumpPast.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp bumpPast.contDiff)

theorem testFn_apply (x : M4) : testFn x = ((bumpFuture x : ℝ) : ℂ) := rfl

theorem pastFn_apply (x : M4) : pastFn x = ((bumpPast x : ℝ) : ℂ) := rfl

-- Expected-true: the bump is `1` at its centre.
theorem testFn_timeUnit : testFn timeUnit = 1 := by
  rw [testFn_apply,
    bumpFuture.one_of_mem_closedBall (mem_closedBall_self bumpFuture.rIn_pos.le)]
  norm_num

-- Expected-false: the bump vanishes at the time-reflected centre, two units away.
theorem testFn_neg_timeUnit : testFn (-timeUnit) = 0 := by
  rw [testFn_apply, bumpFuture.zero_of_le_dist ?_]
  · norm_num
  · show (1 : ℝ) ≤ _
    rw [dist_eq_norm]
    have h : (-timeUnit : M4) - timeUnit = (-2 : ℝ) • (timeUnit : M4) := by module
    rw [h, norm_smul]
    simp

/-! ### The Schwartz-level time reflection -/

-- Expected-true: the Schwartz time flip moves the bump to the past.
example : timeReflectionSchwartzCLM testFn (-timeUnit) = 1 := by
  rw [timeReflectionSchwartzCLM_apply_apply, timeReflection_neg_timeUnit, testFn_timeUnit]

-- Expected-false: the Schwartz time flip is not the identity — `testFn` is not
-- time-symmetric.
theorem timeReflectionSchwartzCLM_testFn_ne : timeReflectionSchwartzCLM testFn ≠ testFn := by
  intro h
  have hval : timeReflectionSchwartzCLM testFn (-timeUnit) = testFn (-timeUnit) := by rw [h]
  rw [timeReflectionSchwartzCLM_apply_apply, timeReflection_neg_timeUnit, testFn_timeUnit,
    testFn_neg_timeUnit] at hval
  exact one_ne_zero hval

-- Expected-true: the Schwartz time flip is an involution.
example : timeReflectionSchwartzCLM (timeReflectionSchwartzCLM testFn) = testFn :=
  timeReflectionSchwartzCLM_involutive testFn

/-! ### The Minkowski Fourier transform `𝓕η` -/

/-- A Fourier preimage of `testFn`. It exists because Mathlib's Schwartz Fourier
transform is a continuous linear equivalence (Reed & Simon, *Methods of Modern
Mathematical Physics II*, §IX.1). -/
noncomputable def testFnPre : 𝓢(M4, ℂ) :=
  (FourierTransform.fourierCLE ℂ 𝓢(M4, ℂ)).symm testFn

theorem fourier_testFnPre : 𝓕 testFnPre = testFn :=
  FourierTransform.fourier_fourierInv_eq testFn

-- Expected-true: `𝓕η` is the Fourier transform followed by the time flip.
example : 𝓕η testFnPre = timeReflectionSchwartzCLM testFn := by
  rw [fourierMinkowski_apply, fourier_testFnPre]

-- Expected-false: `𝓕η` is NOT Mathlib's Euclidean Fourier transform. Since `𝓕` is onto
-- `𝓢(M4, ℂ)`, one non-time-symmetric target value is enough to separate them.
example : 𝓕η testFnPre ≠ 𝓕 testFnPre := by
  rw [fourierMinkowski_apply, fourier_testFnPre]
  exact timeReflectionSchwartzCLM_testFn_ne

-- Expected-true: `𝓕η` is invertible (it is a continuous linear equivalence).
example : fourierMinkowskiCLE.symm (𝓕η testFn) = testFn :=
  fourierMinkowskiCLE.symm_apply_apply testFn

/-! ### The closed forward cone -/

-- Expected-true: the apex belongs to the CLOSED cone...
example : (0 : M4) ∈ closedForwardCone := zero_mem_closedForwardCone

-- ...while the frozen P2.4a cone is punctured at the apex. This pair is the
-- closed-versus-punctured discriminator: the vacuum has zero four-momentum, so the
-- spectrum condition needs the apex.
example : ¬ InFutureCausalCone (0 : M4) := by
  rintro ⟨-, h0⟩
  simp at h0

-- Expected-true: the future unit time vector is in the cone.
example : (timeUnit : M4) ∈ closedForwardCone := by
  rw [mem_closedForwardCone_iff]
  norm_num [Fin.ext_iff]

-- Expected-true: the null boundary belongs to the closed cone.
theorem null_mem_closedForwardCone : (timeUnit + spaceUnit : M4) ∈ closedForwardCone := by
  rw [mem_closedForwardCone_iff]
  norm_num [Fin.ext_iff]

-- ...while the open time cone excludes it. This pair is the open-versus-closed
-- discriminator: massless momenta sit on the null boundary.
example : ¬ InFutureTimeCone (timeUnit + spaceUnit : M4) := by
  rintro ⟨h1, -⟩
  simp [Fin.ext_iff] at h1

-- Expected-false: a spacelike vector is outside the cone.
example : (spaceUnit : M4) ∉ closedForwardCone :=
  IsSpacelike.notMem_closedForwardCone (by rw [isSpacelike_iff]; norm_num [Fin.ext_iff])

-- Expected-false: a past-pointing vector is outside the cone.
theorem neg_timeUnit_notMem_closedForwardCone : (-timeUnit : M4) ∉ closedForwardCone := by
  rw [mem_closedForwardCone_iff]
  rintro ⟨-, h0⟩
  simp at h0
  linarith

-- Expected-true: the cone is closed under addition (frozen `InFutureCausalCone.add`).
example : (timeUnit + (timeUnit + spaceUnit) : M4) ∈ closedForwardCone :=
  closedForwardCone.add_mem (by rw [mem_closedForwardCone_iff]; norm_num [Fin.ext_iff])
    null_mem_closedForwardCone

-- Expected-true: the cone is stable under the positive rescaling that Mathlib's `2π`
-- Fourier normalization induces on the frequency variable.
example : ((2 * Real.pi) • timeUnit : M4) ∈ closedForwardCone :=
  closedForwardCone.smul_mem (by positivity)
    (by rw [mem_closedForwardCone_iff]; norm_num [Fin.ext_iff])

-- Expected-true: the cone is a closed set.
example : IsClosed (closedForwardCone : Set M4) := isClosed_closedForwardCone

/-! ### The spectrum-condition support hypothesis -/

/-- The open half space `{v⁰ > -1}` is a neighbourhood of the closed forward cone: every
cone point has `v⁰ ≥ 0`. -/
theorem halfSpace_mem_nhdsSet : {v : M4 | -1 < v 0} ∈ 𝓝ˢ closedForwardCone := by
  refine IsOpen.mem_nhdsSet ?_ |>.2 ?_
  · exact isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 4)).continuous
  · intro v hv
    exact lt_of_lt_of_le (by norm_num) ((mem_closedForwardCone_iff v).1 hv).2

private theorem abs_apply_le_norm (x : M4) (i : Fin 4) : |x i| ≤ ‖x‖ := by
  have h : x i = ⟪(EuclideanSpace.single i (1 : ℝ) : M4), x⟫ := by
    simp [EuclideanSpace.inner_single_left]
  rw [h]
  calc |⟪(EuclideanSpace.single i (1 : ℝ) : M4), x⟫|
      ≤ ‖(EuclideanSpace.single i (1 : ℝ) : M4)‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ = ‖x‖ := by simp

private theorem abs_sub_apply_le_dist (x y : M4) (i : Fin 4) : |x i - y i| ≤ dist x y := by
  rw [dist_eq_norm]
  have h : x i - y i = (x - y) i := rfl
  rw [h]
  exact abs_apply_le_norm _ i

/-- `pastFn` vanishes on the whole half space `{v⁰ > -1}`: its support sits inside the
unit ball around `-2 ∂₀`. -/
theorem pastFn_eqOn_halfSpace :
    Set.EqOn (pastFn : M4 → ℂ) 0 {v : M4 | -1 < v 0} := by
  intro x hx
  have hd : (1 : ℝ) ≤ dist x (EuclideanSpace.single (0 : Fin 4) (-2 : ℝ) : M4) := by
    have hb := abs_sub_apply_le_dist x (EuclideanSpace.single (0 : Fin 4) (-2 : ℝ) : M4) 0
    have hc : (EuclideanSpace.single (0 : Fin 4) (-2 : ℝ) : M4) 0 = -2 := by simp
    rw [hc] at hb
    have hx' : -1 < x 0 := hx
    have hone : (1 : ℝ) ≤ |x 0 - -2| := by rw [abs_of_nonneg (by linarith)]; linarith
    linarith
  simp [pastFn_apply, bumpPast.zero_of_le_dist (show bumpPast.rOut ≤ _ from hd)]

-- Expected-true: the past-supported bump satisfies the spectrum-condition support
-- hypothesis, so the hypothesis is not vacuous. `𝓕η` is onto, so a preimage exists.
theorem fourierVanishes_symm_pastFn :
    FourierVanishesNearClosedForwardCone (fourierMinkowskiCLE.symm pastFn) := by
  refine ⟨{v : M4 | -1 < v 0}, halfSpace_mem_nhdsSet, ?_⟩
  rw [fourierMinkowskiCLE.apply_symm_apply]
  exact pastFn_eqOn_halfSpace

-- Expected-false: a test function whose Minkowski Fourier transform is nonzero at a
-- cone point does NOT satisfy it.
example : ¬ FourierVanishesNearClosedForwardCone (fourierMinkowskiCLE.symm testFn) := by
  rintro ⟨s, hs, heq⟩
  rw [fourierMinkowskiCLE.apply_symm_apply] at heq
  have hmem : (timeUnit : M4) ∈ s :=
    subset_of_mem_nhdsSet hs (by rw [mem_closedForwardCone_iff]; norm_num [Fin.ext_iff])
  have h1 : testFn timeUnit = 0 := heq hmem
  rw [testFn_timeUnit] at h1
  exact one_ne_zero h1

-- Expected-true: the bridge to the distributional form of the hypothesis.
example : IsVanishingNearClosedForwardCone
    (SchwartzMap.toTemperedDistributionCLM M4 ℂ volume (𝓕η (fourierMinkowskiCLE.symm pastFn))) :=
  fourierVanishes_symm_pastFn.isVanishingNear

-- Expected-true: a delta at a past point vanishes near the closed forward cone.
example : IsVanishingNearClosedForwardCone (TemperedDistribution.delta (-timeUnit : M4)) := by
  refine ⟨{(-timeUnit : M4)}ᶜ, ?_, TemperedDistribution.isVanishingOn_delta _⟩
  refine isOpen_compl_singleton.mem_nhdsSet.2 fun v hv hmem => ?_
  rw [Set.mem_singleton_iff] at hmem
  exact neg_timeUnit_notMem_closedForwardCone (hmem ▸ hv)

-- Expected-false: a delta at the apex does NOT — its distributional support is exactly
-- the zero four-momentum, which is in the cone.
example : ¬ IsVanishingNearClosedForwardCone (TemperedDistribution.delta (0 : M4)) := by
  intro h
  have hd := h.disjoint_dsupport
  rw [Distribution.dsupport_delta] at hd
  exact Set.disjoint_singleton_right.1 hd zero_mem_closedForwardCone

/-! ### The Poincaré action on Schwartz space -/

/-- Pure translation by the future unit time vector `∂₀`: the nontrivial-translation
witness element `(∂₀, 1)` of `P↑₊`. -/
noncomputable def translateTimeUnit : PoincareGroup :=
  ⟨timeUnit, (1 : RestrictedLorentzGroup)⟩

theorem translateTimeUnit_inv :
    translateTimeUnit⁻¹ = ⟨-timeUnit, (1 : RestrictedLorentzGroup)⟩ :=
  PoincareGroup.ext (by simp [translateTimeUnit]; rfl) (by simp [translateTimeUnit])

theorem inv_smul_translateTimeUnit (x : M4) :
    translateTimeUnit⁻¹ • x = x - timeUnit := by
  rw [translateTimeUnit_inv, PoincareGroup.smul_def, Subgroup.coe_one]
  show x + -timeUnit = x - timeUnit
  rw [sub_eq_add_neg]

theorem inv_smul_translateTimeUnit_two :
    translateTimeUnit⁻¹ • ((2 : ℝ) • timeUnit) = timeUnit := by
  rw [inv_smul_translateTimeUnit]
  have h : (2 : ℝ) • (timeUnit : M4) - timeUnit = timeUnit := by module
  rw [h]

/-- The bump vanishes two units past its centre, where the translated argument lands. -/
theorem testFn_two_timeUnit : testFn ((2 : ℝ) • timeUnit) = 0 := by
  rw [testFn_apply, bumpFuture.zero_of_le_dist ?_]
  · norm_num
  · show (1 : ℝ) ≤ _
    rw [dist_eq_norm]
    have h : (2 : ℝ) • (timeUnit : M4) - timeUnit = timeUnit := by module
    rw [h]
    simp

/-- The bump also vanishes three units out — the point where acting twice has moved it. -/
theorem testFn_three_timeUnit : testFn ((3 : ℝ) • timeUnit) = 0 := by
  rw [testFn_apply, bumpFuture.zero_of_le_dist ?_]
  · norm_num
  · show (1 : ℝ) ≤ _
    rw [dist_eq_norm]
    have h : (3 : ℝ) • (timeUnit : M4) - timeUnit = (2 : ℝ) • timeUnit := by module
    rw [h, norm_smul]
    simp

-- Expected-true: the identity acts trivially.
example : PoincareGroup.schwartzActionCLM 1 testFn = testFn := by
  rw [PoincareGroup.schwartzActionCLM_one]
  rfl

-- Expected-false: a nontrivial translation moves the bump off its centre.
example : PoincareGroup.schwartzActionCLM translateTimeUnit testFn ≠ testFn := by
  intro h
  have hval := DFunLike.congr_fun h ((2 : ℝ) • timeUnit)
  rw [PoincareGroup.schwartzActionCLM_apply_apply, inv_smul_translateTimeUnit_two,
    testFn_timeUnit, testFn_two_timeUnit] at hval
  exact one_ne_zero hval

-- Expected-true: the Schwartz-level equivalence round-trips through the inverted
-- group element.
example (g : PoincareGroup) (f : 𝓢(M4, ℂ)) :
    PoincareGroup.schwartzActionCLE g⁻¹ (PoincareGroup.schwartzActionCLE g f) = f := by
  rw [PoincareGroup.schwartzActionCLE_apply, PoincareGroup.schwartzActionCLE_apply]
  exact PoincareGroup.schwartzActionCLM_apply_comp_inv g f

-- Expected-true: the concrete round-trip at the witness translation evaluates back to
-- the untouched bump.
example : PoincareGroup.schwartzActionCLE translateTimeUnit⁻¹
    (PoincareGroup.schwartzActionCLE translateTimeUnit testFn) timeUnit = 1 := by
  rw [PoincareGroup.schwartzActionCLE_apply, PoincareGroup.schwartzActionCLE_apply,
    PoincareGroup.schwartzActionCLM_apply_comp_inv, testFn_timeUnit]

-- Expected-true: translations compose in the covariant order — acting twice shifts the
-- argument twice, so the bump reappears one unit before `3∂₀`.
theorem schwartzAction_translateTimeUnit_sq :
    PoincareGroup.schwartzActionCLM (translateTimeUnit * translateTimeUnit) testFn
      ((3 : ℝ) • timeUnit) = 1 := by
  rw [PoincareGroup.schwartzActionCLM_mul, ContinuousLinearMap.coe_comp,
    Function.comp_apply, PoincareGroup.schwartzActionCLM_apply_apply,
    inv_smul_translateTimeUnit]
  have h : (3 : ℝ) • (timeUnit : M4) - timeUnit = (2 : ℝ) • timeUnit := by module
  rw [h, PoincareGroup.schwartzActionCLM_apply_apply, inv_smul_translateTimeUnit_two,
    testFn_timeUnit]

-- Expected-false: the double translation is not the identity — the untouched bump
-- vanishes at the very point where the doubly-translated one peaks.
example : PoincareGroup.schwartzActionCLM (translateTimeUnit * translateTimeUnit) testFn
    ≠ testFn := by
  intro h
  have hval := DFunLike.congr_fun h ((3 : ℝ) • timeUnit)
  rw [schwartzAction_translateTimeUnit_sq, testFn_three_timeUnit] at hval
  exact one_ne_zero hval

-- Expected-true: the monoid-hom packaging engages Mathlib's generic `map_mul`.
example (g₁ g₂ : PoincareGroup) :
    PoincareGroup.schwartzActionHom (g₁ * g₂)
      = PoincareGroup.schwartzActionHom g₁ * PoincareGroup.schwartzActionHom g₂ :=
  map_mul _ g₁ g₂

-- Expected-true: instantiated at a bounded continuous integrand, `∫ a, f a • Ψ a` is a
-- definite Bochner integral.
example : Integrable (fun a : M4 => testFn a • (1 : ℂ)) volume :=
  integrable_smul_of_bounded testFn continuous_const (C := 1) (fun _ => by simp)

end Spacetime.Minkowski
