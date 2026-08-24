import Atlas.Proofs.KleinGordon

/-!
# P2.6b — the invariant positive mass-shell measure

Second foundation lane of the momentum-measure node (**P2.6b**), building on the frozen L0
layer `Atlas.Proofs.KleinGordon`. Everything lives on the time-zero slice `M3 = ℝ³` of the
frozen Minkowski carrier `Spacetime.Minkowski.M4`.

The existing `onShell m k` is parametrized by the **Fourier frequency** `k` of Mathlib's
`e^{-2πi⟪x,ξ⟫}` normalization; its spatial part is the physical momentum `2πk`. This module
introduces the **physical-momentum** parametrization of the positive sheet,

* `QFT.KleinGordon.massShellParam m p = (√(‖p‖² + m²), p)`,

proves its geometry (the form identity `η(q, q) = -m²`, the future-cone anchor, injectivity,
and the exact range characterization `range (massShellParam m) = massShell m` for `0 < m`),
and defines the **Lorentz-invariant candidate measure** on the sheet as the pushforward of
`d³p / (2 ω_p)`:

* `QFT.KleinGordon.massShellMeasure m =
    map (massShellParam m) (volume.withDensity (p ↦ ofReal (1 / (2 ω_p))))`,

together with the exact pushforward formulas for `lintegral` and `integral`, the nullness of
the complement of the shell, and the Fourier-coordinate form carrying the **explicit**
`(2π)³` Jacobian: in frequency coordinates the same measure reads
`(2π)³ · dk / (2 Ω(k))` pushed forward along `onShell m` — the `dk / (2Ω(k))` shortcut
without the factor is wrong under the repo's Fourier convention.

## Contents

* `QFT.KleinGordon.physicalEnergy` — the physical energy `ω_p = √(‖p‖² + m²)` with square
  identity, positivity (`0 < m`), continuity/smoothness, measurability, and the conversion
  `physicalEnergy m (2π • k) = dispersion m k`.
* `QFT.KleinGordon.massShellParam` — the physical-momentum parametrization `p ↦ (ω_p, p)`;
  coordinate simp lemmas, continuity, measurability, injectivity, the mass-shell identity
  `minkowskiForm_massShellParam_self`, the future-cone fact, and the two conversions
  `onShell_eq_massShellParam` / `massShellParam_eq_onShell` tying it to the frozen L0
  frequency parametrization.
* `QFT.KleinGordon.massShell` — the positive sheet `{q | η(q,q) = -m² ∧ 0 < q⁰}` as a
  measurable set, with the exact characterization `mem_range_massShellParam` of the range of
  `massShellParam m` for `0 < m`.
* `QFT.KleinGordon.massShellDensity` / `QFT.KleinGordon.massShellMeasure` — the weight
  `d³p/(2ω_p)` as an `ℝ≥0∞`-valued density (measurable, a.e.-finite) and the pushforward
  measure, with `massShellMeasure_apply`, `lintegral_massShellMeasure`,
  `integral_massShellMeasure`, and `massShellMeasure_compl_null`.
* `QFT.KleinGordon.massShellMeasure_eq_map_onShell` /
  `QFT.KleinGordon.lintegral_massShellMeasure_fourier` — the Fourier-coordinate identity
  with the explicit `(2π)³` Jacobian.

## Conventions

* Fourier normalization is Mathlib's `e^{-2πi⟪x,ξ⟫}` (see the conventions block of
  `Atlas/Proofs/KleinGordon.lean`): a spatial **frequency** `k` corresponds to the physical
  momentum `p = 2πk`, and `d³p = (2π)³ d³k`. Every `dk`-formula below therefore carries the
  explicit `(2π)³`; nothing silently identifies `d³p/(2ω)` with `dk/(2Ω)`.
* Minkowski sign convention is the frozen mostly-plus one: the positive mass shell is
  `η(p, p) = -m²` with `p⁰ > 0`.
* The density is normalized with the modern free-field factor `1/2`:
  `d³p/(2ω_p)` rather than Wigner's `d³p/p⁰`. The two differ by the conventional constant
  `1/2` and have identical Lorentz-transformation behavior.

## Sources

* E. P. Wigner, *On Unitary Representations of the Inhomogeneous Lorentz Group*, Annals of
  Mathematics 40 (1939), §6, eq. (59a): the scalar product of wave functions carried by the
  mass hyperboloid `p·p = P` is the integral against the weight `|p₄|⁻¹ dp₁dp₂dp₃`, i.e. the
  invariant measure `d³p/p⁰` on the hyperboloid; footnote 26 of that section records that the
  invariance of such integrals follows from the Jacobian of the Lorentz transformation.
  Cited at section level with the display equation read directly from the 1939 text.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II*, Academic Press (1975),
  §X.7 *Free quantum fields* — cited at section level (matching `KleinGordon.lean`): the free
  field of mass `m` is built from the mass shell `H_m` and its one-particle energy `μ(p)`;
  no display number of that section is asserted here beyond the `(X.80)` reference already
  fixed in `KleinGordon.lean`.
* R. F. Streater, A. S. Wightman, *PCT, Spin and Statistics, and All That* (1964; Princeton
  Landmarks ed. 2000), Ch. 3 — cited at chapter level: the spectrum-condition/forward-cone
  framework whose one-particle input this measure supplies.
-/

open MeasureTheory Real Spacetime.Minkowski
open scoped ENNReal

namespace QFT.KleinGordon

/-! ### The physical energy on the spatial momentum slice -/

/-- The **physical energy** `ω_p = √(‖p‖² + m²)` of a physical spatial momentum `p : M3`:
the time component of `massShellParam m p`, and the value of the dispersion relation at the
Fourier frequency `k` with `p = 2πk` (Wigner 1939, §6, eq. (59a): `p₄ = √(m² + p₁² + p₂² +
p₃²)` on the mass hyperboloid). -/
noncomputable def physicalEnergy (m : ℝ) (p : M3) : ℝ :=
  √(‖p‖ ^ 2 + m ^ 2)

variable (m : ℝ) (p : M3)

/-- The square identity `ω_p² = ‖p‖² + m²`. -/
theorem physicalEnergy_sq : physicalEnergy m p ^ 2 = ‖p‖ ^ 2 + m ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The physical energy is nonnegative. -/
@[simp] theorem physicalEnergy_nonneg : 0 ≤ physicalEnergy m p :=
  Real.sqrt_nonneg _

theorem physicalEnergy_pos (hm : 0 < m) : 0 < physicalEnergy m p := by
  refine Real.sqrt_pos.mpr ?_
  have hm2 : 0 < m ^ 2 := sq_pos_iff.mpr hm.ne'
  nlinarith [norm_nonneg p]

/-- Continuity of the physical energy. -/
@[fun_prop] theorem continuous_physicalEnergy : Continuous (physicalEnergy m) :=
  Real.continuous_sqrt.comp (by fun_prop)

/-- Smoothness of the physical energy for nonzero mass: the radicand is bounded below by
`m² > 0`, so `Real.sqrt` is smooth on the whole range. -/
theorem contDiff_physicalEnergy {n : WithTop ℕ∞} (hm : m ≠ 0) :
    ContDiff ℝ n (physicalEnergy m) := by
  have hsmooth : ContDiff ℝ n fun x : M3 => ‖x‖ ^ 2 + m ^ 2 :=
    (contDiff_norm_sq ℝ).add contDiff_const
  refine hsmooth.sqrt fun x => ne_of_gt ?_
  have hm2 : 0 < m ^ 2 := sq_pos_iff.mpr hm
  nlinarith [norm_nonneg x]

/-- Measurability of the physical energy (from continuity). -/
theorem measurable_physicalEnergy : Measurable (physicalEnergy m) :=
  continuous_physicalEnergy m |>.measurable

/-- The physical energy of the momentum `2πk` attached to Fourier frequency `k` is exactly
the dispersion relation `Ω(k)` of the frozen L0 layer. -/
theorem physicalEnergy_two_pi_smul (k : M3) :
    physicalEnergy m ((2 * π : ℝ) • k) = dispersion m k := by
  rw [physicalEnergy, dispersion, norm_smul, Real.norm_eq_abs,
    abs_of_pos (show 0 < (2 : ℝ) * π from by positivity)]
  congr 1
  ring

/-! ### The physical-momentum parametrization of the positive mass shell -/

/-- The **positive-energy mass-shell parametrization** in physical momentum:
`massShellParam m p = (√(‖p‖² + m²), p) ∈ M4`. Its image (for `0 < m`) is the positive sheet
of the hyperboloid `η(q, q) = -m²` (Wigner 1939, §6, eq. (59a); Reed & Simon II, §X.7). -/
noncomputable def massShellParam (m : ℝ) (p : M3) : M4 :=
  !₂[physicalEnergy m p, p 0, p 1, p 2]

@[simp] theorem massShellParam_apply_zero : massShellParam m p 0 = physicalEnergy m p := by
  simp [massShellParam]

@[simp] theorem massShellParam_apply_one : massShellParam m p 1 = p 0 := by
  simp [massShellParam]

@[simp] theorem massShellParam_apply_two : massShellParam m p 2 = p 1 := by
  simp [massShellParam]

@[simp] theorem massShellParam_apply_three : massShellParam m p 3 = p 2 := by
  simp [massShellParam]

/-- Coordinate expansion of the squared Euclidean norm on `M3`. -/
private theorem norm_sq_three (x : M3) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

/-- The parametrization is continuous. -/
@[fun_prop] theorem continuous_massShellParam : Continuous (massShellParam m) := by
  have hpe : Continuous (physicalEnergy m) := continuous_physicalEnergy m
  show Continuous fun p : M3 => (!₂[physicalEnergy m p, p 0, p 1, p 2] : M4)
  fun_prop

/-- The parametrization is measurable. -/
theorem measurable_massShellParam : Measurable (massShellParam m) :=
  continuous_massShellParam m |>.measurable

/-- The parametrization is injective: the three spatial coordinates recover `p`. -/
theorem injective_massShellParam : Function.Injective (massShellParam m) := by
  intro p₁ p₂ h
  ext i
  fin_cases i
  · simpa using congrArg (fun q : M4 => q 1) h
  · simpa using congrArg (fun q : M4 => q 2) h
  · simpa using congrArg (fun q : M4 => q 3) h

/-- **The mass-shell identity** for the physical-momentum parametrization:
`η(q, q) = -m²` for `q = massShellParam m p` (Wigner 1939, §6: `p₄² - p₁² - p₂² - p₃² = m²`
in his mostly-minus signs; here mostly-plus). -/
theorem minkowskiForm_massShellParam_self :
    minkowskiForm (massShellParam m p) (massShellParam m p) = -(m ^ 2) := by
  have hprod : physicalEnergy m p * physicalEnergy m p =
      p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + m ^ 2 := by
    rw [← pow_two (physicalEnergy m p), physicalEnergy_sq, norm_sq_three]
  rw [minkowskiForm_eq, massShellParam_apply_zero, massShellParam_apply_one,
    massShellParam_apply_two, massShellParam_apply_three, hprod]
  ring

/-- The parametrized four-momentum lies in the frozen open future time cone for `0 < m`. -/
theorem massShellParam_inFutureTimeCone (hm : 0 < m) :
    InFutureTimeCone (massShellParam m p) := by
  have hm2 : 0 < m ^ 2 := sq_pos_iff.mpr hm.ne'
  refine ⟨?_, by simpa using physicalEnergy_pos m p hm⟩
  rw [massShellParam_apply_zero, massShellParam_apply_one, massShellParam_apply_two,
    massShellParam_apply_three, physicalEnergy_sq, norm_sq_three]
  linarith

/-- **Conversion to the frozen L0 frequency parametrization**: `onShell m k` is the
parametrization evaluated at the physical momentum `2πk` conjugate to the Fourier frequency
`k` of Mathlib's transform. -/
theorem onShell_eq_massShellParam (k : M3) :
    onShell m k = massShellParam m ((2 * π : ℝ) • k) := by
  ext j
  fin_cases j
  · simpa using (physicalEnergy_two_pi_smul m k).symm
  · simp
  · simp
  · simp

/-- The converse conversion: the parametrization at physical momentum `p` is `onShell` at
the frequency `(2π)⁻¹p`. -/
theorem massShellParam_eq_onShell (p : M3) :
    massShellParam m p = onShell m ((2 * π : ℝ)⁻¹ • p) := by
  rw [onShell_eq_massShellParam]
  congr 1
  rw [smul_smul, mul_inv_cancel₀ (show (2 : ℝ) * π ≠ 0 by positivity), one_smul]

/-! ### The positive sheet as a measurable set -/

/-- The **positive sheet** of the mass hyperboloid of mass `m` in the frozen carrier:
`{q | η(q, q) = -m² ∧ 0 < q⁰}`. This is the support carrier of the invariant measure
(Wigner 1939, §6, eq. (59a): the orbit `p·p = m², p₄ > 0`). -/
def massShell (m : ℝ) : Set M4 :=
  {q : M4 | minkowskiForm q q = -(m ^ 2) ∧ 0 < q 0}

/-- The squared self-form `q ↦ η(q, q)` is measurable (it is a polynomial in the
coordinates). -/
theorem measurable_minkowskiForm_self : Measurable fun q : M4 => minkowskiForm q q := by
  have hEq : (fun q : M4 => minkowskiForm q q)
      = fun q : M4 => (-(q 0 * q 0) + q 1 * q 1 + q 2 * q 2 + q 3 * q 3) := by
    funext q
    rw [minkowskiForm_eq]
  rw [hEq]
  fun_prop

/-- The positive sheet is measurable. -/
theorem measurableSet_massShell (m : ℝ) : MeasurableSet (massShell m) := by
  have h1 : MeasurableSet {q : M4 | minkowskiForm q q = -(m ^ 2)} :=
    measurable_minkowskiForm_self (measurableSet_singleton (-(m ^ 2)))
  have h2 : MeasurableSet {q : M4 | 0 < q 0} := by
    have hEq : {q : M4 | 0 < q 0} = (fun q : M4 => q 0) ⁻¹' Set.Ioi (0 : ℝ) := rfl
    rw [hEq]
    exact ((EuclideanSpace.proj 0).continuous.measurable) measurableSet_Ioi
  have hEq : massShell m =
      {q : M4 | minkowskiForm q q = -(m ^ 2)} ∩ {q : M4 | 0 < q 0} := rfl
  rw [hEq]
  exact h1.inter h2

/-- Every parametrized point lies on the positive sheet when the mass is positive. -/
theorem massShellParam_mem_massShell (hm : 0 < m) :
    massShellParam m p ∈ massShell m :=
  ⟨minkowskiForm_massShellParam_self m p, by simpa using physicalEnergy_pos m p hm⟩

/-- **Exact range characterization**: for `0 < m` the image of the physical-momentum
parametrization is exactly the positive sheet — forward because `ω_p > 0` and
`η(q, q) = -m²` on parametrized points, backward because a point of the sheet satisfies
`q⁰ = √((q¹)² + (q²)² + (q³)² + m²)` (Wigner 1939, §6: `p₄ = √(m² + p₁² + p₂² + p₃²)`,
eq. (59a) context). -/
theorem mem_range_massShellParam (hm : 0 < m) (q : M4) :
    q ∈ Set.range (massShellParam m) ↔ q ∈ massShell m := by
  constructor
  · rintro ⟨p, rfl⟩
    exact massShellParam_mem_massShell m p hm
  · rintro ⟨hform, hpos⟩
    have hform' : -(q 0 * q 0) + q 1 * q 1 + q 2 * q 2 + q 3 * q 3 = -(m ^ 2) := by
      rw [← minkowskiForm_eq]; exact hform
    have hsq : ‖(!₂[q 1, q 2, q 3] : M3)‖ ^ 2 = q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 := by
      rw [norm_sq_three]
      simp
    have htime : physicalEnergy m (!₂[q 1, q 2, q 3] : M3) = q 0 := by
      have hsquare : physicalEnergy m (!₂[q 1, q 2, q 3] : M3) ^ 2 = q 0 ^ 2 := by
        rw [physicalEnergy_sq, hsq]
        nlinarith
      have h1 : q 0 = Real.sqrt (q 0 ^ 2) := (Real.sqrt_sq hpos.le).symm
      rw [h1, ← hsquare]
      exact (Real.sqrt_sq (physicalEnergy_nonneg m _)).symm
    refine ⟨!₂[q 1, q 2, q 3], ?_⟩
    ext j
    fin_cases j
    · simpa using htime
    · simp
    · simp
    · simp

/-! ### The invariant candidate measure -/

/-- The **Lorentz-invariant weight** `d³p/(2ω_p)` of the positive mass shell as a density:
`p ↦ ofReal (1 / (2 ω_p))` (Wigner 1939, §6, eq. (59a), up to the conventional constant
factor `1/2`; Reed & Simon II, §X.7, section-level). -/
noncomputable def massShellDensity (m : ℝ) (p : M3) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * physicalEnergy m p))

/-- Measurability of densities of the shape `ofReal (1/(2·f))` for measurable real `f`. -/
private theorem measurable_ofReal_inv_two {h : M3 → ℝ} (hh : Measurable h) :
    Measurable fun x : M3 => ENNReal.ofReal (1 / (2 * h x)) :=
  by
    simp only [one_div]
    exact Measurable.ennreal_ofReal ((hh.const_mul 2).inv)

/-- The weight is measurable. -/
theorem measurable_massShellDensity : Measurable (massShellDensity m) :=
  measurable_ofReal_inv_two (measurable_physicalEnergy m)

/-- The weight is everywhere finite (its values are real coercions). -/
theorem massShellDensity_lt_top : massShellDensity m p < ⊤ :=
  ENNReal.ofReal_lt_top

/-- A.e. finiteness of the weight with respect to spatial volume. -/
theorem ae_massShellDensity_lt_top :
    ∀ᵐ p ∂volume, massShellDensity m p < ⊤ :=
  Filter.Eventually.of_forall (massShellDensity_lt_top m)

/-- The **positive mass-shell measure** of mass `m`: the pushforward of the weighted
spatial measure `d³p/(2ω_p)` along the physical-momentum parametrization,
`map (massShellParam m) (volume.withDensity (p ↦ ofReal (1/(2ω_p))))`. This is the
Lorentz-invariant measure on the positive sheet (Wigner 1939, §6, eq. (59a); Streater &
Wightman, Ch. 3, spectrum-condition framework). -/
noncomputable def massShellMeasure (m : ℝ) : Measure M4 :=
  Measure.map (massShellParam m)
    (Measure.withDensity volume (massShellDensity m))

/-- Set-level pushforward formula: the measure of a measurable set is the weighted measure
of its preimage on the momentum slice. -/
theorem massShellMeasure_apply {s : Set M4} (hs : MeasurableSet s) :
    massShellMeasure m s =
      Measure.withDensity volume (massShellDensity m) (massShellParam m ⁻¹' s) := by
  rw [massShellMeasure]
  exact Measure.map_apply (measurable_massShellParam m) hs

/-- **Exact `lintegral` pushforward formula**: integration against the shell measure is
integration of the pulled-back function against the weighted momentum measure
`d³p/(2ω_p)`. -/
theorem lintegral_massShellMeasure {g : M4 → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ q, g q ∂massShellMeasure m
      = ∫⁻ p, g (massShellParam m p) * massShellDensity m p ∂volume := by
  rw [massShellMeasure, lintegral_map hg (measurable_massShellParam m)]
  calc ∫⁻ p, g (massShellParam m p) ∂(Measure.withDensity volume (massShellDensity m))
      = ∫⁻ p, massShellDensity m p * g (massShellParam m p) ∂volume :=
        lintegral_withDensity_eq_lintegral_mul volume (measurable_massShellDensity m)
          (hg.comp (measurable_massShellParam m))
    _ = ∫⁻ p, g (massShellParam m p) * massShellDensity m p ∂volume :=
        lintegral_congr fun p => mul_comm _ _

/-- **Exact Bochner pushforward formula** (`integral_map` plus the density-to-weight
transfer): for a.e.-strongly measurable `g`, the integral against the shell measure is the
weighted spatial integral with weight `toReal (1/(2ω_p))`. -/
theorem integral_massShellMeasure {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : M4 → G} (hg : AEStronglyMeasurable g (massShellMeasure m)) :
    ∫ q, g q ∂massShellMeasure m
      = ∫ p, (massShellDensity m p).toReal • g (massShellParam m p) ∂volume := by
  rw [massShellMeasure, integral_map (measurable_massShellParam m).aemeasurable hg,
    integral_withDensity_eq_integral_toReal_smul (measurable_massShellDensity m)
      (ae_massShellDensity_lt_top m)]

/-- **Null outside the shell**: for `0 < m` the whole momentum slice maps into
the positive sheet, so its complement has measure zero. This measure-theoretic
support statement is the downstream contract. A topological
`support μ ⊆ massShell m` theorem is not added because no current consumer needs
it; for positive mass the sheet is closed and such a refinement remains valid
future work. -/
theorem massShellMeasure_compl_null (hm : 0 < m) :
    massShellMeasure m (massShell m)ᶜ = 0 := by
  rw [massShellMeasure,
    Measure.map_apply (measurable_massShellParam m) ((measurableSet_massShell m).compl),
    withDensity_apply _
      (measurable_massShellParam m ((measurableSet_massShell m).compl))]
  have hpre : massShellParam m ⁻¹' (massShell m)ᶜ = ∅ := by
    refine Set.subset_empty_iff.mp ?_
    intro p hp
    exact hp (massShellParam_mem_massShell m p hm)
  rw [hpre, Measure.restrict_empty, lintegral_zero_measure]

/-- Measurability of the frequency-coordinate weight `k ↦ ofReal (1/(2Ω(k)))`. -/
private theorem measurable_freqWeight (m : ℝ) :
    Measurable fun k : M3 => ENNReal.ofReal (1 / (2 * dispersion m k)) :=
  measurable_ofReal_inv_two (continuous_dispersion m).measurable

/-- Measurability of the frozen L0 frequency parametrization `onShell m`. -/
theorem measurable_onShell : Measurable (onShell m) := by
  have hdisp : Continuous (dispersion m) := continuous_dispersion m
  show Measurable fun k : M3 =>
    (!₂[dispersion m k, 2 * π * k 0, 2 * π * k 1, 2 * π * k 2] : M4)
  fun_prop

/-- Change of spatial variables `p = c·k` for Haar/volume measure on `M3`: the substitution
formula with explicit Jacobian `c³` (Mathlib: `map_addHaar_smul` for the dilation, whose
coefficient is `|c ^ finrank|⁻¹` with `finrank ℝ M3 = 3`). -/
private theorem lintegral_dilation (c : ℝ) (hc : 0 < c) {Φ : M3 → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    ∫⁻ x, Φ x ∂volume = ENNReal.ofReal (c ^ 3) * ∫⁻ k, Φ (c • k) ∂volume := by
  have hc3 : 0 < (c ^ 3 : ℝ) := pow_pos hc 3
  have hmap : Measure.map ((c : ℝ) • ·) (volume : Measure M3)
      = ENNReal.ofReal ((c ^ 3 : ℝ)⁻¹) • (volume : Measure M3) := by
    have hfr3 : Module.finrank ℝ M3 = 3 := finrank_euclideanSpace_fin
    rw [Measure.map_addHaar_smul (μ := (volume : Measure M3)) (ne_of_gt hc), hfr3,
      abs_of_pos (inv_pos.mpr hc3)]
  have hpow : ENNReal.ofReal (c ^ 3 : ℝ) * ENNReal.ofReal ((c ^ 3 : ℝ)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hc3.le, mul_inv_cancel₀ (ne_of_gt hc3),
      ENNReal.ofReal_one]
  have hvolEq : (volume : Measure M3)
      = ENNReal.ofReal (c ^ 3) • Measure.map ((c : ℝ) • ·) (volume : Measure M3) := by
    rw [hmap, smul_smul, hpow, one_smul]
  trans ENNReal.ofReal (c ^ 3) * ∫⁻ x, Φ x ∂Measure.map ((c : ℝ) • ·) volume
  · conv_lhs => rw [hvolEq]
    rw [lintegral_smul_measure, smul_eq_mul]
  · exact congrArg _ (lintegral_map hΦ (measurable_const_smul _))

/-- The Jacobian `(2π)³` of the linear change of variables `p = 2πk` between physical
momentum and Fourier frequency on `M3`, induced by Mathlib's `e^{-2πi⟪x,ξ⟫}` transform
convention. -/
noncomputable def freqJacobian : ℝ≥0∞ := ENNReal.ofReal (((2 : ℝ) * π) ^ 3)
/-- Integration against the frequency-coordinate presentation `(2π)³ · dk/(2Ω(k))`
pushed forward along `onShell m`, computed pointwise. -/
private theorem lintegral_map_onShell_freqWeight {m : ℝ} {g : M4 → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ q, g q ∂(Measure.map (onShell m)
        (freqJacobian • Measure.withDensity volume
          (fun k : M3 => ENNReal.ofReal (1 / (2 * dispersion m k)))))
      = freqJacobian * ∫⁻ k, g (onShell m k) *
          ENNReal.ofReal (1 / (2 * dispersion m k)) ∂volume := by
  trans freqJacobian * ∫⁻ k, g (onShell m k) ∂
      (Measure.withDensity volume
        (fun k : M3 => ENNReal.ofReal (1 / (2 * dispersion m k))))
  · rw [lintegral_map hg (measurable_onShell m), lintegral_smul_measure, smul_eq_mul]
  · calc freqJacobian * ∫⁻ k, g (onShell m k) ∂(Measure.withDensity volume
          (fun k : M3 => ENNReal.ofReal (1 / (2 * dispersion m k))))
        = freqJacobian * ∫⁻ k,
            ENNReal.ofReal (1 / (2 * dispersion m k)) * g (onShell m k) ∂volume :=
          congrArg _
            (lintegral_withDensity_eq_lintegral_mul volume (measurable_freqWeight m)
              (hg.comp (measurable_onShell m)))
      _ = freqJacobian * ∫⁻ k, g (onShell m k) *
              ENNReal.ofReal (1 / (2 * dispersion m k)) ∂volume :=
          congrArg _ (lintegral_congr fun k => mul_comm _ _)

/-- **Fourier-coordinate identity with explicit Jacobian**: under the repo's `e^{-2πi⟪x,ξ⟫}`
convention the physical momentum attached to frequency `k` is `2πk`, so the same measure
reads, in frequency coordinates, the pushforward along `onShell m` of the scaled frequency
weight `(2π)³ · dk/(2Ω(k))`. The factor `(2π)³` is exactly the Jacobian of `p = 2πk`; the
identity holds for every mass (no `m ≠ 0` needed). -/
theorem massShellMeasure_eq_map_onShell (m : ℝ) :
    massShellMeasure m
      = Measure.map (onShell m)
          (freqJacobian • Measure.withDensity volume
            (fun k : M3 => ENNReal.ofReal (1 / (2 * dispersion m k)))) := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hΦ : Measurable fun p : M3 => g (massShellParam m p) * massShellDensity m p :=
    (hg.comp (measurable_massShellParam m)).mul (measurable_massShellDensity m)
  calc ∫⁻ q, g q ∂massShellMeasure m
      = ∫⁻ p, g (massShellParam m p) * massShellDensity m p ∂volume :=
        lintegral_massShellMeasure m hg
    _ = freqJacobian * ∫⁻ k, g (onShell m k) *
          ENNReal.ofReal (1 / (2 * dispersion m k)) ∂volume := by
        rw [lintegral_dilation (2 * π) (by positivity) hΦ]
        have hcoef : ENNReal.ofReal (((2 : ℝ) * π) ^ 3) = freqJacobian := rfl
        rw [hcoef]
        refine congrArg _ (lintegral_congr fun k => ?_)
        simp only [onShell_eq_massShellParam, massShellDensity,
          physicalEnergy_two_pi_smul]
    _ = ∫⁻ q, g q ∂(Measure.map (onShell m)
          (freqJacobian • Measure.withDensity volume
            (fun k : M3 => ENNReal.ofReal (1 / (2 * dispersion m k))))) :=
        (lintegral_map_onShell_freqWeight hg).symm

/-- The Fourier-coordinate reading of the pushforward formula, spelled out pointwise:
`∫ g dμ_shell = (2π)³ ∫ g(onShell m k) · dk/(2Ω(k))`. Any downstream use of `dk/(2Ω)`
without the `(2π)³` prefactor is inconsistent with the repo's Fourier convention. -/
theorem lintegral_massShellMeasure_fourier {g : M4 → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ q, g q ∂massShellMeasure m
      = freqJacobian * ∫⁻ k, g (onShell m k) *
          ENNReal.ofReal (1 / (2 * dispersion m k)) ∂volume := by
  rw [massShellMeasure_eq_map_onShell]
  exact lintegral_map_onShell_freqWeight hg

end QFT.KleinGordon
