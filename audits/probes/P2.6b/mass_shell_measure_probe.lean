import Atlas.Proofs.MassShellMeasure
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# P2.6b adversarial kernel probes — the invariant positive mass-shell measure

Independent kernel checks of `Atlas.Proofs.MassShellMeasure` (the proof modules are
imported directly; witnesses are never touched):

* **Geometry**: `massShellParam m p = (ω_p, p)` lies on `η(q, q) = -m²` with positive
  energy, checked generically through the module API and arithmetically on concrete
  momenta, including the frozen future-cone anchor.
* **Exact range**: at `m = 1` the range characterization
  `q ∈ range (massShellParam 1) ↔ q ∈ massShell 1` is exercised at the observable point
  `q = (1, 0, 0, 0)` in both directions, the parametrizing momentum is pinned to `p = 0`,
  and the negative-energy twin `(-1, 0, 0, 0)` is refuted: it satisfies the hyperboloid
  equation yet belongs to neither the positive sheet nor the range.
* **Fourier conversion**: `onShell m k = massShellParam m (2π k)` holds generically and
  coordinate-by-coordinate at `k = (1, 0, 0)` — the spatial part is the *physical*
  momentum `2πk`.
* **The `(2π)³` Jacobian**: the Fourier-coordinate formula carries the explicit factor
  `freqJacobian = (2π)³ > 1`, and dropping it is refuted arithmetically: for a concrete
  positive test integrand the true shell value strictly exceeds the bare-`dk` impostor
  value, so `massShellMeasure 1 ≠` the impostor pushforward. This is the Wigner
  (1939, §6, eq. (59a)) invariant weight read in the repo's `e^{-2πi⟪x,ξ⟫}` Fourier
  convention: `d³p/(2ω_p)` becomes `(2π)³ dk/(2Ω(k))`, never bare `dk/(2Ω(k))`.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.6b/` only.

## Sources

* E. P. Wigner, *On Unitary Representations of the Inhomogeneous Lorentz Group*, Annals
  of Mathematics 40 (1939), §6, eq. (59a): the scalar product on the mass hyperboloid
  `p·p = P, p₄ > 0` integrates against `|p₄|⁻¹ dp₁dp₂dp₃`, i.e. `d³p/p⁰` (here
  `d³p/(2ω_p)`; the factor `1/2` is conventional and Lorentz-behavior-neutral).
  Footnote 26 records the Jacobian argument for invariance — the same Jacobian
  bookkeeping probed here in frequency coordinates.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics II*, Academic Press (1975),
  §X.7, cited at section level as in `Atlas.Proofs.KleinGordon`.
-/

open MeasureTheory Real Spacetime.Minkowski QFT.KleinGordon
open scoped ENNReal

/-! ## A. Geometry of the physical parametrization -/

-- Generic: every parametrized four-momentum sits on the hyperboloid `η = -m²`.
theorem probe_massShellParam_form (m : ℝ) (p : M3) :
    minkowskiForm (massShellParam m p) (massShellParam m p) = -(m ^ 2) :=
  minkowskiForm_massShellParam_self m p

-- Concrete: `m = 1`, `p = (1, 1, 0)`, `ω_p = √3`, checked by direct coordinate algebra.
theorem probe_massShellParam_form_concrete :
    minkowskiForm (massShellParam 1 (!₂[(1 : ℝ), 1, 0]))
        (massShellParam 1 (!₂[(1 : ℝ), 1, 0])) = -(1 ^ 2) := by
  have hnorm : ‖(!₂[(1 : ℝ), 1, 0] : M3)‖ ^ 2 = 1 + 1 + 0 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp
  have hpe : physicalEnergy 1 (!₂[(1 : ℝ), 1, 0] : M3) *
      physicalEnergy 1 (!₂[(1 : ℝ), 1, 0] : M3) = 1 + 1 + 0 + 1 ^ 2 := by
    rw [← pow_two, physicalEnergy_sq, hnorm]
  rw [minkowskiForm_eq, massShellParam_apply_zero, massShellParam_apply_one,
    massShellParam_apply_two, massShellParam_apply_three, hpe]
  simp

-- Generic: positive energy for `0 < m`.
theorem probe_massShellParam_energy_pos {m : ℝ} (hm : 0 < m) (p : M3) :
    0 < massShellParam m p 0 := by
  simpa using physicalEnergy_pos m p hm

-- Concrete: the rest-momentum parametrization has energy `√(0² + 1²) = 1 > 0`.
example : 0 < massShellParam 1 (0 : M3) 0 := by
  simp [massShellParam, physicalEnergy]

-- Concrete: it anchors the frozen open future time cone.
theorem probe_massShellParam_future (p : M3) : InFutureTimeCone (massShellParam 1 p) :=
  massShellParam_inFutureTimeCone 1 p one_pos

/-! ## B. Exact range characterization at `m = 1` on the observable point -/

private def probeOriginPoint : M4 := !₂[(1 : ℝ), 0, 0, 0]

-- The module's iff, instantiated at the observable point.
theorem probe_range_char_concrete :
    probeOriginPoint ∈ Set.range (massShellParam 1) ↔ probeOriginPoint ∈ massShell 1 :=
  mem_range_massShellParam 1 one_pos probeOriginPoint

-- Forward sheet membership, verified arithmetically: `η(q, q) = -1` and `q⁰ = 1 > 0`.
theorem probe_originPoint_in_massShell : probeOriginPoint ∈ massShell 1 := by
  refine ⟨?_, by norm_num [probeOriginPoint]⟩
  rw [minkowskiForm_eq]
  simp [probeOriginPoint]

-- Hence, through the characterization, the point is parametrized…
theorem probe_originPoint_in_range :
    probeOriginPoint ∈ Set.range (massShellParam 1) :=
  probe_range_char_concrete.mpr probe_originPoint_in_massShell

-- …and the witness is forced: only `p = 0` parametrizes `(1, 0, 0, 0)`.
theorem probe_range_witness_unique {p : M3}
    (hp : massShellParam 1 p = probeOriginPoint) : p = 0 :=
  injective_massShellParam 1
    (hp.trans (by simp [massShellParam, physicalEnergy, probeOriginPoint]))

-- The negative-energy twin satisfies the hyperboloid equation…
theorem probe_negTwin_hyperboloid :
    minkowskiForm (-probeOriginPoint) (-probeOriginPoint) = -(1 ^ 2) := by
  rw [minkowskiForm_eq]
  simp [probeOriginPoint]

-- …but is excluded from the positive sheet by the energy condition…
theorem probe_negTwin_not_in_massShell : (-probeOriginPoint) ∉ massShell 1 := by
  intro h
  simp [massShell, minkowskiForm_eq, probeOriginPoint] at h
  linarith

-- …and hence from the range: the parametrized energy `√(‖p‖² + m²)` is never negative.
theorem probe_negTwin_not_in_range :
    (-probeOriginPoint) ∉ Set.range (massShellParam 1) := by
  rintro ⟨p, hp⟩
  have h0 := congrArg (fun q : M4 => q 0) hp
  simp [probeOriginPoint] at h0
  linarith [physicalEnergy_nonneg 1 p]

/-! ## C. The frequency conversion `onShell m k = massShellParam m (2π k)` -/

-- Generic: `onShell` is the physical parametrization at momentum `2πk`.
theorem probe_onShell_conversion (m : ℝ) (k : M3) :
    onShell m k = massShellParam m ((2 * π : ℝ) • k) :=
  onShell_eq_massShellParam m k

-- Concrete: both sides are `(√(4π² + 1), 2π, 0, 0)` at `k = (1, 0, 0)`, `m = 1`,
-- derived coordinate-by-coordinate without invoking the conversion lemma.
theorem probe_onShell_conversion_concrete :
    onShell 1 (!₂[(1 : ℝ), 0, 0])
      = massShellParam 1 ((2 * π : ℝ) • (!₂[(1 : ℝ), 0, 0] : M3)) := by
  have hnorm : ‖(!₂[(1 : ℝ), 0, 0] : M3)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp
  have hL : dispersion 1 (!₂[(1 : ℝ), 0, 0]) = √(4 * π ^ 2 + 1) := by
    rw [dispersion, hnorm]
    ring_nf
  have hs : ((2 : ℝ) * π) • (!₂[(1 : ℝ), 0, 0] : M3) = (!₂[(2 : ℝ) * π, 0, 0] : M3) := by
    ext j
    fin_cases j <;> simp
  have hn2 : ‖(!₂[(2 : ℝ) * π, 0, 0] : M3)‖ ^ 2 = (2 * π) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp
  have hR : physicalEnergy 1 (((2 : ℝ) * π) • (!₂[(1 : ℝ), 0, 0] : M3))
      = √(4 * π ^ 2 + 1) := by
    rw [physicalEnergy, hs, hn2]
    ring_nf
  have henergy : dispersion 1 (!₂[(1 : ℝ), 0, 0])
      = physicalEnergy 1 ((2 * π : ℝ) • (!₂[(1 : ℝ), 0, 0] : M3)) := hL.trans hR.symm
  ext j
  fin_cases j
  · simpa using henergy
  · simp
  · simp
  · simp

/-! ## D. The Fourier-coordinate formula carries the explicit `(2π)³` -/

-- The Jacobian is literally `(2π)³`.
theorem probe_freqJacobian_value :
    freqJacobian = ENNReal.ofReal (((2 : ℝ) * π) ^ 3) := rfl

-- It exceeds `1` — in particular it cannot be absorbed into the weight.
theorem probe_freqJacobian_gt_one : 1 < freqJacobian := by
  have hp : (3 : ℝ) < π := Real.pi_gt_three
  have hp2 : (9 : ℝ) < π ^ 2 := by nlinarith
  have hp3 : (27 : ℝ) < π ^ 3 := by nlinarith
  have hval : (1 : ℝ) < (2 * π) ^ 3 := by
    calc (1 : ℝ) ≤ 8 * 27 := by norm_num
      _ < 8 * π ^ 3 := by linarith
      _ = (2 * π) ^ 3 := by ring
  rw [← ENNReal.ofReal_one, probe_freqJacobian_value]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hval

-- Shape check: the Fourier-coordinate identity exhibits `(2π)³` as the prefactor.
theorem probe_fourier_formula_explicit {g : M4 → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ q : M4, g q ∂massShellMeasure 1
      = ENNReal.ofReal (((2 : ℝ) * π) ^ 3) *
          ∫⁻ k : M3, g (onShell 1 k) *
            ENNReal.ofReal (1 / (2 * dispersion 1 k)) ∂volume :=
  lintegral_massShellMeasure_fourier 1 hg

/-! ## E. Arithmetic refutation of the bare-`dk` impostor -/

/-- The **bare-`dk` impostor**: the frequency-coordinate presentation *without* the
`(2π)³` Jacobian — the pushforward along `onShell 1` of `dk/(2Ω(k))`. -/
noncomputable def bareDkShellMeasure : Measure M4 :=
  Measure.map (onShell 1) (Measure.withDensity volume
    (fun k : M3 => ENNReal.ofReal (1 / (2 * dispersion 1 k))))

/-- A concrete **positive test integrand**: the indicator of the time slice
`{q | q⁰ ≤ 2}`, which the shell meets on the sublevel set `{k | Ω(k) ≤ 2}`. -/
noncomputable def probeTestFun : M4 → ℝ≥0∞ :=
  Set.indicator {q : M4 | q 0 ≤ 2} 1

/-- The frequency-side value of the test integrand weighted by `dk/(2Ω(k))`. -/
noncomputable def shellFreqIntegrand : M3 → ℝ≥0∞ :=
  fun k => probeTestFun (onShell 1 k) * ENNReal.ofReal (1 / (2 * dispersion 1 k))

theorem measurable_probeTestFun : Measurable probeTestFun := by
  have hs : MeasurableSet {q : M4 | q 0 ≤ 2} := by
    have hEq : {q : M4 | q 0 ≤ 2} = (fun q : M4 => q 0) ⁻¹' Set.Iic 2 := rfl
    rw [hEq]
    exact (EuclideanSpace.proj (0 : Fin 4)).continuous.measurable measurableSet_Iic
  exact Measurable.indicator measurable_const hs

private theorem measurable_bareWeight :
    Measurable fun k : M3 => ENNReal.ofReal (1 / (2 * dispersion 1 k)) := by
  simp only [one_div]
  exact Measurable.ennreal_ofReal (((continuous_dispersion 1).measurable.const_mul 2).inv)

theorem measurable_shellFreqIntegrand : Measurable shellFreqIntegrand :=
  (measurable_probeTestFun.comp (measurable_onShell 1)).mul measurable_bareWeight

theorem probeTestFun_onShell (k : M3) :
    probeTestFun (onShell 1 k) = if dispersion 1 k ≤ 2 then (1 : ℝ≥0∞) else 0 := by
  by_cases h : dispersion 1 k ≤ 2
  · rw [probeTestFun, if_pos h,
      Set.indicator_of_mem (by simpa [onShell_apply_zero] using h), Pi.one_apply]
  · rw [probeTestFun, if_neg h]
    have hnm : onShell 1 k ∉ {q : M4 | q 0 ≤ 2} := fun hmem =>
      h (by simpa [onShell_apply_zero] using hmem)
    simp [Set.indicator, hnm]

-- The impostor's exact pushforward formula: no Jacobian prefactor.
theorem lintegral_bareDk {g : M4 → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ q : M4, g q ∂bareDkShellMeasure
      = ∫⁻ k : M3, g (onShell 1 k) *
          ENNReal.ofReal (1 / (2 * dispersion 1 k)) ∂volume := by
  have hstep : ∫⁻ a : M3, (g ∘ onShell 1) a ∂
      (Measure.withDensity volume
        (fun k : M3 => ENNReal.ofReal (1 / (2 * dispersion 1 k))))
      = ∫⁻ a : M3,
          ((fun k : M3 => ENNReal.ofReal (1 / (2 * dispersion 1 k))) *
              (g ∘ onShell 1)) a ∂volume :=
    lintegral_withDensity_eq_lintegral_mul volume measurable_bareWeight
      (hg.comp (measurable_onShell 1))
  calc ∫⁻ q : M4, g q ∂bareDkShellMeasure
      = ∫⁻ a : M3, (g ∘ onShell 1) a ∂
          (Measure.withDensity volume
            (fun k : M3 => ENNReal.ofReal (1 / (2 * dispersion 1 k)))) := by
        rw [bareDkShellMeasure]
        exact lintegral_map hg (measurable_onShell 1)
    _ = ∫⁻ k : M3, g (onShell 1 k) *
            ENNReal.ofReal (1 / (2 * dispersion 1 k)) ∂volume := by
        rw [hstep]
        exact lintegral_congr fun k => by
          simp only [Pi.mul_apply, Function.comp_apply]
          exact mul_comm _ _

-- Positivity: the test integrand has strictly positive frequency-side integral.
theorem shellFreqIntegral_pos : 0 < ∫⁻ k : M3, shellFreqIntegrand k ∂volume := by
  by_contra hcon
  have hzero : ∫⁻ k : M3, shellFreqIntegrand k ∂volume = 0 :=
    le_antisymm (not_lt.mp hcon) bot_le
  rw [lintegral_eq_zero_iff measurable_shellFreqIntegrand] at hzero
  have hUopen : IsOpen {k : M3 | dispersion 1 k < 2} :=
    (continuous_dispersion 1).isOpen_preimage _ isOpen_Iio
  have hUne : {k : M3 | dispersion 1 k < 2}.Nonempty := ⟨0, by simp⟩
  have hUpos : (0 : ℝ≥0∞) < volume {k : M3 | dispersion 1 k < 2} :=
    hUopen.measure_pos volume hUne
  have hmem_ne : ∀ k : M3, dispersion 1 k < 2 → shellFreqIntegrand k ≠ 0 := by
    intro k hk'
    have hΩ1 : (1 : ℝ) ≤ dispersion 1 k :=
      le_dispersion 1 k (by norm_num : (0 : ℝ) ≤ 1)
    intro hEq
    have hpos : (0 : ℝ≥0∞) < shellFreqIntegrand k := by
      rw [shellFreqIntegrand, probeTestFun_onShell, if_pos hk'.le, one_mul]
      exact ENNReal.ofReal_pos.mpr (div_pos one_pos (by linarith))
    exact absurd hEq hpos.ne'
  have hsub : {k : M3 | dispersion 1 k < 2}
      ⊆ {k : M3 | shellFreqIntegrand k ≠ 0} :=
    fun k hk => hmem_ne k hk
  have hnull : volume {k : M3 | shellFreqIntegrand k ≠ 0} = 0 :=
    (MeasureTheory.ae_iff).mp hzero
  exact lt_irrefl _ (lt_of_lt_of_le hUpos ((measure_mono hsub).trans hnull.le))

/-- Constant times an indicator integrates to constant times the measure. -/
private theorem lintegral_indicator_one_eq (s : Set M3) (hs : MeasurableSet s) :
    ∫⁻ k : M3, s.indicator 1 k ∂volume = volume s := by
  rw [lintegral_indicator hs (1 : M3 → ℝ≥0∞)]
  calc ∫⁻ k : M3 in s, (1 : M3 → ℝ≥0∞) k ∂volume
      = ∫⁻ _k : M3 in s, (1 : ℝ≥0∞) ∂volume := lintegral_congr fun _ => rfl
    _ = (1 : ℝ≥0∞) * volume s := setLIntegral_const s 1
    _ = volume s := one_mul _

-- Finiteness: the integral is bounded by `(1/2) · vol{Ω ≤ 2}`, and `{Ω ≤ 2}` is bounded.
theorem shellFreqIntegral_lt_top : ∫⁻ k : M3, shellFreqIntegrand k ∂volume < ⊤ := by
  have hs' : MeasurableSet {k : M3 | dispersion 1 k ≤ 2} :=
    MeasurableSet.preimage measurableSet_Iic (continuous_dispersion 1).measurable
  have hmono : ∫⁻ k : M3, shellFreqIntegrand k ∂volume
      ≤ ENNReal.ofReal (1 / 2) * volume {k : M3 | dispersion 1 k ≤ 2} := by
    have hpt : ∀ k : M3, shellFreqIntegrand k
        ≤ ENNReal.ofReal (1 / 2) * {k : M3 | dispersion 1 k ≤ 2}.indicator 1 k := by
      intro k
      by_cases h : dispersion 1 k ≤ 2
      · have hΩ1 : (1 : ℝ) ≤ dispersion 1 k :=
          le_dispersion 1 k (by norm_num : (0 : ℝ) ≤ 1)
        rw [shellFreqIntegrand, probeTestFun_onShell, if_pos h, one_mul,
          Set.indicator_of_mem (by simpa using h), Pi.one_apply, mul_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_div_iff₀ (by linarith) two_pos]
        linarith
      · rw [shellFreqIntegrand, probeTestFun_onShell, if_neg h, zero_mul]
        exact bot_le
    have h1 : ∫⁻ k : M3, shellFreqIntegrand k ∂volume
        ≤ ∫⁻ k : M3, ENNReal.ofReal (1 / 2) *
            {k : M3 | dispersion 1 k ≤ 2}.indicator 1 k ∂volume := lintegral_mono hpt
    rw [lintegral_const_mul (r := ENNReal.ofReal (1 / 2))
        (f := fun k : M3 => {k : M3 | dispersion 1 k ≤ 2}.indicator 1 k)
        (Measurable.indicator measurable_const hs'),
      lintegral_indicator_one_eq _ hs'] at h1
    exact h1
  have hvolsub : {k : M3 | dispersion 1 k ≤ 2} ⊆ Metric.closedBall (0 : M3) (1 / π) := by
    intro k hk
    have hk' : dispersion 1 k ≤ 2 := hk
    have h2 : (2 : ℝ) * π * ‖k‖ ≤ 2 := le_trans (two_pi_norm_le_dispersion 1 k) hk'
    have hπpos : (0 : ℝ) < π := Real.pi_pos
    have hkpi : ‖k‖ * π ≤ 1 := by linarith
    refine Metric.mem_closedBall.mpr ?_
    rw [dist_zero_right]
    exact le_div_iff₀ hπpos |>.mpr hkpi
  have hvoltop : volume {k : M3 | dispersion 1 k ≤ 2} < ⊤ := by
    calc volume {k : M3 | dispersion 1 k ≤ 2}
        ≤ volume (Metric.closedBall (0 : M3) (1 / π)) := measure_mono hvolsub
      _ ≤ volume (Metric.ball (0 : M3) 2) :=
        measure_mono (Metric.closedBall_subset_ball (by
          rw [div_lt_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]))
      _ < ⊤ := measure_ball_lt_top
  exact lt_of_le_of_lt hmono
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvoltop)

-- Strict gap: the true Fourier-coordinate value strictly exceeds the impostor value.
theorem shellFreqIntegral_lt_smul :
    ∫⁻ k : M3, shellFreqIntegrand k ∂volume
      < freqJacobian * ∫⁻ k : M3, shellFreqIntegrand k ∂volume := by
  have h := ENNReal.mul_lt_mul_right (ne_of_gt shellFreqIntegral_pos)
    (ne_of_lt shellFreqIntegral_lt_top) probe_freqJacobian_gt_one
  rwa [mul_one,
    mul_comm (∫⁻ k : M3, shellFreqIntegrand k ∂volume) freqJacobian] at h

/-- **The impostor is refuted**: the invariant shell measure differs from the bare-`dk`
pushforward. On the positive test integrand above the shell measure evaluates to
`(2π)³ · I` with `0 < I < ∞`, while the impostor evaluates to `I`; since `(2π)³ > 1`
these differ. Any `dk/(2Ω(k))` reading of the shell measure under the repo's Fourier
convention is thus wrong by exactly the Jacobian `(2π)³` (Wigner 1939, §6, eq. (59a)
convention check). -/
theorem probe_bareDk_impostor_refuted :
    massShellMeasure 1 ≠ bareDkShellMeasure := by
  intro heq
  have hfour := probe_fourier_formula_explicit measurable_probeTestFun
  have hbare := lintegral_bareDk measurable_probeTestFun
  rw [heq] at hfour
  have h1 : ∫⁻ q : M4, probeTestFun q ∂bareDkShellMeasure
      = freqJacobian * ∫⁻ k : M3, shellFreqIntegrand k ∂volume := hfour
  have h2 : ∫⁻ q : M4, probeTestFun q ∂bareDkShellMeasure
      = ∫⁻ k : M3, shellFreqIntegrand k ∂volume := hbare
  have hgap := shellFreqIntegral_lt_smul
  rw [← h1, ← h2] at hgap
  exact lt_irrefl _ hgap

#print axioms probe_massShellParam_form
#print axioms probe_massShellParam_form_concrete
#print axioms probe_massShellParam_energy_pos
#print axioms probe_massShellParam_future
#print axioms probe_range_char_concrete
#print axioms probe_originPoint_in_massShell
#print axioms probe_originPoint_in_range
#print axioms probe_range_witness_unique
#print axioms probe_negTwin_hyperboloid
#print axioms probe_negTwin_not_in_massShell
#print axioms probe_negTwin_not_in_range
#print axioms probe_onShell_conversion
#print axioms probe_onShell_conversion_concrete
#print axioms probe_freqJacobian_value
#print axioms probe_freqJacobian_gt_one
#print axioms probe_fourier_formula_explicit
#print axioms probe_bareDk_impostor_refuted
