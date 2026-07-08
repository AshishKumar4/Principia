import Atlas.Witnesses.Minkowski
import Atlas.Proofs.CausalLemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.IntermediateValue

/-!
# P1.W2 — Minkowski causal structure: cone characterization and global hyperbolicity

Witness (blueprint node P1.W2) that the frozen P1.2/P1.3 specs are non-vacuous on the
P1.W1 Minkowski model: the chronology relation of `minkowskiTimeOrientation` is exactly
the open future time cone in the displacement vector, the slice `{x | x 0 = 0}` is a
Cauchy surface, and Minkowski space is globally hyperbolic.

## Contents

* `InFutureTimeCone` / `InFutureCausalCone` — coordinate form of the open future time
  cone and the (punctured) future causal cone, with closure under addition (convexity).
* `minkowski_chronoStep_iff`, `minkowski_chrono_iff` — the cone characterization
  `p ≪ q ↔ η(q-p, q-p) < 0 ∧ q-p future-directed` (O'Neill, *Semi-Riemannian
  Geometry*, Ch. 5, pp. 143–146 and Ch. 14; the causal predicates are evaluated at `q`,
  which is immaterial since the metric is constant), plus expected-false examples:
  spacelike, past-directed and null displacements are not chronologically related.
* `minkowski_causal_iff` — the causal analogue `p ⤳ q ↔ q = p ∨ q-p ∈ future causal
  cone`.
* `isCauchySurface_zeroTimeSlice`, `minkowski_isGloballyHyperbolic` — the `{t = 0}`
  slice is closed, achronal and met exactly once by every inextendible future-directed
  timelike curve; hence Minkowski space is globally hyperbolic (O'Neill, Ch. 14,
  p. 415; Wald, *General Relativity*, §8.3).

## Proof architecture

The forward (hard) direction of the cone characterization is a monotonicity argument:
along any future-directed timelike segment, every functional `x ↦ x 0 - (c·x̄)` with
`|c| ≤ 1` has positive derivative (Cauchy–Schwarz in the spatial slice against the
timelike inequality on the velocity), hence is strictly increasing; optimizing over `c`
puts the displacement in the open cone, and the relations' `TransGen`/`ReflTransGen`
chains stay in the cone because it is closed under addition. The Cauchy-surface
existence proof runs the same monotonicity through a limiting argument: if the time
coordinate of an inextendible curve were bounded on one side, the functionals
`γ⁰ ± γⁱ` would be monotone and bounded, so every coordinate would converge by monotone
convergence, producing an endpoint and contradicting inextendibility; the intermediate
value theorem then yields the crossing, and achronality (P1.3b(ii),
`Atlas/Proofs/CausalLemmas.lean`) its uniqueness.
-/

open Bundle Set Filter
open scoped ContDiff Manifold Topology

namespace Spacetime.Minkowski

open Spacetime

variable {γ : ℝ → M4} {s : Set ℝ} {p q v w : M4}

/-! ### The future cones in coordinates -/

/-- The open future time cone of Minkowski space, in coordinates: `v` is timelike
(`(v¹)² + (v²)² + (v³)² < (v⁰)²`) and future-pointing (`v⁰ > 0`). Coordinate form of
O'Neill's time cone of `∂₀` (*Semi-Riemannian Geometry*, Ch. 5, pp. 143–146); see
`timelike_futureDirected_iff` for the equivalence with the frozen spec predicates. -/
def InFutureTimeCone (v : M4) : Prop :=
  v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 < v 0 ^ 2 ∧ 0 < v 0

/-- The future causal cone of Minkowski space (zero vector excluded), in coordinates:
`v` is causal (`(v¹)² + (v²)² + (v³)² ≤ (v⁰)²`) and future-pointing (`v⁰ > 0`). See
`futureDirected_iff` for the equivalence with the frozen spec predicate. -/
def InFutureCausalCone (v : M4) : Prop :=
  v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 ≤ v 0 ^ 2 ∧ 0 < v 0

theorem InFutureTimeCone.inFutureCausalCone (h : InFutureTimeCone v) :
    InFutureCausalCone v :=
  ⟨h.1.le, h.2⟩

private theorem cauchy_schwarz₃ (a b c x y z : ℝ) :
    (a * x + b * y + c * z) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (a * y - b * x), sq_nonneg (a * z - c * x), sq_nonneg (b * z - c * y)]

/-- The open future time cone is closed under addition (it is a convex cone: O'Neill,
*Semi-Riemannian Geometry*, Ch. 5, Lemma 5.30 has the underlying time-cone facts). -/
theorem InFutureTimeCone.add (hv : InFutureTimeCone v) (hw : InFutureTimeCone w) :
    InFutureTimeCone (v + w) := by
  obtain ⟨hv1, hv0⟩ := hv
  obtain ⟨hw1, hw0⟩ := hw
  have hcs := cauchy_schwarz₃ (v 1) (v 2) (v 3) (w 1) (w 2) (w 3)
  have hsv : (0:ℝ) ≤ v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by positivity
  have hsw : (0:ℝ) ≤ w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := by positivity
  have hdot : v 1 * w 1 + v 2 * w 2 + v 3 * w 3 < v 0 * w 0 := by
    nlinarith [mul_pos hv0 hw0]
  refine ⟨?_, by simp only [PiLp.add_apply]; linarith⟩
  simp only [PiLp.add_apply]
  nlinarith

/-- The future causal cone is closed under addition. -/
theorem InFutureCausalCone.add (hv : InFutureCausalCone v) (hw : InFutureCausalCone w) :
    InFutureCausalCone (v + w) := by
  obtain ⟨hv1, hv0⟩ := hv
  obtain ⟨hw1, hw0⟩ := hw
  have hcs := cauchy_schwarz₃ (v 1) (v 2) (v 3) (w 1) (w 2) (w 3)
  have hsv : (0:ℝ) ≤ v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by positivity
  have hsw : (0:ℝ) ≤ w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := by positivity
  have hdot : v 1 * w 1 + v 2 * w 2 + v 3 * w 3 ≤ v 0 * w 0 := by
    nlinarith [mul_pos hv0 hw0]
  refine ⟨?_, by simp only [PiLp.add_apply]; linarith⟩
  simp only [PiLp.add_apply]
  nlinarith

/-- Key velocity bound: a vector of the open future time cone dominates every spatial
contrast with coefficient vector of Euclidean norm at most `1` (Cauchy–Schwarz in the
spatial slice). This is what makes `x ↦ x 0 - (c·x̄)` increase along timelike curves. -/
theorem InFutureTimeCone.contrast_pos (h : InFutureTimeCone v) {c1 c2 c3 : ℝ}
    (hc : c1 ^ 2 + c2 ^ 2 + c3 ^ 2 ≤ 1) :
    0 < v 0 - (c1 * v 1 + c2 * v 2 + c3 * v 3) := by
  obtain ⟨hsp, h0⟩ := h
  have hcs := cauchy_schwarz₃ c1 c2 c3 (v 1) (v 2) (v 3)
  have hsv : (0:ℝ) ≤ v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by positivity
  nlinarith

/-- Weak version of `InFutureTimeCone.contrast_pos` for the causal cone. -/
theorem InFutureCausalCone.contrast_nonneg (h : InFutureCausalCone v) {c1 c2 c3 : ℝ}
    (hc : c1 ^ 2 + c2 ^ 2 + c3 ^ 2 ≤ 1) :
    0 ≤ v 0 - (c1 * v 1 + c2 * v 2 + c3 * v 3) := by
  obtain ⟨hsp, h0⟩ := h
  have hcs := cauchy_schwarz₃ c1 c2 c3 (v 1) (v 2) (v 3)
  have hsv : (0:ℝ) ≤ v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by positivity
  nlinarith

/-- Converse optimization: domination of all unit spatial contrasts, strictly, puts a
vector in the open future time cone (choose `c` along the spatial part). -/
private theorem inFutureTimeCone_of_forall_contrast
    (h : ∀ c1 c2 c3 : ℝ, c1 ^ 2 + c2 ^ 2 + c3 ^ 2 ≤ 1 →
      c1 * w 1 + c2 * w 2 + c3 * w 3 < w 0) :
    InFutureTimeCone w := by
  have h0 : 0 < w 0 := by simpa using h 0 0 0 (by norm_num)
  refine ⟨?_, h0⟩
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 by positivity) with hS | hS
  · nlinarith
  · set S := Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) with hSdef
    have hSpos : 0 < S := Real.sqrt_pos.2 hS
    have hSsq : S ^ 2 = w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := Real.sq_sqrt hS.le
    have hc : (w 1 / S) ^ 2 + (w 2 / S) ^ 2 + (w 3 / S) ^ 2 ≤ 1 := by
      have hsum : (w 1 / S) ^ 2 + (w 2 / S) ^ 2 + (w 3 / S) ^ 2 =
          (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) / S ^ 2 := by ring
      rw [hsum, ← hSsq, div_self (by positivity)]
    have hlt := h (w 1 / S) (w 2 / S) (w 3 / S) hc
    have hlt' : w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 < w 0 * S := by
      refine (div_lt_iff₀ hSpos).1 ?_
      calc (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) / S
          = (w 1 / S) * w 1 + (w 2 / S) * w 2 + (w 3 / S) * w 3 := by ring
        _ < w 0 := hlt
    nlinarith [mul_pos (show 0 < w 0 * S - (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) by linarith)
      (show 0 < w 0 + S by linarith)]

/-- Weak converse optimization for the causal cone; the strict inequality `0 < w 0`
must be supplied separately. -/
private theorem inFutureCausalCone_of_forall_contrast (h0 : 0 < w 0)
    (h : ∀ c1 c2 c3 : ℝ, c1 ^ 2 + c2 ^ 2 + c3 ^ 2 ≤ 1 →
      c1 * w 1 + c2 * w 2 + c3 * w 3 ≤ w 0) :
    InFutureCausalCone w := by
  refine ⟨?_, h0⟩
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 by positivity) with hS | hS
  · nlinarith
  · set S := Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) with hSdef
    have hSpos : 0 < S := Real.sqrt_pos.2 hS
    have hSsq : S ^ 2 = w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := Real.sq_sqrt hS.le
    have hc : (w 1 / S) ^ 2 + (w 2 / S) ^ 2 + (w 3 / S) ^ 2 ≤ 1 := by
      have hsum : (w 1 / S) ^ 2 + (w 2 / S) ^ 2 + (w 3 / S) ^ 2 =
          (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) / S ^ 2 := by ring
      rw [hsum, ← hSsq, div_self (by positivity)]
    have hle := h (w 1 / S) (w 2 / S) (w 3 / S) hc
    have hle' : w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 ≤ w 0 * S := by
      refine (div_le_iff₀ hSpos).1 ?_
      calc (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) / S
          = (w 1 / S) * w 1 + (w 2 / S) * w 2 + (w 3 / S) * w 3 := by ring
        _ ≤ w 0 := hle
    nlinarith [mul_nonneg (show 0 ≤ w 0 * S - (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) by linarith)
      (show 0 ≤ w 0 + S by positivity)]

/-! ### The cones against the frozen spec predicates -/

@[simp]
theorem minkowskiTimeOrientation_X (x : M4) :
    minkowskiTimeOrientation.X x = EuclideanSpace.single 0 1 :=
  rfl

/-- Timelikeness for the Minkowski metric, in coordinates. -/
theorem timelike_iff (x v : M4) :
    minkowskiMetric.Timelike x v ↔ v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 < v 0 ^ 2 := by
  show minkowskiMetric.val x v v < 0 ↔ _
  rw [minkowskiMetric_val_eq]
  constructor <;> intro h <;> nlinarith

private theorem val_single_zero (x v : M4) :
    minkowskiMetric.val x v (EuclideanSpace.single 0 1) = -(v 0) := by
  rw [minkowskiMetric_val_eq]
  simp

/-- Future-directedness for the Minkowski time orientation is exactly membership in
the future causal cone. -/
theorem futureDirected_iff (x v : M4) :
    minkowskiTimeOrientation.FutureDirected x v ↔ InFutureCausalCone v := by
  constructor
  · rintro ⟨hc, hx⟩
    rw [minkowskiTimeOrientation_X, val_single_zero] at hx
    have h0 : 0 < v 0 := by linarith
    refine ⟨?_, h0⟩
    rcases hc with ht | ⟨hn, _⟩
    · exact ((timelike_iff x v).1 ht).le
    · rw [minkowskiMetric_val_eq] at hn
      nlinarith
  · rintro ⟨hsp, h0⟩
    refine ⟨?_, ?_⟩
    · rcases lt_or_eq_of_le hsp with h | h
      · exact Or.inl ((timelike_iff x v).2 h)
      · refine Or.inr ⟨by rw [minkowskiMetric_val_eq]; nlinarith, fun hv => h0.ne' ?_⟩
        rw [hv]; rfl
    · rw [minkowskiTimeOrientation_X, val_single_zero]
      linarith

/-- The conjunction "timelike and future-directed" of the frozen spec predicates is
exactly membership in the open future time cone. -/
theorem timelike_futureDirected_iff (x v : M4) :
    minkowskiMetric.Timelike x v ∧ minkowskiTimeOrientation.FutureDirected x v ↔
      InFutureTimeCone v := by
  rw [futureDirected_iff, timelike_iff]
  exact ⟨fun ⟨ht, _, h0⟩ => ⟨ht, h0⟩, fun ⟨ht, h0⟩ => ⟨ht, ht.le, h0⟩⟩

/-! ### Velocities of causal curves in coordinates -/

/-- On a vector space viewed as a manifold over itself, the manifold velocity of a
curve is its elementary derivative. -/
theorem velocity_eq_deriv (γ : ℝ → M4) (t : ℝ) :
    mfderiv 𝓘(ℝ) 𝓘(ℝ, M4) γ t 1 = deriv γ t := by
  rw [mfderiv_eq_fderiv]; rfl

private theorem futureTimelikeOn_deriv (hγ : FutureTimelikeOn minkowskiTimeOrientation γ s)
    {t : ℝ} (ht : t ∈ s) : DifferentiableAt ℝ γ t ∧ InFutureTimeCone (deriv γ t) := by
  obtain ⟨hmd, htl, hfd⟩ := hγ t ht
  refine ⟨hmd.differentiableAt, ?_⟩
  have h := (timelike_futureDirected_iff (γ t) (mfderiv 𝓘(ℝ) 𝓘(ℝ, M4) γ t 1)).1 ⟨htl, hfd⟩
  rwa [velocity_eq_deriv] at h

private theorem futureCausalOn_deriv (hγ : FutureCausalOn minkowskiTimeOrientation γ s)
    {t : ℝ} (ht : t ∈ s) : DifferentiableAt ℝ γ t ∧ InFutureCausalCone (deriv γ t) := by
  obtain ⟨hmd, hfd⟩ := hγ t ht
  refine ⟨hmd.differentiableAt, ?_⟩
  have h := (futureDirected_iff (γ t) (mfderiv 𝓘(ℝ) 𝓘(ℝ, M4) γ t 1)).1 hfd
  rwa [velocity_eq_deriv] at h

/-! ### Monotone functionals along causal curves -/

private theorem strictMonoOn_clm_comp (hconv : Convex ℝ s) (ℓ : M4 →L[ℝ] ℝ)
    (hd : ∀ t ∈ s, DifferentiableAt ℝ γ t) (hpos : ∀ t ∈ s, 0 < ℓ (deriv γ t)) :
    StrictMonoOn (fun u => ℓ (γ u)) s := by
  refine strictMonoOn_of_deriv_pos hconv
    (fun t ht => (ℓ.continuous.continuousAt.comp (hd t ht).continuousAt).continuousWithinAt)
    (fun t ht => ?_)
  have ht' : t ∈ s := interior_subset ht
  have hder : HasDerivAt (fun u => ℓ (γ u)) (ℓ (deriv γ t)) t :=
    ℓ.hasFDerivAt.comp_hasDerivAt t (hd t ht').hasDerivAt
  rw [hder.deriv]
  exact hpos t ht'

private theorem monotoneOn_clm_comp (hconv : Convex ℝ s) (ℓ : M4 →L[ℝ] ℝ)
    (hd : ∀ t ∈ s, DifferentiableAt ℝ γ t) (hpos : ∀ t ∈ s, 0 ≤ ℓ (deriv γ t)) :
    MonotoneOn (fun u => ℓ (γ u)) s := by
  refine monotoneOn_of_deriv_nonneg hconv
    (fun t ht => (ℓ.continuous.continuousAt.comp (hd t ht).continuousAt).continuousWithinAt)
    (fun t ht => ?_) (fun t ht => ?_)
  · exact (ℓ.hasFDerivAt.comp_hasDerivAt t
      (hd t (interior_subset ht)).hasDerivAt).differentiableAt.differentiableWithinAt
  · have ht' : t ∈ s := interior_subset ht
    have hder : HasDerivAt (fun u => ℓ (γ u)) (ℓ (deriv γ t)) t :=
      ℓ.hasFDerivAt.comp_hasDerivAt t (hd t ht').hasDerivAt
    rw [hder.deriv]
    exact hpos t ht'

/-- The spatial-contrast continuous linear functional `x ↦ x⁰ - (c¹x¹ + c²x² + c³x³)`. -/
private noncomputable def contrastCLM (c1 c2 c3 : ℝ) : M4 →L[ℝ] ℝ :=
  EuclideanSpace.proj 0 - (c1 • EuclideanSpace.proj 1 + c2 • EuclideanSpace.proj 2 +
    c3 • EuclideanSpace.proj 3)

private theorem contrastCLM_apply (c1 c2 c3 : ℝ) (v : M4) :
    contrastCLM c1 c2 c3 v = v 0 - (c1 * v 1 + c2 * v 2 + c3 * v 3) := by
  simp [contrastCLM]

/-- The time coordinate is strictly increasing along every future-directed causal
curve. -/
private theorem strictMonoOn_coordZero (hγ : FutureCausalOn minkowskiTimeOrientation γ s)
    (hconv : Convex ℝ s) : StrictMonoOn (fun u => γ u 0) s := by
  have h := strictMonoOn_clm_comp hconv (contrastCLM 0 0 0)
    (fun t ht => (futureCausalOn_deriv hγ ht).1)
    (fun t ht => by
      rw [contrastCLM_apply]
      have := (futureCausalOn_deriv hγ ht).2.2
      simpa using this)
  intro a ha b hb hab
  have hab' := h ha hb hab
  simp only [contrastCLM_apply] at hab'
  simpa using hab'

/-- Every spatial contrast with `|c| ≤ 1` is strictly increasing along a
future-directed timelike curve. -/
private theorem strictMonoOn_contrast (hγ : FutureTimelikeOn minkowskiTimeOrientation γ s)
    (hconv : Convex ℝ s) {c1 c2 c3 : ℝ} (hc : c1 ^ 2 + c2 ^ 2 + c3 ^ 2 ≤ 1) :
    StrictMonoOn (fun u => γ u 0 - (c1 * γ u 1 + c2 * γ u 2 + c3 * γ u 3)) s := by
  have h := strictMonoOn_clm_comp hconv (contrastCLM c1 c2 c3)
    (fun t ht => (futureTimelikeOn_deriv hγ ht).1)
    (fun t ht => by
      rw [contrastCLM_apply]
      exact (futureTimelikeOn_deriv hγ ht).2.contrast_pos hc)
  intro a ha b hb hab
  have hab' := h ha hb hab
  simpa only [contrastCLM_apply] using hab'

/-- Every spatial contrast with `|c| ≤ 1` is (weakly) increasing along a
future-directed causal curve. -/
private theorem monotoneOn_contrast (hγ : FutureCausalOn minkowskiTimeOrientation γ s)
    (hconv : Convex ℝ s) {c1 c2 c3 : ℝ} (hc : c1 ^ 2 + c2 ^ 2 + c3 ^ 2 ≤ 1) :
    MonotoneOn (fun u => γ u 0 - (c1 * γ u 1 + c2 * γ u 2 + c3 * γ u 3)) s := by
  have h := monotoneOn_clm_comp hconv (contrastCLM c1 c2 c3)
    (fun t ht => (futureCausalOn_deriv hγ ht).1)
    (fun t ht => by
      rw [contrastCLM_apply]
      exact (futureCausalOn_deriv hγ ht).2.contrast_nonneg hc)
  intro a ha b hb hab
  have hab' := h ha hb hab
  simpa only [contrastCLM_apply] using hab'

/-! ### Straight segments -/

private theorem hasDerivAt_segment (p w : M4) (t : ℝ) :
    HasDerivAt (fun u : ℝ => p + u • w) w t := by
  simpa using ((hasDerivAt_id t).smul_const w).const_add p

/-- The straight segment `t ↦ p + t • w` is a future-directed timelike curve whenever
its constant velocity `w` lies in the open future time cone. -/
private theorem futureTimelikeOn_segment (p : M4) (h : InFutureTimeCone w) :
    FutureTimelikeOn minkowskiTimeOrientation (fun u : ℝ => p + u • w) (Icc 0 1) := by
  intro t _
  have hd := hasDerivAt_segment p w t
  have hv : mfderiv 𝓘(ℝ) 𝓘(ℝ, M4) (fun u : ℝ => p + u • w) t 1 = w := by
    rw [velocity_eq_deriv, hd.deriv]
  have hc := (timelike_futureDirected_iff (p + t • w) w).2 h
  exact ⟨hd.differentiableAt.mdifferentiableAt, by rw [hv]; exact hc.1, by rw [hv]; exact hc.2⟩

/-- The straight segment `t ↦ p + t • w` is a future-directed causal curve whenever
its constant velocity `w` lies in the future causal cone. -/
private theorem futureCausalOn_segment (p : M4) (h : InFutureCausalCone w) :
    FutureCausalOn minkowskiTimeOrientation (fun u : ℝ => p + u • w) (Icc 0 1) := by
  intro t _
  have hd := hasDerivAt_segment p w t
  have hv : mfderiv 𝓘(ℝ) 𝓘(ℝ, M4) (fun u : ℝ => p + u • w) t 1 = w := by
    rw [velocity_eq_deriv, hd.deriv]
  exact ⟨hd.differentiableAt.mdifferentiableAt,
    by rw [hv]; exact (futureDirected_iff (p + t • w) w).2 h⟩

/-! ### The chronology relation is the open future time cone -/

private theorem chronoStep_of_inFutureTimeCone (h : InFutureTimeCone (q - p)) :
    ChronoStep minkowskiTimeOrientation p q :=
  ⟨fun u : ℝ => p + u • (q - p), 0, 1, one_pos, by simp, by simp,
    futureTimelikeOn_segment p h⟩

private theorem inFutureTimeCone_sub_of_chronoStep
    (h : ChronoStep minkowskiTimeOrientation p q) : InFutureTimeCone (q - p) := by
  obtain ⟨γ, a, b, hab, rfl, rfl, hγ⟩ := h
  have hconv : Convex ℝ (Icc a b) := convex_Icc a b
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab.le
  refine inFutureTimeCone_of_forall_contrast fun c1 c2 c3 hc => ?_
  have hlt := strictMonoOn_contrast hγ hconv hc ha hb hab
  simp only [PiLp.sub_apply]
  dsimp only at hlt
  linarith

private theorem causalStep_of_inFutureCausalCone (h : InFutureCausalCone (q - p)) :
    CausalStep minkowskiTimeOrientation p q :=
  ⟨fun u : ℝ => p + u • (q - p), 0, 1, one_pos, by simp, by simp,
    futureCausalOn_segment p h⟩

private theorem inFutureCausalCone_sub_of_causalStep
    (h : CausalStep minkowskiTimeOrientation p q) : InFutureCausalCone (q - p) := by
  obtain ⟨γ, a, b, hab, rfl, rfl, hγ⟩ := h
  have hconv : Convex ℝ (Icc a b) := convex_Icc a b
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab.le
  have h0 : 0 < (γ b - γ a) 0 := by
    have := strictMonoOn_coordZero hγ hconv ha hb hab
    simp only [PiLp.sub_apply]
    dsimp only at this
    linarith
  refine inFutureCausalCone_of_forall_contrast h0 fun c1 c2 c3 hc => ?_
  have hle := monotoneOn_contrast hγ hconv hc ha hb hab.le
  simp only [PiLp.sub_apply]
  dsimp only at hle
  linarith

/-- Single-segment reachability in Minkowski space is displacement in the open future
time cone: `ChronoStep p q` iff `q - p` is timelike and future-directed. The spec
predicates are evaluated at `q`; the choice is immaterial since the metric and the
time orientation are constant. -/
theorem minkowski_chronoStep_iff (p q : M4) :
    ChronoStep minkowskiTimeOrientation p q ↔
      minkowskiMetric.Timelike q (q - p) ∧
        minkowskiTimeOrientation.FutureDirected q (q - p) := by
  rw [timelike_futureDirected_iff]
  exact ⟨inFutureTimeCone_sub_of_chronoStep, chronoStep_of_inFutureTimeCone⟩

/-- **Minkowski cone characterization** (P1.W2): the chronology relation of the frozen
specs on the Minkowski witness is exactly the open future time cone in the displacement
vector, `p ≪ q ↔ q - p` timelike and future-directed (O'Neill, *Semi-Riemannian
Geometry*, Ch. 5, pp. 143–146; Ch. 14, p. 403). The spec predicates are evaluated at
`q`; the choice is immaterial since the metric and the time orientation are constant. -/
theorem minkowski_chrono_iff (p q : M4) :
    p ≪[minkowskiTimeOrientation] q ↔
      minkowskiMetric.Timelike q (q - p) ∧
        minkowskiTimeOrientation.FutureDirected q (q - p) := by
  rw [timelike_futureDirected_iff]
  constructor
  · intro h
    have h' : Relation.TransGen (ChronoStep minkowskiTimeOrientation) p q := h
    clear h
    induction h' with
    | single hstep => exact inFutureTimeCone_sub_of_chronoStep hstep
    | tail _ hstep ih =>
        have h2 := inFutureTimeCone_sub_of_chronoStep hstep
        have h3 := h2.add ih
        rwa [sub_add_sub_cancel] at h3
  · exact fun h => Relation.TransGen.single (chronoStep_of_inFutureTimeCone h)

/-- **Minkowski causal characterization** (P1.W2): the causality relation is the
(reflexive) future causal cone in the displacement vector; `FutureDirected` already
encodes causality of `q - p`, so no separate causal conjunct is needed. -/
theorem minkowski_causal_iff (p q : M4) :
    p ⤳[minkowskiTimeOrientation] q ↔
      q = p ∨ minkowskiTimeOrientation.FutureDirected q (q - p) := by
  rw [futureDirected_iff]
  constructor
  · intro h
    have h' : Relation.ReflTransGen (CausalStep minkowskiTimeOrientation) p q := h
    clear h
    induction h' with
    | refl => exact Or.inl rfl
    | tail _ hstep ih =>
        have h2 := inFutureCausalCone_sub_of_causalStep hstep
        rcases ih with rfl | ih
        · exact Or.inr h2
        · refine Or.inr ?_
          have h3 := h2.add ih
          rwa [sub_add_sub_cancel] at h3
  · rintro (rfl | h)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (causalStep_of_inFutureCausalCone h)

/-! ### Expected-true and expected-false examples

Chronology is the *open* cone interior: timelike future displacements are related,
while spacelike, past-directed and null displacements are not. -/

-- One unit of coordinate time to the future: `0 ≪ ∂₀`.
example : (0 : M4) ≪[minkowskiTimeOrientation] EuclideanSpace.single 0 1 := by
  rw [minkowski_chrono_iff, timelike_futureDirected_iff]
  constructor <;> simp

-- Spacelike separation: `∂₁` is not in the chronological future of `0`.
example : ¬ ((0 : M4) ≪[minkowskiTimeOrientation] EuclideanSpace.single 1 1) := by
  intro h
  have hc := (timelike_futureDirected_iff _ _).1 ((minkowski_chrono_iff _ _).1 h)
  have h1 := hc.1
  norm_num [Fin.ext_iff] at h1

-- Past direction: `0` is not in the chronological future of `∂₀`.
example : ¬ (EuclideanSpace.single 0 1 ≪[minkowskiTimeOrientation] (0 : M4)) := by
  intro h
  have hc := (timelike_futureDirected_iff _ _).1 ((minkowski_chrono_iff _ _).1 h)
  have h1 := hc.2
  norm_num [Fin.ext_iff] at h1

-- Null separation: the lightlike displacement `∂₀ + ∂₁` is not chronological
-- (chronology is the strict cone interior)...
example :
    ¬ ((0 : M4) ≪[minkowskiTimeOrientation]
        (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 : M4)) := by
  intro h
  have hc := (timelike_futureDirected_iff _ _).1 ((minkowski_chrono_iff _ _).1 h)
  have h1 := hc.1
  norm_num [Fin.ext_iff] at h1

-- ...but it is causal: null future displacements realize `⤳`.
example :
    (0 : M4) ⤳[minkowskiTimeOrientation]
      (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 : M4) := by
  rw [minkowski_causal_iff, futureDirected_iff]
  refine Or.inr ?_
  constructor <;> simp

/-! ### The zero-time slice is a Cauchy surface

Existence of the crossing is the hard part. If the time coordinate of an inextendible
future-directed timelike curve were bounded above, then the monotone bounded
functionals `γ⁰` and `γ⁰ ± γⁱ` would all converge toward the future end of the domain
(monotone convergence along `atTop` of the domain subtype), so every coordinate of `γ`
would converge — an endpoint, contradicting future inextendibility. Mirrored to the
past, `γ⁰` attains both signs, and the intermediate value theorem produces the
crossing; achronality (P1.3b(ii)) makes it unique. -/

/-- The `{t = 0}` coordinate slice of Minkowski space: the canonical Cauchy surface. -/
def zeroTimeSlice : Set M4 :=
  {x : M4 | x 0 = 0}

theorem isClosed_zeroTimeSlice : IsClosed zeroTimeSlice :=
  isClosed_singleton.preimage (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 4)).continuous

/-- The zero-time slice is achronal: chronologically related points have strictly
increasing time coordinate by the cone characterization. -/
theorem isAchronal_zeroTimeSlice :
    IsAchronal minkowskiTimeOrientation zeroTimeSlice := by
  intro p hp q hq h
  have hc := (timelike_futureDirected_iff _ _).1 ((minkowski_chrono_iff _ _).1 h)
  have h0 := hc.2
  have hp' : p 0 = 0 := hp
  have hq' : q 0 = 0 := hq
  rw [show (q - p) 0 = q 0 - p 0 from rfl, hp', hq'] at h0
  norm_num at h0

/-- Monotone convergence of a spatial coordinate toward the future end of the domain,
given a bound on the time coordinate: `γ⁰ + γⁱ` is monotone and bounded above (past of
`t₀` by monotonicity, future of `t₀` because `γ⁰ + γⁱ = 2γ⁰ - (γ⁰ - γⁱ)` with `γ⁰`
bounded and `γ⁰ - γⁱ` monotone), so it converges; subtracting the limit of `γ⁰` gives
the limit of `γⁱ`. -/
private theorem tendsto_component_atTop {t₀ : ℝ} (ht₀ : t₀ ∈ s) {c L0 : ℝ} (i : Fin 4)
    (hbd : ∀ t ∈ s, γ t 0 ≤ c)
    (hplus : MonotoneOn (fun u => γ u 0 + γ u i) s)
    (hminus : MonotoneOn (fun u => γ u 0 - γ u i) s)
    (hL0 : Tendsto (fun t : s => γ t 0) atTop (𝓝 L0)) :
    ∃ L, Tendsto (fun t : s => γ t i) atTop (𝓝 L) := by
  have hbdd : ∀ t ∈ s,
      γ t 0 + γ t i ≤ max (γ t₀ 0 + γ t₀ i) (2 * c - (γ t₀ 0 - γ t₀ i)) := by
    intro t ht
    rcases le_total t t₀ with hle | hle
    · exact le_max_of_le_left (hplus ht ht₀ hle)
    · refine le_max_of_le_right ?_
      have h1 := hminus ht₀ ht hle
      have h2 := hbd t ht
      dsimp only at h1
      linarith
  obtain ⟨Lp, hLp⟩ : ∃ L, Tendsto (fun t : s => γ t 0 + γ t i) atTop (𝓝 L) :=
    ⟨_, tendsto_atTop_ciSup (fun a b hab => hplus a.2 b.2 hab)
      ⟨_, by rintro x ⟨t, rfl⟩; exact hbdd t t.2⟩⟩
  exact ⟨Lp - L0, by simpa using hLp.sub hL0⟩

/-- Past mirror of `tendsto_component_atTop`. -/
private theorem tendsto_component_atBot {t₀ : ℝ} (ht₀ : t₀ ∈ s) {c L0 : ℝ} (i : Fin 4)
    (hbd : ∀ t ∈ s, c ≤ γ t 0)
    (hplus : MonotoneOn (fun u => γ u 0 + γ u i) s)
    (hminus : MonotoneOn (fun u => γ u 0 - γ u i) s)
    (hL0 : Tendsto (fun t : s => γ t 0) atBot (𝓝 L0)) :
    ∃ L, Tendsto (fun t : s => γ t i) atBot (𝓝 L) := by
  have hbdd : ∀ t ∈ s,
      min (γ t₀ 0 + γ t₀ i) (2 * c - (γ t₀ 0 - γ t₀ i)) ≤ γ t 0 + γ t i := by
    intro t ht
    rcases le_total t t₀ with hle | hle
    · refine min_le_of_right_le ?_
      have h1 := hminus ht ht₀ hle
      have h2 := hbd t ht
      dsimp only at h1
      linarith
    · exact min_le_of_left_le (hplus ht₀ ht hle)
  obtain ⟨Lp, hLp⟩ : ∃ L, Tendsto (fun t : s => γ t 0 + γ t i) atBot (𝓝 L) :=
    ⟨_, tendsto_atBot_ciInf (fun a b hab => hplus a.2 b.2 hab)
      ⟨_, by rintro x ⟨t, rfl⟩; exact hbdd t t.2⟩⟩
  exact ⟨Lp - L0, by simpa using hLp.sub hL0⟩

/-- The functionals `γ⁰ + γⁱ` and `γ⁰ - γⁱ` are monotone along every future-directed
causal curve, for every spatial index `i` (unit-coefficient instances of
`monotoneOn_contrast`). -/
private theorem monotoneOn_pair (hγ : FutureCausalOn minkowskiTimeOrientation γ s)
    (hconv : Convex ℝ s) {i : Fin 4} (hi : i ≠ 0) :
    MonotoneOn (fun u => γ u 0 + γ u i) s ∧ MonotoneOn (fun u => γ u 0 - γ u i) s := by
  have key : ∀ c1 c2 c3 : ℝ, c1 ^ 2 + c2 ^ 2 + c3 ^ 2 ≤ 1 →
      MonotoneOn (fun u => γ u 0 - (c1 * γ u 1 + c2 * γ u 2 + c3 * γ u 3)) s :=
    fun c1 c2 c3 hc => monotoneOn_contrast hγ hconv hc
  fin_cases i
  · exact absurd rfl hi
  · constructor
    · show MonotoneOn (fun u => γ u 0 + γ u 1) s
      intro a ha b hb hab
      have h := key (-1) 0 0 (by norm_num) ha hb hab
      dsimp only at h ⊢
      linarith
    · show MonotoneOn (fun u => γ u 0 - γ u 1) s
      intro a ha b hb hab
      have h := key 1 0 0 (by norm_num) ha hb hab
      dsimp only at h ⊢
      linarith
  · constructor
    · show MonotoneOn (fun u => γ u 0 + γ u 2) s
      intro a ha b hb hab
      have h := key 0 (-1) 0 (by norm_num) ha hb hab
      dsimp only at h ⊢
      linarith
    · show MonotoneOn (fun u => γ u 0 - γ u 2) s
      intro a ha b hb hab
      have h := key 0 1 0 (by norm_num) ha hb hab
      dsimp only at h ⊢
      linarith
  · constructor
    · show MonotoneOn (fun u => γ u 0 + γ u 3) s
      intro a ha b hb hab
      have h := key 0 0 (-1) (by norm_num) ha hb hab
      dsimp only at h ⊢
      linarith
    · show MonotoneOn (fun u => γ u 0 - γ u 3) s
      intro a ha b hb hab
      have h := key 0 0 1 (by norm_num) ha hb hab
      dsimp only at h ⊢
      linarith

/-- A future-directed timelike curve whose time coordinate is bounded above has a
future endpoint: all coordinates converge toward the future end of the domain. -/
private theorem exists_isFutureEndpoint_of_bddAbove
    (hγ : FutureTimelikeOn minkowskiTimeOrientation γ s) (hconv : Convex ℝ s)
    {c : ℝ} (hbd : ∀ t ∈ s, γ t 0 ≤ c) :
    ∃ p : M4, IsFutureEndpoint γ s p := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · refine ⟨0, ?_⟩
    rw [IsFutureEndpoint, Subsingleton.elim (atTop : Filter (∅ : Set ℝ)) ⊥]
    exact tendsto_bot
  · have hcau := hγ.futureCausalOn
    have hmono0 : MonotoneOn (fun u => γ u 0) s :=
      (strictMonoOn_coordZero hcau hconv).monotoneOn
    obtain ⟨L0, hL0⟩ : ∃ L, Tendsto (fun t : s => γ t 0) atTop (𝓝 L) :=
      ⟨_, tendsto_atTop_ciSup (fun a b hab => hmono0 a.2 b.2 hab)
        ⟨c, by rintro x ⟨t, rfl⟩; exact hbd t t.2⟩⟩
    have hcomp : ∀ i : Fin 4, ∃ L, Tendsto (fun t : s => γ t i) atTop (𝓝 L) := by
      intro i
      by_cases hi : i = 0
      · subst hi
        exact ⟨L0, hL0⟩
      · obtain ⟨hplus, hminus⟩ := monotoneOn_pair hcau hconv hi
        exact tendsto_component_atTop ht₀ i hbd hplus hminus hL0
    choose L hL using hcomp
    exact ⟨(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm L,
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.continuous.tendsto L).comp
        (tendsto_pi_nhds.2 hL)⟩

/-- Past mirror of `exists_isFutureEndpoint_of_bddAbove`. -/
private theorem exists_isPastEndpoint_of_bddBelow
    (hγ : FutureTimelikeOn minkowskiTimeOrientation γ s) (hconv : Convex ℝ s)
    {c : ℝ} (hbd : ∀ t ∈ s, c ≤ γ t 0) :
    ∃ p : M4, IsPastEndpoint γ s p := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · refine ⟨0, ?_⟩
    rw [IsPastEndpoint, Subsingleton.elim (atBot : Filter (∅ : Set ℝ)) ⊥]
    exact tendsto_bot
  · have hcau := hγ.futureCausalOn
    have hmono0 : MonotoneOn (fun u => γ u 0) s :=
      (strictMonoOn_coordZero hcau hconv).monotoneOn
    obtain ⟨L0, hL0⟩ : ∃ L, Tendsto (fun t : s => γ t 0) atBot (𝓝 L) :=
      ⟨_, tendsto_atBot_ciInf (fun a b hab => hmono0 a.2 b.2 hab)
        ⟨c, by rintro x ⟨t, rfl⟩; exact hbd t t.2⟩⟩
    have hcomp : ∀ i : Fin 4, ∃ L, Tendsto (fun t : s => γ t i) atBot (𝓝 L) := by
      intro i
      by_cases hi : i = 0
      · subst hi
        exact ⟨L0, hL0⟩
      · obtain ⟨hplus, hminus⟩ := monotoneOn_pair hcau hconv hi
        exact tendsto_component_atBot ht₀ i hbd hplus hminus hL0
    choose L hL using hcomp
    exact ⟨(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm L,
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.continuous.tendsto L).comp
        (tendsto_pi_nhds.2 hL)⟩

private theorem exists_coordZero_nonneg
    (hγ : FutureTimelikeOn minkowskiTimeOrientation γ s) (hconv : Convex ℝ s)
    (hin : FutureInextendible γ s) : ∃ t ∈ s, 0 ≤ γ t 0 := by
  by_contra hb
  push Not at hb
  obtain ⟨p, hp⟩ :=
    exists_isFutureEndpoint_of_bddAbove hγ hconv (c := 0) fun t ht => (hb t ht).le
  exact hin p hp

private theorem exists_coordZero_nonpos
    (hγ : FutureTimelikeOn minkowskiTimeOrientation γ s) (hconv : Convex ℝ s)
    (hin : PastInextendible γ s) : ∃ t ∈ s, γ t 0 ≤ 0 := by
  by_contra hb
  push Not at hb
  obtain ⟨p, hp⟩ :=
    exists_isPastEndpoint_of_bddBelow hγ hconv (c := 0) fun t ht => (hb t ht).le
  exact hin p hp

/-- Crossing existence: an inextendible future-directed timelike curve crosses the
zero-time slice. The time coordinate attains both signs (else the curve would have an
endpoint) and is continuous, so the intermediate value theorem applies. -/
private theorem exists_coordZero_eq_zero
    (hγ : FutureTimelikeOn minkowskiTimeOrientation γ s) (hs : s.OrdConnected)
    (hin : Inextendible γ s) : ∃ t ∈ s, γ t 0 = 0 := by
  have hconv : Convex ℝ s := convex_iff_ordConnected.2 hs
  obtain ⟨tp, htps, htp⟩ := exists_coordZero_nonneg hγ hconv hin.1
  obtain ⟨tm, htms, htm⟩ := exists_coordZero_nonpos hγ hconv hin.2
  rcases le_total tm tp with hle | hle
  · have hsub : Icc tm tp ⊆ s := hs.out htms htps
    have hcont : ContinuousOn (fun u => γ u 0) (Icc tm tp) := fun u hu =>
      (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 4)).continuous.continuousAt).comp
        (futureTimelikeOn_deriv hγ (hsub hu)).1.continuousAt).continuousWithinAt
    obtain ⟨u, hu, hu0⟩ := intermediate_value_Icc hle hcont ⟨htm, htp⟩
    exact ⟨u, hsub hu, hu0⟩
  · have hmono := (strictMonoOn_coordZero hγ.futureCausalOn hconv).monotoneOn
    have h := hmono htps htms hle
    dsimp only at h
    exact ⟨tp, htps, le_antisymm (by linarith) htp⟩

/-- **P1.W2**: the zero-time slice is a Cauchy surface of Minkowski space — closed,
achronal, and met in exactly one parameter value by every inextendible future-directed
timelike curve (O'Neill, *Semi-Riemannian Geometry*, Ch. 14, p. 415). -/
theorem isCauchySurface_zeroTimeSlice :
    IsCauchySurface minkowskiTimeOrientation zeroTimeSlice := by
  refine ⟨isClosed_zeroTimeSlice, isAchronal_zeroTimeSlice, fun γ s hs hγ hin => ?_⟩
  obtain ⟨t, hts, ht0⟩ := exists_coordZero_eq_zero hγ hs hin
  refine ⟨t, ⟨hts, ht0⟩, ?_⟩
  rintro u ⟨hus, hu0⟩
  exact isAchronal_zeroTimeSlice.eq_of_futureTimelikeOn hs hγ hus hts hu0 ht0

/-- **P1.W2**: Minkowski space is globally hyperbolic (Wald, *General Relativity*,
§8.3; the `{t = 0}` slice witnesses the definition). -/
theorem minkowski_isGloballyHyperbolic :
    IsGloballyHyperbolic minkowskiTimeOrientation :=
  ⟨zeroTimeSlice, isCauchySurface_zeroTimeSlice⟩

-- The origin lies on the slice; the unit future timelike vector does not.
example : (0 : M4) ∈ zeroTimeSlice := rfl
example : (EuclideanSpace.single 0 1 : M4) ∉ zeroTimeSlice := by
  intro h
  have h' : (EuclideanSpace.single 0 1 : M4) 0 = 0 := h
  norm_num at h'

end Spacetime.Minkowski
