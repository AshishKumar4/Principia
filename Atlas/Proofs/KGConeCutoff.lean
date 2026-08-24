import Atlas.Proofs.KleinGordon
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# P2.6c / L2 — smoothed cone cutoff for finite propagation speed

The geometric input of the local-energy proof of finite propagation speed for the
Klein–Gordon equation: a smooth cutoff supported in the forward cone of slope `1` with apex
`(x0, R)`, whose spatial gradient is dominated by minus its time derivative. That domination
is what later lets the boundary flux of the local energy over a shrinking ball absorb into
the time decay (Evans, *Partial Differential Equations*, 2nd ed., §2.4 "Wave equation",
§2.4.3 "Energy methods" — uniqueness, domain of dependence, finite propagation speed;
cited at section level, no numbered display of that section is asserted here).

Two objects on the time-zero slice `M3 = ℝ³`:

* `QFT.KleinGordon.psi_delta x0 δ` — the smoothed distance `x ↦ √(‖x - x0‖² + δ²)`.
  For `δ ≠ 0` it is everywhere smooth, brackets the true distance
  (`le_psi_delta`, `psi_delta_le_add`), and has gradient norm `≤ 1`
  (`gradient_psi_delta`, `norm_gradient_psi_delta_le_one`).
* `QFT.KleinGordon.chi x0 R δ ε t` — the cutoff
  `x ↦ Real.smoothTransition ((R - (t + psi_delta x0 δ x)) / ε)`, `ε > 0` explicit.
  Values in `[0, 1]`; jointly smooth in `(t, x)`; `support χ(t,·) ⊆ closedBall x0 (R - t)`
  (so `χ` lives inside the forward cone `t + ‖x - x0‖ ≤ R`); `χ = 1` strictly inside
  (`t + ‖x - x0‖ + δ + ε ≤ R`, in particular at `x0` once `t ≤ R - ε - δ`);
  time derivative `≤ 0`; and the cone inequality `‖∇_x χ‖ ≤ -∂_t χ`
  (`norm_gradient_chi_le`), proved by the chain rule on both sides,
  `‖∇ psi_delta‖ ≤ 1`, and `Monotone.deriv_nonneg` on `Real.smoothTransition`.

This lane is independent of the propagator lane (P2.6c/L1): it touches only elementary
calculus on `M3`.

## Conventions

* `∇` is Mathlib's `gradient` (`Mathlib/Analysis/Calculus/Gradient/Basic.lean`); `∂_t` is
  `deriv` in the `t` variable with `x` frozen.
* `Real.smoothTransition` is Mathlib's smooth step (`Mathlib/Analysis/SpecialFunctions/
  SmoothTransition.lean`): `0` on `(-∞, 0]`, `1` on `[1, ∞)`, monotone, `C^∞`.
* Smoothness is stated at the `∞` level (`ContDiff ℝ ∞`, `open scoped ContDiff`); every
  ingredient lemma used is available verbatim at that level.

## Sources

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS (2010), Graduate Studies in
  Math. 19: §2.4 *Wave equation*, subsection §2.4.3 *Energy methods* — energy method for
  `u_tt - Δu`, domain of dependence and finite propagation speed via localized energy on
  the shrinking ball `B(x0, t0 - t)`; the sharp cutoff `1_{B(x0, t0-t)}` used there is
  smoothed here by `psi_delta` composed with `Real.smoothTransition`. Cited at section
  level: the subsection number was checked against two independent university course
  schedules citing Evans' numbering, and no numbered display of that subsection is
  asserted here.
* Mathlib sources, verified in-tree (toolchain v4.31): `Mathlib/Analysis/SpecialFunctions/
  SmoothTransition.lean` (`Real.smoothTransition` and its `nonneg`, `le_one`,
  `one_of_one_le`, `zero_iff_nonpos`, `monotone`, `contDiff` API);
  `Mathlib/Analysis/Calculus/Deriv/Slope.lean` (`Monotone.deriv_nonneg`);
  `Mathlib/Analysis/Calculus/Deriv/Comp.lean` (`HasDerivAt.scomp`,
  `HasDerivAt.comp_hasFDerivAt`); `Mathlib/Analysis/SpecialFunctions/Sqrt.lean`
  (`HasFDerivAt.sqrt`, `ContDiff.sqrt`); `Mathlib/Analysis/InnerProductSpace/Calculus.lean`
  (`HasFDerivAt.norm_sq`, `contDiff_norm_sq`).
-/

namespace QFT.KleinGordon

open scoped ContDiff Gradient

/-! ### Generic helpers -/

/-- Derivative transport inside `HasFDerivAt`: equal continuous linear maps give the same
statement. -/
private theorem hasFDerivAt_congr_deriv' {D₁ D₂ : M3 →L[ℝ] ℝ} {f : M3 → ℝ} {x : M3}
    (h : HasFDerivAt f D₁ x) (hD : D₁ = D₂) : HasFDerivAt f D₂ x := by
  rw [hD] at h
  exact h

/-- Pointwise description of `innerSL` applied to a vector, for computations. -/
private theorem innerSL_coe_apply (w y : M3) : (innerSL ℝ w) y = inner ℝ w y := rfl

/-- Natural-number scalar action on a real number is multiplication by the cast. -/
private theorem nat_smul_real (n : ℕ) (r : ℝ) : n • r = n * r := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [succ_nsmul, ih, Nat.cast_succ, add_one_mul]

/-! ### The smoothed distance `psi_delta` -/

/-- The smoothed distance to `x0` with smoothing width `delta`:
`x ↦ √(‖x - x0‖² + delta²)`. For `delta ≠ 0` the radicand never vanishes, so this is a
globally smooth replacement for `x ↦ ‖x - x0‖` (Evans §2.4.3, section level: the smoothed
version of the ball radius `B(x0, t0 - t)` in the local-energy argument). -/
noncomputable def psi_delta (x0 : M3) (delta : ℝ) (x : M3) : ℝ :=
  √(‖x - x0‖ ^ 2 + delta ^ 2)

theorem psi_delta_nonneg (x0 : M3) (delta : ℝ) (x : M3) : 0 ≤ psi_delta x0 delta x :=
  Real.sqrt_nonneg _

/-- Lower bracket: `psi_delta` dominates the true distance (both sides nonnegative, compare
the radicands under the square root). -/
theorem le_psi_delta (x0 : M3) (delta : ℝ) (x : M3) :
    ‖x - x0‖ ≤ psi_delta x0 delta x := by
  have h : ‖x - x0‖ = √(‖x - x0‖ ^ 2) := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg (x - x0))]
  rw [h]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg delta))

/-- Upper bracket: `psi_delta` exceeds the true distance by at most `|delta|`. -/
theorem psi_delta_le_add (x0 : M3) (delta : ℝ) (x : M3) :
    psi_delta x0 delta x ≤ ‖x - x0‖ + |delta| := by
  have habs : delta ^ 2 = |delta| ^ 2 := by rw [sq_abs]
  have key : ‖x - x0‖ ^ 2 + delta ^ 2 ≤ (‖x - x0‖ + |delta|) ^ 2 := by
    rw [habs]
    nlinarith [mul_nonneg (norm_nonneg (x - x0)) (abs_nonneg delta)]
  calc psi_delta x0 delta x = √(‖x - x0‖ ^ 2 + delta ^ 2) := rfl
    _ ≤ √((‖x - x0‖ + |delta|) ^ 2) := Real.sqrt_le_sqrt key
    _ = ‖x - x0‖ + |delta| :=
        Real.sqrt_sq (add_nonneg (norm_nonneg (x - x0)) (abs_nonneg delta))

/-- Upper bracket with a nonnegative smoothing parameter spelled without the absolute
value. -/
theorem psi_delta_le_add_of_nonneg (x0 : M3) {delta : ℝ} (hdelta : 0 ≤ delta) (x : M3) :
    psi_delta x0 delta x ≤ ‖x - x0‖ + delta := by
  have h := psi_delta_le_add x0 delta x
  rwa [abs_of_nonneg hdelta] at h

theorem psi_delta_pos (x0 : M3) {delta : ℝ} (hdelta : delta ≠ 0) (x : M3) :
    0 < psi_delta x0 delta x := by
  refine Real.sqrt_pos.2 ?_
  exact lt_of_le_of_lt (sq_nonneg (‖x - x0‖)) (lt_add_of_pos_right _ (sq_pos_iff.mpr hdelta))

private theorem psi_radicand_ne_zero (x0 : M3) {delta : ℝ} (hdelta : delta ≠ 0) (x : M3) :
    ‖x - x0‖ ^ 2 + delta ^ 2 ≠ 0 := by
  intro h
  apply hdelta
  have h1 : 0 ≤ ‖x - x0‖ ^ 2 := sq_nonneg _
  have h2 : delta ^ 2 = 0 := by linarith [h, h1, sq_nonneg delta]
  exact sq_eq_zero_iff.mp h2

/-- Smoothness away from the exceptional point: for `delta ≠ 0` the radicand
`‖x - x0‖² + delta²` is smooth and nowhere zero, so `Real.sqrt` composes freely
(`ContDiff.sqrt`, `Mathlib/Analysis/SpecialFunctions/Sqrt.lean`; squared-norm smoothness
from `contDiff_norm_sq`, `Mathlib/Analysis/InnerProductSpace/Calculus.lean`). -/
theorem contDiff_psi_delta (x0 : M3) {delta : ℝ} (hdelta : delta ≠ 0) {n : ℕ∞ω} :
    ContDiff ℝ n (psi_delta x0 delta) := by
  refine ContDiff.sqrt ?_ fun x => psi_radicand_ne_zero x0 hdelta x
  exact ((((contDiff_id (E := M3)).sub contDiff_const).norm_sq ℝ).add contDiff_const)

/-- Fréchet derivative of the smoothed distance:
`d(psi_delta)(x) = innerSL ((x - x0) / psi_delta x)`. Chain rule `HasFDerivAt.sqrt`
(Mathlib Sqrt.lean) applied to the squared norm, whose derivative is `2 • innerSL`
(`HasFDerivAt.norm_sq`, `Mathlib/Analysis/InnerProductSpace/Calculus.lean`). -/
theorem hasFDerivAt_psi_delta (x0 : M3) {delta : ℝ} (hdelta : delta ≠ 0) (x : M3) :
    HasFDerivAt (psi_delta x0 delta)
      (innerSL ℝ ((psi_delta x0 delta x)⁻¹ • (x - x0))) x := by
  have hnormsq : HasFDerivAt (fun z : M3 => ‖z - x0‖ ^ 2)
      ((2:ℝ) • innerSL ℝ (x - x0)) x := by
    have h0 := ((hasFDerivAt_id x).sub_const x0).norm_sq
    refine hasFDerivAt_congr_deriv' h0 ?_
    ext z
    simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      id_eq, innerSL_coe_apply, nat_smul_real, smul_eq_mul]
    ring
  have hsum : HasFDerivAt (fun z : M3 => ‖z - x0‖ ^ 2 + delta ^ 2)
      ((2:ℝ) • innerSL ℝ (x - x0)) x :=
    hasFDerivAt_congr_deriv' (hnormsq.add (hasFDerivAt_const (delta ^ 2) x)) (by simp)
  have hs := hsum.sqrt (psi_radicand_ne_zero x0 hdelta x)
  refine hasFDerivAt_congr_deriv' hs ?_
  ext z
  simp only [smul_apply, smul_eq_mul, innerSL_coe_apply,
    real_inner_smul_left]
  have hc : ((1:ℝ) / (2 * √(‖x - x0‖ ^ 2 + delta ^ 2))) * 2
      = (psi_delta x0 delta x)⁻¹ := by
    have hq0 : (0:ℝ) < ‖x - x0‖ ^ 2 + delta ^ 2 :=
      lt_of_le_of_lt (sq_nonneg (‖x - x0‖)) (lt_add_of_pos_right _ (sq_pos_iff.mpr hdelta))
    have hps : 0 < √(‖x - x0‖ ^ 2 + delta ^ 2) := Real.sqrt_pos.2 hq0
    have heq : √(‖x - x0‖ ^ 2 + delta ^ 2) = psi_delta x0 delta x := rfl
    rw [heq]
    field_simp [ne_of_gt hps]
  rw [← mul_assoc, hc]

/-- Gradient version: `∇ psi_delta x = (x - x0) / psi_delta x`. -/
theorem hasGradientAt_psi_delta (x0 : M3) {delta : ℝ} (hdelta : delta ≠ 0) (x : M3) :
    HasGradientAt (psi_delta x0 delta)
      ((psi_delta x0 delta x)⁻¹ • (x - x0)) x := by
  have h := hasFDerivAt_psi_delta x0 hdelta x
  rw [show (innerSL ℝ ((psi_delta x0 delta x)⁻¹ • (x - x0)))
      = InnerProductSpace.toDual ℝ M3
        ((psi_delta x0 delta x)⁻¹ • (x - x0)) from rfl] at h
  simpa using h.hasGradientAt

@[simp]
theorem gradient_psi_delta (x0 : M3) {delta : ℝ} (hdelta : delta ≠ 0) (x : M3) :
    gradient (psi_delta x0 delta) x = (psi_delta x0 delta x)⁻¹ • (x - x0) :=
  (hasGradientAt_psi_delta x0 hdelta x).gradient

/-- **The smoothed distance is 1-Lipschitz in gradient**: `‖∇ psi_delta x‖ ≤ 1`. Directly
from the explicit gradient and the lower bracket `le_psi_delta`. -/
theorem norm_gradient_psi_delta_le_one (x0 : M3) {delta : ℝ} (hdelta : delta ≠ 0) (x : M3) :
    ‖gradient (psi_delta x0 delta) x‖ ≤ 1 := by
  rw [gradient_psi_delta x0 hdelta x, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 <| psi_delta_nonneg ..), inv_mul_eq_div,
    div_le_one (psi_delta_pos x0 hdelta x)]
  exact le_psi_delta x0 delta x

/-! ### The cone cutoff `chi` -/

/-- The smoothed cone cutoff of the local-energy argument (Evans §2.4.3, section level):
`χ(t, x) = smoothTransition ((R - (t + psi_delta x0 δ x)) / ε)`. Equal to `1` deep inside
the forward cone `t + ‖x - x0‖ + δ + ε ≤ R`, equal to `0` outside `t + ‖x - x0‖ ≤ R`, and
its spatial gradient is dominated by minus its time derivative. -/
noncomputable def chi (x0 : M3) (R delta eps : ℝ) (t : ℝ) (x : M3) : ℝ :=
  Real.smoothTransition ((R - (t + psi_delta x0 delta x)) / eps)

theorem chi_nonneg (x0 : M3) (R delta eps : ℝ) (t : ℝ) (x : M3) : 0 ≤ chi x0 R delta eps t x :=
  Real.smoothTransition.nonneg _

theorem chi_le_one (x0 : M3) (R delta eps : ℝ) (t : ℝ) (x : M3) : chi x0 R delta eps t x ≤ 1 :=
  Real.smoothTransition.le_one _

/-- Joint smoothness of the cutoff in `(t, x)` (PJ.2a): an affine rearrangement of the
jointly smooth `(p.1, psi_delta p.2)`, scaled by `ε`, composed with the globally smooth
`Real.smoothTransition`. -/
theorem contDiff_chi (x0 : M3) (R delta eps : ℝ) (hdelta : delta ≠ 0) :
    ContDiff ℝ ∞ fun p : ℝ × M3 => chi x0 R delta eps p.1 p.2 := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition :=
    contDiff_infty.2 fun m => Real.smoothTransition.contDiff (n := m)
  have hA : ContDiff ℝ ∞
      (fun p : ℝ × M3 => (R - (p.1 + psi_delta x0 delta p.2)) / eps) :=
    (contDiff_const.sub
      ((contDiff_fst.add ((contDiff_psi_delta x0 hdelta).comp contDiff_snd)))).div_const eps
  exact hs.comp hA

/-- Spatial support inclusion (PJ.2a): where the cutoff does not vanish lies in the closed
ball of radius `R - t` around `x0`, i.e. inside the forward cone. Indeed a nonpositive
argument forces `smoothTransition` to vanish. -/
theorem support_chi_subset_closedBall (x0 : M3) (R delta eps : ℝ) (heps : 0 < eps) (t : ℝ) :
    Function.support (chi x0 R delta eps t) ⊆ Metric.closedBall x0 (R - t) := by
  intro x hx
  simp only [Function.mem_support] at hx
  have hu : 0 < (R - (t + psi_delta x0 delta x)) / eps :=
    not_le.mp fun h => hx (Real.smoothTransition.zero_of_nonpos h)
  have hnum : 0 < R - (t + psi_delta x0 delta x) := by
    have hm : eps * ((R - (t + psi_delta x0 delta x)) / eps)
        = R - (t + psi_delta x0 delta x) := by field_simp
    have h2 : 0 < eps * ((R - (t + psi_delta x0 delta x)) / eps) := mul_pos heps hu
    rwa [hm] at h2
  exact le_of_lt (by
    calc ‖x - x0‖ ≤ psi_delta x0 delta x := le_psi_delta x0 delta x
      _ < R - t := by linarith)

/-- Topological support version of `support_chi_subset_closedBall`: the closure of the
support is still inside the closed ball (which is closed,
`Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`). -/
theorem tsupport_chi_subset_closedBall (x0 : M3) (R delta eps : ℝ) (heps : 0 < eps) (t : ℝ) :
    tsupport (chi x0 R delta eps t) ⊆ Metric.closedBall x0 (R - t) :=
  closure_minimal (support_chi_subset_closedBall x0 R delta eps heps t)
    Metric.isClosed_closedBall

/-- The cutoff equals `1` strictly inside the cone (PJ.2a): whenever
`t + ‖x - x0‖ + delta + eps ≤ R`, the argument of `smoothTransition` is at least `1`
(`one_of_one_le`). -/
theorem chi_eq_one_of_dist_le (x0 : M3) (R delta eps : ℝ) (hdelta : 0 ≤ delta) (heps : 0 < eps)
    (t : ℝ) (x : M3) (h : t + ‖x - x0‖ + delta + eps ≤ R) :
    chi x0 R delta eps t x = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  rw [one_le_div heps]
  have hpsi := psi_delta_le_add_of_nonneg x0 hdelta x
  linarith

/-- Special case of `chi_eq_one_of_dist_le` at the center `x0` (PJ.2a): `χ(t, x0) = 1` for
`t ≤ R - eps - delta`, since `‖x0 - x0‖ = 0`. -/
theorem chi_center_eq_one (x0 : M3) (R delta eps : ℝ) (hdelta : 0 ≤ delta) (heps : 0 < eps)
    (t : ℝ) (h : t ≤ R - eps - delta) :
    chi x0 R delta eps t x0 = 1 := by
  refine chi_eq_one_of_dist_le x0 R delta eps hdelta heps t x0 ?_
  have hx0 : ‖x0 - x0‖ = 0 := by simp
  have hpsi := psi_delta_le_add_of_nonneg x0 hdelta x0
  linarith

/-- Time derivative of the cutoff by the chain rule (`HasDerivAt.scomp`,
`Mathlib/Analysis/Calculus/Deriv/Comp.lean`): with `u = (R - (t + psi_delta x))/ε`,
`∂_t χ(t, x) = -ε⁻¹ · (Real.smoothTransition)'(u)`. -/
theorem deriv_chi_time (x0 : M3) (R delta eps : ℝ) (t : ℝ) (x : M3) :
    deriv (fun τ => chi x0 R delta eps τ x) t
        = -(eps⁻¹) *
          deriv Real.smoothTransition ((R - (t + psi_delta x0 delta x)) / eps) := by
  have hs_diff : Differentiable ℝ Real.smoothTransition :=
    Real.smoothTransition.contDiff (n := 1) |>.differentiable (by simp)
  have h1 : HasDerivAt (fun τ => τ + psi_delta x0 delta x) 1 t :=
    (hasDerivAt_id t).add_const (psi_delta x0 delta x)
  have hphi : HasDerivAt (fun τ => (R - (τ + psi_delta x0 delta x)) / eps) (-1 / eps) t := by
    simpa using (HasDerivAt.const_sub R h1).div_const eps
  have hd : HasDerivAt (fun τ => chi x0 R delta eps τ x)
      (((-1 : ℝ) / eps) •
        deriv Real.smoothTransition ((R - (t + psi_delta x0 delta x)) / eps)) t :=
    HasDerivAt.scomp t
      ((hs_diff ((R - (t + psi_delta x0 delta x)) / eps)).hasDerivAt) hphi
  rw [show (((-1 : ℝ) / eps) •
      deriv Real.smoothTransition ((R - (t + psi_delta x0 delta x)) / eps))
      = -(eps⁻¹) *
        deriv Real.smoothTransition ((R - (t + psi_delta x0 delta x)) / eps) from by
        simp only [smul_eq_mul]
        ring] at hd
  exact hd.deriv

/-- The time derivative of the cutoff is nonpositive (PJ.2b, first half): the chain-rule
coefficient `-ε⁻¹` is nonpositive and `(Real.smoothTransition)' ≥ 0` everywhere because
`Real.smoothTransition` is monotone (`Monotone.deriv_nonneg`,
`Mathlib/Analysis/Calculus/Deriv/Slope.lean`). -/
theorem deriv_chi_time_nonpos (x0 : M3) (R delta eps : ℝ) (heps : 0 < eps) (t : ℝ) (x : M3) :
    deriv (fun τ => chi x0 R delta eps τ x) t ≤ 0 := by
  rw [deriv_chi_time x0 R delta eps]
  have hD : 0 ≤ deriv Real.smoothTransition ((R - (t + psi_delta x0 delta x)) / eps) :=
    Real.smoothTransition.monotone.deriv_nonneg
  have hinv : 0 ≤ eps⁻¹ := inv_nonneg.2 heps.le
  nlinarith

/-- Spatial gradient of the cutoff by the chain rule
(`HasDerivAt.comp_hasFDerivAt`): `∇_x χ(t, x) = (∂_t χ)(t, x) • ∇ psi_delta x`. The same
scalar factor appears in both because the argument `R - (t + psi_delta x)` couples `t` and
`psi_delta x` with opposite signs. -/
theorem hasGradientAt_chi (x0 : M3) (R delta eps : ℝ) (hdelta : delta ≠ 0) (_heps : 0 < eps)
    (t : ℝ) (x : M3) :
    HasGradientAt (chi x0 R delta eps t)
      ((deriv (fun τ => chi x0 R delta eps τ x) t) •
        gradient (psi_delta x0 delta) x) x := by
  have hs_diff : Differentiable ℝ Real.smoothTransition :=
    Real.smoothTransition.contDiff (n := 1) |>.differentiable (by simp)
  have hpsi := hasFDerivAt_psi_delta x0 hdelta x
  have hphi : HasFDerivAt (fun z => (R - (t + psi_delta x0 delta z)) / eps)
      (eps⁻¹ • -(innerSL ℝ ((psi_delta x0 delta x)⁻¹ • (x - x0)))) x := by
    have hstep : HasFDerivAt
        ((fun _ : M3 => R) - ((fun _ : M3 => t) + psi_delta x0 delta))
        (-(innerSL ℝ ((psi_delta x0 delta x)⁻¹ • (x - x0)))) x := by
      refine hasFDerivAt_congr_deriv'
        ((hasFDerivAt_const R x).sub ((hasFDerivAt_const t x).add hpsi)) ?_
      ext z
      simp [innerSL_coe_apply]
    have hsub : HasFDerivAt (fun z => R - (t + psi_delta x0 delta z))
        (-(innerSL ℝ ((psi_delta x0 delta x)⁻¹ • (x - x0)))) x :=
      hstep.congr_of_eventuallyEq (by filter_upwards with z; simp)
    have hscale := hsub.const_smul (eps⁻¹)
    refine hscale.congr_of_eventuallyEq ?_
    filter_upwards with z
    have hcoe : (eps⁻¹ • (fun w => R - (t + psi_delta x0 delta w))) z
        = eps⁻¹ * (R - (t + psi_delta x0 delta z)) := rfl
    rw [hcoe, div_eq_inv_mul]
  have hchain := HasDerivAt.comp_hasFDerivAt x
    ((hs_diff ((R - (t + psi_delta x0 delta x)) / eps)).hasDerivAt) hphi
  rw [deriv_chi_time x0 R delta eps, gradient_psi_delta x0 hdelta x]
  have hvec : (deriv Real.smoothTransition ((R - (t + psi_delta x0 delta x)) / eps)) •
      (eps⁻¹ • -(innerSL ℝ ((psi_delta x0 delta x)⁻¹ • (x - x0))))
      = innerSL ℝ (((-(eps⁻¹) *
          deriv Real.smoothTransition ((R - (t + psi_delta x0 delta x)) / eps))) •
        ((psi_delta x0 delta x)⁻¹ • (x - x0))) := by
    ext y
    simp only [smul_apply, neg_apply, smul_eq_mul,
      innerSL_coe_apply, real_inner_smul_left]
    ring
  rw [hvec] at hchain
  have hfun : (fun z => chi x0 R delta eps t z)
      = (Real.smoothTransition ∘
          fun z => (R - (t + psi_delta x0 delta z)) / eps) := by
    rfl
  rw [← hfun] at hchain
  rw [show (innerSL ℝ ((-(eps⁻¹) *
        deriv Real.smoothTransition ((R - (t + psi_delta x0 delta x)) / eps)) •
        ((psi_delta x0 delta x)⁻¹ • (x - x0))))
      = InnerProductSpace.toDual ℝ M3 ((-(eps⁻¹) *
        deriv Real.smoothTransition ((R - (t + psi_delta x0 delta x)) / eps)) •
        ((psi_delta x0 delta x)⁻¹ • (x - x0))) from rfl] at hchain
  simpa using hchain.hasGradientAt

@[simp]
theorem gradient_chi (x0 : M3) (R delta eps : ℝ) (hdelta : delta ≠ 0) (heps : 0 < eps)
    (t : ℝ) (x : M3) :
    gradient (chi x0 R delta eps t) x
      = (deriv (fun τ => chi x0 R delta eps τ x) t) •
        gradient (psi_delta x0 delta) x :=
  (hasGradientAt_chi x0 R delta eps hdelta heps t x).gradient

/-- **The cone inequality** (PJ.2b): `‖∇_x χ(t, x)‖ ≤ -∂_t χ(t, x)`. This is the load-bearing
estimate of the local-energy argument (Evans §2.4.3, section level): it lets the boundary
flux of the energy over the shrinking ball be absorbed by the time decay. Proof: by
`gradient_chi` the left side is `|∂_t χ| · ‖∇ psi_delta x‖`, the time derivative is
nonpositive (`deriv_chi_time_nonpos`), and `‖∇ psi_delta‖ ≤ 1`
(`norm_gradient_psi_delta_le_one`). -/
theorem norm_gradient_chi_le (x0 : M3) (R delta eps : ℝ) (hdelta : delta ≠ 0) (heps : 0 < eps)
    (t : ℝ) (x : M3) :
    ‖gradient (chi x0 R delta eps t) x‖
        ≤ -deriv (fun τ => chi x0 R delta eps τ x) t := by
  have hdt : deriv (fun τ => chi x0 R delta eps τ x) t ≤ 0 :=
    deriv_chi_time_nonpos x0 R delta eps heps t x
  rw [gradient_chi x0 R delta eps hdelta heps t x, norm_smul, Real.norm_eq_abs,
    abs_of_nonpos hdt]
  have hn := norm_gradient_psi_delta_le_one x0 hdelta x
  have hnn : 0 ≤ ‖gradient (psi_delta x0 delta) x‖ := norm_nonneg _
  have h2 : 0 ≤ -deriv (fun τ => chi x0 R delta eps τ x) t := by linarith
  nlinarith [mul_nonneg h2 (by linarith : (0:ℝ) ≤ 1 - ‖gradient (psi_delta x0 delta) x‖)]

end QFT.KleinGordon
