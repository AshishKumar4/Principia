import Atlas.Proofs.KGConeCutoff

/-!
# P2.6c adversarial probes — the smoothed cone cutoff lane (P2.6c/L2)

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.6c/` only. It pins the
landed surface of `Atlas.Proofs.KGConeCutoff` to **final observables** at the explicit
parameters `x₀ = 0`, `R = 2`, `δ = 1/2`, `ε = 1/4`, with `outPoint = 5·e₁`.

Positive checks:

* `psi_delta` brackets the true distance (`probe_psi_bracket_out`) and evaluates to the
  exact smoothing radius at the centre (`probe_psi_origin_exact`);
* `χ = 1` strictly inside the cone at two explicit interior points
  (`probe_chi_interior_center`, `probe_chi_interior_offcenter`);
* `χ = 0` outside the cone, both spatially and temporally past the apex
  (`probe_chi_outside_space`, `probe_chi_outside_time`);
* the support sits in the shrinking ball and `∂ₜχ ≤ 0`
  (`probe_support_inside_ball`, `probe_dt_nonpos`);
* the final cone inequality `‖∇χ‖ ≤ -∂ₜχ` at explicit parameters
  (`probe_cone_inequality_final`).

Refutations at explicit differentiable points:

* the unsmoothed distance `x ↦ ‖x‖` is **not** differentiable at the origin — exactly
  where the smoothed distance `psi_delta 0 δ` is differentiable
  (`probe_unsmoothed_distance_not_differentiable`,
  `probe_smoothed_distance_differentiable_origin`);
* the wrong-sign time cutoff `χ⁻` built from `smoothTransition((R + (t + ψ))/ε)` is
  jointly smooth everywhere yet fails the support semantics: at the regular point
  `(t, x) = (0, outPoint)` it observes `1` where the correct cutoff observes `0`
  (`probe_wrong_sign_cutoff_fails`).
-/

open scoped ContDiff Gradient Topology Filter

namespace QFT.KleinGordonCutoffProbe

open QFT.KleinGordon

/-- Probe exterior point: five units along the first spatial axis, well beyond `R = 2`. -/
noncomputable def outPoint : M3 := EuclideanSpace.single (0 : Fin 3) (5 : ℝ)

theorem norm_outPoint : ‖outPoint‖ = 5 := by simp [outPoint]

/-! ### The smoothed distance at explicit parameters -/

/-- Final observable: at the centre the smoothed distance equals the smoothing radius,
so the deformation is visible even where the true distance vanishes. -/
theorem probe_psi_origin_exact :
    psi_delta (0 : M3) (1 / 2 : ℝ) (0 : M3) = 1 / 2 := by
  have h0 : ‖((0 : M3) - (0 : M3))‖ = 0 := by simp
  rw [psi_delta, h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
    Real.sqrt_sq (show (0 : ℝ) ≤ 1 / 2 by norm_num)]

/-- Final observable of the two-sided bracket `‖x‖ ≤ ψ ≤ ‖x‖ + δ` at the exterior point. -/
theorem probe_psi_bracket_out :
    (5 : ℝ) ≤ psi_delta (0 : M3) (1 / 2 : ℝ) outPoint ∧
      psi_delta (0 : M3) (1 / 2 : ℝ) outPoint ≤ 11 / 2 := by
  constructor
  · have h := le_psi_delta (0 : M3) (1 / 2 : ℝ) outPoint
    rwa [sub_zero, norm_outPoint] at h
  · have h := psi_delta_le_add_of_nonneg (0 : M3)
        (show (0 : ℝ) ≤ 1 / 2 by norm_num) outPoint
    rw [sub_zero, norm_outPoint] at h
    linarith

/-- The smoothed distance is differentiable at the centre — the property the unsmoothed
distance lacks (see `probe_unsmoothed_distance_not_differentiable`). -/
theorem probe_smoothed_distance_differentiable_origin :
    DifferentiableAt ℝ (psi_delta (0 : M3) (1 / 2 : ℝ)) (0 : M3) :=
  (hasFDerivAt_psi_delta (0 : M3) (by norm_num) (0 : M3)).differentiableAt

/-! ### The cutoff at explicit parameters -/

/-- Final observable (**PJ.2a**): `χ = 1` at the apex time slice's deep interior. -/
theorem probe_chi_interior_center :
    chi (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) 0 (0 : M3) = 1 :=
  chi_eq_one_of_dist_le (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) (by norm_num) (by norm_num) 0
    (0 : M3) (by simp; norm_num)

/-- Final observable (**PJ.2a**): `χ = 1` still off-centre, one unit from the apex. -/
theorem probe_chi_interior_offcenter :
    chi (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) 0
        (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = 1 := by
  refine chi_eq_one_of_dist_le (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) (by norm_num)
    (by norm_num) 0 _ ?_
  have hn : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : M3) - (0 : M3)‖ = 1 := by
    rw [sub_zero]
    simp
  rw [hn]
  norm_num

/-- Final observable (**PJ.2a**): `χ = 0` spatially outside the ball `B(x₀, R)`. -/
theorem probe_chi_outside_space :
    chi (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) 0 outPoint = 0 := by
  rw [chi]
  refine Real.smoothTransition.zero_of_nonpos ?_
  have hψ : (5 : ℝ) ≤ psi_delta (0 : M3) (1 / 2 : ℝ) outPoint := by
    have h := le_psi_delta (0 : M3) (1 / 2 : ℝ) outPoint
    rwa [sub_zero, norm_outPoint] at h
  rw [div_le_iff₀ (show (0 : ℝ) < 1 / 4 by norm_num)]
  linarith

/-- Final observable (**PJ.2a**): `χ = 0` at the centre once the cone swept past, i.e.
for `t = 3 > R = 2`: the whole time slice lies outside the forward cone. -/
theorem probe_chi_outside_time :
    chi (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) 3 (0 : M3) = 0 := by
  rw [chi]
  refine Real.smoothTransition.zero_of_nonpos ?_
  rw [div_le_iff₀ (show (0 : ℝ) < 1 / 4 by norm_num)]
  have hp := probe_psi_origin_exact
  norm_num [hp]

/-- Final observable (**PJ.2a**): the spatial support lives in the shrinking ball
`closedBall x₀ (R - t)` at `t = 0`. -/
theorem probe_support_inside_ball :
    Function.support (chi (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) 0)
      ⊆ Metric.closedBall (0 : M3) 2 := by
  simpa using support_chi_subset_closedBall (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ)
    (show (0 : ℝ) < 1 / 4 by norm_num) 0

/-- The selected PJ.2b point lies strictly inside the transition band. This
prevents a flat `0 ≤ 0` check from masquerading as sign evidence. -/
theorem probe_chi_transition_value :
    0 < chi (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) (11 / 8 : ℝ) (0 : M3) ∧
      chi (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) (11 / 8 : ℝ) (0 : M3) < 1 := by
  rw [chi]
  have hp := probe_psi_origin_exact
  constructor
  · apply Real.smoothTransition.pos_of_pos
    norm_num [hp]
  · apply Real.smoothTransition.lt_one_of_lt_one
    norm_num [hp]

/-- Final observable (**PJ.2b**, first half): the time derivative is
nonpositive at a point strictly inside the transition band. -/
theorem probe_dt_nonpos :
    deriv (fun τ => chi (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) τ (0 : M3))
      (11 / 8 : ℝ) ≤ 0 :=
  deriv_chi_time_nonpos (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ)
    (show (0 : ℝ) < 1 / 4 by norm_num) (11 / 8 : ℝ) (0 : M3)

/-- Final observable (**PJ.2b**, the cone inequality): `‖∇χ‖ ≤ -∂ₜχ`
at a point strictly inside the transition band. -/
theorem probe_cone_inequality_final :
    ‖gradient (chi (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) (11 / 8 : ℝ))
        (0 : M3)‖ ≤
      -deriv (fun τ => chi (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) τ
        (0 : M3)) (11 / 8 : ℝ) :=
  norm_gradient_chi_le (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ)
    (by norm_num) (by norm_num) (11 / 8 : ℝ) (0 : M3)

/-! ### Refutation: the unsmoothed distance is not differentiable at the centre -/

/-- The naive replacement `x ↦ ‖x - x₀‖` fails differentiability exactly at `x₀ = 0`,
the point where the smoothed distance is differentiable. Restricting to the ray
`t ↦ t·e₁` reduces this to the non-differentiability of `|·|` at `0`: the right slopes
force derivative `1` while the left slopes force `-1`. -/
theorem probe_unsmoothed_distance_not_differentiable :
    ¬ DifferentiableAt ℝ (fun x : M3 => ‖x - (0 : M3)‖) (0 : M3) := by
  intro h
  have hcurveDiff : DifferentiableAt ℝ
      (fun t : ℝ => t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (0 : ℝ) :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))).differentiableAt
  have hcomp : DifferentiableAt ℝ
      ((fun x : M3 => ‖x - (0 : M3)‖) ∘
        (fun t : ℝ => t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) (0 : ℝ) :=
    DifferentiableAt.comp (𝕜 := ℝ)
      (g := fun x : M3 => ‖x - (0 : M3)‖)
      (f := fun t : ℝ => t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (x := 0)
      (by simpa using h) hcurveDiff
  have he1 : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : M3)‖ = 1 := by
    simp [EuclideanSpace.single]
  have hfEq : (fun t : ℝ =>
        ‖(t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : M3) - (0 : M3)‖)
      = fun t : ℝ => |t| := by
    funext t
    rw [sub_zero, norm_smul, Real.norm_eq_abs, he1, mul_one]
  have habsd : DifferentiableAt ℝ (fun t : ℝ => |t|) (0 : ℝ) := by
    rw [← hfEq]
    exact hcomp
  have habs := habsd.hasFDerivAt.hasDerivAt
  have hevR : (fun t : ℝ => t⁻¹ • (|0 + t| - |0|)) =ᶠ[𝓝[>] (0:ℝ)] fun _ => (1 : ℝ) := by
    have hfR : ((𝓝[>] (0:ℝ)) : Filter ℝ) = nhds (0 : ℝ) ⊓ 𝓟 (Set.Ioi (0 : ℝ)) := by
      simp [nhdsWithin]
    rw [hfR]
    exact Filter.eventually_inf_principal.mpr
      (Filter.Eventually.of_forall fun t htpos => by
        have ht0 : (0 : ℝ) < t := htpos
        simp [abs_of_pos ht0, inv_mul_cancel₀ (ne_of_gt ht0)])
  have hevL : (fun t : ℝ => t⁻¹ • (|0 + t| - |0|)) =ᶠ[𝓝[<] (0:ℝ)] fun _ => (-1 : ℝ) := by
    have hfL : ((𝓝[<] (0:ℝ)) : Filter ℝ) = nhds (0 : ℝ) ⊓ 𝓟 (Set.Iio (0 : ℝ)) := by
      simp [nhdsWithin]
    rw [hfL]
    exact Filter.eventually_inf_principal.mpr
      (Filter.Eventually.of_forall fun t htneg => by
        have ht0 : t < (0 : ℝ) := htneg
        simp [abs_of_neg ht0, inv_mul_cancel₀ (ne_of_lt ht0)])
  have hd1 : (fderiv ℝ (fun t : ℝ => |t|) (0 : ℝ)) 1 = 1 :=
    tendsto_nhds_unique (Filter.Tendsto.congr' hevR habs.tendsto_slope_zero_right)
      tendsto_const_nhds
  have hd2 : (fderiv ℝ (fun t : ℝ => |t|) (0 : ℝ)) 1 = -1 :=
    tendsto_nhds_unique (Filter.Tendsto.congr' hevL habs.tendsto_slope_zero_left)
      tendsto_const_nhds
  rw [hd1] at hd2
  norm_num at hd2

/-! ### Refutation: the wrong-sign time cutoff -/

/-- The wrong-sign cutoff: the time variable enters with a **plus** sign, so the marked
region grows with time instead of trailing the forward cone. -/
noncomputable def chiWrong (x0 : M3) (R delta eps : ℝ) (t : ℝ) (x : M3) : ℝ :=
  Real.smoothTransition ((R + (t + psi_delta x0 delta x)) / eps)

/-- The wrong-sign cutoff is jointly smooth in `(t, x)` — its failure below is purely
semantic, not a regularity artifact. -/
private theorem contDiff_chiWrong (x0 : M3) (R delta eps : ℝ) (hdelta : delta ≠ 0) :
    ContDiff ℝ ∞ fun p : ℝ × M3 => chiWrong x0 R delta eps p.1 p.2 := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition :=
    contDiff_infty.2 fun m => Real.smoothTransition.contDiff (n := m)
  have hA : ContDiff ℝ ∞
      (fun p : ℝ × M3 => (R + (p.1 + psi_delta x0 delta p.2)) / eps) :=
    (contDiff_const.add
      ((contDiff_fst.add ((contDiff_psi_delta x0 hdelta).comp contDiff_snd)))).div_const eps
  exact hs.comp hA

/-- At the explicit regular point `(t, x) = (0, outPoint)` the wrong-sign cutoff
observes `1` although the point lies far outside the forward cone. -/
theorem probe_chiWrong_outside_one :
    chiWrong (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) 0 outPoint = 1 := by
  show Real.smoothTransition
      ((2 + (0 + psi_delta (0 : M3) (1 / 2 : ℝ) outPoint)) / (1 / 4 : ℝ)) = 1
  refine Real.smoothTransition.one_of_one_le ?_
  rw [one_le_div (show (0 : ℝ) < 1 / 4 by norm_num)]
  have hψ : (5 : ℝ) ≤ psi_delta (0 : M3) (1 / 2 : ℝ) outPoint := by
    have h := le_psi_delta (0 : M3) (1 / 2 : ℝ) outPoint
    rwa [sub_zero, norm_outPoint] at h
  linarith

/-- Final refutation observable: at one and the same differentiable explicit point, the
wrong-sign cutoff observes `1` while the correct cutoff observes `0`. -/
theorem probe_wrong_sign_cutoff_fails :
    DifferentiableAt ℝ
      (fun p : ℝ × M3 => chiWrong (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) p.1 p.2)
      (0, outPoint) ∧
      chiWrong (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) 0 outPoint = 1 ∧
      chi (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) 0 outPoint = 0 := by
  refine ⟨?_, probe_chiWrong_outside_one, probe_chi_outside_space⟩
  have h := contDiff_chiWrong (0 : M3) 2 (1 / 2 : ℝ) (1 / 4 : ℝ) (by norm_num)
  exact h.differentiable (by simp) |>.differentiableAt

end QFT.KleinGordonCutoffProbe
