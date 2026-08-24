import Atlas.Witnesses.WightmanUtilities

/-!
# P2.5a adversarial kernel probes — the vanishing hypothesis really depends on the cone

`IsVanishingNearClosedForwardCone` says a tempered distribution vanishes on a
neighbourhood of `V̄₊`. Swapping `V̄₊` for the *open* forward cone gives a strictly
weaker requirement on the distribution, hence a strictly stronger axiom. These probes
show the two are genuinely different by exhibiting the discriminating object:
`δ₀`, the Dirac distribution at zero four-momentum.

* `δ₀` vanishes on the whole open forward cone, because the apex is not in it — so `δ₀`
  satisfies the open-cone version of the hypothesis.
* `δ₀` does NOT vanish near `V̄₊`. This is proved twice, independently: once through
  Mathlib's own `dsupport_delta`, and once from first principles by exhibiting a bump
  test function supported in any given neighbourhood of the apex and pairing it against
  `δ₀`.

Zero four-momentum is the vacuum. A spectrum condition written with the open cone would
demand that the smeared translations annihilate the vacuum sector too, which the free
field does not do. So the closed cone is not a stylistic choice.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.5a/` only.
-/

open Metric
open Spacetime.Minkowski
open scoped SchwartzMap Topology ContDiff

/-! ## The open forward cone is open, and misses the apex -/

theorem probe_openTimeCone_isOpen : IsOpen {v : M4 | InFutureTimeCone v} := by
  have hset : {v : M4 | InFutureTimeCone v} =
      {v : M4 | v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 < v 0 ^ 2} ∩ {v : M4 | 0 < v 0} :=
    Set.ext fun _ => Iff.rfl
  rw [hset]
  exact (isOpen_lt (by fun_prop) (by fun_prop)).inter
    (isOpen_lt continuous_const (by fun_prop))

theorem probe_apex_notMem_openTimeCone : (0 : M4) ∉ {v : M4 | InFutureTimeCone v} := by
  intro h
  simpa using h.2

/-! ## `δ₀` satisfies the OPEN-cone version of the hypothesis -/

theorem probe_delta_apex_vanishes_on_openTimeCone :
    Distribution.IsVanishingOn (TemperedDistribution.delta (0 : M4))
      {v : M4 | InFutureTimeCone v} := by
  intro φ hφ
  rw [TemperedDistribution.delta_apply]
  exact image_eq_zero_of_notMem_tsupport fun hmem =>
    probe_apex_notMem_openTimeCone (hφ hmem)

theorem probe_delta_apex_vanishes_near_openTimeCone :
    ∃ s ∈ 𝓝ˢ {v : M4 | InFutureTimeCone v},
      Distribution.IsVanishingOn (TemperedDistribution.delta (0 : M4)) s :=
  ⟨_, probe_openTimeCone_isOpen.mem_nhdsSet_self,
    probe_delta_apex_vanishes_on_openTimeCone⟩

/-! ## `δ₀` fails the CLOSED-cone version — route 1, via Mathlib's `dsupport` -/

theorem probe_delta_apex_not_vanishing_near_closedCone_dsupport :
    ¬ IsVanishingNearClosedForwardCone (TemperedDistribution.delta (0 : M4)) := by
  intro h
  have hd := h.disjoint_dsupport
  rw [Distribution.dsupport_delta] at hd
  exact Set.disjoint_singleton_right.1 hd zero_mem_closedForwardCone

/-! ## `δ₀` fails the CLOSED-cone version — route 2, from first principles

No appeal to `dsupport`: given any neighbourhood of `V̄₊` we build a bump test function
supported inside it and centred on the apex, and pair it against `δ₀`. -/

theorem probe_delta_apex_not_vanishing_near_closedCone_bump :
    ¬ IsVanishingNearClosedForwardCone (TemperedDistribution.delta (0 : M4)) := by
  rintro ⟨s, hs, hvan⟩
  obtain ⟨t, ht_open, hKt, hts⟩ := mem_nhdsSet_iff_exists.1 hs
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 ht_open 0 (hKt zero_mem_closedForwardCone)
  let b : ContDiffBump (0 : M4) := ⟨r / 3, r / 2, by linarith, by linarith⟩
  have hrOut : b.rOut = r / 2 := rfl
  have hcs : HasCompactSupport fun x : M4 => ((b x : ℝ) : ℂ) :=
    b.hasCompactSupport.comp_left (g := fun z : ℝ => (z : ℂ)) Complex.ofReal_zero
  have hsmooth : ContDiff ℝ ∞ fun x : M4 => ((b x : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hsupp : Function.support (fun x : M4 => ((b x : ℝ) : ℂ))
      = Function.support (b : M4 → ℝ) := by
    ext x; simp [Function.mem_support, Complex.ofReal_eq_zero]
  have htsupp : tsupport (fun x : M4 => ((b x : ℝ) : ℂ)) ⊆ s := by
    rw [tsupport, hsupp, b.support_eq, hrOut]
    refine (closure_ball_subset_closedBall.trans ?_).trans hts
    exact (closedBall_subset_ball (by linarith)).trans hball
  have hpair := hvan (hcs.toSchwartzMap hsmooth) htsupp
  rw [TemperedDistribution.delta_apply] at hpair
  have hone : b 0 = 1 := b.one_of_mem_closedBall (mem_closedBall_self b.rIn_pos.le)
  have hval : ((b 0 : ℝ) : ℂ) = 0 := hpair
  rw [hone] at hval
  norm_num at hval

/-! ## Therefore the two hypotheses are different predicates -/

theorem probe_open_and_closed_hypotheses_differ :
    (∃ s ∈ 𝓝ˢ {v : M4 | InFutureTimeCone v},
        Distribution.IsVanishingOn (TemperedDistribution.delta (0 : M4)) s) ∧
      ¬ IsVanishingNearClosedForwardCone (TemperedDistribution.delta (0 : M4)) :=
  ⟨probe_delta_apex_vanishes_near_openTimeCone,
    probe_delta_apex_not_vanishing_near_closedCone_bump⟩
