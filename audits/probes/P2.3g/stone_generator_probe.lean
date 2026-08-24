import Atlas

/-!
# P2.3g kernel probes — the Stone generator, computed two ways

* **Node**: P2.3g (one-parameter unitary groups and the Stone generator),
  `Atlas/Specs/OperatorTheory/UnitaryGroup.lean`.
* **Original review**: 2026-07-09 (BLUEPRINT P2.3: "g `done` — spec frozen + witnesses
  + bounded-generator thm, 2026-07-09"). The probe file of that review lived in a
  session-temporary scratchpad and was lost; this file is the X.3 backfill
  (`audits/README.md`), re-created 2026-08-23.
* **What it refutes**: the *opposite (Weidmann) sign convention* and the *skew-adjoint
  reading* of the generator. On the group `U t = exp(t·i)` the frozen generator is
  `+id`, so it is not `-id` (`probe_expI_generator_ne_neg`), its value at `1` is not
  `-1` (`probe_expI_generator_one_ne_neg_one`), and it is not the derivative
  `i • id` itself (`probe_expI_generator_ne_skew`) — Weidmann, §7.6, calls that
  skew-adjoint derivative the "infinitesimal generator", and the frozen spec does not.

## The two routes, and why the agreement is the probe

For each model the generator value is computed along two independent routes through
the frozen spec, and the results are asserted to agree in one statement
(`probe_trivial_generator_two_ways`, `probe_expI_generator_two_ways`):

1. **the value rule** — `generator_apply_of_hasDerivAt`: from the orbit derivative `d`
   at `0`, the generator is `-i • d`;
2. **the round-trip lemma plus uniqueness of the derivative** —
   `hasDerivAt_of_mem_generatorDomain` says the orbit derivative *is* `i • A x`;
   `HasDerivAt.unique` against the computed derivative gives `i • A x = d`, and
   cancelling `i` gives `A x`.

Route 1 reads the `deriv`-spelled definition; route 2 reads the round-trip lemma. A
sign error in either one alone would make the two disagree, and the conjunction would
not compile. The models are built in this file, so nothing is inherited from
`Atlas/Witnesses/UnitaryGroups.lean`.

* `probeTrivial H` (`U t = 1`): both routes give `A = 0` on the whole space;
* `probeExpI` (`U t = exp(t·i) · 1` on `ℂ`): both routes give `A = id` with domain `⊤`
  — the gold-standard sign check, since `A = -id` is what the opposite convention would
  produce.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*
  (1980), §VIII.4, Thm VIII.7 (`exp(i t A)` is a strongly continuous one-parameter
  unitary group with generator `A`), Thm VIII.8 (Stone's theorem).
* M. H. Stone, "On one-parameter unitary groups in Hilbert space", *Ann. of Math.* 33
  (1932), 643–648.
* J. Weidmann, *Linear Operators in Hilbert Spaces*, GTM 68 (1980), §7.6, Thm 7.38
  (Stone's theorem with the opposite "infinitesimal generator" convention).

Theorem/section numbers are quoted from the source list of the frozen spec
`Atlas/Specs/OperatorTheory/UnitaryGroup.lean`; they were not re-checked against the
printed editions in this backfill.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.3g/` only; compiles via
`lake env lean audits/probes/P2.3g/stone_generator_probe.lean`.
-/

open OperatorTheory Complex
open scoped Topology

noncomputable section

namespace P23gProbe

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The trivial group `U t = 1` -/

/-- The constant one-parameter unitary group `U t = 1`, built here. -/
def probeTrivial (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : OneParameterUnitaryGroup H where
  toFun _ := 1
  map_zero_eq_one' := rfl
  map_add_eq_mul' _ _ := (one_mul _).symm
  continuous_apply' x := by
    simp only [OneMemClass.coe_one, one_apply_eq_self]
    exact continuous_const

theorem probe_trivial_orbit (x : H) :
    (fun t : ℝ ↦ ((probeTrivial H) t : H →L[ℂ] H) x) = fun _ ↦ x := by
  funext t
  simp [probeTrivial, OneParameterUnitaryGroup.coe_mk]

/-- The orbit of the trivial group is constant, so its derivative at `0` is `0`. -/
theorem probe_trivial_hasDerivAt (x : H) :
    HasDerivAt (fun t : ℝ ↦ ((probeTrivial H) t : H →L[ℂ] H) x) 0 0 := by
  rw [probe_trivial_orbit]
  exact hasDerivAt_const 0 x

theorem probe_mem_trivial_domain (x : H) : x ∈ (probeTrivial H).generatorDomain :=
  ⟨0, probe_trivial_hasDerivAt x⟩

/-- **The trivial group's generator, computed two ways.** Route 1 is the frozen value
rule; route 2 is the frozen round-trip lemma against uniqueness of the derivative. Both
give `0`. -/
theorem probe_trivial_generator_two_ways (x : H) :
    (probeTrivial H).generator ⟨x, probe_mem_trivial_domain x⟩ = -Complex.I • (0 : H)
      ∧ Complex.I • (probeTrivial H).generator ⟨x, probe_mem_trivial_domain x⟩ = 0
      ∧ (probeTrivial H).generator ⟨x, probe_mem_trivial_domain x⟩ = 0 := by
  have hroute1 : (probeTrivial H).generator ⟨x, probe_mem_trivial_domain x⟩
      = -Complex.I • (0 : H) :=
    (probeTrivial H).generator_apply_of_hasDerivAt (probe_trivial_hasDerivAt x)
  have hroute2 : Complex.I • (probeTrivial H).generator ⟨x, probe_mem_trivial_domain x⟩
      = 0 :=
    ((probeTrivial H).hasDerivAt_of_mem_generatorDomain
      (probe_mem_trivial_domain x)).unique (probe_trivial_hasDerivAt x)
  refine ⟨hroute1, hroute2, ?_⟩
  have h := congrArg (fun v : H ↦ (-Complex.I) • v) hroute2
  simpa [smul_smul, neg_mul, Complex.I_mul_I] using h

/-- The generator of the trivial group is the zero operator, on the whole space. -/
theorem probe_trivial_generator : (probeTrivial H).generator = 0 := by
  apply LinearPMap.ext
  · rw [OneParameterUnitaryGroup.generator_domain, LinearPMap.zero_domain,
      Submodule.eq_top_iff']
    exact fun x ↦ probe_mem_trivial_domain x
  · intro x _ _
    have h := (probe_trivial_generator_two_ways (x : H)).2.2
    simpa using h

/-! ## The group `U t = exp(t·i)` on `ℂ` -/

private theorem probe_star_exp (t : ℝ) :
    star (Complex.exp (t * I)) = Complex.exp (-(t * I)) := by
  rw [RCLike.star_def, ← Complex.exp_conj]
  simp

private theorem probe_exp_mem_unitary (t : ℝ) :
    Complex.exp (t * I) • (1 : ℂ →L[ℂ] ℂ) ∈ unitary (ℂ →L[ℂ] ℂ) := by
  have hstar : star (Complex.exp (t * I) • (1 : ℂ →L[ℂ] ℂ))
      = Complex.exp (-(t * I)) • (1 : ℂ →L[ℂ] ℂ) := by
    rw [star_smul, star_one, probe_star_exp]
  rw [Unitary.mem_iff, hstar]
  refine ⟨?_, ?_⟩ <;>
  · ext
    simp [← Complex.exp_add]

/-- The one-parameter unitary group `U t = exp(t·i) · 1` on `ℂ`, built here. -/
def probeExpI : OneParameterUnitaryGroup ℂ where
  toFun t := ⟨Complex.exp (t * I) • 1, probe_exp_mem_unitary t⟩
  map_zero_eq_one' := by ext; simp
  map_add_eq_mul' s t := by
    ext
    push_cast
    simp [mul_add, Complex.exp_add, mul_comm]
  continuous_apply' x := by
    simp only [smul_apply, one_apply_eq_self, smul_eq_mul]
    fun_prop

theorem probe_expI_orbit (x : ℂ) :
    (fun t : ℝ ↦ (probeExpI t : ℂ →L[ℂ] ℂ) x) = fun t : ℝ ↦ Complex.exp (t * I) * x := by
  funext t
  simp [probeExpI, OneParameterUnitaryGroup.coe_mk, smul_eq_mul]

/-- The orbit derivative at `0`: `(d/dt)|₀ exp(t·i) x = i · x`. -/
theorem probe_expI_hasDerivAt (x : ℂ) :
    HasDerivAt (fun t : ℝ ↦ (probeExpI t : ℂ →L[ℂ] ℂ) x) (I * x) 0 := by
  rw [probe_expI_orbit]
  have hc : HasDerivAt (fun z : ℂ ↦ Complex.exp (z * I) * x)
      (Complex.exp ((((0 : ℝ) : ℂ)) * I) * (1 * I) * x) (((0 : ℝ) : ℂ)) :=
    (((Complex.hasDerivAt_exp ((((0 : ℝ) : ℂ)) * I)).comp (((0 : ℝ) : ℂ))
      ((hasDerivAt_id (((0 : ℝ) : ℂ))).mul_const I))).mul_const x
  simpa using hc.comp_ofReal

theorem probe_mem_expI_domain (x : ℂ) : x ∈ probeExpI.generatorDomain :=
  ⟨I * x, probe_expI_hasDerivAt x⟩

/-- **The gold-standard sign check, computed two ways.** Route 1 (value rule) gives
`A x = -i • (i x)`; route 2 (round-trip lemma + uniqueness of the derivative) gives
`i • A x = i x`. Both deliver `A x = x`: the generator of `t ↦ exp(t·i)` is `+id`, not
`-id`. -/
theorem probe_expI_generator_two_ways (x : ℂ) :
    probeExpI.generator ⟨x, probe_mem_expI_domain x⟩ = -Complex.I • (Complex.I * x)
      ∧ Complex.I • probeExpI.generator ⟨x, probe_mem_expI_domain x⟩ = Complex.I * x
      ∧ probeExpI.generator ⟨x, probe_mem_expI_domain x⟩ = x := by
  have hroute1 : probeExpI.generator ⟨x, probe_mem_expI_domain x⟩
      = -Complex.I • (Complex.I * x) :=
    probeExpI.generator_apply_of_hasDerivAt (probe_expI_hasDerivAt x)
  have hroute2 : Complex.I • probeExpI.generator ⟨x, probe_mem_expI_domain x⟩
      = Complex.I * x :=
    (probeExpI.hasDerivAt_of_mem_generatorDomain
      (probe_mem_expI_domain x)).unique (probe_expI_hasDerivAt x)
  refine ⟨hroute1, hroute2, ?_⟩
  rw [smul_eq_mul] at hroute2
  exact mul_left_cancel₀ Complex.I_ne_zero hroute2

/-- The generator of `t ↦ exp(t·i)` on `ℂ` is the identity operator with domain `⊤`. -/
theorem probe_expI_generator :
    probeExpI.generator = (LinearMap.id : ℂ →ₗ[ℂ] ℂ).toPMap ⊤ := by
  apply LinearPMap.ext
  · rw [OneParameterUnitaryGroup.generator_domain, LinearMap.toPMap_domain,
      Submodule.eq_top_iff']
    exact fun x ↦ probe_mem_expI_domain x
  · intro x _ _
    rw [LinearMap.toPMap_apply, LinearMap.id_apply]
    exact (probe_expI_generator_two_ways (x : ℂ)).2.2

/-- The generator value at `1` is `1`. -/
theorem probe_expI_generator_one :
    probeExpI.generator ⟨1, probe_mem_expI_domain 1⟩ = 1 :=
  (probe_expI_generator_two_ways 1).2.2

/-! ## Refutations of the opposite conventions -/

/-- **The opposite sign convention, refuted pointwise**: the value is `1`, not `-1`. -/
theorem probe_expI_generator_one_ne_neg_one :
    probeExpI.generator ⟨1, probe_mem_expI_domain 1⟩ ≠ -1 := by
  rw [probe_expI_generator_one]
  norm_num

/-- **The skew-adjoint (Weidmann) reading, refuted**: the frozen generator is `A`, not
the derivative `i • A`; at `x = 1` the two differ (`1 ≠ i`). -/
theorem probe_expI_generator_ne_skew :
    probeExpI.generator ⟨1, probe_mem_expI_domain 1⟩ ≠ Complex.I := by
  rw [probe_expI_generator_one]
  intro h
  have him := congrArg Complex.im h
  norm_num at him

/-- **The opposite sign convention, refuted at the operator level**: the generator is
not `-id`. -/
theorem probe_expI_generator_ne_neg :
    probeExpI.generator ≠ -(LinearMap.id : ℂ →ₗ[ℂ] ℂ).toPMap ⊤ := by
  intro h
  have hmem : (1 : ℂ) ∈ (-(LinearMap.id : ℂ →ₗ[ℂ] ℂ).toPMap ⊤).domain := by
    rw [LinearPMap.neg_domain, LinearMap.toPMap_domain]; exact Submodule.mem_top
  have hval := (LinearPMap.ext_iff.mp h).2 (x := 1)
    (hf := probe_mem_expI_domain 1) (hg := hmem)
  rw [probe_expI_generator_one, LinearPMap.neg_apply, LinearMap.toPMap_apply,
    LinearMap.id_apply] at hval
  norm_num at hval

/-- The two models have different generators, so the trivial one is not the only model
of the frozen structure — the sign checks above are not vacuous. -/
theorem probe_generators_differ :
    probeExpI.generator ≠ (probeTrivial ℂ).generator := by
  intro h
  have hval := (LinearPMap.ext_iff.mp h).2 (x := 1)
    (hf := probe_mem_expI_domain 1) (hg := probe_mem_trivial_domain (1 : ℂ))
  rw [probe_expI_generator_one, (probe_trivial_generator_two_ways (1 : ℂ)).2.2] at hval
  norm_num at hval

end P23gProbe

end
