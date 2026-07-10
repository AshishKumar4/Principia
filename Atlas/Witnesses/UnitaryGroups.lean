import Atlas.Specs.OperatorTheory.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Non-vacuity witnesses for one-parameter unitary groups (P2.3g)

Concrete models of `OperatorTheory.OneParameterUnitaryGroup` with fully computed Stone
generators, instantiating the frozen spec `Atlas/Specs/OperatorTheory/UnitaryGroup.lean`:

* `trivialGroup H`: the constant group `U t = 1`, with generator the zero operator on
  the whole space (`trivialGroup_generator`).
* `expI`: the group `U t = exp(t·I)·1` on `ℂ`, the gold-standard witness pinning the
  sign convention of the generator. Its generator is the *identity* with domain `⊤`
  (`expI_generator`); a sign error anywhere in the spec would make it `-id`.

Expected-true examples record membership in the generator domain; expected-false
examples (`expI_generator_one`, and the `≠ -1` / `≠ -id` statements) exclude the
opposite (Weidmann) sign convention. See the spec module docstring on conventions.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I* (1980), §VIII.4,
  Thm VIII.7 (`exp(I · t • A)` and its generator `A`).
-/

open OperatorTheory Complex
open scoped Topology

noncomputable section

namespace OperatorTheory.Witnesses

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The trivial group `U t = 1` -/

/-- The constant one-parameter unitary group `U t = 1` on any complex Hilbert space. -/
def trivialGroup (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : OneParameterUnitaryGroup H where
  toFun _ := 1
  map_zero_eq_one' := rfl
  map_add_eq_mul' _ _ := (one_mul _).symm
  continuous_apply' x := by
    simp only [OneMemClass.coe_one, one_apply_eq_self]
    exact continuous_const

theorem trivialGroup_orbit (x : H) :
    (fun t : ℝ ↦ ((trivialGroup H) t : H →L[ℂ] H) x) = fun _ ↦ x := by
  funext t
  simp [trivialGroup, OneParameterUnitaryGroup.coe_mk]

theorem trivialGroup_hasDerivAt (x : H) :
    HasDerivAt (fun t : ℝ ↦ ((trivialGroup H) t : H →L[ℂ] H) x) 0 0 := by
  rw [trivialGroup_orbit]
  exact hasDerivAt_const 0 x

/-- Every vector lies in the domain of the trivial group's generator. -/
theorem mem_trivialGroup_generatorDomain (x : H) : x ∈ (trivialGroup H).generatorDomain :=
  ⟨0, trivialGroup_hasDerivAt x⟩

/-- The Stone generator of the trivial group `U t = 1` is the zero operator (domain the
whole space, value `0`). -/
theorem trivialGroup_generator : (trivialGroup H).generator = 0 := by
  apply LinearPMap.ext
  · rw [OneParameterUnitaryGroup.generator_domain, LinearPMap.zero_domain,
      Submodule.eq_top_iff']
    exact fun x ↦ mem_trivialGroup_generatorDomain x
  · intro x _ _
    have := (trivialGroup H).generator_apply_of_hasDerivAt (trivialGroup_hasDerivAt x)
    simpa using this

/-! ### The group `U t = exp(t·I)·1` on `ℂ` (sign-convention witness) -/

private theorem star_exp_smul (t : ℝ) :
    star (Complex.exp (t * I)) = Complex.exp (-(t * I)) := by
  rw [RCLike.star_def, ← Complex.exp_conj]
  simp

private theorem exp_mem_unitary (t : ℝ) :
    Complex.exp (t * I) • (1 : ℂ →L[ℂ] ℂ) ∈ unitary (ℂ →L[ℂ] ℂ) := by
  have hstar : star (Complex.exp (t * I) • (1 : ℂ →L[ℂ] ℂ))
      = Complex.exp (-(t * I)) • (1 : ℂ →L[ℂ] ℂ) := by
    rw [star_smul, star_one, star_exp_smul]
  rw [Unitary.mem_iff, hstar]
  refine ⟨?_, ?_⟩ <;>
  · ext
    simp [← Complex.exp_add]

/-- The one-parameter unitary group `U t = exp(t·I)·1` on `ℂ`. -/
def expI : OneParameterUnitaryGroup ℂ where
  toFun t := ⟨Complex.exp (t * I) • 1, exp_mem_unitary t⟩
  map_zero_eq_one' := by ext; simp
  map_add_eq_mul' s t := by
    ext
    push_cast
    simp [mul_add, Complex.exp_add, mul_comm]
  continuous_apply' x := by
    simp only [smul_apply, one_apply_eq_self, smul_eq_mul]
    fun_prop

theorem expI_orbit (x : ℂ) :
    (fun t : ℝ ↦ (expI t : ℂ →L[ℂ] ℂ) x) = fun t : ℝ ↦ Complex.exp (t * I) * x := by
  funext t
  simp [expI, OneParameterUnitaryGroup.coe_mk, smul_eq_mul]

/-- The orbit `t ↦ exp(t·I)·x` has derivative `I·x` at `0`: this is `(d/dt)|₀ = I • A x`
with `A = id`. -/
theorem expI_hasDerivAt (x : ℂ) :
    HasDerivAt (fun t : ℝ ↦ (expI t : ℂ →L[ℂ] ℂ) x) (I * x) 0 := by
  rw [expI_orbit]
  have hc : HasDerivAt (fun z : ℂ ↦ Complex.exp (z * I) * x)
      (Complex.exp ((((0 : ℝ) : ℂ)) * I) * (1 * I) * x) (((0 : ℝ) : ℂ)) :=
    (((Complex.hasDerivAt_exp ((((0 : ℝ) : ℂ)) * I)).comp (((0 : ℝ) : ℂ))
      ((hasDerivAt_id (((0 : ℝ) : ℂ))).mul_const I))).mul_const x
  simpa using hc.comp_ofReal

/-- Every vector lies in the domain of `expI`'s generator. -/
theorem mem_expI_generatorDomain (x : ℂ) : x ∈ expI.generatorDomain :=
  ⟨I * x, expI_hasDerivAt x⟩

/-- **Gold-standard sign check.** The Stone generator of `t ↦ exp(t·I)` on `ℂ` is the
identity operator with domain `⊤`. A sign error anywhere in the spec would make this
`-id` instead. -/
theorem expI_generator : expI.generator = (LinearMap.id : ℂ →ₗ[ℂ] ℂ).toPMap ⊤ := by
  apply LinearPMap.ext
  · rw [OneParameterUnitaryGroup.generator_domain, LinearMap.toPMap_domain,
      Submodule.eq_top_iff']
    exact fun x ↦ mem_expI_generatorDomain x
  · intro x _ _
    have h := expI.generator_apply_of_hasDerivAt (expI_hasDerivAt x)
    rw [LinearMap.toPMap_apply, LinearMap.id_apply]
    calc expI.generator ⟨x, _⟩ = -I • (I * x) := h
      _ = x := by rw [smul_eq_mul, neg_mul, ← mul_assoc, Complex.I_mul_I]; ring

/-- The generator value on `1` is `1` (expected-true), pinning the physicists' sign
convention. -/
theorem expI_generator_one :
    expI.generator ⟨1, mem_expI_generatorDomain 1⟩ = 1 := by
  have h := expI.generator_apply_of_hasDerivAt (expI_hasDerivAt 1)
  rw [h, smul_eq_mul]
  simp [Complex.I_mul_I]

/-- Sign-flip exclusion (expected-false): the generator value on `1` is `1`, not `-1`. -/
example : expI.generator ⟨1, mem_expI_generatorDomain 1⟩ ≠ -1 := by
  rw [expI_generator_one]; norm_num

/-- Operator-level sign-flip exclusion: the generator is not `-id`. -/
theorem expI_generator_ne_neg :
    expI.generator ≠ -(LinearMap.id : ℂ →ₗ[ℂ] ℂ).toPMap ⊤ := by
  intro h
  have hmem : (1 : ℂ) ∈ (-(LinearMap.id : ℂ →ₗ[ℂ] ℂ).toPMap ⊤).domain := by
    rw [LinearPMap.neg_domain, LinearMap.toPMap_domain]; exact Submodule.mem_top
  have hval := (LinearPMap.ext_iff.mp h).2 (x := 1)
    (hf := mem_expI_generatorDomain 1) (hg := hmem)
  rw [expI_generator_one, LinearPMap.neg_apply, LinearMap.toPMap_apply, LinearMap.id_apply] at hval
  norm_num at hval

/-- The round-trip lemma delivers the derivative `I • A x` (spec sign convention). -/
example (x : ℂ) (hx : x ∈ expI.generatorDomain) :
    HasDerivAt (fun t : ℝ ↦ (expI t : ℂ →L[ℂ] ℂ) x)
      (Complex.I • expI.generator ⟨x, hx⟩) 0 :=
  expI.hasDerivAt_of_mem_generatorDomain hx

end OperatorTheory.Witnesses
