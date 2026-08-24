import Atlas

/-!
# P2.3d kernel probes — diagonal spectral values and junk-value separation

* **Node**: P2.3d (projection-valued measures),
  `Atlas/Specs/OperatorTheory/ProjectionValuedMeasure.lean`.
* **Original review**: 2026-07-10 (BLUEPRINT P2.3: "d PVM spec FROZEN 2026-07-10
  e4ef3d9, `VectorMeasure`-shaped weak σ-additivity; adequacy kernel-probed"). The
  probe file of that review lived in a session-temporary scratchpad and was lost; this
  file is the X.3 backfill (`audits/README.md`), re-created 2026-08-23.
* **What it refutes**:
  1. the *junk-value impostor* — a `ProjectionValuedMeasure` that would assign a
     nonzero projection to a non-measurable set. On a two-point type carrying the
     trivial σ-algebra `⊥` (where singletons are not measurable) **no** inhabitant of
     the frozen structure has `P {a} = 1` (`probe_no_pvm_assigns_one_to_junk`), so the
     `not_measurable'` field genuinely constrains rather than documenting an intention;
  2. the *value-slack impostor* — a diagonal operator with the same pointwise norms as
     the intended symbol (hence passing the domain and graph-norm clauses) fails
     `IsSpectralIntegral` at the `inner_apply` clause
     (`probe_not_isSpectralIntegral_perturbed`);
  3. the *domain-slack impostor* — the correct operator restricted to the trivial
     domain `⊥` fails the `mem_domain_iff` clause
     (`probe_not_isSpectralIntegral_restricted`).

## What is checked, and how independently

The *model* is the frozen two-point coordinate PVM of `Atlas/Witnesses/BoolPVM.lean`
(node P2.3d's witness); rebuilding its weak σ-additivity here would test nothing new.
Everything computed about it below is re-derived in this file from the frozen spec API
(`ProjectionValuedMeasure.diagMeasure_apply`, `diagMeasure_univ`, `not_measurable`,
the `IsSpectralIntegral` fields) plus the model's own definitional behaviour, pinned
locally by `probe_pvm_apply` (`rfl`). No *claim* of the witness file is imported — no
lemma statement of it is cited — and the probe's diagonal operators are defined here.

* `probe_diagMeasure_singleton` — the diagonal spectral values `μ_x {b} = ‖x b‖ₑ²`
  (Rudin, Def 12.17: `E_{x,x}(ω) = ‖E(ω) x‖²`);
* `probe_diagMeasure_add`, `probe_diagMeasure_univ` — those values add up to the total
  mass `‖x‖ₑ²`, so the diagonal measure is the density `|x|²` of the counting model;
* `probe_diag_x0_true`, `probe_diag_x0_false` — concrete masses `0` and `1` at the unit
  vector on the `false` coordinate line;
* `probe_isBoundedIntegral` — the expected-true side: the bounded diagonal operator
  satisfies the frozen bounded relation for *every* symbol, so the refutations below
  are not refutations of an unsatisfiable relation.

## Sources

* W. Rudin, *Functional Analysis*, 2nd ed. (1991), Def 12.17 (resolution of the
  identity), Thm 12.21 (the bounded `Ψ(f)`), Thm 13.24 (the unbounded `Ψ(f)` and its
  natural domain).
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*
  (1980), §VII.3, §VIII.3, Thm VIII.6 (spectral theorem in PVM form).

Theorem/section numbers are quoted from the source list of the frozen spec
`Atlas/Specs/OperatorTheory/ProjectionValuedMeasure.lean`; they were not re-checked
against the printed editions in this backfill.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.3d/` only; compiles via
`lake env lean audits/probes/P2.3d/bool_pvm_probe.lean`.
-/

open MeasureTheory OperatorTheory
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace P23dProbe

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The two-point Hilbert space `ℂ²`. -/
abbrev H2 : Type := EuclideanSpace ℂ Bool

/-- **The model under test**: the frozen two-point coordinate projection-valued measure
(node P2.3d's witness). Everything below is recomputed from the spec API and the
definitional pin `probe_pvm_apply`. -/
abbrev P : ProjectionValuedMeasure Bool H2 := OperatorTheory.Witnesses.BoolPVM.pvm

/-- Definitional pin of the model: `P s` is the coordinate projection onto the lines in
`s`. Everything the probe knows about `P` beyond the frozen structure comes from this
`rfl`. -/
theorem probe_pvm_apply (s : Set Bool) (x : H2) (b : Bool) :
    P s x b = s.indicator (fun c => x c) b := rfl

/-- The inner product of `ℂ²` in coordinates. -/
theorem probe_inner_eq (x y : H2) : ⟪x, y⟫ = ∑ b, conj (x b) * y b := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_bool]
  ring

/-! ## Diagonal spectral values -/

/-- The projection onto a coordinate line has the coordinate's norm. -/
theorem probe_norm_proj_singleton (x : H2) (b : Bool) : ‖P {b} x‖ = ‖x b‖ := by
  classical
  rw [EuclideanSpace.norm_eq, Fintype.sum_bool]
  simp only [probe_pvm_apply]
  cases b <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, Real.sqrt_sq (norm_nonneg _)]

/-- **The diagonal spectral values**: `μ_x {b} = ‖x b‖ₑ²` (Rudin, Def 12.17:
`E_{x,x}(ω) = ‖E(ω) x‖²`), computed from the frozen `diagMeasure_apply`. -/
theorem probe_diagMeasure_singleton (x : H2) (b : Bool) :
    P.diagMeasure x {b} = ‖x b‖ₑ ^ 2 := by
  rw [P.diagMeasure_apply x (MeasurableSet.singleton b), ← ofReal_norm, ← ofReal_norm,
    probe_norm_proj_singleton]

/-- Total mass: `μ_x univ = ‖x‖ₑ²`, from the frozen `diagMeasure_univ`. -/
theorem probe_diagMeasure_univ (x : H2) : P.diagMeasure x Set.univ = ‖x‖ₑ ^ 2 :=
  P.diagMeasure_univ x

/-- The two diagonal values exhaust the total mass: `μ_x {true} + μ_x {false} =
μ_x univ`. Additivity of the spectral measure, on the model. -/
theorem probe_diagMeasure_add (x : H2) :
    P.diagMeasure x {true} + P.diagMeasure x {false} = P.diagMeasure x Set.univ := by
  have hu : ({true} ∪ {false} : Set Bool) = Set.univ := by
    ext b; cases b <;> simp
  rw [← hu, measure_union (by simp) (MeasurableSet.singleton false)]

/-- The unit vector on the `false` coordinate line. -/
def x₀ : H2 := WithLp.toLp 2 fun b => if b then 0 else 1

@[simp] theorem probe_x₀_true : x₀ true = 0 := rfl
@[simp] theorem probe_x₀_false : x₀ false = 1 := rfl

/-- Concrete diagonal value: no mass on `{true}`. -/
theorem probe_diag_x0_true : P.diagMeasure x₀ {true} = 0 := by
  rw [probe_diagMeasure_singleton]; simp

/-- Concrete diagonal value: unit mass on `{false}`. -/
theorem probe_diag_x0_false : P.diagMeasure x₀ {false} = 1 := by
  rw [probe_diagMeasure_singleton]; simp

/-! ## Integrals against the diagonal measure -/

theorem probe_lintegral_diag (g : Bool → ℝ≥0∞) (x : H2) :
    ∫⁻ b, g b ∂(P.diagMeasure x)
      = g true * ‖x true‖ₑ ^ 2 + g false * ‖x false‖ₑ ^ 2 := by
  rw [lintegral_fintype, Fintype.sum_bool, probe_diagMeasure_singleton,
    probe_diagMeasure_singleton]

theorem probe_lintegral_diag_lt_top (g : Bool → ℝ≥0∞) (hg : ∀ b, g b ≠ ⊤) (x : H2) :
    ∫⁻ b, g b ∂(P.diagMeasure x) < ⊤ := by
  rw [probe_lintegral_diag]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (hg true).lt_top (ENNReal.pow_lt_top enorm_lt_top),
     ENNReal.mul_lt_top (hg false).lt_top (ENNReal.pow_lt_top enorm_lt_top)⟩

theorem probe_integral_diag (g : Bool → ℂ) (x : H2) :
    ∫ b, g b ∂(P.diagMeasure x)
      = (‖x true‖ ^ 2 : ℂ) * g true + (‖x false‖ ^ 2 : ℂ) * g false := by
  rw [integral_fintype .of_finite, Fintype.sum_bool]
  simp only [measureReal_def, probe_diagMeasure_singleton, ENNReal.toReal_pow,
    toReal_enorm, Complex.real_smul]
  push_cast
  ring

/-! ## The probe's diagonal operators -/

/-- The diagonal (multiplication) operator `x ↦ (b ↦ f b * x b)`, defined here. -/
def probeDiag (f : Bool → ℂ) : H2 →ₗ[ℂ] H2 where
  toFun x := WithLp.toLp 2 fun b => f b * x b
  map_add' x y := by
    refine PiLp.ext fun b => ?_
    simp [mul_add]
  map_smul' c x := by
    refine PiLp.ext fun b => ?_
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem probeDiag_apply (f : Bool → ℂ) (x : H2) (b : Bool) :
    probeDiag f x b = f b * x b := rfl

/-- Its bounded form (continuity is automatic in finite dimension). -/
def probeDiagCLM (f : Bool → ℂ) : H2 →L[ℂ] H2 :=
  ⟨probeDiag f, (probeDiag f).continuous_of_finiteDimensional⟩

@[simp] theorem probeDiagCLM_apply (f : Bool → ℂ) (x : H2) (b : Bool) :
    probeDiagCLM f x b = f b * x b := rfl

/-- **Expected-true**: the bounded diagonal operator satisfies the frozen bounded
spectral-integral relation, for every symbol (Rudin, Thm 12.21). The refutations below
are therefore refutations of impostors, not of an empty relation. -/
theorem probe_isBoundedIntegral (f : Bool → ℂ) :
    P.IsBoundedIntegral f (probeDiagCLM f) := by
  intro x
  rw [probe_inner_eq, probe_integral_diag, Fintype.sum_bool]
  simp only [probeDiagCLM_apply]
  have h1 := RCLike.conj_mul (x true)
  have h2 := RCLike.conj_mul (x false)
  push_cast at h1 h2 ⊢
  linear_combination f true * h1 + f false * h2

/-! ## The value- and domain-slack impostors, refuted -/

/-- Reference symbol `f₀ = (1, 2)`. -/
def f₀ : Bool → ℂ := fun b => if b then 1 else 2

/-- The sign-flipped impostor `g₀ = (1, -2)`: the *same pointwise norms* as `f₀`, so it
passes the domain and graph-norm clauses of `IsSpectralIntegral P f₀`. -/
def g₀ : Bool → ℂ := fun b => if b then 1 else -2

theorem probe_same_norms : ∀ b, ‖g₀ b‖ = ‖f₀ b‖ := by
  intro b; cases b <;> simp [f₀, g₀]

/-- The impostor passes the DOMAIN clause (same norms ⇒ same natural domain). -/
theorem probe_perturbed_domain_clause : ∀ x : H2,
    x ∈ ((probeDiag g₀).toPMap ⊤).domain ↔
      ∫⁻ a, ‖f₀ a‖ₑ ^ 2 ∂(P.diagMeasure x) < ⊤ := by
  intro x
  rw [LinearMap.toPMap_domain]
  refine iff_of_true Submodule.mem_top ?_
  exact probe_lintegral_diag_lt_top _ (fun b => by simp [enorm_ne_top]) x

/-- **Refutation 1 — the value clause has teeth**: the same-norm impostor fails
`IsSpectralIntegral P f₀` at `inner_apply`, where the two sides compute to `-2` and
`2` on the unit vector `x₀`. -/
theorem probe_not_isSpectralIntegral_perturbed :
    ¬ P.IsSpectralIntegral f₀ ((probeDiag g₀).toPMap ⊤) := by
  intro h
  have hx : x₀ ∈ ((probeDiag g₀).toPMap ⊤).domain := by
    rw [LinearMap.toPMap_domain]; exact Submodule.mem_top
  have h2 := h.inner_apply ⟨x₀, hx⟩
  rw [LinearMap.toPMap_apply, probe_inner_eq, probe_integral_diag, Fintype.sum_bool] at h2
  simp only [probeDiag_apply, probe_x₀_true, probe_x₀_false] at h2
  norm_num [f₀, g₀] at h2

/-- **Refutation 2 — the domain clause has teeth**: the *correct* operator restricted to
the trivial domain `⊥` fails `mem_domain_iff`, so the frozen relation pins the domain to
be exactly the natural domain (Rudin, Thm 13.24; Reed & Simon I, Thm VIII.6). -/
theorem probe_not_isSpectralIntegral_restricted :
    ¬ P.IsSpectralIntegral f₀ ((probeDiag f₀).toPMap ⊥) := by
  intro h
  have hfin : ∫⁻ a, ‖f₀ a‖ₑ ^ 2 ∂(P.diagMeasure x₀) < ⊤ :=
    probe_lintegral_diag_lt_top _ (fun b => by simp [enorm_ne_top]) x₀
  have hx := (h.mem_domain_iff x₀).mpr hfin
  rw [LinearMap.toPMap_domain, Submodule.mem_bot] at hx
  have hone : (1 : ℂ) = 0 := by
    calc (1 : ℂ) = x₀ false := rfl
    _ = (0 : H2) false := by rw [hx]
    _ = 0 := rfl
  norm_num at hone

/-! ## The junk-value impostor, refuted

On `Bool` with the `⊤` σ-algebra every set is measurable, so the model above has no
junk values at all. The junk-value convention can therefore only be probed on a
σ-algebra where non-measurable sets exist — the point of the separation below. -/

theorem probe_bool_all_measurable (s : Set Bool) : MeasurableSet s :=
  MeasurableSet.of_discrete

/-- A two-point type carrying the trivial σ-algebra `⊥`. -/
inductive TwoPt : Type where
  | a : TwoPt
  | b : TwoPt
  deriving DecidableEq

instance : MeasurableSpace TwoPt := ⊥
instance : Nonempty TwoPt := ⟨TwoPt.a⟩

theorem probe_a_ne_b : TwoPt.a ≠ TwoPt.b := by decide

/-- In the trivial σ-algebra only `∅` and `univ` are measurable, so `{a}` is **not**
measurable — a genuine junk set. -/
theorem probe_not_measurableSet_singleton :
    ¬ MeasurableSet ({TwoPt.a} : Set TwoPt) := by
  rw [MeasurableSpace.measurableSet_bot_iff]
  rintro (h | h)
  · exact Set.singleton_ne_empty _ h
  · have hb : TwoPt.b ∈ ({TwoPt.a} : Set TwoPt) := h ▸ Set.mem_univ _
    exact probe_a_ne_b (Set.mem_singleton_iff.mp hb).symm

theorem probe_zero_ne_one_clm : (0 : ℂ →L[ℂ] ℂ) ≠ 1 := by
  intro h
  have hval := congrArg (fun T : ℂ →L[ℂ] ℂ => T 1) h
  simp at hval

/-- **The junk-value impostor, refuted**: *no* inhabitant of the frozen
`ProjectionValuedMeasure` structure assigns the identity to the non-measurable
singleton `{a}` — the `not_measurable'` field forces the junk value `0`, and `0 ≠ 1`.
The frozen layout is thus honest in Mathlib's `VectorMeasure` sense rather than merely
documenting an intention. -/
theorem probe_no_pvm_assigns_one_to_junk :
    ¬ ∃ Q : ProjectionValuedMeasure TwoPt ℂ, Q {TwoPt.a} = 1 := by
  rintro ⟨Q, hQ⟩
  rw [Q.not_measurable probe_not_measurableSet_singleton] at hQ
  exact probe_zero_ne_one_clm hQ

end P23dProbe

end
