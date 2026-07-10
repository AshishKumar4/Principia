import Atlas.Specs.OperatorTheory.ProjectionValuedMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Non-vacuity witnesses for projection-valued measures (P2.3d)

Concrete models of the frozen spec `Atlas/Specs/OperatorTheory/ProjectionValuedMeasure.lean`.
Per CLAUDE.md, no spec is consumed downstream until a nontrivial model instantiates it
together with expected-true and expected-false `example`s; this file is that witness for
the `ProjectionValuedMeasure` structure and the `IsSpectralIntegral` /
`IsBoundedIntegral` relations.

## The two-point coordinate PVM (`BoolPVM`)

On `α = Bool` with the `⊤` σ-algebra (every set measurable, so the junk field is
vacuous) and `H = EuclideanSpace ℂ Bool`, the map `s ↦` orthogonal projection onto the
coordinate lines in `s`. This is the finite-dimensional multiplication PVM promised in
the spec's witness plan.

* **Expected-true — the structure is inhabited by a genuine model** (`pvm`): all seven
  fields compute, including weak σ-additivity `m_iUnion'` (every measurable
  pairwise-disjoint family in a finite σ-algebra is, below any point, supported on a
  single index).
* **Expected-true — `diagMeasure` computes** (`diagMeasure_singleton` and the concrete
  `example`s): the diagonal spectral measure at `x` is `{b} ↦ ‖x b‖ₑ²`, i.e. the
  density measure `|x|²` of the finite counting model.
* **Expected-true — the spectral-integral relation holds** (`isSpectralIntegral_diag`,
  `isBoundedIntegral_diag`): for *every* `f : Bool → ℂ` the honest diagonal
  (multiplication) operator satisfies `IsSpectralIntegral pvm f` on its full natural
  domain, and its bounded form satisfies `IsBoundedIntegral pvm f`.
* **Expected-false — the relation is not slack** (`not_isSpectralIntegral_perturbed`,
  `not_isSpectralIntegral_restricted`): a value-perturbed impostor with the *same*
  pointwise norms (hence passing the domain and graph-norm clauses, exhibited by the
  intermediate `example`s) is refuted by `inner_apply`; and the correct operator
  restricted to the trivial domain `⊥` is refuted by `mem_domain_iff`. So both the value
  clause and the domain clause of the frozen relation are load-bearing.

## The junk-value PVM (`JunkPVM`)

On a two-point type carrying the trivial σ-algebra `⊥` (where singletons are *not*
measurable) the structure's `not_measurable'` field forces `P {pt} = 0`. This exercises
the junk-value honesty of the frozen layout (`measureOf'` total on `Set α`, junk `0` off
the σ-algebra, following `MeasureTheory.VectorMeasure`) on a σ-algebra where junk sets
actually exist — impossible on `Bool` with `⊤`.

## Sources

* W. Rudin, *Functional Analysis*, 2nd ed. (1991): Def 12.17 (resolution of the
  identity), Thm 12.21 (bounded `Ψ(f)`), Thm 13.24 (unbounded `Ψ(f)`, natural domain).
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I* (1980): §VII.3, §VIII.3,
  Thm VIII.6 (spectral theorem in PVM form).
-/

open MeasureTheory OperatorTheory
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace OperatorTheory.Witnesses.BoolPVM

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The two-point Hilbert space `ℂ²`, as `EuclideanSpace ℂ Bool`. -/
abbrev H2 : Type := EuclideanSpace ℂ Bool

/-- Coordinate projection onto the coordinate lines in `s`, as a linear map:
`x ↦ (b ↦ if b ∈ s then x b else 0)`. -/
def projLM (s : Set Bool) : H2 →ₗ[ℂ] H2 where
  toFun x := WithLp.toLp 2 (s.indicator fun b => x b)
  map_add' x y := by
    classical
    refine PiLp.ext fun b => ?_
    by_cases hb : b ∈ s <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hb]
  map_smul' c x := by
    classical
    refine PiLp.ext fun b => ?_
    by_cases hb : b ∈ s <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hb]

/-- Coordinate projection, as a bounded operator (continuity is automatic in finite
dimension). -/
def proj (s : Set Bool) : H2 →L[ℂ] H2 :=
  ⟨projLM s, (projLM s).continuous_of_finiteDimensional⟩

@[simp] lemma proj_apply (s : Set Bool) (x : H2) (b : Bool) :
    proj s x b = s.indicator (fun c => x c) b := rfl

/-- The inner product on `H2 = ℂ²` in coordinates. -/
lemma inner_eq (x y : H2) : ⟪x, y⟫ = ∑ b, conj (x b) * y b := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_bool]
  ring

/-- **The two-point coordinate projection-valued measure**: a genuine model of the frozen
`ProjectionValuedMeasure` structure on `Bool` with values on `H2 = ℂ²`. All seven fields
compute — in particular weak σ-additivity `m_iUnion'`, via the observation that a
measurable pairwise-disjoint family is, at each coordinate `b`, supported on the single
index whose set contains `b`. -/
def pvm : ProjectionValuedMeasure Bool H2 where
  measureOf' := proj
  isSelfAdjoint' s := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    classical
    simp only [ContinuousLinearMap.coe_coe]
    rw [inner_eq, inner_eq]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ∈ s <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hb]
  empty' := by
    refine ContinuousLinearMap.ext fun x => ?_
    refine PiLp.ext fun b => ?_
    simp
  univ' := by
    refine ContinuousLinearMap.ext fun x => ?_
    refine PiLp.ext fun b => ?_
    simp
  not_measurable' s hs := absurd (MeasurableSet.of_discrete) hs
  inter' s t _ _ := by
    refine ContinuousLinearMap.ext fun x => ?_
    refine PiLp.ext fun b => ?_
    classical
    by_cases hbs : b ∈ s <;> by_cases hbt : b ∈ t <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, hbs, hbt]
  m_iUnion' x y w hw hd := by
    classical
    have key : ∀ b : Bool,
        HasSum (fun i => conj (x b) * (w i).indicator (fun c => y c) b)
          (conj (x b) * (⋃ i, w i).indicator (fun c => y c) b) := by
      intro b
      by_cases hb : b ∈ ⋃ i, w i
      · obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp hb
        have hfun : (fun i => conj (x b) * (w i).indicator (fun c => y c) b)
            = fun i => if i = i₀ then conj (x b) * y b else 0 := by
          funext i
          rcases eq_or_ne i i₀ with rfl | hi
          · simp [Set.indicator_of_mem hi₀]
          · have hbi : b ∉ w i := fun hbi => Set.disjoint_left.mp (hd hi) hbi hi₀
            simp [Set.indicator_of_notMem hbi, hi]
        rw [hfun, Set.indicator_of_mem hb]
        exact hasSum_ite_eq i₀ _
      · have hbi : ∀ i, b ∉ w i := fun i hbi => hb (Set.mem_iUnion.mpr ⟨i, hbi⟩)
        simp only [Set.indicator_of_notMem hb, Set.indicator_of_notMem (hbi _), mul_zero]
        exact hasSum_zero
    have hsum := hasSum_sum (s := (Finset.univ : Finset Bool))
      (f := fun b i => conj (x b) * (w i).indicator (fun c => y c) b)
      (a := fun b => conj (x b) * (⋃ i, w i).indicator (fun c => y c) b)
      (fun b _ => key b)
    convert hsum using 1
    · funext i
      rw [inner_eq]
      simp only [proj_apply]
    · rw [inner_eq]
      simp only [proj_apply]

@[simp] lemma pvm_apply (s : Set Bool) : pvm s = proj s := rfl

/-- The diagonal spectral measure of the coordinate PVM on a singleton computes as the
squared coordinate norm: `μ_x {b} = ‖x b‖ₑ²` (Rudin, §12.17: `E_{x,x}(ω) = ‖E(ω) x‖²`). -/
lemma diagMeasure_singleton (x : H2) (b : Bool) :
    pvm.diagMeasure x {b} = ‖x b‖ₑ ^ 2 := by
  rw [pvm.diagMeasure_apply x (MeasurableSet.singleton b)]
  have hnorm : ‖pvm {b} x‖ = ‖x b‖ := by
    classical
    rw [EuclideanSpace.norm_eq, Fintype.sum_bool]
    cases b <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem,
        Real.sqrt_sq (norm_nonneg _)]
  rw [← ofReal_norm, ← ofReal_norm, hnorm]

/-- The `lintegral` against the diagonal spectral measure is the finite counting sum
weighted by the squared coordinate norms. -/
lemma lintegral_diag (g : Bool → ℝ≥0∞) (x : H2) :
    ∫⁻ b, g b ∂(pvm.diagMeasure x)
      = g true * ‖x true‖ₑ ^ 2 + g false * ‖x false‖ₑ ^ 2 := by
  rw [lintegral_fintype, Fintype.sum_bool, diagMeasure_singleton, diagMeasure_singleton]

/-- Any bounded `g` is `L²` against the (finite) diagonal spectral measure — the natural
domain of `∫ f dP` contains everything when `f` is bounded. -/
lemma lintegral_diag_lt_top (g : Bool → ℝ≥0∞) (hg : ∀ b, g b ≠ ⊤) (x : H2) :
    ∫⁻ b, g b ∂(pvm.diagMeasure x) < ⊤ := by
  rw [lintegral_diag]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (hg true).lt_top (ENNReal.pow_lt_top enorm_lt_top),
     ENNReal.mul_lt_top (hg false).lt_top (ENNReal.pow_lt_top enorm_lt_top)⟩

/-- The Bochner integral of a `ℂ`-valued `g` against the diagonal spectral measure. -/
lemma integral_diag_c (g : Bool → ℂ) (x : H2) :
    ∫ b, g b ∂(pvm.diagMeasure x)
      = (‖x true‖ ^ 2 : ℂ) * g true + (‖x false‖ ^ 2 : ℂ) * g false := by
  rw [integral_fintype .of_finite, Fintype.sum_bool]
  simp only [measureReal_def, diagMeasure_singleton, ENNReal.toReal_pow, toReal_enorm,
    Complex.real_smul]
  push_cast
  ring

/-- The Bochner integral of an `ℝ`-valued `g` against the diagonal spectral measure. -/
lemma integral_diag_r (g : Bool → ℝ) (x : H2) :
    ∫ b, g b ∂(pvm.diagMeasure x)
      = ‖x true‖ ^ 2 * g true + ‖x false‖ ^ 2 * g false := by
  rw [integral_fintype .of_finite, Fintype.sum_bool]
  simp only [measureReal_def, diagMeasure_singleton, ENNReal.toReal_pow, toReal_enorm,
    smul_eq_mul]

/-- The honest diagonal (multiplication) operator `x ↦ (b ↦ f b * x b)` for
`f : Bool → ℂ`, as a linear map. -/
def diagLM (f : Bool → ℂ) : H2 →ₗ[ℂ] H2 where
  toFun x := WithLp.toLp 2 fun b => f b * x b
  map_add' x y := by
    refine PiLp.ext fun b => ?_
    simp [mul_add]
  map_smul' c x := by
    refine PiLp.ext fun b => ?_
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] lemma diagLM_apply (f : Bool → ℂ) (x : H2) (b : Bool) :
    diagLM f x b = f b * x b := rfl

/-- **Expected-true (unbounded form)**: the frozen relation `IsSpectralIntegral` holds for
the genuine diagonal operator on its full natural domain `⊤`, for *every* `f : Bool → ℂ`.
All three clauses — natural domain, diagonal values, graph norm — compute. -/
theorem isSpectralIntegral_diag (f : Bool → ℂ) :
    pvm.IsSpectralIntegral f ((diagLM f).toPMap ⊤) where
  mem_domain_iff x := by
    rw [LinearMap.toPMap_domain]
    exact iff_of_true Submodule.mem_top
      (lintegral_diag_lt_top _ (fun b => by simp [enorm_ne_top]) x)
  inner_apply x := by
    rw [LinearMap.toPMap_apply, inner_eq, integral_diag_c, Fintype.sum_bool]
    simp only [diagLM_apply]
    have h1 := RCLike.conj_mul ((x : H2) true)
    have h2 := RCLike.conj_mul ((x : H2) false)
    push_cast at h1 h2 ⊢
    linear_combination f true * h1 + f false * h2
  norm_sq_apply x := by
    rw [LinearMap.toPMap_apply, integral_diag_r]
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_bool]
    simp only [diagLM_apply, norm_mul]
    ring

/-- The bounded (everywhere-defined, continuous) form of the diagonal operator. -/
def diagCLM (f : Bool → ℂ) : H2 →L[ℂ] H2 :=
  ⟨diagLM f, (diagLM f).continuous_of_finiteDimensional⟩

@[simp] lemma diagCLM_apply (f : Bool → ℂ) (x : H2) (b : Bool) :
    diagCLM f x b = f b * x b := rfl

/-- **Expected-true (bounded form)**: `IsBoundedIntegral` holds for the bounded diagonal
operator, for every `f : Bool → ℂ` (Rudin, Thm 12.21). -/
theorem isBoundedIntegral_diag (f : Bool → ℂ) :
    pvm.IsBoundedIntegral f (diagCLM f) := by
  intro x
  rw [inner_eq, integral_diag_c, Fintype.sum_bool]
  simp only [diagCLM_apply]
  have h1 := RCLike.conj_mul (x true)
  have h2 := RCLike.conj_mul (x false)
  push_cast at h1 h2 ⊢
  linear_combination f true * h1 + f false * h2

/-! ### Expected-false examples

The two refutations below pin, respectively, the `inner_apply` (value) clause and the
`mem_domain_iff` (domain) clause of the frozen relation. The intermediate examples show
that the value-perturbed impostor still passes the domain and graph-norm clauses, so the
value clause is genuinely load-bearing rather than redundant. -/

/-- Reference diagonal symbol `f₀ = (1, 2)`. -/
def f₀ : Bool → ℂ := fun b => if b then 1 else 2

/-- The sign-flipped impostor `g₀ = (1, -2)` — same pointwise norms as `f₀`. -/
def g₀ : Bool → ℂ := fun b => if b then 1 else -2

/-- The perturbation has the same pointwise norms as `f₀`. -/
example : ∀ b, ‖g₀ b‖ = ‖f₀ b‖ := by
  intro b; cases b <;> simp [f₀, g₀]

/-- The unit vector on the `false` coordinate line. -/
def x₀ : H2 := WithLp.toLp 2 fun b => if b then 0 else 1

@[simp] lemma x₀_true : x₀ true = 0 := rfl
@[simp] lemma x₀_false : x₀ false = 1 := rfl

/-- Concrete diagonal-measure values at `x₀`: mass `0` on `{true}`, mass `1` on
`{false}`. -/
example : pvm.diagMeasure x₀ {true} = 0 := by rw [diagMeasure_singleton]; simp
example : pvm.diagMeasure x₀ {false} = 1 := by rw [diagMeasure_singleton]; simp

/-- The perturbed operator still satisfies the DOMAIN clause of
`IsSpectralIntegral pvm f₀` (same norms ⇒ same natural domain). -/
example : ∀ x : H2,
    x ∈ ((diagLM g₀).toPMap ⊤).domain ↔
      ∫⁻ a, ‖f₀ a‖ₑ ^ 2 ∂(pvm.diagMeasure x) < ⊤ := by
  intro x
  have hcong : ∫⁻ a, ‖f₀ a‖ₑ ^ 2 ∂(pvm.diagMeasure x)
      = ∫⁻ a, ‖g₀ a‖ₑ ^ 2 ∂(pvm.diagMeasure x) :=
    lintegral_congr fun a => by cases a <;> simp [f₀, g₀]
  rw [hcong]
  exact (isSpectralIntegral_diag g₀).mem_domain_iff x

/-- The perturbed operator still satisfies the graph-NORM clause of
`IsSpectralIntegral pvm f₀`. -/
example : ∀ x : ((diagLM g₀).toPMap ⊤).domain,
    ‖((diagLM g₀).toPMap ⊤) x‖ ^ 2 = ∫ a, ‖f₀ a‖ ^ 2 ∂(pvm.diagMeasure (x : H2)) := by
  intro x
  rw [(isSpectralIntegral_diag g₀).norm_sq_apply x]
  congr 1
  funext b
  cases b <;> simp [f₀, g₀]

/-- **Expected-false 1**: the relation FAILS for the same-norm perturbed operator — the
`inner_apply` clause is what pins the operator values. -/
theorem not_isSpectralIntegral_perturbed :
    ¬ pvm.IsSpectralIntegral f₀ ((diagLM g₀).toPMap ⊤) := by
  intro h
  have hx : x₀ ∈ ((diagLM g₀).toPMap ⊤).domain := by
    rw [LinearMap.toPMap_domain]; exact Submodule.mem_top
  have h2 := h.inner_apply ⟨x₀, hx⟩
  rw [LinearMap.toPMap_apply, inner_eq, integral_diag_c, Fintype.sum_bool] at h2
  simp only [diagLM_apply, x₀_true, x₀_false] at h2
  norm_num [f₀, g₀] at h2

/-- **Expected-false 2**: the relation FAILS for the correct operator on the strictly
smaller trivial domain `⊥` — `mem_domain_iff` pins the domain to be exactly the natural
domain. -/
theorem not_isSpectralIntegral_restricted :
    ¬ pvm.IsSpectralIntegral f₀ ((diagLM f₀).toPMap ⊥) := by
  intro h
  have hfin : ∫⁻ a, ‖f₀ a‖ₑ ^ 2 ∂(pvm.diagMeasure x₀) < ⊤ :=
    lintegral_diag_lt_top _ (fun b => by simp [enorm_ne_top]) x₀
  have hx := (h.mem_domain_iff x₀).mpr hfin
  rw [LinearMap.toPMap_domain, Submodule.mem_bot] at hx
  have : (1 : ℂ) = 0 := by
    calc (1 : ℂ) = x₀ false := rfl
    _ = (0 : H2) false := by rw [hx]
    _ = 0 := rfl
  norm_num at this

/-- Sanity: the scalar spectral measure is the evident coordinate form, definitionally. -/
example (x y : H2) : pvm.scalarMeasure x y {true} = conj (x true) * y true := by
  rw [ProjectionValuedMeasure.scalarMeasure_apply, inner_eq, Fintype.sum_bool]
  classical
  simp

end OperatorTheory.Witnesses.BoolPVM

/-! ## The junk-value witness

A PVM on a two-point type carrying the *trivial* σ-algebra `⊥`, where singletons are not
measurable. This exercises the junk-value branch of the frozen structure
(`measureOf'` total on `Set α`, junk `0` off the σ-algebra, following
`MeasureTheory.VectorMeasure`) on a σ-algebra where non-measurable sets genuinely exist —
impossible on `Bool` with `⊤`, where every set is measurable. -/

namespace OperatorTheory.Witnesses.JunkPVM

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A two-point type carrying the trivial σ-algebra `⊥`. -/
inductive TwoPt : Type where
  | a : TwoPt
  | b : TwoPt
  deriving DecidableEq

instance : MeasurableSpace TwoPt := ⊥
instance : Nonempty TwoPt := ⟨TwoPt.a⟩

lemma a_ne_b : TwoPt.a ≠ TwoPt.b := by decide

/-- In the trivial σ-algebra only `∅` and `univ` are measurable, so the singleton `{a}`
is **not** measurable. -/
lemma not_measurableSet_singleton : ¬ MeasurableSet ({TwoPt.a} : Set TwoPt) := by
  rw [MeasurableSpace.measurableSet_bot_iff]
  rintro (h | h)
  · exact Set.singleton_ne_empty _ h
  · have : TwoPt.b ∈ ({TwoPt.a} : Set TwoPt) := h ▸ Set.mem_univ _
    exact a_ne_b (Set.mem_singleton_iff.mp this).symm

/-- **A junk-exercising projection-valued measure** on the trivially-measurable two-point
type, with values on `ℂ`: `s ↦ 1` if `s = univ`, else `0`. Since only `∅` and `univ` are
measurable, every value is honest (`0` or `1`) and every non-measurable set — every
singleton — receives the junk value `0`. -/
def junkPVM : ProjectionValuedMeasure TwoPt ℂ where
  measureOf' s := if s = Set.univ then 1 else 0
  isSelfAdjoint' s := by by_cases h : s = Set.univ <;> simp [h]
  empty' := by simp [Set.empty_ne_univ]
  univ' := by simp
  not_measurable' s hs := by
    rw [if_neg]
    rintro rfl
    exact hs MeasurableSet.univ
  inter' s t _ _ := by
    by_cases hs : s = Set.univ
    · subst hs
      by_cases ht : t = Set.univ
      · subst ht; simp
      · simp [Set.univ_inter, ht]
    · have hst : s ∩ t ≠ Set.univ := fun h =>
        hs (Set.univ_subset_iff.mp (h ▸ Set.inter_subset_left))
      simp [hst, hs]
  m_iUnion' x y w hw hd := by
    have hcl : ∀ i, w i = ∅ ∨ w i = Set.univ := fun i =>
      MeasurableSpace.measurableSet_bot_iff.mp (hw i)
    by_cases huniv : ∃ i₀, w i₀ = Set.univ
    · obtain ⟨i₀, hi₀⟩ := huniv
      have hother : ∀ i, i ≠ i₀ → w i = ∅ := by
        intro i hi
        rcases hcl i with h | h
        · exact h
        · have hdd : Disjoint (w i) (w i₀) := hd hi
          rw [h, hi₀] at hdd
          exact absurd (Set.disjoint_univ.mp hdd).symm Set.empty_ne_univ
      have hunion : (⋃ i, w i) = Set.univ :=
        Set.univ_subset_iff.mp (hi₀ ▸ Set.subset_iUnion w i₀)
      have hfun : (fun i => ⟪x, (if w i = Set.univ then (1 : ℂ →L[ℂ] ℂ) else 0) y⟫)
          = fun i => if i = i₀ then ⟪x, y⟫ else 0 := by
        funext i
        rcases eq_or_ne i i₀ with rfl | hi
        · simp [hi₀]
        · simp [hother i hi, Set.empty_ne_univ, hi]
      have htgt : ⟪x, (if (⋃ i, w i) = Set.univ then (1 : ℂ →L[ℂ] ℂ) else 0) y⟫
          = ⟪x, y⟫ := by rw [hunion]; simp
      rw [hfun, htgt]
      exact hasSum_ite_eq i₀ _
    · have hall : ∀ i, w i = ∅ := fun i =>
        (hcl i).resolve_right fun h => huniv ⟨i, h⟩
      have hunion : (⋃ i, w i) = ∅ := by simp only [hall, Set.iUnion_empty]
      have h0 : ∀ i, (if w i = Set.univ then (1 : ℂ →L[ℂ] ℂ) else 0) = 0 :=
        fun i => if_neg (by rw [hall i]; exact Set.empty_ne_univ)
      have hu0 : (if (⋃ i, w i) = Set.univ then (1 : ℂ →L[ℂ] ℂ) else 0) = 0 :=
        if_neg (by rw [hunion]; exact Set.empty_ne_univ)
      simp only [h0, hu0, zero_apply, inner_zero_right]
      exact hasSum_zero

/-- **Expected-true (junk-value honesty)**: the junk PVM sends the non-measurable
singleton `{a}` to `0`, via the frozen structure's `not_measurable` field. -/
example : junkPVM {TwoPt.a} = 0 :=
  junkPVM.not_measurable not_measurableSet_singleton

/-- The junk value `0` is still a star projection — the design note that makes the
algebraic fields (`isStarProjection`, `commute`) hold unconditionally. -/
example : IsStarProjection (junkPVM {TwoPt.a}) :=
  junkPVM.isStarProjection {TwoPt.a}

/-- The honest values are still present: the whole space maps to `1`. -/
example : junkPVM Set.univ = 1 := junkPVM.univ

end OperatorTheory.Witnesses.JunkPVM

end
