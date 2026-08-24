import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Star.CHSH
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

/-!
# Local realism as a candidate theory, fenced by the CHSH and CH-Eberhard bounds

This is the candidate theory that the NIST loophole-free Bell test refutes. It is
stated the way this repository states physics: the physical assumptions are the
fields of a structure, so every theorem below quantifies over the models that
satisfy them and nothing is postulated.

## The assumptions, and where they live

* `SpinModel`: a hidden variable fixes a `±1` outcome for each of two settings at
  each party. Determinism and locality are both in the type: the outcome is a
  function of the party's own setting and the hidden variable alone.
* `DetectionModel`: the same for a detection experiment, where the outcome of a
  trial is a click or no click. No efficiency assumption appears, which is why the
  bound applies to an experiment with loss.
* `Distribution`: one finitely supported distribution over hidden variables,
  shared by all four settings pairs. Sharing it is measurement independence: the
  hidden variable is not correlated with the settings.

## What is proved, and what is imported

The `±1` bound is Mathlib's `CHSH_inequality_of_comm`, applied to `ℝ`, where a
hidden variable's response values commute because they are real numbers. It is
imported, never restated. What is proved here is the part Mathlib does not have:
the Clauser-Horne form used by an experiment with undetected trials,

`P(++|ab) - P(+0|ab') - P(0+|a'b) - P(++|a'b') ≤ 0`,

which is the inequality tested by `principia.evaluators.bell_ch`. Both bounds are
lifted from one hidden variable to an expectation over `Distribution`, which is
the form the measured frequencies estimate.

## Sources

* Clauser, Horne, Shimony, Holt, *Proposed experiment to test local hidden-variable
  theories*, Phys. Rev. Lett. 23, 880 (1969), for the `±1` inequality.
* Clauser and Horne, *Experimental consequences of objective local theories*,
  Phys. Rev. D 10, 526 (1974), and Eberhard, Phys. Rev. A 47, R747 (1993), for the
  detection form. The exact arrangement of the four terms is Eq. (S1) of the
  Supplemental Material of Shalm et al., Phys. Rev. Lett. 115, 250402 (2015).
* Fine, Phys. Rev. Lett. 48, 291 (1982), for the reduction of a local realistic
  distribution to a mixture of deterministic ones, which is why deterministic
  response functions lose no generality.

## Non-vacuity

`signFlip` and `alwaysClick` are local models that reach the two bounds exactly, so
neither bound can be tightened. `observedFunctional` is the CH-Eberhard functional
of the counts committed in `evidence/data/shalm-2015-xor3-pulses-4-8.json`, and
`observedFunctional_pos` says it is positive: no model of this file reproduces the
measured frequencies.
-/

namespace CandidateLab.Bell.LocalRealism

universe u

variable {Λ : Type u}

/-- Response functions of a local hidden-variable theory with `±1` outcomes.

`alice s l` is the outcome Alice records for setting `s` when the hidden variable is
`l`; it does not mention Bob's setting, which is locality, and it is a function, which
is outcome determinism. The squares are one, so the outcomes are `±1`. -/
structure SpinModel (Λ : Type u) where
  /-- Alice's outcome for her setting and the hidden variable. -/
  alice : Bool → Λ → ℝ
  /-- Bob's outcome for his setting and the hidden variable. -/
  bob : Bool → Λ → ℝ
  /-- Alice's outcomes are `±1`. -/
  alice_sq : ∀ (s : Bool) (l : Λ), alice s l ^ 2 = 1
  /-- Bob's outcomes are `±1`. -/
  bob_sq : ∀ (s : Bool) (l : Λ), bob s l ^ 2 = 1

/-- Response functions of a local hidden-variable theory for a detection experiment.

`alice s l = true` means Alice's detector fires. A trial with no click is an outcome
like any other, so nothing here assumes that detected trials are a fair sample. -/
structure DetectionModel (Λ : Type u) where
  /-- Whether Alice's detector fires, for her setting and the hidden variable. -/
  alice : Bool → Λ → Bool
  /-- Whether Bob's detector fires, for his setting and the hidden variable. -/
  bob : Bool → Λ → Bool

/-- A finitely supported distribution over hidden variables.

One distribution is shared by every settings pair, which is measurement
independence: the settings carry no information about the hidden variable. -/
structure Distribution (Λ : Type u) where
  /-- The hidden variables that occur. -/
  support : Finset Λ
  /-- The weight of each hidden variable. -/
  weight : Λ → ℝ
  /-- Weights are non-negative. -/
  weight_nonneg : ∀ l ∈ support, 0 ≤ weight l
  /-- Weights sum to one. -/
  weight_sum : ∑ l ∈ support, weight l = 1

/-- The average of `f` over the hidden variables. -/
def expectation (D : Distribution Λ) (f : Λ → ℝ) : ℝ :=
  ∑ l ∈ D.support, D.weight l * f l

/-- A bound that holds at every hidden variable holds in expectation. -/
theorem expectation_le_of_le (D : Distribution Λ) (f : Λ → ℝ) (c : ℝ)
    (h : ∀ l ∈ D.support, f l ≤ c) : expectation D f ≤ c := by
  calc expectation D f = ∑ l ∈ D.support, D.weight l * f l := rfl
    _ ≤ ∑ l ∈ D.support, D.weight l * c :=
        Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left (h l hl) (D.weight_nonneg l hl)
    _ = c := by rw [← Finset.sum_mul, D.weight_sum, one_mul]

/-- The CHSH combination `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` at one hidden variable. -/
def chsh (M : SpinModel Λ) (l : Λ) : ℝ :=
  M.alice false l * M.bob false l + M.alice false l * M.bob true l
    + M.alice true l * M.bob false l - M.alice true l * M.bob true l

/-- The CHSH bound at one hidden variable.

This is Mathlib's `CHSH_inequality_of_comm` for the commutative `*`-algebra `ℝ`: a
hidden variable's four response values are real numbers, so they commute, and being
`±1` they are self-adjoint involutions. -/
theorem chsh_le_two (M : SpinModel Λ) (l : Λ) : chsh M l ≤ 2 := by
  have tuple : IsCHSHTuple (M.alice false l) (M.alice true l) (M.bob false l) (M.bob true l) :=
    { A₀_inv := M.alice_sq false l
      A₁_inv := M.alice_sq true l
      B₀_inv := M.bob_sq false l
      B₁_inv := M.bob_sq true l
      A₀_sa := star_trivial _
      A₁_sa := star_trivial _
      B₀_sa := star_trivial _
      B₁_sa := star_trivial _
      A₀B₀_commutes := mul_comm _ _
      A₀B₁_commutes := mul_comm _ _
      A₁B₀_commutes := mul_comm _ _
      A₁B₁_commutes := mul_comm _ _ }
  simpa [chsh] using
    CHSH_inequality_of_comm (M.alice false l) (M.alice true l) (M.bob false l) (M.bob true l) tuple

/-- The CHSH bound on the measurable average. -/
theorem chsh_expectation_le_two (M : SpinModel Λ) (D : Distribution Λ) :
    expectation D (chsh M) ≤ 2 :=
  expectation_le_of_le D _ 2 fun l _ => chsh_le_two M l

/-- `1` for a click, `0` for no click. -/
def click (b : Bool) : ℝ := if b then 1 else 0

/-- The CH-Eberhard combination for four explicit detection responses.

The terms are, in the order of Eq. (S1) of the Supplemental Material of Shalm et al.
(2015): both fire at `ab`, only Alice fires at `ab'`, only Bob fires at `a'b`, both
fire at `a'b'`. -/
def chValue (a a' b b' : Bool) : ℝ :=
  click a * click b - click a * click (!b') - click (!a') * click b - click a' * click b'

/-- The CH-Eberhard bound for one hidden variable's responses.

Sixteen response patterns, each checked by arithmetic. This is the inequality
Mathlib does not carry: it constrains an experiment in which a party can fail to
record anything, so it needs no assumption about the undetected trials. -/
theorem chValue_nonpos (a a' b b' : Bool) : chValue a a' b b' ≤ 0 := by
  cases a <;> cases a' <;> cases b <;> cases b' <;> norm_num [chValue, click]

/-- The CH-Eberhard combination of a detection model at one hidden variable. -/
def chEberhard (M : DetectionModel Λ) (l : Λ) : ℝ :=
  chValue (M.alice false l) (M.alice true l) (M.bob false l) (M.bob true l)

/-- The CH-Eberhard bound at one hidden variable. -/
theorem chEberhard_nonpos (M : DetectionModel Λ) (l : Λ) : chEberhard M l ≤ 0 :=
  chValue_nonpos _ _ _ _

/-- The CH-Eberhard bound on the measurable average.

This is the null hypothesis of the Bell gate: the frequencies of the four outcomes
that make up the functional estimate this expectation, and no local model of this
file can push it above zero. -/
theorem chEberhard_expectation_nonpos (M : DetectionModel Λ) (D : Distribution Λ) :
    expectation D (chEberhard M) ≤ 0 :=
  expectation_le_of_le D _ 0 fun l _ => chEberhard_nonpos M l

/-! ## Non-vacuity witnesses -/

/-- A local model whose CHSH combination is exactly `2`: Alice always answers `+1`,
Bob answers `-1` for his second setting. -/
def signFlip : SpinModel Unit where
  alice := fun _ _ => 1
  bob := fun s _ => if s then -1 else 1
  alice_sq := by intro s l; norm_num
  bob_sq := by intro s l; cases s <;> norm_num

/-- The CHSH bound is attained, so `chsh_le_two` cannot be tightened. -/
theorem chsh_signFlip : chsh signFlip () = 2 := by
  norm_num [chsh, signFlip]

/-- The local strategy that fires both detectors on every trial. It is the strategy
that maximises the chance of an `++ab` trial among the relevant ones, which is why
Eq. (S3) of the Shalm et al. Supplemental Material uses it to bound the p-value. -/
def alwaysClick : DetectionModel Unit where
  alice := fun _ _ => true
  bob := fun _ _ => true

/-- The CH-Eberhard bound is attained, so `chEberhard_nonpos` cannot be tightened. -/
theorem chEberhard_alwaysClick : chEberhard alwaysClick () = 0 := by
  norm_num [chEberhard, chValue, click, alwaysClick]

/-- The one-point hidden-variable distribution, so `Distribution` is inhabited. -/
def pointDistribution : Distribution Unit where
  support := {()}
  weight := fun _ => 1
  weight_nonneg := by intro l _; norm_num
  weight_sum := by simp

/-- The CH-Eberhard functional of the committed counts.

Read off `evidence/data/shalm-2015-xor3-pulses-4-8.json`, itself Table S-II of the
Shalm et al. Supplemental Material: each term is a count divided by the number of
trials with that settings pair, in the order of Eq. (S1). -/
def observedFunctional : ℚ :=
  6378 / 44349054 - 2825 / 44343867 - 2818 / 44333232 - 106 / 44332198

/-- The measured functional is positive, while `chEberhard_expectation_nonpos` says
every local model of this file keeps it at zero or below. The two statements are
what the Bell gate weighs against each other. -/
theorem observedFunctional_pos : 0 < observedFunctional := by
  norm_num [observedFunctional]

/-- Expected-true: the point distribution averages the saturating strategy to the
bound itself. -/
example : expectation pointDistribution (chEberhard alwaysClick) = 0 := by
  simp [expectation, pointDistribution, chEberhard_alwaysClick]

/-- Expected-false: `2` is not a loose bound for the CHSH combination. -/
example : ¬chsh signFlip () ≤ 1 := by
  norm_num [chsh, signFlip]

/-- Expected-false: the measured functional is not what a local model produces. -/
example : ¬(observedFunctional ≤ 0) := by
  norm_num [observedFunctional]

end CandidateLab.Bell.LocalRealism
