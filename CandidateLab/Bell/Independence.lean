import CandidateLab.Bell.LocalRealism

/-!
# Independence witnesses for the CH-Eberhard bound

`CandidateLab/Bell/LocalRealism.lean` proves `chEberhard_expectation_nonpos`: the
CH-Eberhard functional of a local, deterministic, measurement-independent model is at
most zero. Two of the assumptions behind that bound are invisible in its statement,
because they are built into the types rather than written as hypotheses:

* **Locality.** `DetectionModel.alice` takes Alice's setting and the hidden variable.
  Bob's setting is not an argument.
* **Measurement independence.** `chEberhard_expectation_nonpos` averages all four
  settings pairs against one `Distribution`.

This file proves that both are load-bearing. Each assumption is dropped in turn, in the
smallest way that leaves every other assumption standing, and a concrete model is
exhibited whose functional is positive. The models are finite and the arithmetic is
`norm_num`, so each violation is kernel-checked rather than argued.

Dropping either assumption alone takes the functional from the local bound `0` to `1`,
and `signalingCH_le_one` and `correlatedCH_le_one` show that `1` is the algebraic
maximum. Neither assumption is a convenience of the proof. Each one carries the whole
bound by itself.

## First witnesses of the incompatibility engine

These are the first committed independence witnesses of the incompatibility engine. A
no-go theorem is worth only as much as the map of what it forbids, and that map is built
from countermodels: for each assumption, a kernel-checked model that keeps every other
assumption and breaks the conclusion. `signalingResponse` and `settingsCorrelated` are
the first two entries.

## Why the generalisations are faithful

A countermodel proves nothing if the functional changed along with the assumption. Two
lemmas pin that down:

* `signalingCH_ofLocal` — on a local model, `signalingCH` is `chEberhard`, by `rfl`.
* `correlatedCH_const` — given one distribution for all four settings pairs,
  `correlatedCH` is `expectation D (chEberhard M)`.

In both cases the functional is the same functional, and the assumption is the only
thing that changed.

## Sources

* J. S. Bell, *On the Einstein Podolsky Rosen paradox*, Physics 1, 195 (1964), for
  locality: a party's outcome does not depend on the distant setting. `SignalingModel`
  drops exactly this.
* A. Fine, *Hidden variables, joint probability, and the Bell inequalities*, Phys. Rev.
  Lett. 48, 291 (1982), for the reduction of a stochastic local model to a mixture of
  deterministic ones. This is why `DetectionModel` may be deterministic without loss,
  and hence why determinism is not among the assumptions tested here.
* L. K. Shalm et al., Phys. Rev. Lett. 115, 250402 (2015), Supplemental Material,
  Eq. (S1), for the four-term arrangement of the functional, reproduced term by term in
  `signalingCH` and `correlatedCH`.

The citations to Bell (1964) and to Fine (1982) are at article level. They name the
assumption and the reduction; no display number is claimed for either.
-/

namespace CandidateLab.Bell.Independence

open CandidateLab.Bell.LocalRealism

universe u

variable {Λ : Type u}

/-! ## Response arithmetic

Two facts about `click` that both bounds below need: a product of two clicks lies in
`[0, 1]`. -/

private theorem click_mul_click_le_one (b c : Bool) : click b * click c ≤ 1 := by
  cases b <;> cases c <;> norm_num [click]

private theorem click_mul_click_nonneg (b c : Bool) : 0 ≤ click b * click c := by
  cases b <;> cases c <;> norm_num [click]

/-- Non-negativity of an average, the companion of `expectation_le_of_le`. -/
private theorem expectation_nonneg (D : Distribution Λ) (f : Λ → ℝ)
    (h : ∀ l ∈ D.support, 0 ≤ f l) : 0 ≤ expectation D f :=
  Finset.sum_nonneg fun l hl => mul_nonneg (D.weight_nonneg l hl) (h l hl)

/-! ## Dropping locality

Bell, Physics 1, 195 (1964): locality is the assumption that a party's outcome is a
function of that party's own setting. Removing it from Alice, and from nothing else,
gives `SignalingModel`. -/

/-- Response functions of a detection experiment with locality dropped at Alice: her
detector reads Bob's setting as well as her own. Determinism is untouched, the outcomes
are still clicks, and Bob is still local. -/
structure SignalingModel (Λ : Type u) where
  /-- Whether Alice's detector fires, for her setting, Bob's setting, and the hidden
  variable. -/
  alice : Bool → Bool → Λ → Bool
  /-- Whether Bob's detector fires, for his setting and the hidden variable. -/
  bob : Bool → Λ → Bool

/-- The CH-Eberhard functional of a signaling family at one hidden variable.

The four terms are those of Eq. (S1) of the Shalm et al. (2015) Supplemental Material,
in the same order: both fire at `ab`, only Alice fires at `ab'`, only Bob fires at `a'b`,
both fire at `a'b'`. The one change from `chEberhard` is that Alice's response in each
term is read at the settings pair of that term. -/
def signalingCH (M : SignalingModel Λ) (l : Λ) : ℝ :=
  click (M.alice false false l) * click (M.bob false l)
    - click (M.alice false true l) * click (!M.bob true l)
    - click (!M.alice true false l) * click (M.bob false l)
    - click (M.alice true true l) * click (M.bob true l)

/-- A local model, read as a signaling family that ignores the distant setting. -/
def SignalingModel.ofLocal (M : DetectionModel Λ) : SignalingModel Λ where
  alice := fun s _ => M.alice s
  bob := M.bob

/-- **The generalisation is faithful**: on a local model `signalingCH` is `chEberhard`
term for term, by definitional unfolding. Dropping locality is the only difference
between the two functionals. -/
theorem signalingCH_ofLocal (M : DetectionModel Λ) (l : Λ) :
    signalingCH (SignalingModel.ofLocal M) l = chEberhard M l := rfl

/-- Signaling raises the bound to `1` and no higher: the first term is a product of two
clicks, so it is at most `1`, and the three subtracted terms are non-negative. -/
theorem signalingCH_le_one (M : SignalingModel Λ) (l : Λ) : signalingCH M l ≤ 1 := by
  have h₁ := click_mul_click_le_one (M.alice false false l) (M.bob false l)
  have h₂ := click_mul_click_nonneg (M.alice false true l) (!M.bob true l)
  have h₃ := click_mul_click_nonneg (!M.alice true false l) (M.bob false l)
  have h₄ := click_mul_click_nonneg (M.alice true true l) (M.bob true l)
  simp only [signalingCH]
  linarith

/-- The signaling countermodel: Alice's detector fires exactly when Bob's setting is his
first one, whatever her own setting and whatever the hidden variable, and Bob's detector
fires exactly at his first setting. Nothing else is given up: the responses are still
deterministic functions of the hidden variable, and Bob is still local. -/
def signalingResponse : SignalingModel Unit where
  alice := fun _ t _ => !t
  bob := fun s _ => !s

/-- The countermodel reaches `1`, the algebraic maximum of `signalingCH_le_one`: the
`ab` term fires, and each of the three subtracted terms is killed by the setting the
model reads. -/
theorem signalingCH_signalingResponse : signalingCH signalingResponse () = 1 := by
  norm_num [signalingCH, signalingResponse, click]

/-- **Locality is load-bearing.** A family that differs from a local model only in that
Alice reads Bob's setting pushes the CH-Eberhard functional to `1`, while
`chEberhard_nonpos` holds it at or below `0` for every local model. -/
theorem signalingResponse_breaks_bound : 0 < signalingCH signalingResponse () := by
  norm_num [signalingCH, signalingResponse, click]

/-! ## Dropping measurement independence

`chEberhard_expectation_nonpos` shares one `Distribution` across all four settings
pairs. Giving each pair its own distribution, and changing nothing else, gives
`correlatedCH`. Fine, Phys. Rev. Lett. 48, 291 (1982) is why determinism of the
responses costs nothing here: the model below stays local and deterministic. -/

/-- The CH-Eberhard functional of a local model when the hidden-variable distribution
depends on the settings pair. Each term of Eq. (S1) is averaged against the distribution
of its own settings pair. -/
def correlatedCH (M : DetectionModel Λ) (D : Bool → Bool → Distribution Λ) : ℝ :=
  expectation (D false false) (fun l => click (M.alice false l) * click (M.bob false l))
    - expectation (D false true) (fun l => click (M.alice false l) * click (!M.bob true l))
    - expectation (D true false) (fun l => click (!M.alice true l) * click (M.bob false l))
    - expectation (D true true) (fun l => click (M.alice true l) * click (M.bob true l))

/-- **The generalisation is faithful**: one distribution for all four settings pairs
recovers `expectation D (chEberhard M)` exactly, by linearity of the average. Dropping
measurement independence is the only difference between the two functionals. -/
theorem correlatedCH_const (M : DetectionModel Λ) (D : Distribution Λ) :
    correlatedCH M (fun _ _ => D) = expectation D (chEberhard M) := by
  simp only [correlatedCH, expectation, chEberhard, chValue, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Settings-correlated weights raise the bound to `1` and no higher: the `ab` average
is at most `1` and the three subtracted averages are non-negative. -/
theorem correlatedCH_le_one (M : DetectionModel Λ) (D : Bool → Bool → Distribution Λ) :
    correlatedCH M D ≤ 1 := by
  have h₁ := expectation_le_of_le (D false false)
    (fun l => click (M.alice false l) * click (M.bob false l)) 1
    fun l _ => click_mul_click_le_one _ _
  have h₂ := expectation_nonneg (D false true)
    (fun l => click (M.alice false l) * click (!M.bob true l))
    fun l _ => click_mul_click_nonneg _ _
  have h₃ := expectation_nonneg (D true false)
    (fun l => click (!M.alice true l) * click (M.bob false l))
    fun l _ => click_mul_click_nonneg _ _
  have h₄ := expectation_nonneg (D true true)
    (fun l => click (M.alice true l) * click (M.bob true l))
    fun l _ => click_mul_click_nonneg _ _
  simp only [correlatedCH]
  linarith

/-- The distribution concentrated on one hidden variable. -/
def pointMass (l : Λ) : Distribution Λ where
  support := {l}
  weight := fun _ => 1
  weight_nonneg := fun _ _ => zero_le_one
  weight_sum := by simp

/-- `pointMass` at the one-point type is `LocalRealism.pointDistribution`, so the two
definitions are one definition. -/
theorem pointMass_unit : pointMass () = pointDistribution := rfl

/-- A local, deterministic model on two hidden variables: at `false` both detectors fire
at both settings, at `true` neither fires. Under any single distribution it obeys the
bound, which `correlatedCH_const` makes explicit. -/
def bothOrNothing : DetectionModel Bool where
  alice := fun _ l => !l
  bob := fun _ l => !l

/-- The settings-correlated countermodel: measurement independence dropped and nothing
else. The settings pair `(a, b)` draws the hidden variable at which both detectors fire,
`(a', b')` draws the one at which neither does, so the weights depend on the settings.
Two distributions, both point masses. -/
def settingsCorrelated (s t : Bool) : Distribution Bool := pointMass (s && t)

/-- The countermodel reaches `1`, the algebraic maximum of `correlatedCH_le_one`: the
`ab` pair draws the clicking hidden variable, and the `a'b'` pair draws the silent
one. -/
theorem correlatedCH_settingsCorrelated :
    correlatedCH bothOrNothing settingsCorrelated = 1 := by
  norm_num [correlatedCH, settingsCorrelated, pointMass, bothOrNothing, expectation, click]

/-- **Measurement independence is load-bearing.** A local, deterministic model whose
hidden-variable weights depend on the settings pair pushes the CH-Eberhard functional to
`1`, while `chEberhard_expectation_nonpos` holds it at or below `0` as soon as the four
pairs share one distribution. -/
theorem settingsCorrelated_breaks_bound :
    0 < correlatedCH bothOrNothing settingsCorrelated := by
  norm_num [correlatedCH, settingsCorrelated, pointMass, bothOrNothing, expectation, click]

/-! ## Sanity examples -/

/-- Expected-true: a local family read as a signaling family still obeys the bound, so
`signalingResponse` breaks it by signaling and by nothing else. -/
example (M : DetectionModel Unit) : signalingCH (SignalingModel.ofLocal M) () ≤ 0 := by
  rw [signalingCH_ofLocal]
  exact chEberhard_nonpos M ()

/-- Expected-true: `bothOrNothing` obeys the bound under every single distribution, so
`settingsCorrelated` breaks it by the settings dependence and by nothing else. -/
example (D : Distribution Bool) : correlatedCH bothOrNothing (fun _ _ => D) ≤ 0 := by
  rw [correlatedCH_const]
  exact chEberhard_expectation_nonpos bothOrNothing D

/-- Expected-false: the signaling countermodel does not merely graze the bound. -/
example : ¬signalingCH signalingResponse () ≤ 0 := by
  norm_num [signalingCH, signalingResponse, click]

/-- Expected-false: nor does the settings-correlated one. -/
example : ¬correlatedCH bothOrNothing settingsCorrelated ≤ 0 := by
  norm_num [correlatedCH, settingsCorrelated, pointMass, bothOrNothing, expectation, click]

/-- Expected-false: `settingsCorrelated` is not a single distribution in disguise. -/
example : settingsCorrelated false false ≠ settingsCorrelated true true := by
  intro h
  have hs : ({false} : Finset Bool) = {true} := congrArg Distribution.support h
  simp at hs

end CandidateLab.Bell.Independence
