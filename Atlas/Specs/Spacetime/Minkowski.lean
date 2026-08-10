import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# P2.4a — Minkowski space: carrier, bilinear form, future cones, spacelike separation

Frozen spec (blueprint node P2.4a): proof sessions must not edit this file; changes
require a spec review and a `[spec-review]` commit (see CLAUDE.md).

## Contents

* `Spacetime.Minkowski.M4` — the spacetime carrier `ℝ⁴` with its Euclidean structure.
* `Spacetime.Minkowski.minkowskiForm` — the mostly-plus Minkowski bilinear form
  `η(v, w) = -v⁰w⁰ + v¹w¹ + v²w² + v³w³`, with its symmetry, separation and
  coordinate lemmas.
* `Spacetime.Minkowski.InFutureTimeCone` / `Spacetime.Minkowski.InFutureCausalCone` —
  the open future time cone and the (punctured) future causal cone in coordinates,
  with closure under addition (convexity), the Cauchy–Schwarz contrast bounds, and the
  characterizations in terms of `minkowskiForm`.
* `Spacetime.Minkowski.IsSpacelike` / `Spacetime.Minkowski.SpacelikeSeparated` —
  strict spacelikeness of a vector, and spacelike separation of two sets by pointwise
  differences; `isSpacelike_iff_not_inFutureCausalCone` is the cone trichotomy.
* `Spacetime.Minkowski.InFutureTimeCone.form_lt_zero` — a future timelike vector pairs
  strictly negatively with every future causal vector (the reversed Cauchy–Schwarz
  sign fact powering orthochronous closure in `Atlas.Specs.Spacetime.Poincare`).

## Provenance ([spec-review] extraction, 2026-08-07)

`M4` and the `minkowskiForm` block are moved verbatim (code; two docstring cross-references updated) from `Atlas/Witnesses/Minkowski.lean`
(P1.W1); the cone definitions and their convexity/contrast toolkit are moved verbatim (code; two docstring cross-references updated)
from `Atlas/Witnesses/MinkowskiCausal.lean` (P1.W2). This is the sanctioned layering fix
of the P2.4/P2.5/P2.6 design dossier (`docs/dossiers/P2-wightman-design.md`): Phase-2
specs (P2.4 Poincaré group, P2.5 Wightman axioms) are frozen statements *about* concrete
Minkowski space, so its carrier, form and cones are load-bearing spec surface, not
witness-only material. The witness files now import this spec; every statement they
retain is unchanged.

Deliberately NOT moved: the `PseudoRiemannianMetric` bundle (`minkowskiMetric`, its
Lorentzian-signature theorem, `minkowskiTimeOrientation`). It instantiates the P1.1
GR-layer spec — it is P1.1's non-vacuity witness — and no Phase-2 spec statement
mentions it. The kernel-checked anchor tying `IsSpacelike` to the frozen P1.2 causal
relations (`IsSpacelike (x - y) ↔ ¬x ⤳ y ∧ ¬y ⤳ x`) is proved in the witness layer as
`Spacetime.Minkowski.isSpacelike_sub_iff_not_causallyPrecedes`
(`Atlas/Witnesses/MinkowskiCausal.lean`), where the required curve machinery lives.

## Conventions

* Sign convention: mostly-plus `(-, +, +, +)`; coordinate `0` is time; the future time
  direction is `EuclideanSpace.single 0 1`. This matches the frozen P1.1 spec and the
  P1.W1/P1.W2 witnesses.
* `IsSpacelike v` is the *strict* condition `0 < η(v, v)`. Unlike the P1.1
  causal-character predicate `PseudoRiemannianMetric.Spacelike` (which follows O'Neill
  in counting the zero vector as spacelike), the zero vector is NOT `IsSpacelike`.
  This is forced by the causal anchor: `x ⤳ x` always holds, so
  `IsSpacelike (x - y) ↔ ¬x ⤳ y ∧ ¬y ⤳ x` requires `IsSpacelike 0` to be false. It is
  also the sense of "spacelike separated" in the Wightman axioms (Streater–Wightman,
  `(x - y)² < 0` in their mostly-minus convention, i.e. `η(x - y, x - y) > 0` here).
* The future causal cone `InFutureCausalCone` excludes the zero vector (`0 < v⁰`);
  chronology is the open cone `InFutureTimeCone`.

## Sources

* O'Neill, *Semi-Riemannian Geometry with Applications to Relativity* (1983), Ch. 3
  (Minkowski space as the model Lorentz vector space of index 1), Ch. 5, pp. 143–146
  (time cones; Lemma 5.30 for the underlying time-cone facts).
* Wald, *General Relativity* (1984), §1.3, §8.1.
* Streater & Wightman, *PCT, Spin and Statistics, and All That* (1964; Princeton
  Landmarks ed. 2000), Ch. 1 (Minkowski space, spacelike vectors, the cones `V±`).
-/

open RealInnerProductSpace

namespace Spacetime.Minkowski

/-- Four-dimensional spacetime carrier: `ℝ⁴` with its Euclidean structure, used as a
manifold over itself. Its tangent space at every point is definitionally `ℝ⁴`. -/
abbrev M4 : Type := EuclideanSpace ℝ (Fin 4)

variable {u v w : M4}

/-! ### The Minkowski bilinear form -/

/-- The Minkowski bilinear form `η(v, w) = ⟪v, w⟫ - 2 * (v 0) * (w 0)`, as a continuous
bilinear map. Subtracting twice the time-time product from the Euclidean inner product
flips the sign of the `0`-th (time) coordinate, giving the mostly-plus form
`-(v 0) * (w 0) + ∑_{i ≠ 0} (v i) * (w i)`. -/
noncomputable def minkowskiForm : M4 →L[ℝ] M4 →L[ℝ] ℝ :=
  innerSL ℝ - (2 : ℝ) • (EuclideanSpace.proj 0).smulRight (EuclideanSpace.proj 0)

theorem minkowskiForm_apply (v w : M4) :
    minkowskiForm v w = ⟪v, w⟫ - 2 * v 0 * w 0 := by
  have h : minkowskiForm v w
      = innerSL ℝ v w - 2 * (EuclideanSpace.proj 0 v * EuclideanSpace.proj 0 w) := rfl
  rw [h, innerSL_apply_apply]
  simp only [PiLp.proj_apply]
  ring

theorem minkowskiForm_symm (v w : M4) : minkowskiForm v w = minkowskiForm w v := by
  simp only [minkowskiForm_apply, real_inner_comm v w]; ring

/-- Left-separating: if `η(v, ·) = 0` then `v = 0`. Testing against the standard basis
vectors: `η(v, eᵢ) = v i` for `i ≠ 0` forces the spatial components, and
`η(v, e₀) = -v 0` forces the time component. -/
theorem minkowskiForm_separatingLeft (v : M4) (h : ∀ w, minkowskiForm v w = 0) : v = 0 := by
  have h0 : v 0 = 0 := by
    have hi := h (EuclideanSpace.single 0 1)
    simp only [minkowskiForm_apply, EuclideanSpace.inner_single_right, one_mul,
      conj_trivial, PiLp.single_apply, if_true, mul_one] at hi
    linarith
  ext i
  have hi := h (EuclideanSpace.single i 1)
  simp only [minkowskiForm_apply, EuclideanSpace.inner_single_right, one_mul,
    conj_trivial, h0, zero_mul, mul_zero, sub_zero] at hi
  simpa using hi

/-- The Minkowski form in standard coordinates:
`η(v, w) = -v⁰w⁰ + v¹w¹ + v²w² + v³w³`. The computational workhorse. -/
theorem minkowskiForm_eq (v w : M4) :
    minkowskiForm v w = -(v 0 * w 0) + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 := by
  rw [minkowskiForm_apply, PiLp.inner_apply, Fin.sum_univ_four]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- Pairing against the future time basis vector reads off (minus) the time
coordinate: `η(e₀, v) = -v⁰`. -/
theorem minkowskiForm_single_zero_left (v : M4) :
    minkowskiForm (EuclideanSpace.single 0 1) v = -(v 0) := by
  rw [minkowskiForm_eq]
  simp

/-! ### The future cones in coordinates -/

/-- The open future time cone of Minkowski space, in coordinates: `v` is timelike
(`(v¹)² + (v²)² + (v³)² < (v⁰)²`) and future-pointing (`v⁰ > 0`). Coordinate form of
O'Neill's time cone of `∂₀` (*Semi-Riemannian Geometry*, Ch. 5, pp. 143–146); see
`timelike_futureDirected_iff` in `Atlas/Witnesses/MinkowskiCausal.lean` for the
equivalence with the frozen P1.1 spec predicates. -/
def InFutureTimeCone (v : M4) : Prop :=
  v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 < v 0 ^ 2 ∧ 0 < v 0

/-- The future causal cone of Minkowski space (zero vector excluded), in coordinates:
`v` is causal (`(v¹)² + (v²)² + (v³)² ≤ (v⁰)²`) and future-pointing (`v⁰ > 0`). See
`futureDirected_iff` in `Atlas/Witnesses/MinkowskiCausal.lean` for the equivalence with
the frozen P1.1 spec predicate. -/
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

/-! ### The cones against the form -/

/-- The open future time cone is the future-pointing timelike vectors:
`η(v, v) < 0 ∧ 0 < v⁰`. -/
theorem inFutureTimeCone_iff_form (v : M4) :
    InFutureTimeCone v ↔ minkowskiForm v v < 0 ∧ 0 < v 0 := by
  unfold InFutureTimeCone
  rw [minkowskiForm_eq]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by nlinarith, h2⟩

/-- The future causal cone is the future-pointing causal vectors:
`η(v, v) ≤ 0 ∧ 0 < v⁰`. -/
theorem inFutureCausalCone_iff_form (v : M4) :
    InFutureCausalCone v ↔ minkowskiForm v v ≤ 0 ∧ 0 < v 0 := by
  unfold InFutureCausalCone
  rw [minkowskiForm_eq]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by nlinarith, h2⟩

/-- Reversed Cauchy–Schwarz sign fact: a future timelike vector pairs strictly
negatively with every future causal vector (O'Neill, *Semi-Riemannian Geometry*, Ch. 5,
Lemma 5.30: causal vectors in the same time cone have negative product). This is the
engine of orthochronous closure for the restricted Lorentz group
(`Atlas.Specs.Spacetime.Poincare`). -/
theorem InFutureTimeCone.form_lt_zero (hu : InFutureTimeCone u)
    (hw : InFutureCausalCone w) : minkowskiForm u w < 0 := by
  obtain ⟨hu1, hu0⟩ := hu
  obtain ⟨hw1, hw0⟩ := hw
  have hcs := cauchy_schwarz₃ (u 1) (u 2) (u 3) (w 1) (w 2) (w 3)
  have hsu : (0:ℝ) ≤ u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by positivity
  have hsw : (0:ℝ) ≤ w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := by positivity
  have hdot : u 1 * w 1 + u 2 * w 2 + u 3 * w 3 < u 0 * w 0 := by
    nlinarith [mul_pos hu0 hw0, mul_le_mul_of_nonneg_left hw1 hsu,
      mul_lt_mul_of_pos_right hu1 (pow_pos hw0 2)]
  rw [minkowskiForm_eq]
  linarith

/-! ### Spacelike vectors and spacelike-separated sets -/

/-- A vector is spacelike when the Minkowski form is *strictly* positive on it:
`0 < η(v, v)`. The zero vector is not `IsSpacelike` — a deliberate divergence from the
P1.1 causal-character predicate `PseudoRiemannianMetric.Spacelike` (O'Neill's
convention), forced by the causal anchor
`IsSpacelike (x - y) ↔ ¬x ⤳ y ∧ ¬y ⤳ x` (`Atlas/Witnesses/MinkowskiCausal.lean`),
since `x ⤳ x` always holds. This is the Wightman-axiom sense of spacelike
(Streater–Wightman, §1-1: `(x - y)² < 0` in their mostly-minus convention). -/
def IsSpacelike (v : M4) : Prop :=
  0 < minkowskiForm v v

/-- Spacelikeness in coordinates: `(v⁰)² < (v¹)² + (v²)² + (v³)²`. -/
theorem isSpacelike_iff (v : M4) :
    IsSpacelike v ↔ v 0 ^ 2 < v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by
  unfold IsSpacelike
  rw [minkowskiForm_eq]
  constructor <;> intro h <;> nlinarith

theorem IsSpacelike.neg (h : IsSpacelike v) : IsSpacelike (-v) := by
  unfold IsSpacelike at h ⊢
  simpa using h

/-- Cone trichotomy: a vector is spacelike exactly when it is nonzero and neither it
nor its negation lies in the future causal cone (O'Neill, *Semi-Riemannian Geometry*,
Ch. 5: every nonzero non-spacelike vector lies in one of the two time/causal cones). -/
theorem isSpacelike_iff_not_inFutureCausalCone (v : M4) :
    IsSpacelike v ↔ v ≠ 0 ∧ ¬ InFutureCausalCone v ∧ ¬ InFutureCausalCone (-v) := by
  rw [isSpacelike_iff]
  constructor
  · intro h
    refine ⟨fun hv => by simp [hv] at h, fun ⟨h1, _⟩ => by linarith, fun ⟨h1, _⟩ => ?_⟩
    simp only [PiLp.neg_apply, neg_sq] at h1
    linarith
  · rintro ⟨hne, hc, hcn⟩
    by_contra hlt
    push Not at hlt
    rcases lt_trichotomy (v 0) 0 with h0 | h0 | h0
    · refine hcn ⟨?_, ?_⟩ <;> simp only [PiLp.neg_apply, neg_sq]
      · exact hlt
      · linarith
    · refine hne ?_
      have hv0 : v 0 ^ 2 = 0 := by rw [h0]; ring
      have key : ∀ i : Fin 4, v i ^ 2 ≤ 0 → v i = 0 := fun i hi =>
        pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hi (sq_nonneg _))
      ext i
      fin_cases i
      · simpa using h0
      · simpa using key 1 (by nlinarith [sq_nonneg (v 2), sq_nonneg (v 3)])
      · simpa using key 2 (by nlinarith [sq_nonneg (v 1), sq_nonneg (v 3)])
      · simpa using key 3 (by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)])
    · exact hc ⟨hlt, h0⟩

/-- Two sets of spacetime points are spacelike separated when every pointwise
difference is spacelike. This is the support condition of the microcausality
(local commutativity) axiom (Streater–Wightman, Ch. 3, the Wightman axioms). -/
def SpacelikeSeparated (A B : Set M4) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, IsSpacelike (x - y)

theorem SpacelikeSeparated.symm {A B : Set M4} (h : SpacelikeSeparated A B) :
    SpacelikeSeparated B A := fun y hy x hx => by
  simpa [neg_sub] using (h x hx y hy).neg

end Spacetime.Minkowski
