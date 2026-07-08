import Atlas.Specs.Spacetime.Metric
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Logic.Relation

/-!
# P1.2 — Causal curves, chronology and causality relations, achronal sets

Frozen spec (blueprint node P1.2): proof sessions must not edit this file; changes
require a spec review and a `[spec-review]` commit (see CLAUDE.md).

## Contents

* `FutureTimelikeOn`, `FutureCausalOn`: future-directed timelike/causal curve conditions
  on a parameter set, in the Mathlib curve idiom (total function `γ : ℝ → M`, conditions
  imposed on `s : Set ℝ`, values outside `s` junk — cf. `IsMIntegralCurveOn`,
  `Manifold.pathELength`).
* `ChronoStep`, `CausalStep`: reachability by a single such curve segment on `Icc a b`.
* `ChronologicallyPrecedes` (`p ≪[τ] q`) and `CausallyPrecedes` (`p ⤳[τ] q`), as the
  transitive (resp. reflexive-transitive) closures of single-segment reachability.
* Chronological/causal futures and pasts `I⁺/I⁻/J⁺/J⁻` of points and of sets.
* `IsAchronal`.

## Design notes

* The single-segment relations are closed off with `Relation.TransGen` /
  `Relation.ReflTransGen`. This is definitionally O'Neill's piecewise definition of the
  chronology and causality relations (O'Neill, *Semi-Riemannian Geometry*, Ch. 14,
  p. 402: `p ≪ q` iff there is a future-pointing piecewise-smooth timelike curve from
  `p` to `q`; `p ≤ q` iff `p = q` or there is such a causal curve): a chain of segments
  *is* a piecewise curve, each piece a segment, and transitivity is free instead of
  requiring curve concatenation and smooth gluing.
* `CausallyPrecedes` uses the *reflexive*-transitive closure: `p ⤳[τ] p` always holds,
  matching O'Neill's `p ≤ q` and `p ∈ J⁺(p)` (Wald, *General Relativity*, §8.1).
* Segments are required to be differentiable (`MDifferentiableAt`) with everywhere
  timelike (resp. causal) future-directed velocity; this is the "piecewise `C¹`" reading
  of the sources' piecewise-smooth curves, cf. Minguzzi, *Living Rev. Rel.* 22:3 (2019),
  §2 (causality theory is insensitive to the regularity class between piecewise `C¹`
  and smooth). `MDifferentiableAt` (not `MDifferentiableWithinAt`) makes the velocity
  the unrestricted `mfderiv`, at the price of requiring two-sided differentiability at
  the endpoints of a segment `Icc a b` — harmless, since every `C¹` curve on a closed
  interval extends to an open neighborhood, and O'Neill's curve segments are
  restrictions of smooth curves defined on open intervals.

## Sources

* O'Neill, *Semi-Riemannian Geometry with Applications to Relativity* (1983), Ch. 14,
  pp. 402–403 (chronology and causality relations, `I⁺`, `J⁺`).
* Wald, *General Relativity* (1984), §8.1 (pp. 190–191: `I⁺/I⁻/J⁺/J⁻`; p. 194:
  achronal sets).
* Minguzzi, "Lorentzian causality theory", *Living Rev. Rel.* 22:3 (2019).
-/

open Bundle Set
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {g : PseudoRiemannianMetric I n M}

/-- `FutureTimelikeOn τ γ s` means that on the parameter set `s`, the curve `γ : ℝ → M`
is differentiable with future-directed timelike velocity: `γ` is a future-directed
timelike curve on `s` (O'Neill, *Semi-Riemannian Geometry*, Ch. 14, p. 402; Wald,
*General Relativity*, §8.1). The velocity at time `t` is `mfderiv 𝓘(ℝ) I γ t 1`, the
image of the canonical unit tangent vector of `ℝ`. Values of `γ` outside `s` are junk
(Mathlib curve idiom, cf. `IsMIntegralCurveOn`). -/
def FutureTimelikeOn (τ : g.TimeOrientation) (γ : ℝ → M) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ) I γ t ∧
    g.Timelike (γ t) (mfderiv 𝓘(ℝ) I γ t 1) ∧
    τ.FutureDirected (γ t) (mfderiv 𝓘(ℝ) I γ t 1)

/-- `FutureCausalOn τ γ s` means that on the parameter set `s`, the curve `γ : ℝ → M` is
differentiable with future-directed causal velocity: `γ` is a future-directed causal
curve on `s` (O'Neill, *Semi-Riemannian Geometry*, Ch. 14, p. 402; Wald,
*General Relativity*, §8.1). Values of `γ` outside `s` are junk. -/
def FutureCausalOn (τ : g.TimeOrientation) (γ : ℝ → M) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ) I γ t ∧
    g.Causal (γ t) (mfderiv 𝓘(ℝ) I γ t 1) ∧
    τ.FutureDirected (γ t) (mfderiv 𝓘(ℝ) I γ t 1)

/-- `ChronoStep τ p q` means `q` is reachable from `p` by a single future-directed
timelike curve segment: one piece of the piecewise-timelike curves defining the
chronology relation (O'Neill, *Semi-Riemannian Geometry*, Ch. 14, p. 402). The full
relation `ChronologicallyPrecedes` is the transitive closure of this step relation. -/
def ChronoStep (τ : g.TimeOrientation) (p q : M) : Prop :=
  ∃ (γ : ℝ → M) (a b : ℝ), a < b ∧ γ a = p ∧ γ b = q ∧ FutureTimelikeOn τ γ (Icc a b)

/-- `CausalStep τ p q` means `q` is reachable from `p` by a single future-directed
causal curve segment: one piece of the piecewise-causal curves defining the causality
relation (O'Neill, *Semi-Riemannian Geometry*, Ch. 14, p. 402). The full relation
`CausallyPrecedes` is the reflexive-transitive closure of this step relation. -/
def CausalStep (τ : g.TimeOrientation) (p q : M) : Prop :=
  ∃ (γ : ℝ → M) (a b : ℝ), a < b ∧ γ a = p ∧ γ b = q ∧ FutureCausalOn τ γ (Icc a b)

/-- The chronology relation `p ≪ q`: there is a (piecewise) future-directed timelike
curve from `p` to `q`, formalized as the transitive closure of single-segment
reachability. Definitionally O'Neill's piecewise-smooth definition
(*Semi-Riemannian Geometry*, Ch. 14, p. 402): a `Relation.TransGen` chain of timelike
segments is exactly a future-directed piecewise-timelike curve from `p` to `q`.
Cf. Wald, *General Relativity*, §8.1, p. 190 (`q ∈ I⁺(p)`).

Notation: `p ≪[τ] q` (scoped in the `Spacetime` namespace). -/
def ChronologicallyPrecedes (τ : g.TimeOrientation) : M → M → Prop :=
  Relation.TransGen (ChronoStep τ)

/-- The causality relation `p ⤳ q` (often written `p ≤ q` or `q ∈ J⁺(p)`): `p = q` or
there is a (piecewise) future-directed causal curve from `p` to `q`, formalized as the
reflexive-transitive closure of single-segment reachability. Definitionally O'Neill's
piecewise-smooth definition (*Semi-Riemannian Geometry*, Ch. 14, p. 402); reflexivity
(`p ≤ p`) is part of the sources' convention (Wald, *General Relativity*, §8.1, p. 191:
`p ∈ J⁺(p)`).

Notation: `p ⤳[τ] q` (scoped in the `Spacetime` namespace). -/
def CausallyPrecedes (τ : g.TimeOrientation) : M → M → Prop :=
  Relation.ReflTransGen (CausalStep τ)

@[inherit_doc ChronologicallyPrecedes]
scoped[Spacetime] notation:50 p:51 " ≪[" τ "] " q:51 => ChronologicallyPrecedes τ p q

@[inherit_doc CausallyPrecedes]
scoped[Spacetime] notation:50 p:51 " ⤳[" τ "] " q:51 => CausallyPrecedes τ p q

/-- The chronological future `I⁺(p)` of a point: all points reachable from `p` by a
future-directed piecewise-timelike curve. Wald, *General Relativity*, §8.1, p. 190;
O'Neill, *Semi-Riemannian Geometry*, Ch. 14, p. 402. -/
def chronologicalFuture (τ : g.TimeOrientation) (p : M) : Set M :=
  {q | ChronologicallyPrecedes τ p q}

/-- The chronological past `I⁻(p)` of a point. Wald, *General Relativity*, §8.1, p. 190;
O'Neill, *Semi-Riemannian Geometry*, Ch. 14, p. 402. -/
def chronologicalPast (τ : g.TimeOrientation) (p : M) : Set M :=
  {q | ChronologicallyPrecedes τ q p}

/-- The causal future `J⁺(p)` of a point: `p` itself together with all points reachable
from `p` by a future-directed piecewise-causal curve. Wald, *General Relativity*, §8.1,
p. 191; O'Neill, *Semi-Riemannian Geometry*, Ch. 14, p. 402. -/
def causalFuture (τ : g.TimeOrientation) (p : M) : Set M :=
  {q | CausallyPrecedes τ p q}

/-- The causal past `J⁻(p)` of a point. Wald, *General Relativity*, §8.1, p. 191;
O'Neill, *Semi-Riemannian Geometry*, Ch. 14, p. 402. -/
def causalPast (τ : g.TimeOrientation) (p : M) : Set M :=
  {q | CausallyPrecedes τ q p}

/-- The chronological future of a set, `I⁺(S) = ⋃ p ∈ S, I⁺(p)`. Wald,
*General Relativity*, §8.1, p. 191. -/
def chronologicalFutureOfSet (τ : g.TimeOrientation) (S : Set M) : Set M :=
  ⋃ p ∈ S, chronologicalFuture τ p

/-- The chronological past of a set, `I⁻(S) = ⋃ p ∈ S, I⁻(p)`. Wald,
*General Relativity*, §8.1, p. 191. -/
def chronologicalPastOfSet (τ : g.TimeOrientation) (S : Set M) : Set M :=
  ⋃ p ∈ S, chronologicalPast τ p

/-- The causal future of a set, `J⁺(S) = ⋃ p ∈ S, J⁺(p)`. Wald, *General Relativity*,
§8.1, p. 191. -/
def causalFutureOfSet (τ : g.TimeOrientation) (S : Set M) : Set M :=
  ⋃ p ∈ S, causalFuture τ p

/-- The causal past of a set, `J⁻(S) = ⋃ p ∈ S, J⁻(p)`. Wald, *General Relativity*,
§8.1, p. 191. -/
def causalPastOfSet (τ : g.TimeOrientation) (S : Set M) : Set M :=
  ⋃ p ∈ S, causalPast τ p

/-- A set `S` is achronal if no two of its points are chronologically related
(equivalently, `I⁺(S) ∩ S = ∅`). Wald, *General Relativity*, §8.1, p. 194. -/
def IsAchronal (τ : g.TimeOrientation) (S : Set M) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ¬ ChronologicallyPrecedes τ p q
