import Atlas.Specs.Spacetime.CausalStructure
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# P1.3 — Inextendibility, Cauchy surfaces, global hyperbolicity

Frozen spec (blueprint node P1.3): proof sessions must not edit this file; changes
require a spec review and a `[spec-review]` commit (see CLAUDE.md).

## Contents

* `IsFutureEndpoint`, `IsPastEndpoint`: endpoints of a curve on a parameter set, as
  limits along the endpoint filter of the domain.
* `FutureInextendible`, `PastInextendible`, `Inextendible`: no future/past endpoint
  (Wald, *General Relativity*, §8.1, p. 193).
* `futureDomainOfDependence`, `pastDomainOfDependence`, `domainOfDependence`
  (`D⁺/D⁻/D`, Wald §8.3, p. 200–201).
* `IsCauchySurface` (curve-crossing form) and `IsGloballyHyperbolic` (Wald §8.3,
  p. 201; Geroch, *J. Math. Phys.* 11, 437 (1970)).

## The endpoint filter (spec-review-sensitive)

Wald (p. 193): "`p` is a future endpoint of a curve `λ` if for every neighborhood `O`
of `p` there exists `t₀` such that `λ(t) ∈ O` for all `t > t₀`", with `t` ranging over
the domain of the curve. In the Mathlib curve idiom the domain is a set `s : Set ℝ`,
and this is exactly convergence along `Filter.atTop` *of the subtype `s`*, pushed into
`ℝ` — i.e. `Filter.Tendsto (fun t : s ↦ γ t) Filter.atTop (𝓝 p)`. Behavior across
domain shapes:

* `s` unbounded above: convergence as `t → ∞` within `s`.
* `s = Ico a b`: convergence as `t → b⁻` within `s` (the tails `s ∩ Ici t₀`, `t₀ ∈ s`,
  are cofinal in `𝓝[s] b`).
* `s` with a greatest element `b` (e.g. `Icc a b`): `atTop` on the subtype is the
  principal filter at `b`, so `γ b` is always a future endpoint and no curve whose
  domain has a maximum is future inextendible — matching Wald, where a curve on a
  compact interval always has (future and past) endpoints.
* `s = ∅`: the filter is `⊥`, every point is vacuously an endpoint, and the empty
  curve is *not* inextendible (it never witnesses failure of the Cauchy property).

Note this is *not* `Filter.atTop ⊓ 𝓟 s` on `ℝ`: for any `s` bounded above that filter
is `⊥` (take `Ici t₀ ∈ atTop` with `t₀` an upper bound), which would wrongly make every
curve with bounded-above domain "endpointed". The subtype filter has no such collapse.

## Interval domains

Curves in the sources are defined on intervals (Wald, p. 193). The pointwise conditions
`FutureCausalOn τ γ s` do not constrain the shape of `s`, so the quantifications below
additionally require `s.OrdConnected` (the Mathlib idiom for "s is an interval").
Without it, a genuine causal curve with a parameter gap punched out of its domain
(e.g. `(-∞, 0) ∪ (1, ∞)`) would count as an inextendible causal curve that can skip any
candidate Cauchy surface, making `IsCauchySurface` unsatisfiable.

## Sources

* Wald, *General Relativity* (1984), §8.1 (p. 193: endpoints, inextendibility) and
  §8.3 (pp. 200–201: domains of dependence, Cauchy surfaces, global hyperbolicity).
* O'Neill, *Semi-Riemannian Geometry with Applications to Relativity* (1983), Ch. 14
  (Cauchy hypersurfaces).
* Geroch, "Domain of dependence", *J. Math. Phys.* 11, 437 (1970).
* Minguzzi, "Lorentzian causality theory", *Living Rev. Rel.* 22:3 (2019), §3.
-/

open Bundle Set Filter
open scoped ContDiff Manifold Topology

section Endpoints

variable {X : Type*} [TopologicalSpace X]

/-- `p` is a future endpoint of the curve `γ : ℝ → X` with parameter set `s` if `γ`
converges to `p` toward the future end of `s`, i.e. along `Filter.atTop` of the subtype
`s`. Wald, *General Relativity*, §8.1, p. 193: for every neighborhood `O` of `p` there
exists `t₀` such that `γ t ∈ O` for all `t ∈ s` with `t ≥ t₀`. Purely topological: no
metric or causality enters. See the module docstring for the choice of filter and its
behavior on the various interval shapes. -/
def IsFutureEndpoint (γ : ℝ → X) (s : Set ℝ) (p : X) : Prop :=
  Tendsto (fun t : s ↦ γ t) atTop (𝓝 p)

/-- `p` is a past endpoint of the curve `γ : ℝ → X` with parameter set `s` if `γ`
converges to `p` toward the past end of `s`, i.e. along `Filter.atBot` of the subtype
`s`. Time reverse of `IsFutureEndpoint`; Wald, *General Relativity*, §8.1, p. 193. -/
def IsPastEndpoint (γ : ℝ → X) (s : Set ℝ) (p : X) : Prop :=
  Tendsto (fun t : s ↦ γ t) atBot (𝓝 p)

/-- A curve is future inextendible (on its parameter set) if it has no future endpoint.
Wald, *General Relativity*, §8.1, p. 193. -/
def FutureInextendible (γ : ℝ → X) (s : Set ℝ) : Prop :=
  ∀ p : X, ¬ IsFutureEndpoint γ s p

/-- A curve is past inextendible (on its parameter set) if it has no past endpoint.
Wald, *General Relativity*, §8.1, p. 193. -/
def PastInextendible (γ : ℝ → X) (s : Set ℝ) : Prop :=
  ∀ p : X, ¬ IsPastEndpoint γ s p

/-- A curve is inextendible if it is both future and past inextendible. Wald,
*General Relativity*, §8.1, p. 193. -/
def Inextendible (γ : ℝ → X) (s : Set ℝ) : Prop :=
  FutureInextendible γ s ∧ PastInextendible γ s

end Endpoints

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {g : PseudoRiemannianMetric I n M}

/-- The future domain of dependence `D⁺(S)`: the set of points `p` such that every past
inextendible future-directed causal curve through `p` intersects `S`. Wald,
*General Relativity*, §8.3, p. 200. Curves are quantified in the Mathlib idiom, over
interval (`OrdConnected`) parameter sets; see the module docstring. `S` is typically
achronal, but achronality is not part of this definition. -/
def futureDomainOfDependence (τ : g.TimeOrientation) (S : Set M) : Set M :=
  {p | ∀ (γ : ℝ → M) (s : Set ℝ), s.OrdConnected → FutureCausalOn τ γ s →
    PastInextendible γ s → (∃ t ∈ s, γ t = p) → ∃ t ∈ s, γ t ∈ S}

/-- The past domain of dependence `D⁻(S)`: the set of points `p` such that every future
inextendible future-directed causal curve through `p` intersects `S`. Time reverse of
`futureDomainOfDependence`; Wald, *General Relativity*, §8.3, p. 201. -/
def pastDomainOfDependence (τ : g.TimeOrientation) (S : Set M) : Set M :=
  {p | ∀ (γ : ℝ → M) (s : Set ℝ), s.OrdConnected → FutureCausalOn τ γ s →
    FutureInextendible γ s → (∃ t ∈ s, γ t = p) → ∃ t ∈ s, γ t ∈ S}

/-- The (total) domain of dependence `D(S) = D⁺(S) ∪ D⁻(S)`. Wald,
*General Relativity*, §8.3, p. 201. -/
def domainOfDependence (τ : g.TimeOrientation) (S : Set M) : Set M :=
  futureDomainOfDependence τ S ∪ pastDomainOfDependence τ S

/-- A Cauchy surface: a closed achronal set met in exactly one parameter value by every
inextendible future-directed causal curve (curve-crossing form).

Sources: Wald, *General Relativity*, §8.3, p. 201 defines a Cauchy surface as a closed
achronal set `Σ` with `D(Σ) = M`, and notes that every inextendible causal curve then
intersects `Σ`; O'Neill, *Semi-Riemannian Geometry*, Ch. 14 defines a Cauchy
hypersurface as a set met exactly once by every inextendible timelike curve. This spec
states the crossing condition for *causal* curves and counts *parameter values*
(`∃!` over the domain), per the approved blueprint design (P1.3).

Formalization choices reviewers should scrutinize:
* "exactly once for causal curves" is stronger than "exactly once for timelike curves":
  it excludes achronal Cauchy sets containing null segments along which a causal curve
  can run. Smooth spacelike Cauchy surfaces (in particular `{t = 0}` in Minkowski
  space, node P1.W2) satisfy it, so `IsGloballyHyperbolic` is unaffected for the
  atlas's purposes.
* counting parameter values rather than image points additionally excludes curves
  revisiting the same point of `S` — impossible anyway without closed causal loops. -/
def IsCauchySurface (τ : g.TimeOrientation) (S : Set M) : Prop :=
  IsClosed S ∧ IsAchronal τ S ∧
    ∀ (γ : ℝ → M) (s : Set ℝ), s.OrdConnected → FutureCausalOn τ γ s →
      Inextendible γ s → ∃! t, t ∈ s ∧ γ t ∈ S

/-- A (time-oriented) spacetime is globally hyperbolic if it possesses a Cauchy
surface. Wald, *General Relativity*, §8.3, p. 201; Geroch, *J. Math. Phys.* 11, 437
(1970). Equivalent classical formulations (strong causality plus compact causal
diamonds, etc.) are theorems, not part of this spec. -/
def IsGloballyHyperbolic (τ : g.TimeOrientation) : Prop :=
  ∃ S : Set M, IsCauchySurface τ S
