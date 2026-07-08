import Atlas.Specs.Spacetime.GlobalHyperbolicity

/-!
# Generic lemmas about the frozen causal-structure specs

Free consequences of the frozen P1.2/P1.3 specs (`Atlas/Specs/Spacetime/`), generic in
the spacetime. Main result: blueprint node **P1.3b(ii)** — a future-directed timelike
curve on an interval domain meets an achronal set in at most one parameter value
(`Spacetime.IsAchronal.eq_of_futureTimelikeOn`). This is the uniqueness half of the
Cauchy-surface crossing property; it turns any at-least-once crossing statement into
the exactly-once (`∃!`) form demanded by `Spacetime.IsCauchySurface`.

## Sources

* O'Neill, *Semi-Riemannian Geometry with Applications to Relativity* (1983), Ch. 14
  (chronology relation, achronality).
* Wald, *General Relativity* (1984), §8.1, p. 192 (achronal sets).
-/

open Set
open scoped ContDiff Manifold

namespace Spacetime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {g : PseudoRiemannianMetric I n M} {τ : g.TimeOrientation} {γ : ℝ → M} {s t : Set ℝ}

/-- A future-directed timelike curve condition restricts to subsets of the parameter
set. -/
theorem FutureTimelikeOn.mono (h : FutureTimelikeOn τ γ s) (hts : t ⊆ s) :
    FutureTimelikeOn τ γ t :=
  fun u hu => h u (hts hu)

/-- A future-directed causal curve condition restricts to subsets of the parameter
set. -/
theorem FutureCausalOn.mono (h : FutureCausalOn τ γ s) (hts : t ⊆ s) :
    FutureCausalOn τ γ t :=
  fun u hu => h u (hts hu)

/-- Timelike curves are causal: a future-directed timelike curve is a future-directed
causal curve (O'Neill, *Semi-Riemannian Geometry*, Ch. 14, p. 402). -/
theorem FutureTimelikeOn.futureCausalOn (h : FutureTimelikeOn τ γ s) :
    FutureCausalOn τ γ s :=
  fun u hu => ⟨(h u hu).1, (h u hu).2.2⟩

/-- Two parameters of a future-directed timelike curve on an interval domain are
related by a single timelike segment. -/
theorem FutureTimelikeOn.chronoStep {t₁ t₂ : ℝ} (h : FutureTimelikeOn τ γ s)
    (hs : s.OrdConnected) (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s) (hlt : t₁ < t₂) :
    ChronoStep τ (γ t₁) (γ t₂) :=
  ⟨γ, t₁, t₂, hlt, rfl, rfl, h.mono (hs.out ht₁ ht₂)⟩

/-- Two parameters of a future-directed causal curve on an interval domain are related
by a single causal segment. -/
theorem FutureCausalOn.causalStep {t₁ t₂ : ℝ} (h : FutureCausalOn τ γ s)
    (hs : s.OrdConnected) (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s) (hlt : t₁ < t₂) :
    CausalStep τ (γ t₁) (γ t₂) :=
  ⟨γ, t₁, t₂, hlt, rfl, rfl, h.mono (hs.out ht₁ ht₂)⟩

/-- A future-directed timelike curve on an interval domain realizes the chronology
relation between any two of its points, in increasing parameter order. -/
theorem FutureTimelikeOn.chronologicallyPrecedes {t₁ t₂ : ℝ}
    (h : FutureTimelikeOn τ γ s) (hs : s.OrdConnected) (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s)
    (hlt : t₁ < t₂) : γ t₁ ≪[τ] γ t₂ :=
  Relation.TransGen.single (h.chronoStep hs ht₁ ht₂ hlt)

/-- A future-directed causal curve on an interval domain realizes the causality
relation between any two of its points, in weakly increasing parameter order. -/
theorem FutureCausalOn.causallyPrecedes {t₁ t₂ : ℝ}
    (h : FutureCausalOn τ γ s) (hs : s.OrdConnected) (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s)
    (hle : t₁ ≤ t₂) : γ t₁ ⤳[τ] γ t₂ := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (h.causalStep hs ht₁ ht₂ hlt)

/-- **P1.3b(ii)**: a future-directed timelike curve on an interval domain meets an
achronal set in at most one parameter value. Two distinct crossing parameters would
give a timelike segment between two points of the set, contradicting achronality
(O'Neill, *Semi-Riemannian Geometry*, Ch. 14; Wald, *General Relativity*, §8.1). -/
theorem IsAchronal.eq_of_futureTimelikeOn {S : Set M} (hS : IsAchronal τ S)
    (hs : s.OrdConnected) (hγ : FutureTimelikeOn τ γ s) {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s) (h₁ : γ t₁ ∈ S) (h₂ : γ t₂ ∈ S) : t₁ = t₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hS _ h₁ _ h₂ (hγ.chronologicallyPrecedes hs ht₁ ht₂ hlt)
  · exact hS _ h₂ _ h₁ (hγ.chronologicallyPrecedes hs ht₂ ht₁ hlt)

end Spacetime
