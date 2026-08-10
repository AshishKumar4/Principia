import Atlas.Witnesses.MinkowskiCausal

/-!
# P2.4a adversarial kernel probes — the causal anchor and `IsSpacelike` strictness

Probes `isSpacelike_sub_iff_not_causallyPrecedes` on concrete pairs, in BOTH
directions, deriving each side independently (coordinates for `IsSpacelike`;
`minkowski_causal_iff` for `⤳`) so the anchor is cross-checked rather than assumed.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.4a/` only.
-/

open Spacetime Spacetime.Minkowski

/-! ## Spacelike pair: `x = ∂₁`, `y = 0` -/

-- Independent coordinate fact: the displacement is spacelike.
theorem probe_e1_isSpacelike : IsSpacelike (EuclideanSpace.single 1 1 - 0 : M4) := by
  rw [sub_zero, isSpacelike_iff]
  norm_num [Fin.ext_iff]

-- Anchor forward: hence neither point causally precedes the other.
theorem probe_e1_causally_unrelated :
    ¬ ((EuclideanSpace.single 1 1 : M4) ⤳[minkowskiTimeOrientation] 0) ∧
      ¬ ((0 : M4) ⤳[minkowskiTimeOrientation] EuclideanSpace.single 1 1) :=
  (isSpacelike_sub_iff_not_causallyPrecedes _ _).1 probe_e1_isSpacelike

-- Independent derivation of the same causal facts via `minkowski_causal_iff`
-- (coordinates, no anchor), then the anchor backward must reproduce spacelikeness.
theorem probe_e1_isSpacelike_via_anchor :
    IsSpacelike (EuclideanSpace.single 1 1 - 0 : M4) := by
  refine (isSpacelike_sub_iff_not_causallyPrecedes _ _).2 ⟨?_, ?_⟩
  · intro h
    rcases (minkowski_causal_iff _ _).1 h with h | h
    · exact absurd (congrArg (fun z : M4 => z 1) h) (by norm_num [Fin.ext_iff])
    · have := ((futureDirected_iff _ _).1 h).2
      norm_num [Fin.ext_iff] at this
  · intro h
    rcases (minkowski_causal_iff _ _).1 h with h | h
    · exact absurd (congrArg (fun z : M4 => z 1) h) (by norm_num [Fin.ext_iff])
    · have := ((futureDirected_iff _ _).1 h).2
      norm_num [Fin.ext_iff] at this

/-! ## Timelike pair refutation: `x = 0`, `y = ∂₀` — causally related, so NOT spacelike -/

-- Independent causal fact: `0 ⤳ ∂₀` (future timelike displacement).
theorem probe_zero_causallyPrecedes_e0 :
    (0 : M4) ⤳[minkowskiTimeOrientation] EuclideanSpace.single 0 1 := by
  rw [minkowski_causal_iff, futureDirected_iff]
  refine Or.inr ⟨?_, ?_⟩ <;> simp

-- Anchor forward (contrapositive): the displacement is NOT spacelike.
theorem probe_timelike_not_isSpacelike :
    ¬ IsSpacelike ((0 : M4) - EuclideanSpace.single 0 1) := fun h =>
  ((isSpacelike_sub_iff_not_causallyPrecedes _ _).1 h).1 probe_zero_causallyPrecedes_e0

-- Independent coordinate confirmation of the same refutation.
theorem probe_timelike_not_isSpacelike_coords :
    ¬ IsSpacelike ((0 : M4) - EuclideanSpace.single 0 1) := by
  rw [isSpacelike_iff]
  norm_num [Fin.ext_iff, show ((2 : Fin 4) = 0) = False from by decide,
    show ((3 : Fin 4) = 0) = False from by decide]

/-! ## Null pair: the strictness edge case — `η(v, v) = 0` must NOT be spacelike -/

-- `0 ⤳ ∂₀ + ∂₁` (null future displacement is causal), so the anchor forces
-- `¬ IsSpacelike (∂₀ + ∂₁)`: this is exactly where a non-strict `0 ≤ η(v,v)`
-- definition of `IsSpacelike` would contradict the anchor.
theorem probe_null_not_isSpacelike :
    ¬ IsSpacelike ((0 : M4) - (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1)) := by
  intro h
  refine ((isSpacelike_sub_iff_not_causallyPrecedes _ _).1 h).1 ?_
  rw [minkowski_causal_iff, futureDirected_iff]
  refine Or.inr ⟨?_, ?_⟩ <;> simp

/-! ## Reflexivity: `x ⤳ x` forces `¬ IsSpacelike 0` (why strictness is not optional) -/

theorem probe_causal_refl (x : M4) : x ⤳[minkowskiTimeOrientation] x := by
  rw [minkowski_causal_iff]; exact Or.inl rfl

theorem probe_zero_not_isSpacelike : ¬ IsSpacelike (0 : M4) := fun h => by
  have h' : IsSpacelike ((0 : M4) - 0) := by simpa using h
  exact ((isSpacelike_sub_iff_not_causallyPrecedes _ _).1 h').1 (probe_causal_refl 0)

-- The frozen P1.1 predicate DOES count the zero vector as spacelike (O'Neill
-- convention) — the documented divergence is real, in the claimed direction.
example : minkowskiMetric.Spacelike (0 : M4) (0 : M4) := Or.inr rfl
