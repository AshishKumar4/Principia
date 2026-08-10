import Atlas.Specs.Spacetime.PoincareRep
import Atlas.Witnesses.UnitaryGroups

/-!
# P2.4b adversarial kernel probes — the Stone-bridge anchor, cross-lane

Probes `PoincareRep.translationGroup` end-to-end against the frozen P2.3g lane:

* `trivialRep` — the trivial representation as a full named instantiation (all
  fields, incl. joint continuity): the spec is satisfiable, not vacuous.
* `probe_translationGroup_eq_trivialGroup` — the anchor evaluated on `trivialRep`
  IS the P2.3g witness `trivialGroup H` (a `OneParameterUnitaryGroup` equality
  through both frozen `FunLike` surfaces).
* `probe_translationGroup_generator_zero` — **the cross-lane bridge**: the Stone
  generator (frozen P2.3g `LinearPMap` definition) of the anchor's output is the
  zero operator; computed BOTH by transport along the previous equality AND
  independently through `generator_apply_of_hasDerivAt` with the explicit
  `HasDerivAt` witness (`probe_generator_apply_direct`), so the two frozen specs
  are checked against each other, not against a shared intermediate.
* `probe_map_add_orientation` / `probe_map_neg_eq_inv` — the anchor's group-law
  orientation `U(s + t) = U(s)U(t)` matches Reed & Simon I §VIII.4, and
  `U(-t) = U(t)⁻¹` is reachable through the P2.3g API.
* `probe_translationGroup_zero_dir` — degenerate direction `a = 0`: the anchor
  collapses to the trivial group (edge case is sane, not junk).

No nontrivial `PoincareRep` is cheaply constructible (see
`character_obstruction_probe.lean`: even the scalar character collapses), so the
trivial representation is the strongest satisfiability probe available at freeze
time; the nontrivial-generator content of the bridge must be certified by the
witness node's regular representation on `L²(M4)`.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.4b/` only; compiles via
`lake env lean audits/probes/P2.4b/stone_bridge_probe.lean`.
-/

open Spacetime.Minkowski OperatorTheory

namespace P24bProbe

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The trivial representation `g ↦ 1`, instantiating every frozen field of
`PoincareRep` (the joint action map collapses to `(g, x) ↦ x`). -/
noncomputable def trivialRep (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : PoincareRep H where
  toFun := 1
  continuous_apply₂' := continuous_snd

@[simp]
theorem trivialRep_apply (g : PoincareGroup) : trivialRep H g = 1 :=
  rfl

/-- The frozen `MonoidHomClass` surface engages on the probe model. -/
example (g₁ g₂ : PoincareGroup) :
    trivialRep H (g₁ * g₂) = trivialRep H g₁ * trivialRep H g₂ :=
  map_mul _ g₁ g₂

example (g : PoincareGroup) : trivialRep H g⁻¹ = (trivialRep H g)⁻¹ :=
  map_inv _ g

/-- The joint-continuity theorem and its per-vector consequence apply. -/
example : Continuous fun p : PoincareGroup × H => ((trivialRep H) p.1 : H →L[ℂ] H) p.2 :=
  (trivialRep H).continuous_apply₂

example (x : H) : Continuous fun g : PoincareGroup => ((trivialRep H) g : H →L[ℂ] H) x :=
  (trivialRep H).continuous_apply x

/-- **Anchor output identified with the P2.3g witness**: the translation line of the
trivial representation is the trivial one-parameter unitary group, as elements of the
frozen `OneParameterUnitaryGroup H`. -/
theorem probe_translationGroup_eq_trivialGroup (a : M4) :
    (trivialRep H).translationGroup a = Witnesses.trivialGroup H := by
  ext t
  rfl

/-- **The cross-lane Stone bridge**: the frozen P2.3g Stone generator of the anchor's
output on the trivial representation is the zero `LinearPMap` (domain `⊤`, value `0`),
transported along `probe_translationGroup_eq_trivialGroup` from the independently
proven `trivialGroup_generator`. -/
theorem probe_translationGroup_generator_zero (a : M4) :
    ((trivialRep H).translationGroup a).generator = 0 := by
  rw [probe_translationGroup_eq_trivialGroup, Witnesses.trivialGroup_generator]

/-- Independent recomputation of the same generator value through the frozen
`generator_apply_of_hasDerivAt` computation rule and an explicit `HasDerivAt`
witness — no detour through the P2.3g witness file, so the two routes cross-check. -/
theorem probe_generator_apply_direct (a : M4) (x : H) :
    ((trivialRep H).translationGroup a).generator
        ⟨x, OneParameterUnitaryGroup.mem_generatorDomain.mpr
          ⟨0, hasDerivAt_const 0 x⟩⟩ = 0 := by
  have h : HasDerivAt
      (fun t : ℝ => (((trivialRep H).translationGroup a) t : H →L[ℂ] H) x) 0 0 :=
    hasDerivAt_const 0 x
  simpa using ((trivialRep H).translationGroup a).generator_apply_of_hasDerivAt h

/-- Group-law orientation of the anchor's output matches Reed & Simon I §VIII.4:
`U(s + t) = U(s) U(t)` (probed through the P2.3g API on an arbitrary rep). -/
theorem probe_map_add_orientation (U : PoincareRep H) (a : M4) (s t : ℝ) :
    U.translationGroup a (s + t) = U.translationGroup a s * U.translationGroup a t :=
  (U.translationGroup a).map_add_eq_mul s t

/-- `U(-t) = U(t)⁻¹` is reachable for the anchor's output via P2.3g's
`map_neg_eq_inv` — the anchor genuinely lands in the one-parameter-group API. -/
theorem probe_map_neg_eq_inv (U : PoincareRep H) (a : M4) (t : ℝ) :
    U.translationGroup a (-t) = (U.translationGroup a t)⁻¹ :=
  (U.translationGroup a).map_neg_eq_inv t

/-- The anchor's `simp` normal form: `U.translationGroup a t = U ⟨t • a, 1⟩`. -/
example (U : PoincareRep H) (a : M4) (t : ℝ) :
    U.translationGroup a t = U ⟨t • a, 1⟩ :=
  U.translationGroup_apply a t

/-- Degenerate direction `a = 0`: the translation line collapses to the constant
group `1` for EVERY representation (edge-case sanity of the anchor). -/
theorem probe_translationGroup_zero_dir (U : PoincareRep H) (t : ℝ) :
    U.translationGroup 0 t = 1 := by
  rw [U.translationGroup_apply]
  have h : (⟨t • (0 : M4), 1⟩ : PoincareGroup) = 1 :=
    PoincareGroup.ext (by simp) rfl
  rw [h, map_one]

end P24bProbe
