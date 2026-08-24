import Atlas.Specs.Spacetime.PoincareRep
import Atlas.Proofs.PoincareTopology
import Atlas.Witnesses.UnitaryGroups
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# P2.4bW — non-vacuity witnesses for Poincaré representations

Witnesses (blueprint node P2.4bW) that the frozen P2.4b spec
`Atlas/Specs/Spacetime/PoincareRep.lean` is non-vacuous **beyond the trivial model** —
the freeze condition D2 (`audits/reviews/P2.4b.md`) blocks proof-consumption of
`PoincareRep` until a representation with nontrivial action lands, because the trivial
representation is provably the only cheap model (the committed
`audits/probes/P2.4b/character_obstruction_probe.lean` kernel-certifies that no
character-form representation exists).

## Contents

* `Witnesses.trivialRep H` — the trivial representation `g ↦ 1` as a reusable `def`
  (promoted from the committed reviewer probe, see Attribution), with its translation
  line identified with the P2.3g witness `trivialGroup H` and its Stone generator
  computed to be `0` two independent ways (transport along that identification, and
  directly through the frozen `generator_apply_of_hasDerivAt` computation rule).
* **`Witnesses.regularRep`** — **the nontrivial witness**: the regular
  representation of `P↑₊` on `L²(M4)`, `(U(g)ψ)(x) = ψ(g⁻¹ • x)`.
  `Atlas.Proofs.PoincareTopology` supplies the reusable topology and
  volume-preservation facts. The operator is Mathlib's
  `MeasureTheory.Lp.compMeasurePreserving`, upgraded to a linear isometry
  equivalence by the group law and to a unitary via
  `Unitary.linearIsometryEquiv`. Joint strong continuity is
  `Continuous.compMeasurePreservingLp` applied to the continuous inverse affine
  action.
* `Witnesses.regularRep_translation_ne_one` — **expected false / nontriviality**: the
  translation by `e₁` acts nontrivially (it moves the indicator of a small ball to the
  indicator of a disjoint ball of positive volume); hence
  `Witnesses.regularRep_ne_trivialRep`.
* Expected-true `example`s: the frozen `MonoidHomClass` surface, unitarity
  (`Unitary.norm_map`), joint and per-vector continuity on the nontrivial model, and
  the Stone-bridge pin — `regularRep.translationGroup a` at time `t` is translation by
  `t • a`, acting on `L²` representatives as `ψ ↦ ψ(· - t • a)` (a.e.), the canonical
  strongly continuous translation group of Reed & Simon I §VIII.4.

## Attribution

`trivialRep` and its translation-line/generator lemmas promote the committed
reviewer probe `audits/probes/P2.4b/stone_bridge_probe.lean` into the witness
layer. Generic Poincaré topology and volume facts live in
`Atlas.Proofs.PoincareTopology`; this file contains only the witness models.

## Sources

* Streater & Wightman, *PCT, Spin and Statistics, and All That* (1964; Princeton
  Landmarks ed. 2000), Ch. 1 (states carry a continuous unitary representation of
  `P↑₊`; `U(a, Λ)` and its translation subgroup).
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I* (1980), §VIII.4
  (the translation group `(U(t)ψ)(x) = ψ(x − t)` on `L²` as the canonical strongly
  continuous unitary group, here the translation lines of `regularRep`).
* E. Wigner, "On unitary representations of the inhomogeneous Lorentz group",
  *Ann. of Math.* 40 (1939), 149–204 (nontrivial representations of `P↑₊` are
  infinite-dimensional — the reason this witness lives on `L²(M4)`).
-/

open MeasureTheory
open scoped ENNReal

namespace Spacetime.Minkowski

noncomputable section


namespace Witnesses

open OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The trivial representation

Promoted from the committed reviewer probe
`audits/probes/P2.4b/stone_bridge_probe.lean` (see the module docstring). -/

/-- The trivial representation `g ↦ 1`, instantiating every frozen field of
`PoincareRep` (the joint action map collapses to `(g, x) ↦ x`). By the kernel-certified
character obstruction (`audits/probes/P2.4b/character_obstruction_probe.lean`) this is
the only representation with commutative image of character form; the nontrivial
witness below is necessarily infinite-dimensional. -/
def trivialRep (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : PoincareRep H where
  toFun := 1
  continuous_apply₂' := continuous_snd

@[simp]
theorem trivialRep_apply (g : PoincareGroup) : trivialRep H g = 1 :=
  rfl

/-- The translation line of the trivial representation is the P2.3g witness
`trivialGroup H`, as elements of the frozen `OneParameterUnitaryGroup H`. -/
theorem trivialRep_translationGroup (a : M4) :
    (trivialRep H).translationGroup a = OperatorTheory.Witnesses.trivialGroup H := by
  ext t
  rfl

/-- The Stone generator of every translation line of the trivial representation is the
zero operator — transported along `trivialRep_translationGroup` from the independently
proven `trivialGroup_generator`. -/
theorem trivialRep_translationGroup_generator (a : M4) :
    ((trivialRep H).translationGroup a).generator = 0 := by
  rw [trivialRep_translationGroup, OperatorTheory.Witnesses.trivialGroup_generator]

/-- Independent recomputation of the same generator value through the frozen
`generator_apply_of_hasDerivAt` computation rule and an explicit `HasDerivAt` witness —
no detour through the P2.3g witness file, so the two routes cross-check. -/
theorem trivialRep_generator_apply_direct (a : M4) (x : H) :
    ((trivialRep H).translationGroup a).generator
        ⟨x, OneParameterUnitaryGroup.mem_generatorDomain.mpr
          ⟨0, hasDerivAt_const 0 x⟩⟩ = 0 := by
  have h : HasDerivAt
      (fun t : ℝ => (((trivialRep H).translationGroup a) t : H →L[ℂ] H) x) 0 0 :=
    hasDerivAt_const 0 x
  simpa using ((trivialRep H).translationGroup a).generator_apply_of_hasDerivAt h

/-- The frozen `MonoidHomClass` surface engages on the trivial model. -/
example (g₁ g₂ : PoincareGroup) :
    trivialRep H (g₁ * g₂) = trivialRep H g₁ * trivialRep H g₂ :=
  map_mul _ g₁ g₂

example (g : PoincareGroup) : trivialRep H g⁻¹ = (trivialRep H g)⁻¹ :=
  map_inv _ g

/-! ### The regular representation on `L²(M4)`

`(U(g)ψ)(x) = ψ(g⁻¹ • x)`: composition with the volume-preserving map `g⁻¹ • ·`. -/

/-- The carrier of the regular representation: `L²` of Minkowski space. -/
abbrev L2M4 : Type := Lp ℂ 2 (volume : Measure M4)

/-- `ψ ↦ ψ ∘ (g⁻¹ • ·)` as a linear isometry of `L²(M4)`; isometry is exactly
volume preservation of the Poincaré action. -/
def regularIsometry (g : PoincareGroup) : L2M4 →ₗᵢ[ℂ] L2M4 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : M4 => g⁻¹ • x)
    (PoincareGroup.volume_preserving_smul g⁻¹)

theorem regularIsometry_apply (g : PoincareGroup) (ψ : L2M4) :
    regularIsometry g ψ
      = Lp.compMeasurePreserving (fun x : M4 => g⁻¹ • x)
          (PoincareGroup.volume_preserving_smul g⁻¹) ψ := rfl

private theorem comp_congr_fun {f f' : M4 → M4} (h : f = f')
    (hf : MeasurePreserving f (volume : Measure M4) volume) (ψ : L2M4) :
    Lp.compMeasurePreserving f hf ψ = Lp.compMeasurePreserving f' (h ▸ hf) ψ := by
  subst h; rfl

theorem regularIsometry_one (ψ : L2M4) : regularIsometry 1 ψ = ψ := by
  rw [regularIsometry_apply,
    comp_congr_fun (f' := id) (by funext x; simp)
      (PoincareGroup.volume_preserving_smul 1⁻¹)]
  exact Lp.compMeasurePreserving_id_apply ψ

/-- The contravariance of composition cancels the contravariance of `g ↦ g⁻¹ • ·`:
`U(gh) = U(g) ∘ U(h)`. -/
theorem regularIsometry_mul (g h : PoincareGroup) (ψ : L2M4) :
    regularIsometry (g * h) ψ = regularIsometry g (regularIsometry h ψ) := by
  rw [regularIsometry_apply,
    comp_congr_fun
      (f' := (fun x : M4 => h⁻¹ • x) ∘ fun x : M4 => g⁻¹ • x)
      (by funext x; simp [mul_smul])
      (PoincareGroup.volume_preserving_smul (g * h)⁻¹)]
  exact Lp.compMeasurePreserving_comp_apply ψ
    (PoincareGroup.volume_preserving_smul h⁻¹)
    (PoincareGroup.volume_preserving_smul g⁻¹)

/-- `U(g)` as a linear isometry *equivalence* of `L²(M4)`: the two-sided inverse is
`U(g⁻¹)`, by the composition law. -/
def regularEquiv (g : PoincareGroup) : L2M4 ≃ₗᵢ[ℂ] L2M4 where
  toLinearEquiv := LinearEquiv.ofLinear (regularIsometry g).toLinearMap
    (regularIsometry g⁻¹).toLinearMap
    (LinearMap.ext fun ψ => by
      show regularIsometry g (regularIsometry g⁻¹ ψ) = ψ
      rw [← regularIsometry_mul, mul_inv_cancel, regularIsometry_one])
    (LinearMap.ext fun ψ => by
      show regularIsometry g⁻¹ (regularIsometry g ψ) = ψ
      rw [← regularIsometry_mul, inv_mul_cancel, regularIsometry_one])
  norm_map' := (regularIsometry g).norm_map

theorem regularEquiv_apply (g : PoincareGroup) (ψ : L2M4) :
    regularEquiv g ψ = regularIsometry g ψ := rfl

/-- The regular representation as a homomorphism into the isometry group of `L²(M4)`. -/
def regularHom : PoincareGroup →* (L2M4 ≃ₗᵢ[ℂ] L2M4) where
  toFun := regularEquiv
  map_one' := LinearIsometryEquiv.ext fun ψ => by
    rw [regularEquiv_apply, regularIsometry_one]
    rfl
  map_mul' g h := LinearIsometryEquiv.ext fun ψ => by
    rw [regularEquiv_apply, regularIsometry_mul]
    rfl

/-- **The nontrivial witness** (P2.4b freeze condition D2): the regular representation
of the restricted Poincaré group on `L²(M4)`, `(U(g)ψ)(x) = ψ(g⁻¹ • x)`. The unitary
group is reached through `Unitary.linearIsometryEquiv`; the frozen joint continuity is
`Continuous.compMeasurePreservingLp` composed with continuity of `g ↦ (g⁻¹ • ·)` in
the compact-open topology, which reduces to the `ContinuousInv`/`ContinuousSMul`
instances above. -/
def regularRep : PoincareRep L2M4 where
  toFun := (Unitary.linearIsometryEquiv.symm.toMonoidHom :
    (L2M4 ≃ₗᵢ[ℂ] L2M4) →* unitary (L2M4 →L[ℂ] L2M4)).comp regularHom
  continuous_apply₂' := by
    show Continuous fun p : PoincareGroup × L2M4 =>
      Lp.compMeasurePreserving (fun x : M4 => p.1⁻¹ • x)
        (PoincareGroup.volume_preserving_smul p.1⁻¹) p.2
    have h := Continuous.compMeasurePreservingLp
      (f := fun p : PoincareGroup × L2M4 => p.2)
      (g := fun p : PoincareGroup × L2M4 => PoincareGroup.smulCM p.1⁻¹)
      continuous_snd
      (PoincareGroup.continuous_smulCM.comp (continuous_inv.comp continuous_fst))
      (fun p => PoincareGroup.volume_preserving_smul p.1⁻¹) (by norm_num)
    exact h

/-- Action of the regular representation, unfolded to the composition operator. -/
theorem regularRep_apply (g : PoincareGroup) (ψ : L2M4) :
    (regularRep g : L2M4 →L[ℂ] L2M4) ψ
      = Lp.compMeasurePreserving (fun x : M4 => g⁻¹ • x)
          (PoincareGroup.volume_preserving_smul g⁻¹) ψ := rfl

/-- On `L²` representatives, the regular representation of a pure translation is
translation of the argument: `(U(b, 1)ψ)(x) = ψ(x − b)` almost everywhere (the
Reed & Simon I §VIII.4 translation group, in every direction at once). -/
theorem regularRep_translation_coeFn (b : M4) (ψ : L2M4) :
    ⇑((regularRep (⟨b, 1⟩ : PoincareGroup) : L2M4 →L[ℂ] L2M4) ψ)
      =ᵐ[volume] fun x => ψ (x - b) := by
  rw [regularRep_apply]
  refine (Lp.coeFn_compMeasurePreserving ψ _).trans ?_
  refine Filter.EventuallyEq.of_eq (funext fun x => ?_)
  rw [Function.comp_apply, PoincareGroup.translation_inv_smul]

/-! ### Nontriviality (expected false)

The trivial representation is the zero-content model; the regular representation is
genuinely nontrivial: translating the indicator of a radius-`1/2` ball by `e₁` yields
the indicator of a *disjoint* ball, and the two differ on a set of positive volume. -/

/-- Indicator of the ball of radius `1/2` about `c`, as an element of `L²(M4)`. -/
def ballIndicator (c : M4) : L2M4 :=
  indicatorConstLp 2 (measurableSet_ball (x := c) (ε := 1/2))
    measure_ball_lt_top.ne (1 : ℂ)

/-- **Expected false / nontriviality**: translation by `e₁` does not act as the
identity on `L²(M4)` — it moves `ballIndicator 0` to `ballIndicator e₁`, and the two
balls are disjoint with positive volume. This is the content freeze condition D2
demanded: the frozen structure has a model whose action is not `g ↦ 1`. -/
theorem regularRep_translation_ne_one :
    regularRep ⟨EuclideanSpace.single 1 1, 1⟩ ≠ 1 := by
  intro h
  set b : M4 := EuclideanSpace.single 1 1 with hb
  have hnorm : ‖b‖ = 1 :=
    (PiLp.norm_single 2 (fun _ : Fin 4 => ℝ) 1 (1 : ℝ)).trans norm_one
  have hCLM : (regularRep (⟨b, 1⟩ : PoincareGroup) : L2M4 →L[ℂ] L2M4)
      = (1 : L2M4 →L[ℂ] L2M4) := congrArg Subtype.val h
  have happ : Lp.compMeasurePreserving (fun x : M4 => (⟨b, 1⟩ : PoincareGroup)⁻¹ • x)
      (PoincareGroup.volume_preserving_smul (⟨b, 1⟩ : PoincareGroup)⁻¹)
      (ballIndicator 0) = ballIndicator 0 := by
    have hval := congrArg (fun T : L2M4 →L[ℂ] L2M4 => T (ballIndicator 0)) hCLM
    simpa only [one_apply_eq_self, regularRep_apply] using hval
  rw [show ballIndicator 0
      = indicatorConstLp 2 (measurableSet_ball (x := (0 : M4)) (ε := 1/2))
        measure_ball_lt_top.ne (1 : ℂ) from rfl,
    Lp.indicatorConstLp_compMeasurePreserving] at happ
  have hL := indicatorConstLp_coeFn (μ := (volume : Measure M4)) (p := (2 : ℝ≥0∞))
    (hs := (measurableSet_ball (x := (0 : M4)) (ε := 1/2)).preimage
      (PoincareGroup.volume_preserving_smul (⟨b, 1⟩ : PoincareGroup)⁻¹).measurable)
    (hμs := by
      rw [(PoincareGroup.volume_preserving_smul
        (⟨b, 1⟩ : PoincareGroup)⁻¹).measure_preimage
        measurableSet_ball.nullMeasurableSet]
      exact measure_ball_lt_top.ne)
    (c := (1 : ℂ))
  have hR := indicatorConstLp_coeFn (μ := (volume : Measure M4)) (p := (2 : ℝ≥0∞))
    (hs := measurableSet_ball (x := (0 : M4)) (ε := 1/2))
    (hμs := measure_ball_lt_top.ne) (c := (1 : ℂ))
  rw [happ] at hL
  have hae : ((fun x : M4 => (⟨b, 1⟩ : PoincareGroup)⁻¹ • x)
        ⁻¹' Metric.ball 0 (1/2)).indicator (fun _ => (1 : ℂ))
      =ᵐ[volume] (Metric.ball (0 : M4) (1/2)).indicator (fun _ => (1 : ℂ)) :=
    hL.symm.trans hR
  rw [PoincareGroup.translation_preimage_ball] at hae
  have hnull : volume {x : M4 |
      ¬ ((Metric.ball b (1/2)).indicator (fun _ => (1 : ℂ)) x
        = (Metric.ball (0 : M4) (1/2)).indicator (fun _ => (1 : ℂ)) x)} = 0 :=
    ae_iff.mp hae
  have hsub : Metric.ball b (1/2) ⊆ {x : M4 |
      ¬ ((Metric.ball b (1/2)).indicator (fun _ => (1 : ℂ)) x
        = (Metric.ball (0 : M4) (1/2)).indicator (fun _ => (1 : ℂ)) x)} := by
    intro x hx
    have hx0 : x ∉ Metric.ball (0 : M4) (1/2) := by
      intro hx0
      have h1 : dist b (0 : M4) = 1 := by rw [dist_zero_right]; exact hnorm
      have h2 : dist b x < 1/2 := by rw [dist_comm]; exact Metric.mem_ball.mp hx
      have h3 : dist x (0 : M4) < 1/2 := Metric.mem_ball.mp hx0
      have h4 := dist_triangle b x (0 : M4)
      rw [h1] at h4
      linarith
    simp only [Set.mem_setOf_eq, Set.indicator_of_mem hx, Set.indicator_of_notMem hx0]
    exact one_ne_zero
  exact absurd (measure_mono_null hsub hnull)
    (Metric.measure_ball_pos volume b (by norm_num : (0 : ℝ) < 1/2)).ne'

/-- **Expected false**: the regular representation is not the trivial one — the frozen
structure has at least two models, one of them with nontrivial action. -/
theorem regularRep_ne_trivialRep : regularRep ≠ trivialRep L2M4 := fun h =>
  regularRep_translation_ne_one (by rw [h, trivialRep_apply])

/-! ### Expected-true examples: the frozen API on the nontrivial model -/

/- The frozen `MonoidHomClass` surface and unitarity consequences engage on the
regular representation. -/
example (g₁ g₂ : PoincareGroup) :
    regularRep (g₁ * g₂) = regularRep g₁ * regularRep g₂ :=
  map_mul regularRep g₁ g₂

example (g : PoincareGroup) : regularRep g⁻¹ = (regularRep g)⁻¹ :=
  map_inv regularRep g

example (g : PoincareGroup) (ψ : L2M4) :
    ‖(regularRep g : L2M4 →L[ℂ] L2M4) ψ‖ = ‖ψ‖ :=
  Unitary.norm_map (regularRep g) ψ

/- The frozen joint continuity and its per-vector consequence apply. -/
example : Continuous fun p : PoincareGroup × L2M4 =>
    (regularRep p.1 : L2M4 →L[ℂ] L2M4) p.2 :=
  regularRep.continuous_apply₂

example (ψ : L2M4) :
    Continuous fun g : PoincareGroup => (regularRep g : L2M4 →L[ℂ] L2M4) ψ :=
  regularRep.continuous_apply ψ

/- **The Stone-bridge pin**: the anchor `translationGroup` evaluated on the regular
representation is, at direction `a` and time `t`, the pure translation by `t • a` —
on representatives, `ψ ↦ ψ(· − t • a)` a.e.: the canonical strongly continuous
translation group of `L²` (Reed & Simon I §VIII.4), now with a nontrivial generator
lane for P2.5 to name. -/
example (a : M4) (t : ℝ) :
    regularRep.translationGroup a t = regularRep ⟨t • a, 1⟩ :=
  regularRep.translationGroup_apply a t

example (a : M4) (t : ℝ) (ψ : L2M4) :
    ⇑((regularRep.translationGroup a t : L2M4 →L[ℂ] L2M4) ψ)
      =ᵐ[volume] fun x => ψ (x - t • a) := by
  rw [regularRep.translationGroup_apply]
  exact regularRep_translation_coeFn (t • a) ψ

end Witnesses

end

end Spacetime.Minkowski
