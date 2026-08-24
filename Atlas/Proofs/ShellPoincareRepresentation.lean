import Atlas.Proofs.MassShellMeasurePreserving
import Atlas.Proofs.PoincareTopology
import Atlas.Specs.Spacetime.PoincareRep

/-!
# P2.6b — the Wigner one-particle representation of the restricted Poincaré group

Closing module of the momentum-measure node (**P2.6b**). `Atlas.Proofs.ShellOneParticle`
built the Wigner action `shellPoincare m g hg` *conditionally* on the H1 hypothesis
`LorentzShellPreserves m g.lorentz`, and `Atlas.Proofs.MassShellMeasurePreserving`
discharged that hypothesis for every restricted Lorentz transformation and every physical
mass `0 < m` (`lorentzShellPreserves`). This module removes the hypothesis from the
representation theory and lands the frozen P2.4b structure.

## Contents

* `QFT.KleinGordon.shellPoincareUnitary m hm g` — the **Wigner operator**
  `(U(a, Λ)ψ)(q) = 𝐞(-η(a, q)) · ψ(Λ⁻¹ q)` of `g = ⟨a, Λ⟩`, with the exact a.e. pointwise
  formula (`coeFn_shellPoincareUnitary`), the identity law, the composition law in the
  frozen semidirect order (`shellPoincareUnitary_mul`), the inverse law, unitarity
  (`inner_shellPoincareUnitary`, `norm_shellPoincareUnitary`), and the identification of
  the translation subgroup with `shellTranslate`.
* `QFT.KleinGordon.shellPoincareHom m hm` — the same data as a group homomorphism
  `PoincareGroup →* (ShellOneParticle m ≃ₗᵢ[ℂ] ShellOneParticle m)`.
* `QFT.KleinGordon.shellPoincareRep m hm` — **H3**: the frozen P2.4b structure
  `Spacetime.Minkowski.PoincareRep (ShellOneParticle m)`, i.e. the homomorphism into
  `unitary (ShellOneParticle m →L[ℂ] ShellOneParticle m)` together with joint strong
  continuity of the action map `(g, ψ) ↦ U(g)ψ`.
* Regularity of the shell measure for a physical mass — the analytic input of H3:
  `isFiniteMeasureOnCompacts_massShellMeasure`, `isLocallyFiniteMeasure_massShellMeasure`,
  `innerRegularCompactLTTop_massShellMeasure`.

## The composition law

For `g₁ = ⟨a₁, Λ₁⟩`, `g₂ = ⟨a₂, Λ₂⟩` the frozen P2.4a law is
`g₁g₂ = ⟨a₁ + Λ₁a₂, Λ₁Λ₂⟩`, so

`(U(g₁g₂)ψ)(q) = 𝐞(-η(a₁ + Λ₁a₂, q)) · ψ(Λ₂⁻¹Λ₁⁻¹q)`,
`(U(g₁)U(g₂)ψ)(q) = 𝐞(-η(a₁, q)) · 𝐞(-η(a₂, Λ₁⁻¹q)) · ψ(Λ₂⁻¹Λ₁⁻¹q)`,

and the two agree by additivity of the character (`translationChar_add`) together with the
**cocycle identity** `η(a₂, Λ₁⁻¹q) = η(Λ₁a₂, q)`, which is form preservation of `Λ₁` read
across the pairing (`translationChar_lorentz_transfer`). No new analysis enters: the
semidirect twist is exactly absorbed by the Lorentz invariance of `η`.

## H3 — joint strong continuity, and what makes it work

The frozen P2.4b field is joint continuity of `(g, ψ) ↦ U(g)ψ` in the product of the
P2.4a topology and the `L²`-norm topology. It is assembled from two halves of a factored
operator, `U(⟨a, Λ⟩) = M(𝐞(-η(a, ·))) ∘ P(Λ)`:

* the **multiplier half** is jointly continuous by the epsilon-free dominated-convergence
  argument of `Atlas.Proofs.ShellOneParticle` (`continuous_shellTranslate`, dominator
  `4‖ψ‖²`) upgraded from per-vector to joint continuity by Mathlib's
  `continuous_prod_of_continuous_lipschitzWith'`, the uniform Lipschitz constant being
  `1` because every `U(g)` is an isometry. This is the "per-vector ⟹ joint" smart
  constructor that the frozen spec's docstring defers to a proof node; no density
  argument is used.
* the **pullback half** `P(Λ)ψ = ψ ∘ Λ⁻¹` is jointly continuous by Mathlib's
  `Continuous.compMeasurePreservingLp`, whose hypotheses are met here for a physical mass:
  `massShellMeasure m` is inner regular for finite-measure sets with respect to compact
  sets, and locally finite. Both follow from finiteness on compact sets, which is the
  only genuinely new measure-theoretic fact needed: for compact `K ⊆ M4`,
  `massShellParam m ⁻¹' K ⊆ spatialOf '' K`, and the weight is bounded by
  `1/(2m)` there.
  Finiteness on compacts gives local finiteness (`M4` is locally compact), hence
  σ-finiteness (`M4` is second countable), hence inner regularity (`M4` is σ-compact and
  metrizable) — Mathlib's instance chain in `Mathlib/MeasureTheory/Measure/Regular.lean`.

The Lorentz half is where the mass is load-bearing twice: `0 < m` bounds the weight, and
`0 < m` is what `lorentzShellPreserves` needs. Continuity of `Λ ↦ Λ⁻¹` on the frozen
operator-norm topology is `Atlas.Proofs.PoincareTopology`.

No density of continuous compactly supported representatives is needed anywhere: the
multiplier half runs on domination, and Mathlib's pullback theorem runs on the
unconditional simple-function density together with continuity of
`Λ ↦ μ((Λ⁻¹ ⁻¹' s) ∆ (Λ₀⁻¹ ⁻¹' s))` at `Λ₀`, which is exactly what the two measure
hypotheses above buy. The `Cc`-density route of the classical texts is therefore not on
the critical path, and `Isometry.tendsto_of_dense` is not used.

## Sources

* E. P. Wigner, *On Unitary Representations of the Inhomogeneous Lorentz Group*, Annals of
  Mathematics 40 (1939), §6 — the one-particle representation carried by wave functions on
  the mass hyperboloid, with the plane-wave translation factor and the invariant scalar
  product; cited at section level, matching `Atlas/Proofs/MassShellMeasure.lean`.
* S. Weinberg, *The Quantum Theory of Fields*, Vol. I (1995), §2.3 — the Poincaré
  composition law realized here in the frozen P2.4a order, and §2.5 for the one-particle
  orbits; section level.
* R. F. Streater, A. S. Wightman, *PCT, Spin and Statistics, and All That* (1964;
  Princeton Landmarks ed. 2000), Ch. 1 — states carry a continuous unitary representation
  of `P↑₊`, the form of continuity frozen in P2.4b; chapter level.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I* (1980), §VIII.4 —
  strongly continuous unitary groups, the form the translation lines of this
  representation take through the frozen `PoincareRep.translationGroup` anchor; section
  level.
* Mathlib v4.31 sources, verified in-tree:
  `Mathlib/MeasureTheory/Function/LpSpace/ContinuousCompMeasurePreserving.lean`
  (`Continuous.compMeasurePreservingLp`),
  `Mathlib/MeasureTheory/Measure/Regular.lean` (the `InnerRegular` /
  `InnerRegularCompactLTTop` instance chain),
  `Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
  (`isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`),
  `Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean` (`sigmaFinite_of_locallyFinite`),
  `Mathlib/Topology/EMetricSpace/Lipschitz.lean`
  (`continuous_prod_of_continuous_lipschitzWith'`),
  `Mathlib/Analysis/InnerProductSpace/Adjoint.lean` (`Unitary.linearIsometryEquiv`).
-/

noncomputable section

open MeasureTheory Real Spacetime.Minkowski Filter
open scoped ENNReal Topology

namespace QFT.KleinGordon

variable {m : ℝ}

/-! ### Regularity of the shell measure for a physical mass

The analytic input of H3. Everything here is about `massShellMeasure m` alone; the group
plays no role yet. -/

/-- The mass bounds the energy from below: `m ≤ ω_p = √(‖p‖² + m²)`. -/
theorem le_physicalEnergy (hm : 0 < m) (p : M3) : m ≤ physicalEnergy m p := by
  refine le_of_not_gt fun hcon => ?_
  have hE : 0 ≤ physicalEnergy m p := physicalEnergy_nonneg m p
  have hprod : 0 < (m - physicalEnergy m p) * (m + physicalEnergy m p) :=
    mul_pos (by linarith) (by linarith)
  have hsq := physicalEnergy_sq m p
  nlinarith [sq_nonneg ‖p‖]

/-- **Uniform bound on the shell weight**: for a physical mass the invariant weight
`1/(2ω_p)` is bounded by `1/(2m)`. This is what makes the non-normalizable measure
`d³p/(2ω_p)` finite on compact sets. -/
theorem massShellDensity_le (hm : 0 < m) (p : M3) :
    massShellDensity m p ≤ ENNReal.ofReal (1 / (2 * m)) := by
  simp only [massShellDensity]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := le_physicalEnergy hm p
  exact one_div_le_one_div_of_le (by linarith) (by linarith)


/-- Preimages under the shell parametrization lie in the image of the public
spatial projection. -/
private theorem preimage_massShellParam_subset (m : ℝ) (K : Set M4) :
    massShellParam m ⁻¹' K ⊆ spatialOf '' K :=
  fun p hp => ⟨massShellParam m p, hp, spatialOf_massShellParam m p⟩

/-- **The shell measure is finite on compact sets** for positive mass: the
preimage lies in compact `spatialOf '' K`, and the weight is bounded by
`1/(2m)` (Wigner 1939, §6, eq. (59a)). -/
theorem isFiniteMeasureOnCompacts_massShellMeasure (hm : 0 < m) :
    IsFiniteMeasureOnCompacts (massShellMeasure m) := by
  refine ⟨fun K hK => ?_⟩
  have hKm : MeasurableSet K := hK.measurableSet
  have himg : IsCompact (spatialOf '' K) := hK.image spatialOf_continuous
  rw [massShellMeasure_apply m hKm,
    withDensity_apply _ (measurable_massShellParam m hKm)]
  calc ∫⁻ p in massShellParam m ⁻¹' K, massShellDensity m p
      ≤ ∫⁻ p in spatialOf '' K, massShellDensity m p :=
        lintegral_mono_set (preimage_massShellParam_subset m K)
    _ ≤ ∫⁻ _ in spatialOf '' K, ENNReal.ofReal (1 / (2 * m)) :=
        lintegral_mono fun p => massShellDensity_le hm p
    _ = ENNReal.ofReal (1 / (2 * m)) * volume (spatialOf '' K) :=
        setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top himg.measure_lt_top

/-- The shell measure is locally finite: `M4` is locally compact, so finiteness on compact
sets suffices. This is the hypothesis Mathlib's joint-continuity theorem puts on the
*target* measure. -/
theorem isLocallyFiniteMeasure_massShellMeasure (hm : 0 < m) :
    IsLocallyFiniteMeasure (massShellMeasure m) :=
  haveI := isFiniteMeasureOnCompacts_massShellMeasure hm
  inferInstance

/-- The shell measure is inner regular for finite-measure sets with respect to compact
sets. This is the hypothesis Mathlib's joint-continuity theorem puts on the *source*
measure; it follows from finiteness on compacts through Mathlib's instance chain
(locally finite, hence σ-finite on a second-countable space, hence inner regular on a
σ-compact metrizable Borel space). -/
theorem innerRegularCompactLTTop_massShellMeasure (hm : 0 < m) :
    (massShellMeasure m).InnerRegularCompactLTTop :=
  haveI := isFiniteMeasureOnCompacts_massShellMeasure hm
  inferInstance

/-! ### The Wigner operator, unconditionally -/

/-- **The Wigner one-particle representation operator** of the restricted Poincaré group on
the mass-`m` shell: `(U(a, Λ)ψ)(q) = 𝐞(-η(a, q)) · ψ(Λ⁻¹ q)`. This is the conditional
action `shellPoincare` of `Atlas.Proofs.ShellOneParticle` instantiated at the H1 theorem
`lorentzShellPreserves hm g.lorentz` of `Atlas.Proofs.MassShellMeasurePreserving`: for a
physical mass `0 < m` no hypothesis is left (Wigner 1939, §6). -/
def shellPoincareUnitary (m : ℝ) (hm : 0 < m) (g : PoincareGroup) :
    ShellOneParticle m ≃ₗᵢ[ℂ] ShellOneParticle m :=
  shellPoincare m g (lorentzShellPreserves hm g.lorentz)

/-- **The exact a.e. Wigner formula**: `(U(g)ψ)(q) = 𝐞(-η(a, q)) · ψ(Λ⁻¹ q)` almost
everywhere on the shell (Wigner 1939, §6). -/
theorem coeFn_shellPoincareUnitary (hm : 0 < m) (g : PoincareGroup)
    (ψ : ShellOneParticle m) :
    ((shellPoincareUnitary m hm g ψ : ShellOneParticle m) : M4 → ℂ)
      =ᵐ[massShellMeasure m] fun q => translationChar g.translation q
        * (ψ : M4 → ℂ) (((g.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q) :=
  coeFn_shellPoincare m g (lorentzShellPreserves hm g.lorentz) ψ

/-- On the translation subgroup the Wigner operator is the multiplier representation of
`Atlas.Proofs.ShellOneParticle`. -/
theorem shellPoincareUnitary_translation (hm : 0 < m) (a : M4) :
    shellPoincareUnitary m hm ⟨a, 1⟩ = shellTranslate m a :=
  shellPoincare_translation m a _

/-- **Identity law**. -/
@[simp]
theorem shellPoincareUnitary_one (hm : 0 < m) : shellPoincareUnitary m hm 1 = 1 :=
  (shellPoincareUnitary_translation hm 0).trans (shellTranslate_zero m)

/-- The inverse of a product of restricted Lorentz transformations, applied to a point:
`(Λ₁Λ₂)⁻¹q = Λ₂⁻¹(Λ₁⁻¹q)`. -/
private theorem lorentz_inv_mul_apply (Λ₁ Λ₂ : RestrictedLorentzGroup) (q : M4) :
    (((Λ₁ * Λ₂)⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q
      = ((Λ₂⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4)
          (((Λ₁⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q) := by
  rw [mul_inv_rev]
  rfl

/-- **The cocycle identity**, in character form: `𝐞(-η(Λa, q)) = 𝐞(-η(a, Λ⁻¹q))`. This is
form preservation of `Λ` read across the pairing; it is exactly the semidirect twist of the
frozen P2.4a composition law `⟨a₁, Λ₁⟩⟨a₂, Λ₂⟩ = ⟨a₁ + Λ₁a₂, Λ₁Λ₂⟩`. -/
theorem translationChar_lorentz_cocycle (Λ : RestrictedLorentzGroup) (a q : M4) :
    translationChar ((Λ : M4 ≃L[ℝ] M4) a) q
      = translationChar a (((Λ⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q) := by
  have h := translationChar_lorentz_transfer Λ⁻¹ a q
  rwa [inv_inv] at h

/-- **Composition law in the frozen semidirect order**: `U(g₁g₂) = U(g₁)U(g₂)` for
`⟨a₁, Λ₁⟩⟨a₂, Λ₂⟩ = ⟨a₁ + Λ₁a₂, Λ₁Λ₂⟩` (Weinberg I, §2.3; the law itself is frozen in
P2.4a). The character factorizes by `translationChar_add`, and the mismatch
`𝐞(-η(Λ₁a₂, q))` versus `𝐞(-η(a₂, Λ₁⁻¹q))` is closed by the cocycle identity. -/
theorem shellPoincareUnitary_mul (hm : 0 < m) (g₁ g₂ : PoincareGroup) :
    shellPoincareUnitary m hm (g₁ * g₂)
      = shellPoincareUnitary m hm g₁ * shellPoincareUnitary m hm g₂ := by
  refine LinearIsometryEquiv.ext fun ψ => ?_
  show shellPoincareUnitary m hm (g₁ * g₂) ψ
    = shellPoincareUnitary m hm g₁ (shellPoincareUnitary m hm g₂ ψ)
  refine Lp.ext ?_
  have hmp : MeasurePreserving
      (fun q : M4 => ((g₁.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q)
      (massShellMeasure m) (massShellMeasure m) :=
    lorentzShellPreserves hm g₁.lorentz⁻¹
  have hinner :
      (fun q : M4 => ((shellPoincareUnitary m hm g₂ ψ : ShellOneParticle m) : M4 → ℂ)
          (((g₁.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q))
        =ᵐ[massShellMeasure m]
          (fun r : M4 => translationChar g₂.translation r
            * (ψ : M4 → ℂ) (((g₂.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) r))
            ∘ fun q : M4 => ((g₁.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q := by
    refine ae_eq_comp hmp.measurable.aemeasurable ?_
    rw [hmp.map_eq]
    exact coeFn_shellPoincareUnitary hm g₂ ψ
  filter_upwards [coeFn_shellPoincareUnitary hm (g₁ * g₂) ψ,
    coeFn_shellPoincareUnitary hm g₁ (shellPoincareUnitary m hm g₂ ψ), hinner]
    with q h1 h2 h3
  calc ((shellPoincareUnitary m hm (g₁ * g₂) ψ : ShellOneParticle m) : M4 → ℂ) q
      = translationChar (g₁ * g₂).translation q
          * (ψ : M4 → ℂ)
            ((((g₁ * g₂).lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q) := h1
    _ = translationChar g₁.translation q
          * (translationChar g₂.translation
                (((g₁.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q)
              * (ψ : M4 → ℂ) (((g₂.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4)
                  (((g₁.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q))) := by
        rw [PoincareGroup.mul_translation, translationChar_add,
          translationChar_lorentz_cocycle, PoincareGroup.mul_lorentz,
          lorentz_inv_mul_apply, mul_assoc]
    _ = translationChar g₁.translation q
          * ((shellPoincareUnitary m hm g₂ ψ : ShellOneParticle m) : M4 → ℂ)
            (((g₁.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q) := by
        rw [h3]
        rfl
    _ = ((shellPoincareUnitary m hm g₁ (shellPoincareUnitary m hm g₂ ψ) :
            ShellOneParticle m) : M4 → ℂ) q := h2.symm

/-- **Inverse law**: `U(g)⁻¹ = U(g⁻¹)` with `g⁻¹ = ⟨-Λ⁻¹a, Λ⁻¹⟩` the frozen semidirect
inverse. -/
theorem shellPoincareUnitary_symm (hm : 0 < m) (g : PoincareGroup) :
    (shellPoincareUnitary m hm g).symm = shellPoincareUnitary m hm g⁻¹ :=
  shellPoincare_symm m g (lorentzShellPreserves hm g.lorentz)

/-- **Unitarity**: the one-particle inner product of Wigner's invariant scalar product is
preserved (Wigner 1939, §6). -/
theorem inner_shellPoincareUnitary (hm : 0 < m) (g : PoincareGroup)
    (ψ φ : ShellOneParticle m) :
    inner ℂ (shellPoincareUnitary m hm g ψ) (shellPoincareUnitary m hm g φ) = inner ℂ ψ φ :=
  (shellPoincareUnitary m hm g).inner_map_map ψ φ

@[simp]
theorem norm_shellPoincareUnitary (hm : 0 < m) (g : PoincareGroup) (ψ : ShellOneParticle m) :
    ‖shellPoincareUnitary m hm g ψ‖ = ‖ψ‖ :=
  (shellPoincareUnitary m hm g).norm_map ψ

/-- **The one-particle representation as a group homomorphism** into the isometry group of
the shell Hilbert space (Wigner 1939, §6; the composition law is the frozen P2.4a one). -/
def shellPoincareHom (m : ℝ) (hm : 0 < m) :
    PoincareGroup →* (ShellOneParticle m ≃ₗᵢ[ℂ] ShellOneParticle m) where
  toFun := shellPoincareUnitary m hm
  map_one' := shellPoincareUnitary_one hm
  map_mul' := shellPoincareUnitary_mul hm

@[simp]
theorem shellPoincareHom_apply (hm : 0 < m) (g : PoincareGroup) :
    shellPoincareHom m hm g = shellPoincareUnitary m hm g := rfl

/-! ### H3 — joint strong continuity -/

/-- The inverse Lorentz transformation as a bundled continuous self-map of the carrier: the
point transformation `q ↦ Λ⁻¹q` of the Wigner formula, in the shape consumed by
`Continuous.compMeasurePreservingLp`. -/
def lorentzInvCM (Λ : RestrictedLorentzGroup) : C(M4, M4) :=
  ⟨fun q => ((Λ⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q,
    ((Λ⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4).continuous⟩

@[simp]
theorem lorentzInvCM_apply (Λ : RestrictedLorentzGroup) (q : M4) :
    lorentzInvCM Λ q = ((Λ⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q := rfl

/-- The inverse Lorentz point transformation preserves the shell measure — H1 at `Λ⁻¹`. -/
theorem measurePreserving_lorentzInvCM (hm : 0 < m) (Λ : RestrictedLorentzGroup) :
    MeasurePreserving (lorentzInvCM Λ) (massShellMeasure m) (massShellMeasure m) :=
  lorentzShellPreserves hm Λ⁻¹

/-- `Λ ↦ (q ↦ Λ⁻¹q)` is continuous into the compact-open topology: operator application is
a bounded bilinear map, and inversion is continuous on the frozen P2.4a topology
(`Atlas.Proofs.PoincareTopology`). -/
theorem continuous_lorentzInvCM : Continuous lorentzInvCM := by
  refine ContinuousMap.continuous_of_continuous_uncurry lorentzInvCM ?_
  have h : (Function.uncurry fun (Λ : RestrictedLorentzGroup) (q : M4) => lorentzInvCM Λ q)
      = fun p : RestrictedLorentzGroup × M4 =>
        (((p.1⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) : M4 →L[ℝ] M4) p.2 := rfl
  rw [h]
  exact isBoundedBilinearMap_apply.continuous.comp
    ((RestrictedLorentzGroup.continuous_coe.comp
      (continuous_inv.comp continuous_fst)).prodMk continuous_snd)

/-- **The multiplier half of H3, jointly**: `(a, ψ) ↦ 𝐞(-η(a, ·)) · ψ` is continuous in
both arguments. Per-vector continuity is the dominated-convergence theorem
`continuous_shellTranslate` of `Atlas.Proofs.ShellOneParticle`; the upgrade to joint
continuity needs only the uniform Lipschitz constant `1` coming from unitarity — the
"per-vector ⟹ joint" smart constructor deferred by the frozen P2.4b docstring. -/
theorem continuous_shellTranslate₂ (m : ℝ) :
    Continuous fun p : M4 × ShellOneParticle m => shellTranslate m p.1 p.2 :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun a => (shellTranslate m a).isometry.lipschitz)
    (fun ψ => continuous_shellTranslate m ψ)

/-- **The pullback half of H3, jointly**: `(g, ψ) ↦ ψ ∘ Λ(g)⁻¹` is continuous. This is
Mathlib's `Continuous.compMeasurePreservingLp`, whose measure hypotheses are supplied by
the regularity of the shell measure proven above. -/
theorem continuous_shellLorentzPullback (hm : 0 < m) :
    Continuous fun p : PoincareGroup × ShellOneParticle m =>
      Lp.compMeasurePreserving (lorentzInvCM p.1.lorentz)
        (measurePreserving_lorentzInvCM hm p.1.lorentz) p.2 := by
  haveI := innerRegularCompactLTTop_massShellMeasure hm
  haveI := isLocallyFiniteMeasure_massShellMeasure hm
  exact Continuous.compMeasurePreservingLp
    (f := fun p : PoincareGroup × ShellOneParticle m => p.2)
    (g := fun p : PoincareGroup × ShellOneParticle m => lorentzInvCM p.1.lorentz)
    continuous_snd
    (continuous_lorentzInvCM.comp (PoincareGroup.continuous_lorentz.comp continuous_fst))
    (fun p => measurePreserving_lorentzInvCM hm p.1.lorentz) (by norm_num)

/-- **Factorization of the Wigner operator**: pull back along `Λ⁻¹`, then multiply by the
translation character. Both factors are the two halves of the continuity argument. -/
theorem shellPoincareUnitary_apply (hm : 0 < m) (g : PoincareGroup) (ψ : ShellOneParticle m) :
    shellPoincareUnitary m hm g ψ
      = shellTranslate m g.translation
          (Lp.compMeasurePreserving (lorentzInvCM g.lorentz)
            (measurePreserving_lorentzInvCM hm g.lorentz) ψ) := rfl

/-- **H3, joint form** — the frozen P2.4b continuity field: the action map
`(g, ψ) ↦ U(g)ψ` is continuous for the product of the P2.4a topology on `P↑₊` and the
`L²`-norm topology on the one-particle space (Streater–Wightman, Ch. 1). -/
theorem continuous_shellPoincareUnitary₂ (hm : 0 < m) :
    Continuous fun p : PoincareGroup × ShellOneParticle m =>
      shellPoincareUnitary m hm p.1 p.2 := by
  have hfact : (fun p : PoincareGroup × ShellOneParticle m =>
        shellPoincareUnitary m hm p.1 p.2)
      = fun p : PoincareGroup × ShellOneParticle m =>
        shellTranslate m p.1.translation
          (Lp.compMeasurePreserving (lorentzInvCM p.1.lorentz)
            (measurePreserving_lorentzInvCM hm p.1.lorentz) p.2) :=
    funext fun p => shellPoincareUnitary_apply hm p.1 p.2
  rw [hfact]
  exact (continuous_shellTranslate₂ m).comp₂
    (PoincareGroup.continuous_translation.comp continuous_fst)
    (continuous_shellLorentzPullback hm)

/-- **H3, per-vector form**: every orbit map `g ↦ U(g)ψ` is norm-continuous (Reed & Simon I,
§VIII.4, for the one-parameter restrictions). -/
theorem continuous_shellPoincareUnitary (hm : 0 < m) (ψ : ShellOneParticle m) :
    Continuous fun g : PoincareGroup => shellPoincareUnitary m hm g ψ :=
  (continuous_shellPoincareUnitary₂ hm).comp₂ continuous_id continuous_const

/-! ### The frozen P2.4b package -/

/-- **The Wigner one-particle representation** of the restricted Poincaré group on the
mass-`m` shell, as the frozen P2.4b structure: a homomorphism into
`unitary (ShellOneParticle m →L[ℂ] ShellOneParticle m)` together with joint strong
continuity. For a physical mass `0 < m` nothing is assumed — H1 is
`lorentzShellPreserves`, H3 is `continuous_shellPoincareUnitary₂` (Wigner 1939, §6;
Streater–Wightman, Ch. 1). -/
def shellPoincareRep (m : ℝ) (hm : 0 < m) : PoincareRep (ShellOneParticle m) where
  toFun := (Unitary.linearIsometryEquiv.symm.toMonoidHom :
      (ShellOneParticle m ≃ₗᵢ[ℂ] ShellOneParticle m) →*
        unitary (ShellOneParticle m →L[ℂ] ShellOneParticle m)).comp (shellPoincareHom m hm)
  continuous_apply₂' := by
    show Continuous fun p : PoincareGroup × ShellOneParticle m =>
      shellPoincareUnitary m hm p.1 p.2
    exact continuous_shellPoincareUnitary₂ hm

@[simp]
theorem shellPoincareRep_apply (hm : 0 < m) (g : PoincareGroup) (ψ : ShellOneParticle m) :
    (shellPoincareRep m hm g : ShellOneParticle m →L[ℂ] ShellOneParticle m) ψ
      = shellPoincareUnitary m hm g ψ := rfl

/-- The a.e. Wigner formula, read off the packaged representation. -/
theorem coeFn_shellPoincareRep_apply (hm : 0 < m) (g : PoincareGroup)
    (ψ : ShellOneParticle m) :
    (((shellPoincareRep m hm g : ShellOneParticle m →L[ℂ] ShellOneParticle m) ψ :
        ShellOneParticle m) : M4 → ℂ)
      =ᵐ[massShellMeasure m] fun q => translationChar g.translation q
        * (ψ : M4 → ℂ) (((g.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) q) :=
  coeFn_shellPoincareUnitary hm g ψ

/-- **The Stone-bridge pin**: the frozen anchor `PoincareRep.translationGroup` evaluated on
this representation is, in direction `a` at time `t`, multiplication by the plane-wave
character of `t • a` — the strongly continuous one-parameter group whose Stone generator is
the energy-momentum component in direction `a` (Reed & Simon I, §VIII.4; naming the
generators is P2.5's business). -/
theorem shellPoincareRep_translationGroup_apply (hm : 0 < m) (a : M4) (t : ℝ)
    (ψ : ShellOneParticle m) :
    (((shellPoincareRep m hm).translationGroup a t :
        ShellOneParticle m →L[ℂ] ShellOneParticle m) ψ)
      = shellTranslate m (t • a) ψ := by
  rw [PoincareRep.translationGroup_apply, shellPoincareRep_apply,
    shellPoincareUnitary_translation]

/- Instance-transparency: the frozen `MonoidHomClass` surface and the frozen continuity
API engage on the one-particle model. -/
example (hm : 0 < m) (g₁ g₂ : PoincareGroup) :
    shellPoincareRep m hm (g₁ * g₂) = shellPoincareRep m hm g₁ * shellPoincareRep m hm g₂ :=
  map_mul (shellPoincareRep m hm) g₁ g₂

example (hm : 0 < m) (g : PoincareGroup) :
    shellPoincareRep m hm g⁻¹ = (shellPoincareRep m hm g)⁻¹ :=
  map_inv (shellPoincareRep m hm) g

example (hm : 0 < m) (ψ : ShellOneParticle m) :
    Continuous fun g : PoincareGroup =>
      (shellPoincareRep m hm g : ShellOneParticle m →L[ℂ] ShellOneParticle m) ψ :=
  (shellPoincareRep m hm).continuous_apply ψ

end QFT.KleinGordon

end
