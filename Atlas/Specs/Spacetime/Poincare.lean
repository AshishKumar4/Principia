import Atlas.Specs.Spacetime.Minkowski

/-!
# P2.4a — The restricted Lorentz group and the restricted Poincaré group

Frozen spec (blueprint node P2.4a): proof sessions must not edit this file; changes
require a spec review and a `[spec-review]` commit (see CLAUDE.md).

## Contents

* `Spacetime.Minkowski.RestrictedLorentzGroup` — the restricted (proper orthochronous)
  Lorentz group `L↑₊` as a `Subgroup (M4 ≃L[ℝ] M4)`: the continuous linear
  automorphisms of Minkowski space preserving `minkowskiForm`, of determinant `1`,
  mapping the future time direction forward. Orthochronous closure under composition
  and inversion is a genuine cone argument (`inFutureCausalCone_map`).
* `Spacetime.Minkowski.RestrictedLorentzGroup.map_inFutureCausalCone` /
  `map_inFutureTimeCone` / `map_massShell` — restricted Lorentz transformations
  preserve the future cones and the positive-energy mass shells.
* `Spacetime.Minkowski.PoincareGroup` — the restricted Poincaré group
  `P↑₊ = ℝ⁴ ⋊ L↑₊` as a hand-rolled semidirect structure (translation, Lorentz pair),
  with its `Group` instance, its affine `MulAction` on `M4`, and the product topology.

## Conventions

* An element of `L↑₊` is a continuous linear automorphism `Λ` of the concrete carrier
  `M4` (not a matrix): `η(Λv, Λw) = η(v, w)` for all `v w`, `det Λ = 1` (via
  `LinearMap.det` of the underlying linear automorphism), and `0 < (Λ e₀)⁰` for the
  future time basis vector `e₀ = EuclideanSpace.single 0 1`. The last condition is the
  matrix condition `Λ⁰₀ > 0` of Streater–Wightman §1-1 in basis-free form.
* Group law of `P↑₊`: `(a₁, Λ₁) * (a₂, Λ₂) = (a₁ + Λ₁ a₂, Λ₁ Λ₂)`, identity `(0, 1)`,
  inverse `(a, Λ)⁻¹ = (-Λ⁻¹ a, Λ⁻¹)`; the action on spacetime is `(a, Λ) • x = Λ x + a`
  (Streater–Wightman, §1-1; Weinberg, *The Quantum Theory of Fields* I, §2.3,
  eq. (2.3.11)). Mathlib's `SemidirectProduct` is deliberately not used: it would require
  packaging `L↑₊ →* MulAut M4` only to unpack it again in every statement, failing the
  deletion test (physlib's `EuclideanGroup` makes the same call).
* Mass shell: with the mostly-plus form, the mass-`m` positive-energy shell is
  `η(p, p) = -m²`, `p⁰ > 0` (the textbook `p² = m², p⁰ > 0` — mostly-minus there — of
  Streater–Wightman Ch. 1 and Weinberg I §2.5). For `m = 0` it is the punctured
  forward light cone.
* Topology: `RestrictedLorentzGroup` carries the topology induced by the inclusion
  into `M4 →L[ℝ] M4` (the operator-norm topology — in finite dimension the unique
  Hausdorff linear topology), and `PoincareGroup` the product topology of
  `M4 × RestrictedLorentzGroup`. This is the standard topology of `P↑₊`; strong
  continuity of representations (P2.4b) is stated against it.
* The action on Schwartz functions (needed for covariant fields) is DEFERRED to the
  P2.5a utilities node, per the P2.4/P2.5/P2.6 design dossier.

## Sources

* Streater & Wightman, *PCT, Spin and Statistics, and All That* (1964; Princeton
  Landmarks ed. 2000), §1-1 (Lorentz and Poincaré groups, `L↑₊`, composition law) and
  Ch. 1 passim (mass shells, cone geometry).
* Weinberg, *The Quantum Theory of Fields*, Vol. I (1995), §2.3 (Poincaré group
  conventions, composition law eq. (2.3.11), orthochronous/proper components),
  §2.5 (mass shells / one-particle orbits).
* O'Neill, *Semi-Riemannian Geometry with Applications to Relativity* (1983), Ch. 5
  (time-cone facts powering orthochronous closure).
-/

namespace Spacetime.Minkowski

variable {Λ : M4 ≃L[ℝ] M4} {v w p : M4}

/- Application unfolding for the automorphism group of `M4 ≃L[ℝ] M4`; both are `rfl`
(upstream candidates: Mathlib's `ContinuousLinearEquiv.automorphismGroup` has no
`one_apply`/`mul_apply` lemmas at v4.31.0). -/

private theorem clm_one_apply (x : M4) : (1 : M4 ≃L[ℝ] M4) x = x := rfl

private theorem clm_mul_apply (e f : M4 ≃L[ℝ] M4) (x : M4) : (e * f) x = e (f x) := rfl

/-! ### Cone preservation for form-preserving orthochronous automorphisms

These are stated for a raw automorphism with the form-preservation and orthochronicity
hypotheses (rather than for group members) because they are the engine of the
`Subgroup` closure proofs below. -/

/-- A form-preserving orthochronous automorphism sends the future time basis vector
into the open future time cone. -/
theorem inFutureTimeCone_map_single
    (hform : ∀ v w, minkowskiForm (Λ v) (Λ w) = minkowskiForm v w)
    (horth : 0 < Λ (EuclideanSpace.single 0 1) 0) :
    InFutureTimeCone (Λ (EuclideanSpace.single 0 1)) := by
  refine (inFutureTimeCone_iff_form _).2 ⟨?_, horth⟩
  rw [hform, minkowskiForm_single_zero_left]
  simp

/-- **Cone preservation**: a form-preserving orthochronous automorphism maps the future
causal cone into itself (O'Neill, *Semi-Riemannian Geometry*, Ch. 5: a causal vector
lies in the future cone iff it pairs negatively with a fixed future timelike vector;
here the pairing partner is `Λ e₀`). The engine of orthochronous closure. -/
theorem inFutureCausalCone_map
    (hform : ∀ v w, minkowskiForm (Λ v) (Λ w) = minkowskiForm v w)
    (horth : 0 < Λ (EuclideanSpace.single 0 1) 0)
    (hv : InFutureCausalCone v) : InFutureCausalCone (Λ v) := by
  obtain ⟨hvf, hv0⟩ := (inFutureCausalCone_iff_form v).1 hv
  have hne : Λ v ≠ 0 := fun h => by
    rw [Λ.map_eq_zero_iff.1 h] at hv0
    simp at hv0
  have hΛf : minkowskiForm (Λ v) (Λ v) ≤ 0 := by rw [hform]; exact hvf
  have htri : InFutureCausalCone (Λ v) ∨ InFutureCausalCone (-(Λ v)) := by
    by_contra hcon
    push Not at hcon
    exact absurd hΛf (not_le.2
      ((isSpacelike_iff_not_inFutureCausalCone (Λ v)).2 ⟨hne, hcon.1, hcon.2⟩))
  rcases htri with h | h
  · exact h
  · exfalso
    have hpair := (inFutureTimeCone_map_single hform horth).form_lt_zero h
    rw [map_neg, hform, minkowskiForm_single_zero_left] at hpair
    linarith

/-- Strict version: the open future time cone is preserved. -/
theorem inFutureTimeCone_map
    (hform : ∀ v w, minkowskiForm (Λ v) (Λ w) = minkowskiForm v w)
    (horth : 0 < Λ (EuclideanSpace.single 0 1) 0)
    (hv : InFutureTimeCone v) : InFutureTimeCone (Λ v) := by
  obtain ⟨hvf, hv0⟩ := (inFutureTimeCone_iff_form v).1 hv
  refine (inFutureTimeCone_iff_form _).2 ⟨by rw [hform]; exact hvf, ?_⟩
  exact (inFutureCausalCone_map hform horth hv.inFutureCausalCone).2

/-! ### The restricted Lorentz group -/

/-- The restricted (proper orthochronous) Lorentz group `L↑₊` of Minkowski space, as a
subgroup of the continuous linear automorphisms of the carrier: the `Λ` preserving the
Minkowski form, of determinant `1`, and orthochronous (`0 < (Λ e₀)⁰`, the basis-free
`Λ⁰₀ > 0` of Streater–Wightman §1-1). Form and determinant closure are algebra;
orthochronous closure under composition and inversion is the cone argument
`inFutureCausalCone_map`. -/
def RestrictedLorentzGroup : Subgroup (M4 ≃L[ℝ] M4) where
  carrier := {Λ | (∀ v w, minkowskiForm (Λ v) (Λ w) = minkowskiForm v w) ∧
    LinearMap.det (Λ.toLinearEquiv : M4 →ₗ[ℝ] M4) = 1 ∧
    0 < Λ (EuclideanSpace.single 0 1) 0}
  one_mem' := by
    refine ⟨fun v w => rfl, ?_, ?_⟩
    · have h : ((1 : M4 ≃L[ℝ] M4).toLinearEquiv : M4 →ₗ[ℝ] M4) = LinearMap.id := rfl
      rw [h, LinearMap.det_id]
    · rw [clm_one_apply]
      simp
  mul_mem' := by
    rintro a b ⟨haf, had, hao⟩ ⟨hbf, hbd, hbo⟩
    refine ⟨fun v w => ?_, ?_, ?_⟩
    · show minkowskiForm (a (b v)) (a (b w)) = minkowskiForm v w
      rw [haf, hbf]
    · have h : ((a * b).toLinearEquiv : M4 →ₗ[ℝ] M4)
          = (a.toLinearEquiv : M4 →ₗ[ℝ] M4).comp (b.toLinearEquiv : M4 →ₗ[ℝ] M4) := rfl
      rw [h, LinearMap.det_comp, had, hbd, one_mul]
    · show 0 < a (b (EuclideanSpace.single 0 1)) 0
      exact (inFutureCausalCone_map haf hao
        (inFutureTimeCone_map_single hbf hbo).inFutureCausalCone).2
  inv_mem' := by
    rintro a ⟨haf, had, hao⟩
    have haf' : ∀ v w, minkowskiForm (a.symm v) (a.symm w) = minkowskiForm v w := by
      intro v w
      conv_rhs => rw [← a.apply_symm_apply v, ← a.apply_symm_apply w, haf]
    refine ⟨haf', ?_, ?_⟩
    · have hcomp : ((a⁻¹).toLinearEquiv : M4 →ₗ[ℝ] M4).comp
          (a.toLinearEquiv : M4 →ₗ[ℝ] M4) = LinearMap.id :=
        LinearMap.ext fun x => a.symm_apply_apply x
      have h := congrArg LinearMap.det hcomp
      rwa [LinearMap.det_comp, had, mul_one, LinearMap.det_id] at h
    · show 0 < a.symm (EuclideanSpace.single 0 1) 0
      have hw : minkowskiForm (a.symm (EuclideanSpace.single 0 1))
          (a.symm (EuclideanSpace.single 0 1)) ≤ 0 := by
        rw [haf', minkowskiForm_single_zero_left]
        simp
      have hne : a.symm (EuclideanSpace.single 0 1) ≠ 0 := fun h => by
        have h0 := congrArg (fun z : M4 => z 0) (a.symm.map_eq_zero_iff.1 h)
        simp at h0
      have htri : InFutureCausalCone (a.symm (EuclideanSpace.single 0 1)) ∨
          InFutureCausalCone (-(a.symm (EuclideanSpace.single 0 1))) := by
        by_contra hcon
        push Not at hcon
        exact absurd hw (not_le.2
          ((isSpacelike_iff_not_inFutureCausalCone _).2 ⟨hne, hcon.1, hcon.2⟩))
      rcases htri with h | h
      · exact h.2
      · exfalso
        have hmap := inFutureCausalCone_map haf hao h
        rw [map_neg, a.apply_symm_apply] at hmap
        have h0 := hmap.2
        simp at h0
        linarith

namespace RestrictedLorentzGroup

theorem form_preserving (Λ : RestrictedLorentzGroup) (v w : M4) :
    minkowskiForm ((Λ : M4 ≃L[ℝ] M4) v) ((Λ : M4 ≃L[ℝ] M4) w) = minkowskiForm v w :=
  Λ.2.1 v w

theorem det_eq_one (Λ : RestrictedLorentzGroup) :
    LinearMap.det ((Λ : M4 ≃L[ℝ] M4).toLinearEquiv : M4 →ₗ[ℝ] M4) = 1 :=
  Λ.2.2.1

theorem orthochronous (Λ : RestrictedLorentzGroup) :
    0 < (Λ : M4 ≃L[ℝ] M4) (EuclideanSpace.single 0 1) 0 :=
  Λ.2.2.2

/-- Restricted Lorentz transformations preserve the future causal cone. -/
theorem map_inFutureCausalCone (Λ : RestrictedLorentzGroup)
    (hv : InFutureCausalCone v) : InFutureCausalCone ((Λ : M4 ≃L[ℝ] M4) v) :=
  inFutureCausalCone_map Λ.2.1 Λ.2.2.2 hv

/-- Restricted Lorentz transformations preserve the open future time cone. -/
theorem map_inFutureTimeCone (Λ : RestrictedLorentzGroup)
    (hv : InFutureTimeCone v) : InFutureTimeCone ((Λ : M4 ≃L[ℝ] M4) v) :=
  inFutureTimeCone_map Λ.2.1 Λ.2.2.2 hv

end RestrictedLorentzGroup

/-! ### Mass shells -/

/-- The mass-`m` positive-energy shell: `η(p, p) = -m²` and `p⁰ > 0` (the mostly-plus
form of `p² = m², p⁰ > 0`; Streater–Wightman, Ch. 1; Weinberg I, §2.5). For `m = 0`
this is the punctured forward light cone; the spectrum condition and the free-field
one-particle space (P2.5/P2.6) live on these sets. -/
def massShell (m : ℝ) : Set M4 :=
  {p | minkowskiForm p p = -(m ^ 2) ∧ 0 < p 0}

/-- Restricted Lorentz transformations preserve every positive-energy mass shell. -/
theorem RestrictedLorentzGroup.map_massShell (Λ : RestrictedLorentzGroup) {m : ℝ}
    (hp : p ∈ massShell m) : (Λ : M4 ≃L[ℝ] M4) p ∈ massShell m := by
  obtain ⟨hpf, hp0⟩ := hp
  refine ⟨by rw [RestrictedLorentzGroup.form_preserving]; exact hpf, ?_⟩
  have hcone : InFutureCausalCone p :=
    (inFutureCausalCone_iff_form p).2 ⟨by rw [hpf]; exact neg_nonpos.2 (sq_nonneg m), hp0⟩
  exact (RestrictedLorentzGroup.map_inFutureCausalCone Λ hcone).2

/-! ### The restricted Poincaré group -/

/-- An element of the restricted Poincaré group `P↑₊ = ℝ⁴ ⋊ L↑₊`: a spacetime
translation together with a restricted Lorentz transformation, acting affinely on
Minkowski space by `(a, Λ) • x = Λ x + a` (Streater–Wightman, §1-1). Hand-rolled
semidirect structure; see the module docstring for why Mathlib's `SemidirectProduct`
is not used. The induced action on Schwartz functions is deferred to P2.5a. -/
@[ext]
structure PoincareGroup where
  /-- The translation component `a`. -/
  translation : M4
  /-- The homogeneous (restricted Lorentz) component `Λ`. -/
  lorentz : RestrictedLorentzGroup

namespace PoincareGroup

instance : One PoincareGroup := ⟨⟨0, 1⟩⟩

instance : Mul PoincareGroup :=
  ⟨fun g₁ g₂ => ⟨g₁.translation + (g₁.lorentz : M4 ≃L[ℝ] M4) g₂.translation,
    g₁.lorentz * g₂.lorentz⟩⟩

instance : Inv PoincareGroup :=
  ⟨fun g => ⟨-((g.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) g.translation,
    g.lorentz⁻¹⟩⟩

@[simp] theorem one_translation : (1 : PoincareGroup).translation = 0 := rfl

@[simp] theorem one_lorentz : (1 : PoincareGroup).lorentz = 1 := rfl

@[simp] theorem mul_translation (g₁ g₂ : PoincareGroup) :
    (g₁ * g₂).translation
      = g₁.translation + (g₁.lorentz : M4 ≃L[ℝ] M4) g₂.translation := rfl

@[simp] theorem mul_lorentz (g₁ g₂ : PoincareGroup) :
    (g₁ * g₂).lorentz = g₁.lorentz * g₂.lorentz := rfl

@[simp] theorem inv_translation (g : PoincareGroup) :
    g⁻¹.translation
      = -((g.lorentz⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) g.translation := rfl

@[simp] theorem inv_lorentz (g : PoincareGroup) : g⁻¹.lorentz = g.lorentz⁻¹ := rfl

/-- The semidirect group law `(a₁, Λ₁)(a₂, Λ₂) = (a₁ + Λ₁ a₂, Λ₁ Λ₂)`
(Streater–Wightman, §1-1; Weinberg I, eq. (2.3.11)). -/
instance : Group PoincareGroup where
  mul_assoc g₁ g₂ g₃ := by
    refine PoincareGroup.ext ?_ (mul_assoc _ _ _)
    simp [Subgroup.coe_mul, clm_mul_apply, map_add, add_assoc]
  one_mul g := by
    refine PoincareGroup.ext ?_ (one_mul _)
    simp [clm_one_apply]
  mul_one g := by
    refine PoincareGroup.ext ?_ (mul_one _)
    simp
  inv_mul_cancel g := by
    refine PoincareGroup.ext ?_ (inv_mul_cancel _)
    simp

instance : SMul PoincareGroup M4 :=
  ⟨fun g x => (g.lorentz : M4 ≃L[ℝ] M4) x + g.translation⟩

/-- The affine action of the restricted Poincaré group on Minkowski space:
`(a, Λ) • x = Λ x + a`. -/
theorem smul_def (g : PoincareGroup) (x : M4) :
    g • x = (g.lorentz : M4 ≃L[ℝ] M4) x + g.translation := rfl

instance : MulAction PoincareGroup M4 where
  one_smul x := by simp [smul_def, clm_one_apply]
  mul_smul g₁ g₂ x := by
    simp only [smul_def, mul_translation, mul_lorentz, Subgroup.coe_mul, clm_mul_apply,
      map_add]
    abel

end PoincareGroup

/-- The restricted Lorentz group carries the topology induced from the operator-norm
topology on `M4 →L[ℝ] M4` (in finite dimension, the unique Hausdorff linear topology).
Strong continuity of Poincaré representations (P2.4b) is stated against this. -/
noncomputable instance : TopologicalSpace RestrictedLorentzGroup :=
  TopologicalSpace.induced
    (fun Λ : RestrictedLorentzGroup => ((Λ : M4 ≃L[ℝ] M4) : M4 →L[ℝ] M4)) inferInstance

/-- The restricted Poincaré group carries the product topology of
`M4 × RestrictedLorentzGroup`. -/
noncomputable instance : TopologicalSpace PoincareGroup :=
  TopologicalSpace.induced
    (fun g : PoincareGroup => (g.translation, g.lorentz)) inferInstance

end Spacetime.Minkowski
