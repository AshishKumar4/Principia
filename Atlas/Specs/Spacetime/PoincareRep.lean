import Atlas.Specs.Spacetime.Poincare
import Atlas.Specs.OperatorTheory.UnitaryGroup

/-!
# P2.4b — Strongly continuous unitary representations of the restricted Poincaré group

Frozen spec (blueprint node P2.4b): proof sessions must not edit this file; changes
require a spec review and a `[spec-review]` commit (see CLAUDE.md).

## Contents

* `Spacetime.Minkowski.PoincareRep H` — a strongly continuous unitary representation of
  the restricted Poincaré group `P↑₊` on a complex Hilbert space `H`: a monoid
  homomorphism `toFun : PoincareGroup →* unitary (H →L[ℂ] H)` together with joint
  continuity of the action map `(g, x) ↦ U g x` in the product topology, plus the
  `FunLike`/`MonoidHomClass` coercion API (`coe_mk`, `ext`, and Mathlib's generic
  `map_one`/`map_mul`/`map_inv`).
* `PoincareRep.continuous_apply₂` / `continuous_apply` — the frozen joint continuity and
  its per-vector consequence (strong continuity of every orbit map `g ↦ U g x`).
* `PoincareRep.translationGroup` — **the Stone-bridge anchor**, proven here, not merely
  stated: for every direction `a : M4`, the restriction `t ↦ U ⟨t • a, 1⟩` of a
  representation to the translation line through `a` is a strongly continuous
  one-parameter unitary group (`OperatorTheory.OneParameterUnitaryGroup H`). This is the
  bridge that hands the energy-momentum generators of a representation to the Stone lane
  (P2.3g–P2.3i): the Stone generator of `U.translationGroup a` is the energy-momentum
  operator in direction `a` (naming and spectral content are P2.5's business, not
  stated here).

No `Prop`-valued targets are stated in this file: covariance of fields, the spectrum
condition, and vacuum invariance are the P2.5 Wightman surface (per the P2.4/P2.5/P2.6
design dossier); nothing beyond the structure, its basic API, and the anchor belongs
here.

## Conventions

* **Strong continuity is frozen in the joint form** (adjudicated at this spec's
  review: the dossier specifies only "monoid hom + strong continuity"; the joint
  form is Streater-Wightman's, and the per-vector form is equivalent for unitary
  reps — see below):
  the action map `PoincareGroup × H → H`, `(g, x) ↦ U g x`, is continuous for the
  product of the frozen P2.4a topology on `PoincareGroup` and the norm topology on `H`
  (Streater–Wightman, Ch. 1: the physical states transform under a *continuous* unitary
  representation of `P↑₊`, continuity being in all variables of `U(a, Λ)φ`). For a
  family of unitaries this is *equivalent* to the per-vector form
  `∀ x, Continuous fun g ↦ U g x`: joint ⟹ per-vector is composition with `g ↦ (g, x)`
  (exposed as `PoincareRep.continuous_apply`); per-vector ⟹ joint needs only the
  uniform bound `‖U g‖ = 1` and the triangle inequality
  `‖U g x − U g₀ x₀‖ ≤ ‖x − x₀‖ + ‖U g x₀ − U g₀ x₀‖` — a smart-constructor lemma on a
  future proof node, not part of this spec (same discipline as
  `OneParameterUnitaryGroup`, whose continuity-at-`0`-suffices remark is likewise a
  theorem, not a field). Note the deliberate asymmetry with the frozen
  `OneParameterUnitaryGroup`, which states the per-vector form because its sources
  (Reed & Simon I, §VIII.4) do; each spec freezes its own sources' form, and the
  anchor below consumes only the trivial (joint ⟹ per-vector) direction, so no
  equivalence theorem is load-bearing for the bridge.
* **Bundling: a `MonoidHom` into the unitary group.** `PoincareGroup` is a `Group`
  (frozen P2.4a law `(a₁, Λ₁) * (a₂, Λ₂) = (a₁ + Λ₁ a₂, Λ₁ Λ₂)`), so
  `PoincareGroup →* unitary (H →L[ℂ] H)` is the native bundling and Mathlib's generic
  `map_one`/`map_mul`/`map_inv` apply to the coercion through the `MonoidHomClass`
  instance — no restated group-law fields. This differs from
  `OneParameterUnitaryGroup`, which bundles a bare function with `AddChar`-style
  fields: its domain is additive `ℝ`, and repackaging through `Multiplicative ℝ` only
  to unpack it in every statement would fail the deletion test. Application to vectors
  is written `(U g : H →L[ℂ] H) x`, the same spelling and coercion chain
  (`FunLike`, then the `Submonoid` subtype coercion) as `OneParameterUnitaryGroup`.
* **Genuine representations, not ray representations.** Wigner's analysis of
  relativistic symmetry produces unitary representations up to a phase (ray
  representations; Wigner 1939), which by Bargmann (1954) lift to genuine unitary
  representations of the covering group `ℝ⁴ ⋊ SL(2, ℂ)`. This structure fixes a
  *genuine* representation of `P↑₊` itself: for the scalar (spin-0) lane the covering
  group is not load-bearing — the physically relevant representations factor through
  `P↑₊` — per the design dossier's physlib verdict. Half-integer spin and the covering
  group are out of scope for this node.
* **The anchor is frozen together with its proof.** `translationGroup` is a `def` with
  its group-law and continuity obligations discharged here (cost: the `MonoidHom`
  property on the translation subgroup `t • a`, where the frozen semidirect law
  degenerates to addition since `Λ = 1`, plus restriction of joint continuity to the
  line `t ↦ (⟨t • a, 1⟩, x)`). Freezing a stated-but-unproven anchor would add a proof
  node for nothing.
* **Element convention.** Elements of `PoincareGroup` are `⟨translation, lorentz⟩`
  (frozen P2.4a); the pure translation by `b : M4` is `⟨b, 1⟩`, so the translation
  line through `a` is `t ↦ ⟨t • a, 1⟩`.
* **Witness placement.** The trivial representation (`toFun = 1`) appears below as an
  in-spec instance-transparency `example` (P2.1a precedent): it certifies at freeze
  time that the frozen fields are jointly satisfiable, at one term's cost
  (`continuous_snd`). Named witness content — the trivial representation as a reusable
  `def`, a representation with nontrivial action, and expected-true/false `example`s —
  is the witness node's business (`Atlas/Witnesses/`), not this file's.

## Sources

* Streater & Wightman, *PCT, Spin and Statistics, and All That* (1964; Princeton
  Landmarks ed. 2000), Ch. 1 (relativistic transformation laws: states carry a
  continuous unitary representation of the restricted Poincaré group; the
  representation `U(a, Λ)` and its translation subgroup).
* E. Wigner, "On unitary representations of the inhomogeneous Lorentz group",
  *Ann. of Math.* 40 (1939), 149–204 (context: unitary representations of `P↑₊` and
  their role in relativistic quantum mechanics).
* V. Bargmann, "On unitary ray representations of continuous groups", *Ann. of Math.*
  59 (1954), 1–46 (context: continuity for ray representations; genuine vs. projective).
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised and enlarged edition (1980), §VIII.4 (strongly continuous one-parameter
  unitary groups — the form of the translation restriction).
* Weinberg, *The Quantum Theory of Fields*, Vol. I (1995), §2.2 (symmetries realized
  by unitary operators; projective vs. genuine representations).
-/

namespace Spacetime.Minkowski

open OperatorTheory

/-- Application of the identity of the automorphism group `M4 ≃L[ℝ] M4`; `rfl`, restated
because the P2.4a spec's copy is `private` (upstream candidate: Mathlib has no
`one_apply` for `ContinuousLinearEquiv.automorphismGroup` at v4.31.0). -/
private theorem clm_one_apply (x : M4) : (1 : M4 ≃L[ℝ] M4) x = x := rfl

/-- A strongly continuous unitary representation of the restricted Poincaré group `P↑₊`
on a complex Hilbert space `H`: a homomorphism `g ↦ U g` into the unitary group of
`H →L[ℂ] H` such that the action map `(g, x) ↦ U g x` is jointly continuous for the
frozen P2.4a topology on `PoincareGroup` and the norm topology on `H`.

This is the representation carried by the physical states of a relativistic quantum
theory (Streater–Wightman, Ch. 1; Wigner 1939) — a genuine (not ray) representation,
which suffices for the scalar lane; see the module docstring. Joint continuity is
equivalent to strong continuity of every orbit map `g ↦ U g x` (the nontrivial
direction uses `‖U g‖ = 1`; a future lemma, not part of this spec); the trivial
direction is `PoincareRep.continuous_apply`.

Elements apply to vectors as `(U g : H →L[ℂ] H) x` (cf. `Unitary.norm_map`,
`Unitary.inner_map_map` for unitarity consequences), and `map_one`/`map_mul`/`map_inv`
apply to the coercion through the `MonoidHomClass` instance. -/
structure PoincareRep (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The underlying homomorphism into the unitary group. Do not use this field
  directly; use the coercion coming from the `FunLike` instance. -/
  toFun : PoincareGroup →* unitary (H →L[ℂ] H)
  /-- Joint strong continuity: the action map `(g, x) ↦ U g x` is continuous in the
  product topology. Do not use this field directly; use
  `PoincareRep.continuous_apply₂`. -/
  continuous_apply₂' :
    Continuous fun p : PoincareGroup × H ↦ (toFun p.1 : H →L[ℂ] H) p.2

namespace PoincareRep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable instance : FunLike (PoincareRep H) PoincareGroup (unitary (H →L[ℂ] H)) where
  coe U := U.toFun
  coe_injective U V h := by
    cases U; cases V
    congr
    exact DFunLike.coe_injective h

instance : MonoidHomClass (PoincareRep H) PoincareGroup (unitary (H →L[ℂ] H)) where
  map_mul U := U.toFun.map_mul
  map_one U := U.toFun.map_one

@[ext]
theorem ext {U V : PoincareRep H} (h : ∀ g, U g = V g) : U = V :=
  DFunLike.ext U V h

@[simp]
theorem coe_mk (f : PoincareGroup →* unitary (H →L[ℂ] H))
    (hf : Continuous fun p : PoincareGroup × H ↦ (f p.1 : H →L[ℂ] H) p.2) :
    ⇑(mk f hf) = ⇑f :=
  rfl

@[simp]
theorem toFun_eq_coe (U : PoincareRep H) : ⇑U.toFun = ⇑U :=
  rfl

variable (U : PoincareRep H)

/-- Joint strong continuity of a Poincaré representation: the action map
`(g, x) ↦ U g x` is continuous in the product topology (Streater–Wightman, Ch. 1;
see the module docstring on the joint vs. per-vector forms). -/
theorem continuous_apply₂ :
    Continuous fun p : PoincareGroup × H ↦ (U p.1 : H →L[ℂ] H) p.2 :=
  U.continuous_apply₂'

/-- Strong continuity of every orbit map `g ↦ U g x`: the per-vector consequence of
the frozen joint form, by composition with `g ↦ (g, x)`. -/
theorem continuous_apply (x : H) :
    Continuous fun g : PoincareGroup ↦ (U g : H →L[ℂ] H) x :=
  U.continuous_apply₂.comp (continuous_id.prodMk continuous_const)

/- Instance-transparency examples (P2.1a precedent): the group-law API is Mathlib's
generic `MonoidHomClass` surface, engaged here so a drifting instance would fail the
freeze, and `map_inv` — adjointness of the inverse — comes free from the group-valued
codomain. -/
example (g : PoincareGroup) : U 1 = 1 ∧ U g⁻¹ = (U g)⁻¹ :=
  ⟨map_one U, map_inv U g⟩

example (g₁ g₂ : PoincareGroup) : U (g₁ * g₂) = U g₁ * U g₂ :=
  map_mul U g₁ g₂

/-! ### The Stone-bridge anchor: translation lines are one-parameter unitary groups -/

/-- **The Stone-bridge anchor**: the restriction of a Poincaré representation `U` to
the translation line through `a : M4` — that is, `t ↦ U ⟨t • a, 1⟩` in the frozen
`⟨translation, lorentz⟩` convention — is a strongly continuous one-parameter unitary
group on `H`.

The group law holds because the frozen semidirect law degenerates to
`⟨b, 1⟩ * ⟨c, 1⟩ = ⟨b + c, 1⟩` on the translation subgroup, and strong continuity is
the frozen joint continuity restricted to the line `t ↦ (⟨t • a, 1⟩, x)`. Through
`OneParameterUnitaryGroup.generator` (P2.3g) and the Stone lane (P2.3h/P2.3i), this
hands each representation its energy-momentum generator in direction `a` — e.g.
`a = e₀` gives the time translations whose generator is the Hamiltonian
(Streater–Wightman, Ch. 1; Reed & Simon I, §VIII.4). Naming those generators and
their spectral content is P2.5's business; this def is only the bridge. -/
noncomputable def translationGroup (a : M4) : OneParameterUnitaryGroup H where
  toFun t := U ⟨t • a, 1⟩
  map_zero_eq_one' := by
    have h : (⟨(0 : ℝ) • a, 1⟩ : PoincareGroup) = 1 :=
      PoincareGroup.ext (by simp) rfl
    rw [h, map_one]
  map_add_eq_mul' s t := by
    have h : (⟨(s + t) • a, 1⟩ : PoincareGroup) = ⟨s • a, 1⟩ * ⟨t • a, 1⟩ :=
      PoincareGroup.ext (by simp [add_smul, clm_one_apply]) (one_mul _).symm
    rw [h, map_mul]
  continuous_apply' x := by
    have hline : Continuous fun t : ℝ ↦ (⟨t • a, 1⟩ : PoincareGroup) :=
      continuous_induced_rng.2
        ((continuous_id.smul continuous_const).prodMk continuous_const)
    exact U.continuous_apply₂.comp (hline.prodMk continuous_const)

@[simp]
theorem translationGroup_apply (a : M4) (t : ℝ) :
    U.translationGroup a t = U ⟨t • a, 1⟩ :=
  rfl

/- Instance-transparency example (P2.1a precedent; see the module docstring on witness
placement): the trivial representation `g ↦ 1` satisfies the frozen fields — the
action map collapses to `(g, x) ↦ x` — so the structure is jointly satisfiable at
freeze time. Named witness content is deferred to the witness node. -/
noncomputable example : PoincareRep H where
  toFun := 1
  continuous_apply₂' := continuous_snd

end PoincareRep

end Spacetime.Minkowski
