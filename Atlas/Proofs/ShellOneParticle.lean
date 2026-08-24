import Atlas.Proofs.MassShellMeasure
import Atlas.Proofs.LpPullback
import Atlas.Specs.Spacetime.Poincare
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# P2.6d — the one-particle mass-shell Hilbert space and the translation representation

The one-particle space of a free scalar of mass `m` (Wigner 1939, §6): wavefunctions carried
by the positive mass sheet, square-integrable against the invariant measure
`QFT.KleinGordon.massShellMeasure m = d³p/(2ω_p)` pushed onto the carrier `M4`:

* `QFT.KleinGordon.ShellOneParticle m := Lp ℂ 2 (massShellMeasure m)`.

**Translations act by multiplication, independently of any change-of-variables input**
(translations do not move the shell coordinates; they only rotate a phase). With
`𝐞 = Real.fourierChar`, i.e. `𝐞 t = exp(2πit)`, the multiplier is the plane-wave character

* `QFT.KleinGordon.translationChar a q = 𝐞 (-η(a, q))`,

and `a ↦ (ψ ↦ ψ · translationChar a)` packages as a group homomorphism
`shellTranslationHom : Multiplicative M4 →* (ShellOneParticle m ≃ₗᵢ[ℂ] ShellOneParticle m)`
(the multiplicative copy of `ℝ⁴`, because the target group is written multiplicatively), with
identity, addition, and inverse laws (`shellTranslate_zero`, `shellTranslate_add`,
`shellTranslate_symm`), unitarity (`inner_shellTranslate`), and the exact a.e. pointwise
formula `⇑(shellTranslate m a ψ) =ᵐ fun q ⇒ translationChar a q * ψ q`
(`coeFn_shellTranslate`).

## Sign and `2π` bookkeeping (checked against the frozen P2.5a kernel)

The frozen forward Minkowski Fourier transform (`Atlas/Specs/QFT/WightmanUtilities.lean`)
is anchored by `fourierMinkowski_apply_eq_integral`:

`𝓕η f p = ∫ a, 𝐞 (-η(a, p)) • f a`.

Translating position-space data contragrediently to the frozen `PoincareGroup` action
`(a, 1) • x = x + a`, i.e. `f ↦ f(· - a)` (Streater–Wightman §1-1; Weinberg I,
eq. (2.3.11)), and using Haar invariance of `d⁴x` together with
`𝐞 (-(s+t)) = 𝐞 (-s) · 𝐞 (-t)` gives

`𝓕η(f(· - a))(p) = 𝐞 (-η(a, p)) · (𝓕η f)(p)`,

machine-checked below as `fourierMinkowski_shift`. The momentum-space multiplier is
therefore exactly `𝐞 (-η(a, q))` — the *action* character, not its inverse. The `2π`
sits inside the character: for a point of the sheet `q = massShellParam m p = (ω_p, p)`
one reads off `translationChar a q = exp(2πi·a⁰·ω_p) · exp(-2πi·a⃗·p⃗) = exp(i p·a)` in
physicist notation `p·a = ω_p a⁰ - p⃗·a⃗`; the factor `2π` appears because the repo's
spatial frequency `k` carries physical momentum `2πk` (conventions block of
`Atlas/Proofs/KleinGordon.lean`).

## Strong continuity (H3, translation case)

For every `ψ`, the map `a ↦ shellTranslate m a ψ` is continuous into the `L²`-norm topology
(`continuous_shellTranslate`). The proof uses domination rather than density:
the integrand of `‖shellTranslate m a ψ - shellTranslate m b ψ‖²` converges
pointwise to zero and is dominated by
`4·‖ψ q‖² ∈ L¹(massShellMeasure m)`, regardless of the total shell measure.
The SecondQuantization dense-set theorem `Isometry.tendsto_of_dense` is not needed.

## The eventual Poincaré action (conditional; H1 assumed, never claimed)

For `g = (a, Λ) ∈ P↑₊` the Wigner formula is
`(U(g)ψ)(q) = 𝐞(-η(a, q)) · ψ(Λ⁻¹ q)`. The multiplication half is unconditional; the
pullback half needs `Λ` to preserve `massShellMeasure m` — exactly the H1 invariance of
`d³p/(2ω_p)`. This module *assumes* it:

* `LorentzShellPreserves m Λ` — the explicit `MeasurePreserving` hypothesis;
* `shellPoincare m g hg` — the resulting linear isometry equivalence, with exact a.e.
  formula `coeFn_shellPoincare` and inverse law `shellPoincare_symm`;
* `shellPoincare_translation` — on the translation subgroup `⟨a, 1⟩` (where the hypothesis
  holds trivially) it coincides with `shellTranslate m a`.

The H1 Jacobian identity is stated in **physical momentum**:
`|det D(shellMap m Λ)(p)| · physicalEnergy m p =
physicalEnergy m (shellMap m Λ p)`. It is proved in
`MassShellInvariance.lean` and promoted to the exact `LorentzShellPreserves`
contract in `MassShellMeasurePreserving.lean`. The unconditional unitary hom
and full strongly continuous representation live in
`ShellPoincareRepresentation.lean`.

## Sources

* E. P. Wigner, *On Unitary Representations of the Inhomogeneous Lorentz Group*, Annals of
  Mathematics 40 (1939), §6 — one-particle carriers are wavefunctions on the mass
  hyperboloid square-integrable against the invariant weight (his `d³p/p⁰`, eq. (59a)
  context; this repo normalizes `d³p/(2ω_p)`, see `MassShellMeasure.lean`); §6 also carries
  the plane-wave realization of the translation generators. Cited at section level,
  matching the assertion already fixed in `Atlas/Proofs/MassShellMeasure.lean`.
* A. S. Wightman, "The Spin-Statistics Connection: Some Pedagogical Remarks in
  Response to Neuenschwander's Question", *Mathematical Physics and Quantum Field
  Theory*, Electron. J. Differential Equations Conf. 04 (2000), pp. 207–213 —
  pp. 210–211 give the positive-sign plane-wave reconstruction and forward-cone
  support; the pages were checked independently in both P2.5a repair re-reviews.
* R. F. Streater, A. S. Wightman, *PCT, Spin and Statistics, and All That*
  (1964; Princeton Landmarks ed. 2000), §1-1 — the group conventions already
  frozen in `Atlas/Specs/Spacetime/Poincare.lean` (section-level citation).
* S. Weinberg, *The Quantum Theory of Fields*, Vol. I (1995), §2.3, eq. (2.3.11) — the
  Poincaré composition law `(a₁,Λ₁)(a₂,Λ₂) = (a₁ + Λ₁a₂, Λ₁Λ₂)` already asserted by the
  frozen P2.4a spec.
* Mathlib v4.31 sources, verified in-tree: `Mathlib/Analysis/Complex/Circle.lean`
  (`Real.fourierChar`, analyst `2π` convention),
  `Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean` (`eLpNorm`),
  `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean` (`Lp`, coercions, norms),
  `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
  (`tendsto_integral_filter_of_dominated_convergence`),
  `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
  (`ofReal_integral_eq_lintegral_ofReal`).
-/

noncomputable section

namespace MeasureTheory

open scoped ENNReal

/-! ### Multiplication by modulus-one functions on `L²`

Generic analytic layer for P2.6d, sitting beside the pullback layer of
`Atlas.Proofs.LpPullback`: a measurable multiplier of modulus one acts on `L²(μ, ℂ)` by
pointwise multiplication, preserving the norm exactly; the action is a complex-linear
isometric self-equivalence. -/

section UnitMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Pointwise `L²`-norm invariance under multiplication by a modulus-one function. -/
theorem eLpNorm_mul_unitModulus {u f : α → ℂ} (h1 : ∀ x, ‖u x‖ = 1) :
    eLpNorm (fun x => u x * f x) 2 μ = eLpNorm f 2 μ := by
  have htwo : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero htwo,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero htwo]
  refine congrArg (fun s : ℝ≥0∞ => s ^ (1 / (2 : ℝ))) (lintegral_congr fun x => ?_)
  have hb : ‖(u x * f x : ℂ)‖ₑ = ‖f x‖ₑ := by
    simp only [enorm, nnnorm_mul]
    have hu1 : ‖u x‖₊ = 1 := by
      apply NNReal.coe_injective
      simpa using h1 x
    rw [hu1, one_mul]
  rw [hb]

/-- Multiplying an `AEEqFun` by a modulus-one multiplier preserves the `L²`-norm. -/
theorem eLpNorm_mul_aeeq_unitModulus {K : α →ₘ[μ] ℂ} {u : α → ℂ}
    (hu : AEStronglyMeasurable u μ) (h1 : ∀ x, ‖u x‖ = 1) :
    eLpNorm (K * AEEqFun.mk u hu) 2 μ = eLpNorm K 2 μ := by
  have hcoe : ⇑(K * AEEqFun.mk u hu) =ᵐ[μ] fun x => u x * ⇑K x :=
    calc ⇑(K * AEEqFun.mk u hu) =ᵐ[μ] ⇑K * ⇑(AEEqFun.mk u hu) := AEEqFun.coeFn_mul K _
      _ =ᵐ[μ] fun x => u x * ⇑K x := by
          filter_upwards [(AEEqFun.coeFn_mk u hu).symm] with x hx
          simp only [Pi.mul_apply, hx, mul_comm]
  exact (eLpNorm_congr_ae hcoe).trans (eLpNorm_mul_unitModulus h1)

/-- Multiply the class of `k` by a strongly measurable modulus-one function. -/
private def Lp.prodUnit {w : α → ℂ} (hw : AEStronglyMeasurable w μ)
    (_h1 : ∀ x, ‖w x‖ = 1) (k : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ⟨k.1 * AEEqFun.mk w hw,
    mem_Lp_iff_eLpNorm_lt_top.2 (by rw [eLpNorm_mul_aeeq_unitModulus hw _h1]; exact k.2)⟩

/-- Pointwise formula for multiplication by a modulus-one function on `Lp`. -/
private theorem Lp.coeFn_prodUnit {w : α → ℂ} (hw : AEStronglyMeasurable w μ)
    (_h1 : ∀ x, ‖w x‖ = 1) (k : Lp ℂ 2 μ) :
    (Lp.prodUnit hw _h1 k : α → ℂ) =ᵐ[μ] fun x => w x * ⇑k x :=
  calc ⇑(Lp.prodUnit hw _h1 k) =ᵐ[μ] ⇑k.1 * ⇑(AEEqFun.mk w hw) := AEEqFun.coeFn_mul _ _
    _ =ᵐ[μ] fun x => w x * ⇑k x := by
        filter_upwards [(AEEqFun.coeFn_mk w hw).symm] with x hx
        simp only [Pi.mul_apply, hx, mul_comm]

/-- Multiplication by a strongly measurable modulus-one function, as a complex-linear
endomorphism of `L²(μ, ℂ)`. -/
def Lp.mulUnitₗ {u : α → ℂ} (hu : AEStronglyMeasurable u μ) (h1 : ∀ x, ‖u x‖ = 1) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun k := Lp.prodUnit hu h1 k
  map_add' k l := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_prodUnit hu h1 (k + l), Lp.coeFn_add k l,
      Lp.coeFn_prodUnit hu h1 k, Lp.coeFn_prodUnit hu h1 l,
      Lp.coeFn_add (Lp.prodUnit hu h1 k) (Lp.prodUnit hu h1 l)] with x e1 e2 e3 e4 e5
    calc (Lp.prodUnit hu h1 (k + l) : α → ℂ) x
        = u x * (⇑k + ⇑l) x := by rw [e1, e2]
      _ = u x * ⇑k x + u x * ⇑l x := mul_add _ _ _
      _ = (Lp.prodUnit hu h1 k + Lp.prodUnit hu h1 l : Lp ℂ 2 μ) x := by
          rw [e5]; simp only [Pi.add_apply]; rw [e3, e4]
  map_smul' c k := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_prodUnit hu h1 (c • k), Lp.coeFn_smul c k,
      Lp.coeFn_prodUnit hu h1 k, Lp.coeFn_smul c (Lp.prodUnit hu h1 k)] with x e1 e2 e3 e4
    calc (Lp.prodUnit hu h1 (c • k) : α → ℂ) x
        = u x * ⇑(c • k) x := by rw [e1]
      _ = u x * (c * ⇑k x) := by rw [e2, Pi.smul_apply, smul_eq_mul]
      _ = c * (u x * ⇑k x) := mul_left_comm _ _ _
      _ = c * (Lp.prodUnit hu h1 k : α → ℂ) x := by rw [e3]
      _ = (c • Lp.prodUnit hu h1 k : Lp ℂ 2 μ) x := by rw [e4, Pi.smul_apply, smul_eq_mul]

/-- Pointwise formula for the unit-multiplier endomorphism. -/
theorem Lp.coeFn_mulUnitₗ {u : α → ℂ} (hu : AEStronglyMeasurable u μ)
    (h1 : ∀ x, ‖u x‖ = 1) (k : Lp ℂ 2 μ) :
    ((mulUnitₗ hu h1 k : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => u x * ⇑k x :=
  Lp.coeFn_prodUnit hu h1 k

/-- Composition of two unit multipliers whose pointwise product is `1` is the identity. -/
private theorem Lp.mulUnitₗ_comp {u v : α → ℂ}
    (hu : AEStronglyMeasurable u μ) (hnu : ∀ x, ‖u x‖ = 1)
    (hv : AEStronglyMeasurable v μ) (hnv : ∀ x, ‖v x‖ = 1)
    (huv : ∀ x, u x * v x = 1) (k : Lp ℂ 2 μ) :
    mulUnitₗ hv hnv (mulUnitₗ hu hnu k) = k := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_prodUnit hv hnv (Lp.prodUnit hu hnu k),
    Lp.coeFn_prodUnit hu hnu k] with x e1 e2
  have hn0 : u x ≠ 0 := by
    intro hzero
    have h0 : ‖(0 : ℂ)‖ = 1 := by rw [← hzero]; exact hnu x
    simp at h0
  calc (Lp.prodUnit hv hnv (Lp.prodUnit hu hnu k) : α → ℂ) x
      = v x * (u x * ⇑k x) := by rw [e1, e2]
    _ = (v x * u x) * ⇑k x := by rw [← mul_assoc]
    _ = ⇑k x := by rw [mul_comm (v x) (u x), huv x, one_mul]

/-- Multiplication by a modulus-one measurable function is a complex-linear isometry
equivalence of `L²(μ, ℂ)`; its inverse multiplies by the pointwise inverse multiplier. -/
def Lp.mulUnitEquiv {u : α → ℂ} (hu : Measurable u) (h1 : ∀ x, ‖u x‖ = 1) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  let hne : ∀ x, u x ≠ 0 := fun x => by
    intro hzero
    have h0 : ‖(0 : ℂ)‖ = 1 := by rw [← hzero]; exact h1 x
    simp at h0
  let h1i : ∀ x, ‖(u x)⁻¹‖ = 1 := fun x => by rw [norm_inv, h1 x, inv_one]
  { toLinearEquiv :=
      LinearEquiv.ofLinear (mulUnitₗ hu.aestronglyMeasurable h1)
        (mulUnitₗ (hu.inv).aestronglyMeasurable h1i)
        (LinearMap.ext fun k =>
          mulUnitₗ_comp (hu.inv).aestronglyMeasurable h1i hu.aestronglyMeasurable h1
            (fun x => inv_mul_cancel₀ (hne x)) k)
        (LinearMap.ext fun k =>
          mulUnitₗ_comp hu.aestronglyMeasurable h1 (hu.inv).aestronglyMeasurable h1i
            (fun x => mul_inv_cancel₀ (hne x)) k)
    norm_map' := fun k => by
      rw [LinearEquiv.ofLinear_apply, Lp.norm_def, Lp.norm_def]
      exact congrArg ENNReal.toReal
        ((eLpNorm_congr_ae (coeFn_mulUnitₗ hu.aestronglyMeasurable h1 k)).trans
          (eLpNorm_mul_unitModulus h1)) }

end UnitMultiplication

end MeasureTheory

namespace QFT.KleinGordon

open MeasureTheory Real Spacetime.Minkowski Filter
open scoped ENNReal Topology

/-! ### The plane-wave translation character -/

/-- The **translation character** attached to a spacetime displacement `a`, evaluated at a
momentum-space point `q`: `𝐞 (-η(a, q))` with `𝐞 = Real.fourierChar`. This is exactly the
kernel of the frozen forward transform `Spacetime.Minkowski.fourierMinkowski_apply_eq_integral`
(`𝓕η f p = ∫ a, 𝐞 (-η(a, p)) • f a`), with the translation playing the role of the position
variable. Wigner 1939, §6; Streater–Wightman 2000, pp. 210–211. -/
noncomputable def translationChar (a q : M4) : ℂ :=
  (Real.fourierChar (-(minkowskiForm a q)) : ℂ)

@[simp]
theorem norm_translationChar (a q : M4) : ‖translationChar a q‖ = 1 :=
  Circle.norm_coe _

/-- Explicit exponential form of the character, `exp(-2πi·η(a,q))`. -/
theorem translationChar_eq_exp (a q : M4) :
    translationChar a q = Complex.exp (((2 * π * -(minkowskiForm a q) : ℝ) : ℂ) * Complex.I) := by
  rw [translationChar, Real.fourierChar_apply]

theorem minkowskiForm_add_left (a b q : M4) :
    minkowskiForm (a + b) q = minkowskiForm a q + minkowskiForm b q := by
  have h : (minkowskiForm (a + b)) = (minkowskiForm a + minkowskiForm b) := map_add _ _ _
  rw [h]
  rfl

theorem minkowskiForm_neg_left (a q : M4) :
    minkowskiForm (-a) q = -(minkowskiForm a q) := by
  have h : (minkowskiForm (-a)) = -(minkowskiForm a) := map_neg _ _
  rw [h]
  rfl

/-- The character is additive-to-multiplicative under the cast to `ℂ`. -/
private theorem fourierChar_add_real (c d : ℝ) :
    (Real.fourierChar (c + d) : ℂ) = (Real.fourierChar c : ℂ) * (Real.fourierChar d : ℂ) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

/-- The character sends negatives to inverses under the cast to `ℂ`. -/
private theorem fourierChar_inv_real (c : ℝ) :
    (Real.fourierChar (-c) : ℂ) = (Real.fourierChar c : ℂ)⁻¹ := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply,
    show ((2 * π * -c : ℝ) : ℂ) = -((2 * π * c : ℝ) : ℂ) from by push_cast; ring,
    neg_mul, Complex.exp_neg]

/-- The character at `0` is `1`. -/
private theorem fourierChar_zero_real : (Real.fourierChar (0 : ℝ) : ℂ) = 1 := by
  rw [AddChar.map_zero_eq_one, Circle.coe_one]

@[simp]
theorem translationChar_zero (q : M4) : translationChar 0 q = 1 := by
  have h : -(minkowskiForm 0 q) = 0 := by simp
  rw [translationChar, h, fourierChar_zero_real]

/-- **Additivity in the translation**: the character is a group homomorphism from the
translation group (Wigner 1939, §6). -/
theorem translationChar_add (a b q : M4) :
    translationChar (a + b) q = translationChar a q * translationChar b q := by
  have h : -(minkowskiForm (a + b) q) = -(minkowskiForm a q) + -(minkowskiForm b q) := by
    rw [minkowskiForm_add_left]; ring
  rw [translationChar, translationChar, translationChar, h, fourierChar_add_real]

/-- **Inverses**: the character of `-a` is the pointwise inverse. -/
theorem translationChar_inv_left (a q : M4) :
    translationChar (-a) q = (translationChar a q)⁻¹ := by
  have h : -(minkowskiForm (-a) q) = -(-(minkowskiForm a q)) := by
    rw [minkowskiForm_neg_left]
  rw [translationChar, translationChar, h, fourierChar_inv_real]

theorem continuous_translationChar_left (a : M4) :
    Continuous fun q : M4 => translationChar a q := by
  have heq : (fun q : M4 => translationChar a q)
      = fun q : M4 => Complex.exp (((2 * π * -(minkowskiForm a q) : ℝ) : ℂ) * Complex.I) :=
    funext fun q => translationChar_eq_exp a q
  rw [heq]
  fun_prop

theorem continuous_translationChar_right (q : M4) :
    Continuous fun a : M4 => translationChar a q := by
  have heq : (fun a : M4 => translationChar a q)
      = fun a : M4 => Complex.exp (((2 * π * -(minkowskiForm a q) : ℝ) : ℂ) * Complex.I) :=
    funext fun a => translationChar_eq_exp a q
  rw [heq]
  fun_prop

theorem measurable_translationChar_left (a : M4) :
    Measurable fun q : M4 => translationChar a q :=
  (continuous_translationChar_left a).measurable

/-! ### Sign check against the frozen P2.5a forward-transform anchor -/

/-- **Sign check against the frozen P2.5a kernel.** The frozen anchor
`Spacetime.Minkowski.fourierMinkowski_apply_eq_integral` reads
`𝓕η f p = ∫ x, 𝐞 (-η(x, p)) • f x`, i.e. the forward kernel at momentum `p` is
`translationChar x p` in the integration variable `x`. Translating the position-space datum
contragrediently to the frozen action `(a, 1) • x = x + a`, i.e. `f ↦ f(· - a)`, multiplies
that integral by exactly the **action** character `translationChar a p`, not by its inverse:
Haar invariance of `d⁴x` plus `translationChar_add`. This pins the sign and the `2π`
normalization simultaneously (Wigner 1939, §6; Wightman 2000, pp. 210–211;
Weinberg I, eq. (2.3.11)). -/
theorem fourierMinkowski_shift {f : M4 → ℂ} (a p : M4) :
    (∫ x : M4, translationChar x p * f (x - a)) =
      translationChar a p * ∫ x : M4, translationChar x p * f x := by
  have step : (∫ x : M4, translationChar x p * f (x - a))
      = ∫ x : M4, translationChar a p * (translationChar x p * f x) := by
    rw [← integral_add_right_eq_self
      (fun x : M4 => translationChar x p * f (x - a)) a]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    calc translationChar (x + a) p * f (x + a - a)
        = (translationChar x p * translationChar a p) * f x := by
          rw [translationChar_add, add_sub_cancel_right]
      _ = translationChar a p * (translationChar x p * f x) := by ring
  rw [step, integral_const_mul]

/-- **The physical reading of the character on the sheet.** At the point
`massShellParam m p = (ω_p, p)` of the positive sheet the multiplier is
`𝐞(a⁰ω_p - a⃗·p⃗) = exp(2πi(a⁰ω_p - a⃗·p⃗))`, i.e. the physicist plane wave `exp(i p·a)` with
`p·a = ω_p a⁰ - p⃗·a⃗` once the repo's `2π`-normalized pairing is accounted for (conventions
block of `Atlas/Proofs/KleinGordon.lean`: a spatial frequency `k` carries physical momentum
`2πk`). -/
theorem translationChar_massShellParam (m : ℝ) (a : M4) (p : M3) :
    translationChar a (massShellParam m p)
      = (Real.fourierChar
          (a 0 * physicalEnergy m p - (a 1 * p 0 + a 2 * p 1 + a 3 * p 2)) : ℂ) := by
  rw [translationChar]
  congr 1
  rw [minkowskiForm_eq, massShellParam_apply_zero, massShellParam_apply_one,
    massShellParam_apply_two, massShellParam_apply_three]
  ring_nf

/-! ### The one-particle shell Hilbert space and the translation representation -/

/-- The **one-particle mass-shell Hilbert space** of mass `m`: square-integrable wavefunctions
on the carrier `M4` against the invariant shell measure `d³p/(2ω_p)` of
`Atlas.Proofs.MassShellMeasure` (Wigner 1939, §6, eq. (59a) context; Streater–Wightman 2000,
pp. 210–211). -/
abbrev ShellOneParticle (m : ℝ) := Lp ℂ 2 (massShellMeasure m)

/-- The **translation representation** on the one-particle shell: multiplication by the
plane-wave character `𝐞(-η(a, q))`. No change-of-variables (H1) input is used: translations
fix the shell pointwise and only rotate a phase (Wigner 1939, §6; sign pinned to the frozen
P2.5a anchor by `fourierMinkowski_shift`). -/
noncomputable def shellTranslate (m : ℝ) (a : M4) :
    ShellOneParticle m ≃ₗᵢ[ℂ] ShellOneParticle m :=
  Lp.mulUnitEquiv (measurable_translationChar_left a) (fun q => norm_translationChar a q)

/-- **The exact a.e. pointwise formula** for the translation representation. -/
theorem coeFn_shellTranslate (m : ℝ) (a : M4) (ψ : ShellOneParticle m) :
    ((shellTranslate m a ψ : ShellOneParticle m) : M4 → ℂ)
      =ᵐ[massShellMeasure m] fun q => translationChar a q * (ψ : M4 → ℂ) q :=
  Lp.coeFn_mulUnitₗ ((measurable_translationChar_left a).aestronglyMeasurable)
    (fun q => norm_translationChar a q) ψ

/-- **Identity law**: the zero translation acts trivially. -/
@[simp]
theorem shellTranslate_zero (m : ℝ) : shellTranslate m 0 = 1 := by
  refine LinearIsometryEquiv.ext fun ψ => ?_
  refine Lp.ext ?_
  filter_upwards [coeFn_shellTranslate m 0 ψ] with q hq
  rw [hq, translationChar_zero, one_mul]
  rfl

/-- **Addition law**: the representation is multiplicative in the translation. -/
theorem shellTranslate_add (m : ℝ) (a b : M4) :
    shellTranslate m (a + b) = shellTranslate m a * shellTranslate m b := by
  refine LinearIsometryEquiv.ext fun ψ => ?_
  show shellTranslate m (a + b) ψ = shellTranslate m a (shellTranslate m b ψ)
  refine Lp.ext ?_
  filter_upwards [coeFn_shellTranslate m (a + b) ψ, coeFn_shellTranslate m b ψ,
    coeFn_shellTranslate m a (shellTranslate m b ψ)] with q e1 e2 e3
  calc ((shellTranslate m (a + b) ψ : ShellOneParticle m) : M4 → ℂ) q
      = translationChar (a + b) q * (ψ : M4 → ℂ) q := e1
    _ = translationChar a q * (translationChar b q * (ψ : M4 → ℂ) q) := by
        rw [translationChar_add, mul_assoc]
    _ = translationChar a q * ((shellTranslate m b ψ : ShellOneParticle m) : M4 → ℂ) q := by
        rw [e2]
    _ = ((shellTranslate m a (shellTranslate m b ψ) : ShellOneParticle m) : M4 → ℂ) q := e3.symm

/-- **Inverse law**: the inverse of a translation is the opposite translation. -/
theorem shellTranslate_symm (m : ℝ) (a : M4) :
    (shellTranslate m a).symm = shellTranslate m (-a) := by
  have hmul : shellTranslate m a * shellTranslate m (-a) = 1 := by
    rw [← shellTranslate_add, add_neg_cancel, shellTranslate_zero]
  have h : shellTranslate m (-a) = (shellTranslate m a)⁻¹ := eq_inv_of_mul_eq_one_right hmul
  rw [h, LinearIsometryEquiv.inv_def]

/-- **The translation representation as a group homomorphism** into the unitary group of the
one-particle space: the translation subgroup representation of the Poincaré group, written on
the multiplicative copy of `ℝ⁴` because the target group is multiplicative (Wigner 1939, §6;
Streater–Wightman 2000, pp. 210–211). -/
noncomputable def shellTranslationHom (m : ℝ) :
    Multiplicative M4 →* (ShellOneParticle m ≃ₗᵢ[ℂ] ShellOneParticle m) where
  toFun a := shellTranslate m (Multiplicative.toAdd a)
  map_one' := shellTranslate_zero m
  map_mul' _ _ := shellTranslate_add m _ _

@[simp]
theorem shellTranslationHom_apply (m : ℝ) (a : Multiplicative M4) :
    shellTranslationHom m a = shellTranslate m (Multiplicative.toAdd a) := rfl

/-- **Unitarity of the translation representation**: the inner product of the one-particle
space is preserved (Wigner 1939, §6: the scalar product carried by the mass hyperboloid is
invariant). -/
theorem inner_shellTranslate (m : ℝ) (a : M4) (ψ φ : ShellOneParticle m) :
    inner ℂ (shellTranslate m a ψ) (shellTranslate m a φ) = inner ℂ ψ φ :=
  (shellTranslate m a).inner_map_map ψ φ

@[simp]
theorem norm_shellTranslate (m : ℝ) (a : M4) (ψ : ShellOneParticle m) :
    ‖shellTranslate m a ψ‖ = ‖ψ‖ :=
  (shellTranslate m a).norm_map ψ

/-! ### H3 — strong continuity of the translation representation -/

/-- Integrability of the dominating function `4‖ψ‖²` for a shell wavefunction. -/
private theorem integrable_four_norm_sq (m : ℝ) (ψ : ShellOneParticle m) :
    Integrable (fun q : M4 => 4 * ‖(ψ : M4 → ℂ) q‖ ^ 2) (massShellMeasure m) := by
  have h2 : Integrable
      (fun q : M4 => ‖(ψ : M4 → ℂ) q‖ ^ (2 : ℝ≥0∞).toReal) (massShellMeasure m) :=
    (Lp.memLp ψ).integrable_norm_rpow two_ne_zero (by simp)
  simpa using h2.const_mul (4 : ℝ)

/-- The `ℝ≥0∞`-norm squared of a complex number as a real `ofReal` value. -/
private theorem enorm_pow_two_eq_ofReal (z : ℂ) :
    ‖z‖ₑ ^ (2 : ℝ≥0∞).toReal = ENNReal.ofReal (‖z‖ ^ 2) := by
  simp [enorm]

/-- The squared `L²`-distance of two translates as an explicit integral over the shell. -/
theorem dist_shellTranslate_sq (m : ℝ) (a b : M4) (ψ : ShellOneParticle m) :
    dist (shellTranslate m a ψ) (shellTranslate m b ψ) ^ 2
      = ∫ q : M4, ‖(translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q‖ ^ 2
          ∂(massShellMeasure m) := by
  have hrep : ((shellTranslate m a ψ - shellTranslate m b ψ : ShellOneParticle m) : M4 → ℂ)
      =ᵐ[massShellMeasure m]
        fun q => (translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q := by
    filter_upwards [Lp.coeFn_sub (shellTranslate m a ψ) (shellTranslate m b ψ),
      coeFn_shellTranslate m a ψ, coeFn_shellTranslate m b ψ] with q hsub ha hb
    rw [hsub, Pi.sub_apply, ha, hb, sub_mul]
  have hmeas : AEStronglyMeasurable
      (fun q : M4 => ‖(translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q‖ ^ 2)
      (massShellMeasure m) := by
    have h1 : AEStronglyMeasurable (fun q : M4 => translationChar a q) (massShellMeasure m) :=
      (measurable_translationChar_left a).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun q : M4 => translationChar b q) (massShellMeasure m) :=
      (measurable_translationChar_left b).aestronglyMeasurable
    exact ((h1.sub h2).mul (Lp.aestronglyMeasurable ψ)).norm.pow 2
  have hdom : ∀ q : M4,
      ‖(translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q‖ ^ 2
        ≤ 4 * ‖(ψ : M4 → ℂ) q‖ ^ 2 := by
    intro q
    have hchar : ‖translationChar a q - translationChar b q‖ ≤ 2 := by
      have h := norm_sub_le (translationChar a q) (translationChar b q)
      rw [norm_translationChar, norm_translationChar] at h
      linarith
    have hmul : ‖(translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q‖
        ≤ 2 * ‖(ψ : M4 → ℂ) q‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hchar (norm_nonneg _))
    nlinarith [norm_nonneg ((translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q),
      norm_nonneg ((ψ : M4 → ℂ) q)]
  have hint : Integrable
      (fun q : M4 => ‖(translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q‖ ^ 2)
      (massShellMeasure m) :=
    (integrable_four_norm_sq m ψ).mono' hmeas (Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hdom q)
  have hJ0 : 0 ≤ ∫ q : M4,
      ‖(translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q‖ ^ 2
        ∂(massShellMeasure m) :=
    integral_nonneg fun q => by positivity
  have hlint : eLpNorm
      ((shellTranslate m a ψ - shellTranslate m b ψ : ShellOneParticle m) : M4 → ℂ) 2
      (massShellMeasure m)
      = (ENNReal.ofReal (∫ q : M4,
          ‖(translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q‖ ^ 2
            ∂(massShellMeasure m))) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    refine congrArg (fun t : ℝ≥0∞ => t ^ (1 / (2 : ℝ))) ?_
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun q => by positivity)]
    refine lintegral_congr_ae ?_
    filter_upwards [hrep] with q hq
    rw [hq, enorm_pow_two_eq_ofReal]
  have hdist : dist (shellTranslate m a ψ) (shellTranslate m b ψ)
      = √(∫ q : M4, ‖(translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q‖ ^ 2
            ∂(massShellMeasure m)) := by
    rw [dist_eq_norm, Lp.norm_def, hlint, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hJ0, ← Real.sqrt_eq_rpow]
  rw [hdist, Real.sq_sqrt hJ0]

/-- **H3 (translation case), quantitative form**: the `L²`-distance between translates tends
to zero as the translation converges. Dominated convergence with dominator
`4‖ψ‖²`; no density transport is needed (Wigner 1939, §6). -/
theorem tendsto_dist_shellTranslate (m : ℝ) (b : M4) (ψ : ShellOneParticle m) :
    Tendsto (fun a : M4 => dist (shellTranslate m a ψ) (shellTranslate m b ψ)) (𝓝 b) (𝓝 0) := by
  have hsq : Tendsto
      (fun a : M4 => dist (shellTranslate m a ψ) (shellTranslate m b ψ) ^ 2) (𝓝 b) (𝓝 0) := by
    have hkey : (fun a : M4 => dist (shellTranslate m a ψ) (shellTranslate m b ψ) ^ 2)
        = fun a : M4 => ∫ q : M4,
            ‖(translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q‖ ^ 2
              ∂(massShellMeasure m) :=
      funext fun a => dist_shellTranslate_sq m a b ψ
    rw [hkey]
    have hlim := tendsto_integral_filter_of_dominated_convergence
      (μ := massShellMeasure m) (l := 𝓝 b)
      (F := fun (a : M4) (q : M4) =>
        ‖(translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q‖ ^ 2)
      (f := fun _ : M4 => (0 : ℝ))
      (bound := fun q : M4 => 4 * ‖(ψ : M4 → ℂ) q‖ ^ 2)
      (Eventually.of_forall fun a => by
        have h1 : AEStronglyMeasurable (fun q : M4 => translationChar a q)
            (massShellMeasure m) :=
          (measurable_translationChar_left a).aestronglyMeasurable
        have h2 : AEStronglyMeasurable (fun q : M4 => translationChar b q)
            (massShellMeasure m) :=
          (measurable_translationChar_left b).aestronglyMeasurable
        exact ((h1.sub h2).mul (Lp.aestronglyMeasurable ψ)).norm.pow 2)
      (Eventually.of_forall fun a => Eventually.of_forall fun q => by
        have hchar : ‖translationChar a q - translationChar b q‖ ≤ 2 := by
          have h := norm_sub_le (translationChar a q) (translationChar b q)
          rw [norm_translationChar, norm_translationChar] at h
          linarith
        have hmul : ‖(translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q‖
            ≤ 2 * ‖(ψ : M4 → ℂ) q‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hchar (norm_nonneg _))
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith [norm_nonneg ((translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q),
          norm_nonneg ((ψ : M4 → ℂ) q)])
      (integrable_four_norm_sq m ψ)
      (Eventually.of_forall fun q => by
        have hcont : Continuous fun a : M4 =>
            ‖(translationChar a q - translationChar b q) * (ψ : M4 → ℂ) q‖ ^ 2 :=
          (((continuous_translationChar_right q).sub continuous_const).mul
            continuous_const).norm.pow 2
        simpa using hcont.tendsto b)
    simpa using hlim
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at h
  exact h.congr fun a => Real.sqrt_sq dist_nonneg

/-- **H3 (translation case)**: the translation representation is strongly continuous — for
every one-particle state `ψ`, the orbit map `a ↦ U(a)ψ` is continuous into the `L²`-norm
topology. -/
theorem continuous_shellTranslate (m : ℝ) (ψ : ShellOneParticle m) :
    Continuous fun a : M4 => shellTranslate m a ψ :=
  continuous_iff_continuousAt.2 fun b =>
    tendsto_iff_dist_tendsto_zero.2 (tendsto_dist_shellTranslate m b ψ)

/-! ### The eventual Poincaré action, conditional on H1

Nothing below claims H1 (Lorentz invariance of `massShellMeasure`): the measure-preservation
of the homogeneous part is an explicit hypothesis in every statement. -/

/-- A restricted Lorentz transformation viewed as a measurable automorphism of the carrier
`M4` (it is a linear homeomorphism, hence a measurable equivalence). -/
noncomputable def lorentzMeasurableEquiv (Λ : RestrictedLorentzGroup) : M4 ≃ᵐ M4 :=
  ((Λ : M4 ≃L[ℝ] M4).toHomeomorph).toMeasurableEquiv

@[simp]
theorem lorentzMeasurableEquiv_apply (Λ : RestrictedLorentzGroup) (x : M4) :
    lorentzMeasurableEquiv Λ x = (Λ : M4 ≃L[ℝ] M4) x := rfl

@[simp]
theorem lorentzMeasurableEquiv_one :
    lorentzMeasurableEquiv (1 : RestrictedLorentzGroup) = MeasurableEquiv.refl M4 := by
  refine MeasurableEquiv.ext ?_
  funext x
  rfl

theorem lorentzMeasurableEquiv_symm (Λ : RestrictedLorentzGroup) :
    (lorentzMeasurableEquiv Λ).symm = lorentzMeasurableEquiv Λ⁻¹ := by
  refine MeasurableEquiv.ext ?_
  funext x
  rfl

/-- **The H1 hypothesis, isolated.** `LorentzShellPreserves m Λ` says that `Λ` preserves the
invariant shell measure `d³p/(2ω_p)`. This is exactly the content of H1 (Wigner 1939, §6,
footnote on the Jacobian of the Lorentz transformation); it is *assumed*, never derived, in
this module. -/
def LorentzShellPreserves (m : ℝ) (Λ : RestrictedLorentzGroup) : Prop :=
  MeasurePreserving (lorentzMeasurableEquiv Λ) (massShellMeasure m) (massShellMeasure m)

theorem LorentzShellPreserves.inv {m : ℝ} {Λ : RestrictedLorentzGroup}
    (h : LorentzShellPreserves m Λ) : LorentzShellPreserves m Λ⁻¹ := by
  rw [LorentzShellPreserves, ← lorentzMeasurableEquiv_symm]
  exact h.symm (lorentzMeasurableEquiv Λ)

/-- **The Wigner action of the Poincaré group on the one-particle shell, conditional on H1**:
`(U(a, Λ)ψ)(q) = 𝐞(-η(a, q)) · ψ(Λ⁻¹q)`, built as the pullback along `Λ⁻¹` (needing the
measure hypothesis `hg`) followed by multiplication with the translation character (needing
nothing). Wigner 1939, §6; Streater–Wightman 2000, pp. 210–211; group law conventions of the
frozen P2.4a spec (Weinberg I, eq. (2.3.11)). -/
noncomputable def shellPoincare (m : ℝ) (g : PoincareGroup)
    (hg : LorentzShellPreserves m g.lorentz) :
    ShellOneParticle m ≃ₗᵢ[ℂ] ShellOneParticle m :=
  (Lp.measurePreservingEquiv (lorentzMeasurableEquiv g.lorentz).symm
    (hg.symm (lorentzMeasurableEquiv g.lorentz))).trans
    (Lp.mulUnitEquiv (measurable_translationChar_left g.translation)
      (fun q => norm_translationChar g.translation q))

/-- **The exact a.e. pointwise formula** of the conditional Poincaré action. -/
theorem coeFn_shellPoincare (m : ℝ) (g : PoincareGroup)
    (hg : LorentzShellPreserves m g.lorentz) (ψ : ShellOneParticle m) :
    ((shellPoincare m g hg ψ : ShellOneParticle m) : M4 → ℂ)
      =ᵐ[massShellMeasure m] fun q => translationChar g.translation q
        * (ψ : M4 → ℂ) ((lorentzMeasurableEquiv g.lorentz).symm q) := by
  have hpull := Lp.coeFn_measurePreservingEquiv (𝕜 := ℂ) (E := ℂ) (p := 2)
    (lorentzMeasurableEquiv g.lorentz).symm
      (hg.symm (lorentzMeasurableEquiv g.lorentz)) ψ
  have hmul := Lp.coeFn_mulUnitₗ
    ((measurable_translationChar_left g.translation).aestronglyMeasurable)
    (fun q => norm_translationChar g.translation q)
    (Lp.measurePreservingEquiv (𝕜 := ℂ) (E := ℂ) (p := 2)
      (lorentzMeasurableEquiv g.lorentz).symm
        (hg.symm (lorentzMeasurableEquiv g.lorentz)) ψ)
  filter_upwards [hpull, hmul] with q h1 h2
  exact h2.trans (by rw [h1])

/-- Form preservation, read as a transfer of the inverse across the pairing:
`η(Λ⁻¹v, w) = η(v, Λw)`. -/
theorem minkowskiForm_inv_left (Λ : RestrictedLorentzGroup) (v w : M4) :
    minkowskiForm (((Λ⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) v) w
      = minkowskiForm v ((Λ : M4 ≃L[ℝ] M4) w) := by
  have h := RestrictedLorentzGroup.form_preserving Λ
    (((Λ⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) v) w
  have hinv : (Λ : M4 ≃L[ℝ] M4) (((Λ⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) v) = v := by
    show (Λ : M4 ≃L[ℝ] M4) ((Λ : M4 ≃L[ℝ] M4).symm v) = v
    exact (Λ : M4 ≃L[ℝ] M4).apply_symm_apply v
  rw [hinv] at h
  exact h.symm

/-- Transfer of the Lorentz inverse from the displacement slot to the momentum slot. -/
theorem translationChar_lorentz_transfer (Λ : RestrictedLorentzGroup) (a q : M4) :
    translationChar (((Λ⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) a) q
      = translationChar a ((Λ : M4 ≃L[ℝ] M4) q) := by
  rw [translationChar, translationChar, minkowskiForm_inv_left]

/-- **The character intertwines the Lorentz pullback**: the multiplier attached to the
inverse Poincaré element, read at `q`, is the inverse of the original multiplier read at
`Λq`. This is the algebraic content of `U(g)⁻¹ = U(g⁻¹)` on the shell. -/
theorem translationChar_inv_lorentz (Λ : RestrictedLorentzGroup) (a q : M4) :
    translationChar (-(((Λ⁻¹ : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) a)) q
      = (translationChar a ((Λ : M4 ≃L[ℝ] M4) q))⁻¹ := by
  rw [translationChar_inv_left, translationChar_lorentz_transfer]

/-- On the translation subgroup the conditional Poincaré action is the translation
representation: the measure hypothesis is vacuous there. -/
theorem shellPoincare_translation (m : ℝ) (a : M4)
    (h1 : LorentzShellPreserves m (1 : RestrictedLorentzGroup)) :
    shellPoincare m ⟨a, 1⟩ h1 = shellTranslate m a := by
  have hrefl : Lp.measurePreservingEquiv (𝕜 := ℂ) (E := ℂ) (p := 2)
      (lorentzMeasurableEquiv (1 : RestrictedLorentzGroup)).symm
        (h1.symm (lorentzMeasurableEquiv (1 : RestrictedLorentzGroup))) = 1 := by
    simp only [lorentzMeasurableEquiv_one, MeasurableEquiv.symm_refl]
    exact Lp.measurePreservingEquiv_refl
  rw [shellPoincare, shellTranslate]
  show (Lp.measurePreservingEquiv (𝕜 := ℂ) (E := ℂ) (p := 2)
      (lorentzMeasurableEquiv (1 : RestrictedLorentzGroup)).symm
        (h1.symm (lorentzMeasurableEquiv (1 : RestrictedLorentzGroup)))).trans _ = _
  rw [hrefl, LinearIsometryEquiv.one_trans]

/-- **Conditional inverse law**: under the H1 hypothesis the inverse of the Poincaré action
of `g` is the action of `g⁻¹`, with `g⁻¹ = (-Λ⁻¹a, Λ⁻¹)` the frozen semidirect inverse. The
algebraic engine is `translationChar_inv_lorentz`, i.e. form preservation
`η(Λ⁻¹a, q) = η(a, Λq)`. -/
theorem shellPoincare_symm (m : ℝ) (g : PoincareGroup)
    (hg : LorentzShellPreserves m g.lorentz) :
    (shellPoincare m g hg).symm = shellPoincare m g⁻¹ hg.inv := by
  have hsymm : (lorentzMeasurableEquiv (g⁻¹).lorentz).symm
      = lorentzMeasurableEquiv g.lorentz := by
    rw [PoincareGroup.inv_lorentz, ← lorentzMeasurableEquiv_symm,
      MeasurableEquiv.symm_symm]
  have hprod : shellPoincare m g hg * shellPoincare m g⁻¹ hg.inv = 1 := by
    refine LinearIsometryEquiv.ext fun ψ => ?_
    show shellPoincare m g hg (shellPoincare m g⁻¹ hg.inv ψ) = ψ
    refine Lp.ext ?_
    have hmp : MeasurePreserving (⇑(lorentzMeasurableEquiv g.lorentz).symm)
        (massShellMeasure m) (massShellMeasure m) :=
      hg.symm (lorentzMeasurableEquiv g.lorentz)
    have houter := coeFn_shellPoincare m g hg (shellPoincare m g⁻¹ hg.inv ψ)
    have hinner' :
        (fun q => ((shellPoincare m g⁻¹ hg.inv ψ : ShellOneParticle m) : M4 → ℂ)
            ((lorentzMeasurableEquiv g.lorentz).symm q))
          =ᵐ[massShellMeasure m]
            (fun q => translationChar (g⁻¹).translation q
              * (ψ : M4 → ℂ) ((lorentzMeasurableEquiv (g⁻¹).lorentz).symm q))
              ∘ fun q => (lorentzMeasurableEquiv g.lorentz).symm q := by
      refine ae_eq_comp hmp.measurable.aemeasurable ?_
      rw [hmp.map_eq]
      exact coeFn_shellPoincare m g⁻¹ hg.inv ψ
    filter_upwards [houter, hinner'] with q h1 h2
    have hchar_ne : translationChar g.translation q ≠ 0 := by
      intro hzero
      have h0 : ‖(0 : ℂ)‖ = 1 := by rw [← hzero]; exact norm_translationChar g.translation q
      simp at h0
    have hpt : translationChar (g⁻¹).translation
        ((lorentzMeasurableEquiv g.lorentz).symm q)
          = (translationChar g.translation q)⁻¹ := by
      rw [PoincareGroup.inv_translation, translationChar_inv_lorentz,
        show ((g.lorentz : M4 ≃L[ℝ] M4)) ((lorentzMeasurableEquiv g.lorentz).symm q) = q from
          (lorentzMeasurableEquiv g.lorentz).apply_symm_apply q]
    calc ((shellPoincare m g hg (shellPoincare m g⁻¹ hg.inv ψ) : ShellOneParticle m) : M4 → ℂ) q
        = translationChar g.translation q
            * ((shellPoincare m g⁻¹ hg.inv ψ : ShellOneParticle m) : M4 → ℂ)
              ((lorentzMeasurableEquiv g.lorentz).symm q) := h1
      _ = translationChar g.translation q
            * ((translationChar g.translation q)⁻¹
              * (ψ : M4 → ℂ) ((lorentzMeasurableEquiv (g⁻¹).lorentz).symm
                  ((lorentzMeasurableEquiv g.lorentz).symm q))) := by
            rw [h2]
            simp only [Function.comp_apply]
            rw [hpt]
      _ = (ψ : M4 → ℂ) q := by
            rw [hsymm]
            rw [show (lorentzMeasurableEquiv g.lorentz)
                ((lorentzMeasurableEquiv g.lorentz).symm q) = q from
              (lorentzMeasurableEquiv g.lorentz).apply_symm_apply q]
            rw [← mul_assoc, mul_inv_cancel₀ hchar_ne, one_mul]
  have h := eq_inv_of_mul_eq_one_right hprod
  rw [h, LinearIsometryEquiv.inv_def]

/-- **Conditional unitarity**: under the H1 hypothesis the Poincaré action preserves the
one-particle inner product; it is by construction a linear isometry *equivalence*, so its
inverse is again of that form. Both facts are conditional on `hg` only through the
existence of the pullback factor. -/
theorem inner_shellPoincare (m : ℝ) (g : PoincareGroup)
    (hg : LorentzShellPreserves m g.lorentz) (ψ φ : ShellOneParticle m) :
    inner ℂ (shellPoincare m g hg ψ) (shellPoincare m g hg φ) = inner ℂ ψ φ :=
  (shellPoincare m g hg).inner_map_map ψ φ

@[simp]
theorem norm_shellPoincare (m : ℝ) (g : PoincareGroup)
    (hg : LorentzShellPreserves m g.lorentz) (ψ : ShellOneParticle m) :
    ‖shellPoincare m g hg ψ‖ = ‖ψ‖ :=
  (shellPoincare m g hg).norm_map ψ

end QFT.KleinGordon
