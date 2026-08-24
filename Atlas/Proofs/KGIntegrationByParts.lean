import Atlas.Proofs.KleinGordon
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# P2.6c / L3 — integration by parts on the spatial slice

The analytic engine of the local-energy argument for finite propagation speed: the
divergence of a `C¹` compactly supported vector field integrates to zero, and the weighted
form of that identity is integration by parts,

`∫ χ · div V = - ∫ ⟪∇χ, V⟫`.

In Evans' energy method for `u_tt - Δu` one differentiates the localized energy
`e(t) = ½∫_{B(x0, t0-t)} (u_t² + |∇u|²)` and moves the spatial derivatives off `u_t` onto the
cutoff; every such step is one application of the weighted identity proved here, with
`V = u_t ∇u` the energy flux and `χ` the smoothed cone cutoff of
`Atlas.Proofs.KGConeCutoff`.

## Layout

Two layers, one adapter.

* **Pi carrier** (`MeasureTheory`, generic in the dimension, upstreamable): the coordinate
  divergence `piDivergence V x = ∑ i, fderiv ℝ V x (Pi.single i 1) i` of a field on
  `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`, and `MeasureTheory.integral_piDivergence_eq_zero`: for `C¹` `V`
  with compact support the integral of `piDivergence V` over all of `ℝⁿ⁺¹` vanishes. The
  proof puts the support strictly inside an axis-parallel box, applies Mathlib's box
  divergence theorem, and kills every face integral because each face lies outside the
  support.
* **`M3` layer** (`QFT.KleinGordon`): the Euclidean divergence
  `divergence V x = ∑ i, fderiv ℝ V x (EuclideanSpace.single i 1) i` on the spatial slice,
  its off-support vanishing, continuity, compact support and integrability, the product
  rule `divergence_smul`, the compact-support corollary `integral_divergence_eq_zero`, and
  the weighted identity `integral_mul_divergence` with its two compact-support
  specializations (cutoff compactly supported, field compactly supported).
* **Adapter**: `M3 = EuclideanSpace ℝ (Fin 3)` is `WithLp 2 (Fin 3 → ℝ)`, a one-field
  structure and *not* the Pi type, so the transfer is explicit: `piTransfer V` conjugates
  `V` by `EuclideanSpace.equiv (Fin 3) ℝ`, `piDivergence_piTransfer` matches the two
  divergences pointwise (the conjugating equivalence sends `Pi.single i 1` to
  `EuclideanSpace.single i 1`), and `PiLp.volume_preserving_toLp` moves the integral. No
  `2π` or frequency/physical-coordinate rescaling enters anywhere in this file: both
  carriers use the same Lebesgue measure and the same standard basis.

## Conventions

* `divergence` and `piDivergence` are the traces of the Fréchet derivative against the
  standard basis; `divergence_eq_sum_inner` records the coordinate-free reading
  `∑ i ⟪eᵢ, dV(x) eᵢ⟫` on the Euclidean slice.
* `∇` is Mathlib's `gradient`; `⟪·,·⟫` is the real inner product of `M3`. The sign
  convention is Evans': the boundary term is absent because of compact support, so the
  weighted identity carries a single minus sign.
* Smoothness is stated at `ContDiff ℝ 1`, the exact regularity the divergence theorem
  needs; every consumer in the cone-cutoff lane is `C^∞`.

## Sources

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS (2010), Graduate Studies in
  Math. 19: §2.4 *Wave equation*, subsection §2.4.3 *Energy methods* — the energy method
  for `u_tt - Δu`, uniqueness, domain of dependence and finite propagation speed. The
  divergence/Green identity used there to integrate `∇u_t · ∇u` by parts on the shrinking
  ball is exactly `integral_mul_divergence` with a smoothed cutoff in place of the sharp
  indicator. Cited at section level; no numbered display of that subsection is asserted.
* Mathlib sources, verified in-tree (toolchain v4.31):
  `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean` —
  `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` is the box divergence
  theorem consumed here (Bochner integral over `Set.Icc a b`, continuity on the closed box,
  differentiability off a countable set, integrable divergence; conclusion a signed sum of
  face integrals), itself a corollary of
  `BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt` in
  `Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean`.
  `Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean` — `PiLp.volume_preserving_toLp`
  and `MeasurableEquiv.toLp` give the volume-preserving identification of the two carriers.
  `Mathlib/Analysis/Calculus/Gradient/Basic.lean` — `inner_gradient_left`.
  `Mathlib/Analysis/Calculus/FDeriv/Mul.lean` — `HasFDerivAt.smul`.
  `Mathlib/Analysis/Calculus/FDeriv/Const.lean` — `support_fderiv_subset`.
-/

noncomputable section

open Set MeasureTheory

/-- Compact support propagates to any function that vanishes off the topological support of
the given one. This is `HasCompactSupport.mono'` with the side condition in the form the
call sites actually have; the `Pi`-algebra lemmas `HasCompactSupport.smul_right` and friends
are unusable here because matching their conclusions forces higher-order unification. -/
private theorem hasCompactSupport_of_vanishing {α β γ : Type*} [TopologicalSpace α] [Zero β]
    [Zero γ] {f : α → β} {g : α → γ} (hf : HasCompactSupport f)
    (h : ∀ x, x ∉ tsupport f → g x = 0) : HasCompactSupport g :=
  hf.mono' fun x hx => by
    by_contra hns
    exact hx (h x hns)

namespace MeasureTheory

/-! ### The Pi carrier `ℝⁿ⁺¹ = Fin (n + 1) → ℝ` -/

section PiCarrier

variable {n : ℕ}

/-- The coordinate divergence of a vector field on `ℝⁿ⁺¹`: the trace of the Fréchet
derivative against the standard basis `eᵢ = Pi.single i 1`. This is verbatim the integrand
of Mathlib's box divergence theorem
(`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`). -/
def piDivergence (V : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, fderiv ℝ V x (Pi.single i 1) i

variable {V : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}

/-- Off the topological support of `V` the derivative, hence the divergence, vanishes
(`support_fderiv_subset`). -/
theorem piDivergence_of_notMem_tsupport {x : Fin (n + 1) → ℝ} (hx : x ∉ tsupport V) :
    piDivergence V x = 0 := by
  have h : fderiv ℝ V x = 0 :=
    Function.notMem_support.mp fun hmem => hx (support_fderiv_subset ℝ hmem)
  simp [piDivergence, h]

theorem continuous_piDivergence (hV : ContDiff ℝ 1 V) : Continuous (piDivergence V) := by
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_apply i).comp
    ((hV.continuous_fderiv one_ne_zero).clm_apply continuous_const)

theorem hasCompactSupport_piDivergence (hV : HasCompactSupport V) :
    HasCompactSupport (piDivergence V) :=
  hasCompactSupport_of_vanishing (g := piDivergence V) hV fun _ hx =>
    piDivergence_of_notMem_tsupport hx

theorem integrable_piDivergence (hV : ContDiff ℝ 1 V) (hsupp : HasCompactSupport V) :
    Integrable (piDivergence V) :=
  (continuous_piDivergence hV).integrable_of_hasCompactSupport
    (hasCompactSupport_piDivergence hsupp)

/-- **The divergence of a compactly supported `C¹` field integrates to zero** on
`ℝⁿ⁺¹`. Proof: the support sits inside the open box `(-S, S)^{n+1}`, so Mathlib's box
divergence theorem `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` applies
on the closed box `[-S, S]^{n+1}`, and every one of its `2(n + 1)` face integrals has an
identically zero integrand — each face is pinned at a coordinate of modulus `S`, hence
outside the support. This is the boundary-term-free case of the Gauss–Green identity used in
Evans' energy method (Evans §2.4.3, section level). -/
theorem integral_piDivergence_eq_zero (V : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hV : ContDiff ℝ 1 V) (hsupp : HasCompactSupport V) :
    ∫ x, piDivergence V x = 0 := by
  obtain ⟨R, hR⟩ := hsupp.isCompact.isBounded.subset_closedBall (0 : Fin (n + 1) → ℝ)
  obtain ⟨S, hSpos, hRS⟩ : ∃ S : ℝ, 0 < S ∧ R < S :=
    ⟨|R| + 1, by positivity, lt_of_le_of_lt (le_abs_self R) (by linarith)⟩
  -- Any point with one large coordinate lies off the support.
  have hout : ∀ (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)), S ≤ |x j| → x ∉ tsupport V := by
    intro x j hj hx
    have h1 : ‖x‖ ≤ R := by
      have h := hR hx
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    have h2 : |x j| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
    linarith
  set a : Fin (n + 1) → ℝ := fun _ => -S with ha
  set b : Fin (n + 1) → ℝ := fun _ => S with hb
  have hai : ∀ i, a i = -S := fun i => by rw [ha]
  have hbi : ∀ i, b i = S := fun i => by rw [hb]
  have hle : a ≤ b := fun i => by rw [hai i, hbi i]; linarith
  -- Outside the box the divergence vanishes, so the full integral is the box integral.
  have hzero : ∀ x : Fin (n + 1) → ℝ, x ∉ Set.Icc a b → piDivergence V x = 0 := by
    intro x hx
    obtain ⟨j, hj⟩ : ∃ j, S ≤ |x j| := by
      by_contra hcon
      simp only [not_exists, not_le] at hcon
      refine hx (Set.mem_Icc.2 ⟨fun i => ?_, fun i => ?_⟩)
      · rw [hai i]; exact (abs_lt.1 (hcon i)).1.le
      · rw [hbi i]; exact (abs_lt.1 (hcon i)).2.le
    exact piDivergence_of_notMem_tsupport (hout x j hj)
  have hset : ∫ x, piDivergence V x = ∫ x in Set.Icc a b, piDivergence V x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable a b hle V (fderiv ℝ V)
    ∅ Set.countable_empty hV.continuous.continuousOn
    (fun x _ => (hV.differentiable one_ne_zero x).hasFDerivAt)
    ((integrable_piDivergence hV hsupp).integrableOn)
  have hbox : ∫ x in Set.Icc a b, piDivergence V x
      = ∑ i : Fin (n + 1),
        ((∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), V (i.insertNth (b i) x) i) -
          ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), V (i.insertNth (a i) x) i) := hdiv
  rw [hset, hbox]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hface : ∀ c : ℝ, S ≤ |c| → ∀ y : Fin n → ℝ, V (i.insertNth c y) i = 0 := by
    intro c hc y
    have hns : i.insertNth c y ∉ tsupport V := by
      refine hout _ i ?_
      rwa [Fin.insertNth_apply_same]
    simp [image_eq_zero_of_notMem_tsupport hns]
  have hfront := hface (b i) (by rw [hbi i, abs_of_pos hSpos])
  have hback := hface (a i) (by rw [hai i, abs_neg, abs_of_pos hSpos])
  simp [hfront, hback]

end PiCarrier

end MeasureTheory

namespace QFT.KleinGordon

open MeasureTheory

/-! ### The Euclidean divergence on the spatial slice -/

/-- The Euclidean divergence of a vector field on the spatial slice `M3 = ℝ³`: the trace of
the Fréchet derivative against the standard orthonormal basis
`eᵢ = EuclideanSpace.single i 1`. -/
def divergence (V : M3 → M3) (x : M3) : ℝ :=
  ∑ i, fderiv ℝ V x (EuclideanSpace.single i (1 : ℝ)) i

/-- Inner-product form of `divergence`: the trace of `dV(x)` against the standard
orthonormal basis, `∑ i ⟪eᵢ, dV(x) eᵢ⟫`. -/
theorem divergence_eq_sum_inner (V : M3 → M3) (x : M3) :
    divergence V x
      = ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ))
          (fderiv ℝ V x (EuclideanSpace.single i (1 : ℝ))) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.inner_single_left]
  simp

variable {V : M3 → M3}

theorem divergence_of_notMem_tsupport {x : M3} (hx : x ∉ tsupport V) : divergence V x = 0 := by
  have h : fderiv ℝ V x = 0 :=
    Function.notMem_support.mp fun hmem => hx (support_fderiv_subset ℝ hmem)
  simp [divergence, h]

theorem continuous_divergence (hV : ContDiff ℝ 1 V) : Continuous (divergence V) := by
  refine continuous_finsetSum _ fun i _ => ?_
  exact (EuclideanSpace.proj i : M3 →L[ℝ] ℝ).continuous.comp
    ((hV.continuous_fderiv one_ne_zero).clm_apply continuous_const)

theorem hasCompactSupport_divergence (hV : HasCompactSupport V) :
    HasCompactSupport (divergence V) :=
  hasCompactSupport_of_vanishing (g := divergence V) hV fun _ hx =>
    divergence_of_notMem_tsupport hx

theorem integrable_divergence (hV : ContDiff ℝ 1 V) (hsupp : HasCompactSupport V) :
    Integrable (divergence V) :=
  (continuous_divergence hV).integrable_of_hasCompactSupport
    (hasCompactSupport_divergence hsupp)

/-! ### Adapter to the Pi carrier

`M3` is `WithLp 2 (Fin 3 → ℝ)`, a one-field structure, so it is a different type from
`Fin 3 → ℝ`. The conjugation by `EuclideanSpace.equiv (Fin 3) ℝ` transports fields, and
`PiLp.volume_preserving_toLp` transports integrals. -/

section Adapter

/-- The conjugating linear identification `M3 ≃L[ℝ] (Fin 3 → ℝ)`; its forward map is
`WithLp.ofLp` and its inverse `WithLp.toLp 2`. -/
private def piEquiv : M3 ≃L[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ

/-- A vector field on `M3` read on the Pi carrier. -/
private def piTransfer (V : M3 → M3) : (Fin 3 → ℝ) → Fin 3 → ℝ :=
  fun z => WithLp.ofLp (V (WithLp.toLp 2 z))

private theorem hasFDerivAt_piTransfer (hV : Differentiable ℝ V) (y : Fin 3 → ℝ) :
    HasFDerivAt (piTransfer V)
      ((piEquiv : M3 →L[ℝ] (Fin 3 → ℝ)).comp
        ((fderiv ℝ V (WithLp.toLp 2 y)).comp (piEquiv.symm : (Fin 3 → ℝ) →L[ℝ] M3))) y := by
  have h1 : HasFDerivAt (fun z : Fin 3 → ℝ => V (WithLp.toLp 2 z))
      ((fderiv ℝ V (WithLp.toLp 2 y)).comp (piEquiv.symm : (Fin 3 → ℝ) →L[ℝ] M3)) y :=
    (hV (WithLp.toLp 2 y)).hasFDerivAt.comp y
      (piEquiv.symm : (Fin 3 → ℝ) →L[ℝ] M3).hasFDerivAt
  exact (piEquiv : M3 →L[ℝ] (Fin 3 → ℝ)).hasFDerivAt.comp y h1

/-- The two divergences agree under the identification: the conjugating equivalence sends
`Pi.single i 1` to `EuclideanSpace.single i 1`, so the traces match term by term. -/
private theorem piDivergence_piTransfer (hV : Differentiable ℝ V) (y : Fin 3 → ℝ) :
    piDivergence (piTransfer V) y = divergence V (WithLp.toLp 2 y) := by
  rw [piDivergence, (hasFDerivAt_piTransfer hV y).fderiv, divergence]
  exact Finset.sum_congr rfl fun i _ => rfl

private theorem contDiff_piTransfer (hV : ContDiff ℝ 1 V) : ContDiff ℝ 1 (piTransfer V) :=
  (piEquiv : M3 →L[ℝ] (Fin 3 → ℝ)).contDiff.comp
    (hV.comp (piEquiv.symm : (Fin 3 → ℝ) →L[ℝ] M3).contDiff)

private theorem hasCompactSupport_piTransfer (hsupp : HasCompactSupport V) :
    HasCompactSupport (piTransfer V) := by
  have h1 : HasCompactSupport (fun z : Fin 3 → ℝ => V (WithLp.toLp 2 z)) :=
    hsupp.comp_isClosedEmbedding piEquiv.symm.toHomeomorph.isClosedEmbedding
  exact h1.comp_left (g := fun w : M3 => WithLp.ofLp w) rfl

end Adapter

/-! ### The divergence theorem on `M3` -/

/-- **The divergence of a compactly supported `C¹` field on the spatial slice integrates to
zero.** Transported from `MeasureTheory.integral_piDivergence_eq_zero` along the
volume-preserving identification `PiLp.volume_preserving_toLp`. -/
theorem integral_divergence_eq_zero (V : M3 → M3) (hV : ContDiff ℝ 1 V)
    (hsupp : HasCompactSupport V) : ∫ x, divergence V x = 0 := by
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin 3 → ℝ) → M3) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin 3 → ℝ) → M3) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
  calc ∫ x : M3, divergence V x
      = ∫ y : Fin 3 → ℝ, divergence V (WithLp.toLp 2 y) := (hmp.integral_comp hemb _).symm
    _ = ∫ y : Fin 3 → ℝ, piDivergence (piTransfer V) y := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        exact (piDivergence_piTransfer (hV.differentiable one_ne_zero) y).symm
    _ = 0 := integral_piDivergence_eq_zero _ (contDiff_piTransfer hV)
        (hasCompactSupport_piTransfer hsupp)

/-! ### Integration by parts -/

/-- **Product rule for the Euclidean divergence**: `div (χ V) = ⟪∇χ, V⟫ + χ · div V`. -/
theorem divergence_smul {chi : M3 → ℝ} {x : M3} (hchi : DifferentiableAt ℝ chi x)
    (hV : DifferentiableAt ℝ V x) :
    divergence (fun y => chi y • V y) x
      = inner ℝ (gradient chi x) (V x) + chi x * divergence V x := by
  have hd : HasFDerivAt (fun y => chi y • V y)
      (chi x • fderiv ℝ V x + (fderiv ℝ chi x).smulRight (V x)) x :=
    hchi.hasFDerivAt.smul hV.hasFDerivAt
  have hgrad : ∀ i : Fin 3,
      fderiv ℝ chi x (EuclideanSpace.single i (1 : ℝ)) = gradient chi x i := by
    intro i
    rw [← inner_gradient_left (𝕜 := ℝ), EuclideanSpace.inner_single_right]
    simp
  have hterm : ∀ i : Fin 3,
      (chi x • fderiv ℝ V x + (fderiv ℝ chi x).smulRight (V x))
          (EuclideanSpace.single i (1 : ℝ)) i
        = gradient chi x i * V x i
          + chi x * fderiv ℝ V x (EuclideanSpace.single i (1 : ℝ)) i := by
    intro i
    have happ : (chi x • fderiv ℝ V x + (fderiv ℝ chi x).smulRight (V x))
        (EuclideanSpace.single i (1 : ℝ))
          = chi x • fderiv ℝ V x (EuclideanSpace.single i (1 : ℝ))
            + fderiv ℝ chi x (EuclideanSpace.single i (1 : ℝ)) • V x := rfl
    rw [happ]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hgrad i]
    ring
  rw [divergence, hd.fderiv, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i,
    Finset.sum_add_distrib, divergence, Finset.mul_sum]
  congr 1
  rw [PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

/-- **Weighted integration by parts on the spatial slice**: for `C¹` weight `χ` and `C¹`
field `V` whose product is compactly supported,

`∫ χ · div V = - ∫ ⟪∇χ, V⟫`.

The boundary term of the Gauss–Green identity is absent because `χ V` has compact support
(Evans, *Partial Differential Equations*, 2nd ed., §2.4.3, section level). Only the left-hand
integrand is assumed integrable: the right-hand one is then the difference of
`div (χ V)` — continuous with compact support — and `χ · div V`. -/
theorem integral_mul_divergence {chi : M3 → ℝ} (hchi : ContDiff ℝ 1 chi) (hV : ContDiff ℝ 1 V)
    (hcs : HasCompactSupport fun x => chi x • V x)
    (hint : Integrable fun x => chi x * divergence V x) :
    ∫ x, chi x * divergence V x = -∫ x, inner ℝ (gradient chi x) (V x) := by
  have hsmul : ContDiff ℝ 1 fun x => chi x • V x := hchi.smul hV
  have hpt : ∀ x, divergence (fun y => chi y • V y) x
      = inner ℝ (gradient chi x) (V x) + chi x * divergence V x := fun x =>
    divergence_smul (hchi.differentiable one_ne_zero x) (hV.differentiable one_ne_zero x)
  have hsum : Integrable fun x =>
      inner ℝ (gradient chi x) (V x) + chi x * divergence V x :=
    (integrable_divergence hsmul hcs).congr (Filter.Eventually.of_forall hpt)
  have hflux : Integrable fun x => (inner ℝ (gradient chi x) (V x) : ℝ) :=
    (hsum.sub hint).congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, add_sub_cancel_right])
  have htotal : (∫ x, inner ℝ (gradient chi x) (V x)) + ∫ x, chi x * divergence V x = 0 := by
    rw [← integral_add hflux hint]
    calc ∫ x, (inner ℝ (gradient chi x) (V x) + chi x * divergence V x)
        = ∫ x, divergence (fun y => chi y • V y) x :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => (hpt x).symm)
      _ = 0 := integral_divergence_eq_zero _ hsmul hcs
  linarith [htotal]

/-- Integration by parts with a compactly supported weight — the shape the cone-cutoff lane
uses, with `χ` the smoothed cutoff of `Atlas.Proofs.KGConeCutoff` and `V` the energy flux.
Both integrability hypotheses of `integral_mul_divergence` are automatic here. -/
theorem integral_mul_divergence_of_hasCompactSupport_weight {chi : M3 → ℝ}
    (hchi : ContDiff ℝ 1 chi) (hV : ContDiff ℝ 1 V) (hcs : HasCompactSupport chi) :
    ∫ x, chi x * divergence V x = -∫ x, inner ℝ (gradient chi x) (V x) :=
  integral_mul_divergence hchi hV
    (hasCompactSupport_of_vanishing (g := fun x => chi x • V x) hcs fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx])
    ((hchi.continuous.mul (continuous_divergence hV)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanishing (g := fun x => chi x * divergence V x) hcs
        fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]))

/-- Integration by parts with a compactly supported field and an unrestricted `C¹` weight. -/
theorem integral_mul_divergence_of_hasCompactSupport_field {chi : M3 → ℝ}
    (hchi : ContDiff ℝ 1 chi) (hV : ContDiff ℝ 1 V) (hcs : HasCompactSupport V) :
    ∫ x, chi x * divergence V x = -∫ x, inner ℝ (gradient chi x) (V x) :=
  integral_mul_divergence hchi hV
    (hasCompactSupport_of_vanishing (g := fun x => chi x • V x) hcs fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx])
    ((hchi.continuous.mul (continuous_divergence hV)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanishing (g := fun x => chi x * divergence V x)
        (hasCompactSupport_divergence hcs) fun x hx => by
          simp [image_eq_zero_of_notMem_tsupport hx]))

end QFT.KleinGordon
