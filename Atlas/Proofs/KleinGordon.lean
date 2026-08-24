import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Atlas.Specs.Spacetime.Minkowski

/-!
# P2.6c / L0 — Klein–Gordon foundation layer: dispersion relation and energy form

Ground floor of the Pauli–Jordan lane (blueprint node **P2.6c**, lemma node **L0**). Two
independent pieces, both stated on the time-zero slice `M3 = ℝ³` of the frozen Minkowski
carrier `Spacetime.Minkowski.M4`:

* the **dispersion relation** `Ω(k) = √(4π²‖k‖² + m²)` — the Fourier symbol of the
  positive operator `B = √(-Δ + m²)` — with its symbol identity, two-sided elementary
  bounds, monotonicity, continuity and smoothness, plus the anchor tying it to the frozen
  Minkowski geometry (the on-shell four-momentum lies in the frozen future time cone);
* the **classical Klein–Gordon energy form** `E(f, g) = ½∫ (‖g‖² + ‖∇f‖² + m²‖f‖²)` on
  Schwartz Cauchy data, with integrability, nonnegativity, and definiteness.

## Contents

* `QFT.KleinGordon.M3` — the spatial slice `ℝ³`, carrier of Cauchy data and of spatial
  momenta.
* `QFT.KleinGordon.dispersion` — `Ω(k)`; `dispersion_sq` is the symbol identity
  `Ω(k)² = 4π²‖k‖² + m²`, `le_dispersion`/`dispersion_pos` the mass lower bound,
  `two_pi_norm_le_dispersion`/`dispersion_le` the two-sided bound
  `max (2π‖k‖) m ≤ Ω(k) ≤ 2π‖k‖ + m`, `dispersion_mono` monotonicity in `‖k‖`, and
  `continuous_dispersion`/`contDiff_dispersion` the regularity (the radicand is bounded
  below by `m² > 0`, so `Real.sqrt` is smooth on the whole range — there is no exceptional
  point to remove).
* `QFT.KleinGordon.onShell` — the positive-energy mass-shell four-momentum
  `p = (Ω(k), 2πk)` in `M4`; `minkowskiForm_onShell_self` is `η(p, p) = -m²` and
  `onShell_inFutureTimeCone` places it in the frozen open future time cone of
  `Atlas.Specs.Spacetime.Minkowski`.
* `QFT.KleinGordon.energyDensity` / `QFT.KleinGordon.energy` — the energy density and the
  energy functional on Schwartz Cauchy data, with `integrable_energyDensity`,
  `energy_nonneg`, `energy_eq_zero_iff` (definiteness for `m ≠ 0`) and its corollary
  `energy_pos`.

Deliberately NOT here: the Plancherel form of the energy (`E(f, g)` rewritten as a
momentum integral against `dispersion`, lemma node L1) and the finite-propagation-speed
estimate for the Klein–Gordon flow (lemma node L2 and above). This file only fixes the
objects those statements are about.

## Conventions

* Fourier normalization is Mathlib's: `Real.fourierIntegral` (`𝓕 f w = ∫ e^{-2πi⟪v,w⟫} f v`,
  `Mathlib/Analysis/Fourier/FourierTransform.lean`) and `Real.fourier_fderiv`
  (`Mathlib/Analysis/Fourier/FourierTransformDeriv.lean`), which multiplies the transform
  by `2πi` times the pairing when a Fréchet derivative is taken. Each `∂ⱼ` therefore
  contributes a factor `±2πiwⱼ`, so `-Δ` has symbol `4π²‖w‖²` (the sign drops out of the
  square) and `B = √(-Δ + m²)` has symbol `Ω(k) = √(4π²‖k‖² + m²)`. Reed & Simon put no
  `2π` in the exponent, and there `-Δ` is multiplication by `|λ|²` (II, §IX.7,
  Thm IX.27(a)), giving the familiar `(|λ|² + m²)^{1/2}`. The two conventions differ
  exactly by `λ = 2πk`, which is the whole content of the `4π²` here.
* Minkowski sign convention is the frozen mostly-plus one of
  `Atlas/Specs/Spacetime/Minkowski.lean`: coordinate `0` is time, `η(v, v) < 0` is
  timelike. The mass shell is therefore `η(p, p) = -m²` with `p⁰ > 0`.
* Cauchy data are real-valued Schwartz functions `f, g : 𝓢(M3, ℝ)`: `f` is the field at
  time zero, `g` its time derivative. `∇` is Mathlib's `gradient`, so `‖∇f x‖` is the
  Euclidean length of the spatial gradient.
* The mass enters as a bare real `m`. Statements needing a nonzero mass carry `m ≠ 0`,
  statements needing a nonnegative one carry `0 ≤ m`; the physical case is `0 < m`, which
  implies both.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II: Fourier Analysis,
  Self-Adjointness*, Academic Press (1975): §X.13 *Classical nonlinear wave equations*,
  p. 293 — the Klein–Gordon Hamiltonian
  `H(u, v) = ½ ∫ (v(x)² + (∇u(x))² + m²u(x)² + (λ/2)u(x)⁴) d³x`, whose `λ = 0` case is
  `energy` here; and p. 295 — the first-order reformulation through the operator
  `B ≥ mI`, the positive square root of `B² = -Δ + m²` on `L²(ℝ³)`, whose symbol is
  `dispersion`. §X.7 *Free quantum fields*, eq. (X.80) — the free Hamiltonian of mass `m`,
  `H₀ = ∫ μ(p) a*(p)a(p) d³p`, the second-quantized form of the same one-particle energy.
  §IX.1, opening Definition — the transform `f̂(λ) = c_n ∫ e^{-iλ·x} f(x) dx`, whose
  exponent carries no `2π`; §IX.7, Thm IX.27(a) — `-Δ` is multiplication by `|λ|²` in
  those variables, the fact the `4π²` above converts.
* R. M. Wald, *General Relativity*, University of Chicago Press (1984), ch. 10 *The
  Initial Value Formulation*, §10.1 *Initial Value Formulation for Particles and Fields* —
  the energy method for the Klein–Gordon equation whose shape lemma nodes L2+ follow.
  Cited at section level: the section number and title are checked against the publisher's
  table of contents, and no numbered display of that section is asserted here.
* Streater & Wightman, *PCT, Spin and Statistics, and All That* (1964; Princeton Landmarks
  ed. 2000), Ch. 3 — the mass-shell/spectrum convention that `onShell` matches.
-/

open MeasureTheory Real
open scoped ENNReal Gradient SchwartzMap

namespace QFT.KleinGordon

/-- The spatial slice `ℝ³`: the time-zero hyperplane of the frozen Minkowski carrier
`Spacetime.Minkowski.M4`, carrying both Cauchy data (as functions of position) and spatial
momenta (as their Fourier variables). Kept as a bare `EuclideanSpace` so that Mathlib's
Haar measure, Schwartz space and Fourier API apply without transport. -/
abbrev M3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ### The Klein–Gordon dispersion relation -/

/-- The Klein–Gordon dispersion relation `Ω(k) = √(4π²‖k‖² + m²)`: the Fourier symbol, in
Mathlib's `e^{-2πi⟪x,ξ⟫}` normalization, of the positive operator `B = √(-Δ + m²)` of
Reed & Simon II, §X.13, p. 295 (`B ≥ mI`, `B² = -Δ + m²` on `L²(ℝ³)`). Second-quantized it
is the one-particle energy `μ(p)` of the free field of mass `m` (Reed & Simon II, §X.7,
eq. (X.80)). -/
noncomputable def dispersion (m : ℝ) (k : M3) : ℝ :=
  √(4 * π ^ 2 * ‖k‖ ^ 2 + m ^ 2)

variable (m : ℝ) (k : M3)

/-- The energy is a square root, hence nonnegative for every mass, real or imaginary. -/
theorem dispersion_nonneg : 0 ≤ dispersion m k :=
  Real.sqrt_nonneg _

/-- **The Klein–Gordon symbol identity**: `Ω(k)² = 4π²‖k‖² + m²`, i.e. `Ω` is the positive
square root of the symbol of `-Δ + m²` (Reed & Simon II, §X.13, p. 295). -/
theorem dispersion_sq : dispersion m k ^ 2 = 4 * π ^ 2 * ‖k‖ ^ 2 + m ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- At zero momentum the dispersion relation returns the rest mass. -/
@[simp] theorem dispersion_apply_zero : dispersion m 0 = |m| := by
  rw [dispersion, norm_zero]
  simpa using Real.sqrt_sq_eq_abs m

/-- **The mass lower bound** `m ≤ Ω(k)`: `B ≥ mI` in Reed & Simon II, §X.13, p. 295. -/
theorem le_dispersion (hm : 0 ≤ m) : m ≤ dispersion m k := by
  have hrad : m ^ 2 ≤ 4 * π ^ 2 * ‖k‖ ^ 2 + m ^ 2 := by
    have hk : (0 : ℝ) ≤ 4 * π ^ 2 * ‖k‖ ^ 2 := by positivity
    linarith
  have h : √(m ^ 2) ≤ dispersion m k := Real.sqrt_le_sqrt hrad
  rwa [Real.sqrt_sq hm] at h

/-- With a nonzero mass the dispersion relation is strictly positive everywhere: the free
one-particle energy has a gap, which is what makes the free field's vacuum unique. -/
theorem dispersion_pos (hm : m ≠ 0) : 0 < dispersion m k := by
  have hm2 : 0 < m ^ 2 := sq_pos_iff.mpr hm
  have hk : (0 : ℝ) ≤ 4 * π ^ 2 * ‖k‖ ^ 2 := by positivity
  refine Real.sqrt_pos.mpr ?_
  linarith

/-- The momentum lower bound `2π‖k‖ ≤ Ω(k)`: an elementary consequence of
`dispersion_sq` — momentum never exceeds energy, with equality only at zero mass. -/
theorem two_pi_norm_le_dispersion : 2 * π * ‖k‖ ≤ dispersion m k := by
  rw [dispersion, show 2 * π * ‖k‖ = √((2 * π * ‖k‖) ^ 2) from
    (Real.sqrt_sq (by positivity)).symm]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg m])

/-- The elementary upper bound `Ω(k) ≤ 2π‖k‖ + m`: subadditivity of the square root on
the two contributions to `dispersion_sq`. Together with `le_dispersion` and
`two_pi_norm_le_dispersion` this pins `Ω` between `max (2π‖k‖) m` and their sum, which is
the comparison used to see that `Ω` grows exactly linearly in `‖k‖`. -/
theorem dispersion_le (hm : 0 ≤ m) : dispersion m k ≤ 2 * π * ‖k‖ + m := by
  rw [dispersion, show 2 * π * ‖k‖ + m = √((2 * π * ‖k‖ + m) ^ 2) from
    (Real.sqrt_sq (by positivity)).symm]
  refine Real.sqrt_le_sqrt ?_
  have hprod : (0 : ℝ) ≤ π * ‖k‖ * m :=
    mul_nonneg (mul_nonneg Real.pi_pos.le (norm_nonneg k)) hm
  nlinarith

/-- The dispersion relation is monotone in the momentum magnitude. -/
theorem dispersion_mono {k₁ k₂ : M3} (h : ‖k₁‖ ≤ ‖k₂‖) :
    dispersion m k₁ ≤ dispersion m k₂ := by
  have hsq : ‖k₁‖ ^ 2 ≤ ‖k₂‖ ^ 2 := by nlinarith [norm_nonneg k₁, norm_nonneg k₂]
  have hkey : 4 * π ^ 2 * ‖k₁‖ ^ 2 ≤ 4 * π ^ 2 * ‖k₂‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  refine Real.sqrt_le_sqrt ?_
  linarith

/-- The dispersion relation is continuous for every mass, including `m = 0`, since
`Real.sqrt` is continuous everywhere. -/
theorem continuous_dispersion : Continuous (dispersion m) :=
  Real.continuous_sqrt.comp (by fun_prop)

/-- The dispersion relation is smooth on all of momentum space when the mass is nonzero:
its radicand is bounded below by `m² > 0`, so the only nonsmooth point of `Real.sqrt` is
never reached. This is the regularity that makes `Ω` a temperate Fourier multiplier and
the free evolution `e^{itΩ}` differentiable in the momentum variable. -/
theorem contDiff_dispersion {n : WithTop ℕ∞} (hm : m ≠ 0) : ContDiff ℝ n (dispersion m) := by
  have hsmooth : ContDiff ℝ n fun x : M3 => 4 * π ^ 2 * ‖x‖ ^ 2 + m ^ 2 :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).add contDiff_const
  refine hsmooth.sqrt fun x => ne_of_gt ?_
  have hm2 : 0 < m ^ 2 := sq_pos_iff.mpr hm
  nlinarith [sq_nonneg ‖x‖, sq_nonneg π]

/-! ### The mass shell inside the frozen Minkowski carrier -/

open Spacetime.Minkowski

/-- Coordinates of the Euclidean norm on `M3`. -/
private theorem norm_sq_coords (x : M3) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

/-- The positive-energy on-shell four-momentum `p = (Ω(k), 2πk)` of a spatial momentum `k`,
as a vector of the frozen Minkowski carrier `M4`. The spatial part carries the `2π` of
Mathlib's Fourier normalization, so that `p` is the physical four-momentum conjugate to the
mass hyperboloid `H_m` of Reed & Simon II, §X.7 (`p·p - m² = 0`, `p⁰ > 0`). -/
noncomputable def onShell (m : ℝ) (k : M3) : M4 :=
  !₂[dispersion m k, 2 * π * k 0, 2 * π * k 1, 2 * π * k 2]

/-- The time coordinate of the on-shell four-momentum is the energy `Ω(k)`. -/
@[simp] theorem onShell_apply_zero : onShell m k 0 = dispersion m k := by
  simp [onShell]

/-- The spatial coordinates of the on-shell four-momentum are `2πk`. -/
@[simp] theorem onShell_apply_one : onShell m k 1 = 2 * π * k 0 := by
  simp [onShell]

@[simp] theorem onShell_apply_two : onShell m k 2 = 2 * π * k 1 := by
  simp [onShell]

@[simp] theorem onShell_apply_three : onShell m k 3 = 2 * π * k 2 := by
  simp [onShell]

/-- **The mass-shell identity** `η(p, p) = -m²` in the frozen mostly-plus convention of
`Atlas/Specs/Spacetime/Minkowski.lean`. This is the Minkowski-geometry content of
`dispersion_sq`, and the defining equation of the hyperboloid `H_m` on which the free
scalar field of mass `m` is built (Reed & Simon II, §X.7). -/
theorem minkowskiForm_onShell_self :
    minkowskiForm (onShell m k) (onShell m k) = -m ^ 2 := by
  rw [minkowskiForm_eq, onShell_apply_zero, onShell_apply_one, onShell_apply_two,
    onShell_apply_three]
  have hscaled : 4 * π ^ 2 * ‖k‖ ^ 2 = 4 * π ^ 2 * (k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2) := by
    rw [norm_sq_coords]
  nlinarith [dispersion_sq m k, hscaled]

/-- With a nonzero mass the on-shell four-momentum lies in the frozen **open future time
cone** `Spacetime.Minkowski.InFutureTimeCone`. This is the anchor the spectrum condition
consumes: the closure of that cone under addition (`InFutureTimeCone.add`, proved in the
P1.W2 witness layer) turns the one-particle spectrum into an `n`-particle spectrum inside
the forward cone (Streater & Wightman, Ch. 3, the spectral axiom). -/
theorem onShell_inFutureTimeCone (hm : m ≠ 0) : InFutureTimeCone (onShell m k) := by
  have hpos : 0 < dispersion m k := dispersion_pos m k hm
  refine ⟨?_, by rw [onShell_apply_zero]; exact hpos⟩
  rw [onShell_apply_zero, onShell_apply_one, onShell_apply_two, onShell_apply_three]
  have hm2 : 0 < m ^ 2 := sq_pos_iff.mpr hm
  have hscaled : 4 * π ^ 2 * ‖k‖ ^ 2 = 4 * π ^ 2 * (k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2) := by
    rw [norm_sq_coords]
  nlinarith [dispersion_sq m k, hscaled]

/-! ### The classical Klein–Gordon energy form on Schwartz Cauchy data -/

/-- The Euclidean gradient and the Fréchet derivative of a real-valued function on `M3`
have the same norm: `gradient` is the image of `fderiv` under the isometric Riesz
identification `InnerProductSpace.toDual`. -/
theorem norm_gradient_eq_norm_fderiv (u : M3 → ℝ) (x : M3) :
    ‖∇ u x‖ = ‖fderiv ℝ u x‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- The Klein–Gordon energy density of Cauchy data `(u, v)` at a point:
`½(‖v‖² + ‖∇u‖² + m²‖u‖²)`. This is the integrand of the free (`λ = 0`) Hamiltonian
`H(u, v) = ½ ∫ (v² + (∇u)² + m²u² + (λ/2)u⁴) d³x` of Reed & Simon II, §X.13, p. 293. -/
noncomputable def energyDensity (m : ℝ) (u v : M3 → ℝ) (x : M3) : ℝ :=
  (‖v x‖ ^ 2 + ‖∇ u x‖ ^ 2 + m ^ 2 * ‖u x‖ ^ 2) / 2

theorem energyDensity_nonneg (u v : M3 → ℝ) (x : M3) : 0 ≤ energyDensity m u v x := by
  unfold energyDensity; positivity

theorem continuous_energyDensity (f g : 𝓢(M3, ℝ)) :
    Continuous (energyDensity m f g) := by
  have hgrad : Continuous fun x => ∇ (f : M3 → ℝ) x :=
    (InnerProductSpace.toDual ℝ M3).symm.continuous.comp
      (SchwartzMap.fderivCLM ℝ M3 ℝ f).continuous
  exact ((((continuous_norm.comp g.continuous).pow 2).add
    ((continuous_norm.comp hgrad).pow 2)).add
    (continuous_const.mul ((continuous_norm.comp f.continuous).pow 2))).div_const 2

/-- The energy density of Schwartz Cauchy data is integrable: each of the three terms is
the squared norm of a Schwartz function (for the gradient term, of `fderivCLM f`), hence
lies in `L¹` by `SchwartzMap.memLp`. -/
theorem integrable_energyDensity (f g : 𝓢(M3, ℝ)) :
    Integrable (energyDensity m f g) := by
  have hf : Integrable fun x => ‖f x‖ ^ 2 :=
    (f.memLp ((2 : ℕ) : ℝ≥0∞) volume).integrable_norm_pow two_ne_zero
  have hg : Integrable fun x => ‖g x‖ ^ 2 :=
    (g.memLp ((2 : ℕ) : ℝ≥0∞) volume).integrable_norm_pow two_ne_zero
  have hgrad : Integrable fun x => ‖∇ (f : M3 → ℝ) x‖ ^ 2 := by
    have h := ((SchwartzMap.fderivCLM ℝ M3 ℝ f).memLp ((2 : ℕ) : ℝ≥0∞)
      volume).integrable_norm_pow two_ne_zero
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [SchwartzMap.fderivCLM_apply]
    exact congrArg (· ^ 2) (norm_gradient_eq_norm_fderiv (f : M3 → ℝ) x).symm
  exact ((hg.add hgrad).add (hf.const_mul (m ^ 2))).div_const 2

/-- The Klein–Gordon energy of Schwartz Cauchy data `(f, g)`:
`E(f, g) = ½ ∫ (‖g‖² + ‖∇f‖² + m²‖f‖²) d³x`, the `λ = 0` Hamiltonian of Reed & Simon II,
§X.13, p. 293. On solutions of the Klein–Gordon equation it is the conserved energy whose
localized version drives the finite-propagation-speed argument (Wald, *General Relativity*,
ch. 10, §10.1). -/
noncomputable def energy (m : ℝ) (f g : 𝓢(M3, ℝ)) : ℝ :=
  ∫ x, energyDensity m f g x

theorem energy_nonneg (f g : 𝓢(M3, ℝ)) : 0 ≤ energy m f g :=
  integral_nonneg fun x => energyDensity_nonneg m f g x

@[simp] theorem energy_zero : energy m 0 0 = 0 := by
  have hgrad : ∀ x : M3, ∇ ((0 : 𝓢(M3, ℝ)) : M3 → ℝ) x = 0 := fun x => by
    have hzero : ((0 : 𝓢(M3, ℝ)) : M3 → ℝ) = fun _ => 0 := rfl
    simp [gradient, hzero]
  simp [energy, energyDensity, hgrad]

/-- **Definiteness of the energy form**: for a nonzero mass, Schwartz Cauchy data of zero
energy vanish identically. The energy density is continuous and nonnegative, so a vanishing
integral forces it to vanish pointwise, and the mass term then kills `f` while the velocity
term kills `g`. This is the coercivity that makes `E` an honest norm on the finite-energy
Cauchy data (Reed & Simon II, §X.13, p. 295: `B ≥ mI` makes `‖Bu‖` an equivalent norm on
`D(B)`). -/
theorem energy_eq_zero_iff (hm : m ≠ 0) (f g : 𝓢(M3, ℝ)) :
    energy m f g = 0 ↔ f = 0 ∧ g = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · have hae := (integral_eq_zero_iff_of_nonneg (fun x => energyDensity_nonneg m f g x)
      (integrable_energyDensity m f g)).mp h
    have hpt : energyDensity m f g = 0 :=
      ((continuous_energyDensity m f g).ae_eq_iff_eq (μ := volume) continuous_const).mp hae
    have hm2 : 0 < m ^ 2 := sq_pos_iff.mpr hm
    have key : ∀ x : M3, f x = 0 ∧ g x = 0 := by
      intro x
      have hx : ‖g x‖ ^ 2 + ‖∇ (f : M3 → ℝ) x‖ ^ 2 + m ^ 2 * ‖f x‖ ^ 2 = 0 := by
        have h0 : (‖g x‖ ^ 2 + ‖∇ (f : M3 → ℝ) x‖ ^ 2 + m ^ 2 * ‖f x‖ ^ 2) / 2 = 0 :=
          congrFun hpt x
        linarith
      have hgn : (0 : ℝ) ≤ ‖g x‖ ^ 2 := sq_nonneg _
      have hdn : (0 : ℝ) ≤ ‖∇ (f : M3 → ℝ) x‖ ^ 2 := sq_nonneg _
      have hfn : (0 : ℝ) ≤ ‖f x‖ ^ 2 := sq_nonneg _
      have hmf : m ^ 2 * ‖f x‖ ^ 2 = 0 :=
        le_antisymm (by linarith) (mul_nonneg (sq_nonneg m) hfn)
      have hfx : ‖f x‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp hmf with h' | h'
        · exact absurd h' hm2.ne'
        · exact h'
      have hgx : ‖g x‖ ^ 2 = 0 := le_antisymm (by linarith) hgn
      exact ⟨norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hfx),
        norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hgx)⟩
    exact ⟨by ext x; exact (key x).1, by ext x; exact (key x).2⟩
  · rintro ⟨rfl, rfl⟩
    exact energy_zero m

/-- Strict positivity of the energy on nontrivial Cauchy data: the contrapositive of
`energy_eq_zero_iff` against `energy_nonneg`. This is the form the localized energy
estimate consumes — vanishing energy on a region means vanishing data there. -/
theorem energy_pos (hm : m ≠ 0) (f g : 𝓢(M3, ℝ)) (h : f ≠ 0 ∨ g ≠ 0) :
    0 < energy m f g := by
  refine lt_of_le_of_ne (energy_nonneg m f g) fun hzero => ?_
  obtain ⟨hf, hg⟩ := (energy_eq_zero_iff m hm f g).mp hzero.symm
  exact h.elim (fun h' => h' hf) fun h' => h' hg

end QFT.KleinGordon
