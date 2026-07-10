import Atlas.Specs.OperatorTheory.Cayley
import Atlas.Proofs.DeficiencyTheory

/-!
# P2.3c — The Cayley transform: proofs

Proofs of the seven frozen targets of `Atlas/Specs/OperatorTheory/Cayley.lean`
(blueprint node P2.3c): `CayleyIsometric`, `CayleyRangeEq`, `CayleyOneNotEigenvalue`,
`InverseCayleyCayley`, `CayleySelfAdjointIffBijective`, `InverseCayleySelfAdjoint`,
`CayleyInverseCayley`.

## Structure

* **No completeness** (`H` any complex inner-product space): the pointwise theory.
  Every element of `dom (cayley A) = ran (A + i)` is `(A + i) x`, and the frozen
  pinning lemma `IsSymmetric.cayley_apply_eq` evaluates the transform there as
  `(A - i) x`; the norm identities of the P2.3a/b spec then give the isometry
  (`IsSymmetric.norm_cayley_apply`), the range computation
  (`IsSymmetric.range_cayley`), injectivity of `U - 1`
  (`IsSymmetric.ker_shift_cayley_one`, from `(A - i) x = (A + i) x ⇒ 2i • x = 0`),
  and the recovery `inverseCayley (cayley A) = A`
  (`IsSymmetric.inverseCayley_cayley`, on `z = (U - 1)((A + i) x) = -2i • x`).
* **Complete `H`, Reed & Simon I Thm VIII.3**: for densely defined symmetric `A`,
  self-adjointness is equivalent to `ran (A ± i) = H`
  (`range_shift_eq_top_of_isSelfAdjoint` / `isSelfAdjoint_of_range_shift_eq_top`);
  read through `cayley_domain` and `IsSymmetric.range_cayley` this is the headliner
  `CayleySelfAdjointIffBijective`. The forward direction combines the deficiency
  theory of P2.3b (ranges dense) with the closed-range lemma
  `isClosed_range_sub_smul_of_norm_identity`; the reverse is the VIII.3 chase
  `(A - i) x = (A† - i) y ⇒ x - y ∈ K₊ = ⊥`.
* **The surjectivity half** (von Neumann): a unitary `U` (as a `ContinuousLinearMap`)
  without eigenvalue `1` yields `A = inverseCayley U` symmetric
  (`isSymmetric_inverseCayley_unitary`, by `⟪U x, U y⟫ = ⟪x, y⟫`), densely defined
  (`dense_domain_inverseCayley_unitary`: `y ⊥ ran (U - 1)` forces `U† y = y`, hence
  `U y = y`, hence `y = 0`), with `ran (A ± i) = H` outright
  (`(A + i)((U - 1) x) = -2i • x` and `(A - i)((U - 1) x) = -2i • U x`, with `x`
  ranging over all of `H` and `U` surjective) — so `A` is self-adjoint and
  `cayley A = U` (`cayley_inverseCayley_unitary`).

## Sources

* W. Rudin, *Functional Analysis*, 2nd ed. (1991), ch. 13, Thm 13.19.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised and enlarged edition (1980), §VIII.2, Thm VIII.3 (the basic criterion).
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II: Fourier Analysis,
  Self-Adjointness* (1975), §X.1.
* J. von Neumann, "Allgemeine Eigenwerttheorie Hermitescher Funktionaloperatoren",
  *Math. Ann.* 102 (1930), 49–131.
-/

namespace OperatorTheory.LinearPMap

open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The Möbius scalar bookkeeping `(-2i) · (i/2) = 1` behind the substitution
`z = -2i • x ↔ x = (i/2) • z` (Rudin, proof of Thm 13.19: `x = (2i)⁻¹(Λ - I) z`). -/
private theorem neg_two_I_mul_I_div_two : -(2 * Complex.I) * (Complex.I / 2) = 1 := by
  linear_combination -Complex.I_mul_I

/-! ### The pointwise theory: isometry, range, fixed points, recovery -/

/-- **The Cayley transform is isometric on its domain** (Rudin, *Functional Analysis*,
2nd ed., Thm 13.19; Reed & Simon II, §X.1): for symmetric `A` and `y = (A + i) x`,
`‖U y‖² = ‖(A - i) x‖² = ‖A x‖² + ‖x‖² = ‖(A + i) x‖² = ‖y‖²` by the frozen norm
identities. Pointwise form of the target `CayleyIsometric`. -/
theorem IsSymmetric.norm_cayley_apply {A : H →ₗ.[ℂ] H} (hA : IsSymmetric A)
    (y : (cayley A).domain) : ‖cayley A y‖ = ‖(y : H)‖ := by
  obtain ⟨x, hxy⟩ := mem_cayley_domain_iff.mp y.2
  rw [hA.cayley_apply_eq hxy, ← hxy]
  calc ‖A x - Complex.I • (x : H)‖
      = Real.sqrt (‖A x - Complex.I • (x : H)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖A x + Complex.I • (x : H)‖ ^ 2) := by
        rw [hA.norm_sub_I_smul_sq x, hA.norm_add_I_smul_sq x]
    _ = ‖A x + Complex.I • (x : H)‖ := Real.sqrt_sq (norm_nonneg _)

/-- **The range of the Cayley transform is `ran (A - i)`** (Rudin, *Functional
Analysis*, 2nd ed., Thm 13.19: `U` maps `ran (A + iI)` onto `ran (A - iI)`): both
inclusions are the pinning computation `(A + i) x ↦ (A - i) x` read in the two
directions. Fixed-`A` form of the target `CayleyRangeEq`. -/
theorem IsSymmetric.range_cayley {A : H →ₗ.[ℂ] H} (hA : IsSymmetric A) :
    LinearMap.range (cayley A).toFun = LinearMap.range (shift A Complex.I).toFun := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, hxy⟩ := mem_cayley_domain_iff.mp y.2
    exact ⟨x, (hA.cayley_apply_eq hxy).symm⟩
  · rintro _ ⟨x, rfl⟩
    have hy : A x + Complex.I • (x : H) ∈ (cayley A).domain :=
      mem_cayley_domain_iff.mpr ⟨x, rfl⟩
    exact ⟨⟨_, hy⟩, hA.cayley_apply_eq (y := ⟨_, hy⟩) rfl⟩

/-- **`1` is not an eigenvalue of the Cayley transform** (Rudin, *Functional Analysis*,
2nd ed., Thm 13.19: `I - U` is one-to-one): `U y = y` with `y = (A + i) x` forces
`(A - i) x = (A + i) x`, i.e. `-2i • x = 0`, so `x = 0` and `y = 0`. Fixed-`A` form of
the target `CayleyOneNotEigenvalue`. -/
theorem IsSymmetric.ker_shift_cayley_one {A : H →ₗ.[ℂ] H} (hA : IsSymmetric A) :
    LinearMap.ker (shift (cayley A) 1).toFun = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro y hy
  obtain ⟨x, hxy⟩ := mem_cayley_domain_iff.mp y.2
  have hval : (shift (cayley A) 1).toFun y = -(2 * Complex.I) • (x : H) := by
    show cayley A y - (1 : ℂ) • (y : H) = -(2 * Complex.I) • (x : H)
    rw [hA.cayley_apply_eq hxy, ← hxy]
    module
  rw [hval] at hy
  have hx0 : (x : H) = 0 := by
    rcases smul_eq_zero.mp hy with h | h
    · exact absurd h (by simp [Complex.I_ne_zero])
    · exact h
  refine Subtype.ext ?_
  rw [← hxy, show x = 0 from Subtype.ext hx0]
  simp

/-- **Recovery of `A` from its Cayley transform**, `inverseCayley (cayley A) = A`
(Rudin, *Functional Analysis*, 2nd ed., Thm 13.19: "`U` determines `A`";
Reed & Simon II, §X.1). On `z = (U - 1)((A + i) x) = -2i • x` the inverse transform
returns `-i • ((A + i) x + (A - i) x) = -2i • A x = A z`; the substitution
`x = (i/2) • z` makes the domain identity `ran (U - 1) = dom A` exact. No density
hypothesis: only injectivity of `A ± i`, which symmetry provides. Fixed-`A` form of
the target `InverseCayleyCayley`. -/
theorem IsSymmetric.inverseCayley_cayley {A : H →ₗ.[ℂ] H} (hA : IsSymmetric A) :
    inverseCayley (cayley A) = A := by
  have hker := hA.ker_shift_cayley_one
  have hdom : (inverseCayley (cayley A)).domain = A.domain := by
    apply le_antisymm
    · intro z hz
      obtain ⟨y, hyz⟩ := mem_inverseCayley_domain_iff.mp hz
      obtain ⟨x, hxy⟩ := mem_cayley_domain_iff.mp y.2
      have hval : cayley A y - (y : H) = -(2 * Complex.I) • (x : H) := by
        rw [hA.cayley_apply_eq hxy, ← hxy]
        module
      rw [← hyz, hval]
      exact A.domain.smul_mem _ x.2
    · intro z hz
      rw [mem_inverseCayley_domain_iff]
      set x : A.domain := (Complex.I / 2) • (⟨z, hz⟩ : A.domain) with hxdef
      have hy : A x + Complex.I • (x : H) ∈ (cayley A).domain :=
        mem_cayley_domain_iff.mpr ⟨x, rfl⟩
      refine ⟨⟨_, hy⟩, ?_⟩
      rw [hA.cayley_apply_eq (y := ⟨_, hy⟩) (x := x) rfl]
      show A x - Complex.I • (x : H) - (A x + Complex.I • (x : H)) = z
      have h1 : A x - Complex.I • (x : H) - (A x + Complex.I • (x : H))
          = -(2 * Complex.I) • (x : H) := by module
      have h2 : (x : H) = (Complex.I / 2) • z := rfl
      rw [h1, h2, smul_smul, neg_two_I_mul_I_div_two, one_smul]
  refine _root_.LinearPMap.ext hdom ?_
  intro z hf hg
  set xz : A.domain := ⟨z, hg⟩ with hxzdef
  set x : A.domain := (Complex.I / 2) • xz with hxdef
  have hy : A x + Complex.I • (x : H) ∈ (cayley A).domain :=
    mem_cayley_domain_iff.mpr ⟨x, rfl⟩
  have hUy : cayley A ⟨_, hy⟩ = A x - Complex.I • (x : H) :=
    hA.cayley_apply_eq (y := ⟨_, hy⟩) (x := x) rfl
  have hxzeq : cayley A ⟨_, hy⟩ - ((⟨_, hy⟩ : (cayley A).domain) : H) = z := by
    rw [hUy]
    show A x - Complex.I • (x : H) - (A x + Complex.I • (x : H)) = z
    have h1 : A x - Complex.I • (x : H) - (A x + Complex.I • (x : H))
        = -(2 * Complex.I) • (x : H) := by module
    have h2 : (x : H) = (Complex.I / 2) • z := rfl
    rw [h1, h2, smul_smul, neg_two_I_mul_I_div_two, one_smul]
  rw [inverseCayley_apply_eq hker (x := ⟨_, hy⟩) hxzeq, hUy]
  show -Complex.I • ((A x + Complex.I • (x : H)) + (A x - Complex.I • (x : H))) = A xz
  have hAx : A x = (Complex.I / 2) • A xz := by
    rw [hxdef, _root_.LinearPMap.map_smul]
  rw [hAx]
  have h3 : -Complex.I • (((Complex.I / 2) • A xz + Complex.I • (x : H))
        + ((Complex.I / 2) • A xz - Complex.I • (x : H)))
      = (-Complex.I * Complex.I) • A xz := by module
  rw [h3, show -Complex.I * Complex.I = (1 : ℂ) by linear_combination -Complex.I_mul_I,
    one_smul]

/-! ### The basic criterion (Reed & Simon I, Thm VIII.3) -/

section CompleteSpace

variable [CompleteSpace H]

/-- **Forward half of Reed & Simon I, Thm VIII.3**: a self-adjoint operator has
`ran (A - c) = H` for non-real `c` with the norm identity. The range is dense (its
orthocomplement is the deficiency space, which vanishes because the adjoint `= A` is
symmetric) and closed (`A` is closed and `A - c` is bounded below by the norm
identity). -/
theorem range_shift_eq_top_of_isSelfAdjoint {A : H →ₗ.[ℂ] H}
    (hd : Dense (A.domain : Set H)) (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.im ≠ 0)
    (hnorm : ∀ x : A.domain, ‖A x - c • (x : H)‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : H)‖ ^ 2) :
    LinearMap.range (shift A c).toFun = ⊤ := by
  have hsym : IsSymmetric A := isSymmetric_of_isSelfAdjoint hA
  have hadj : IsSymmetric A.adjoint := by
    rw [_root_.LinearPMap.isSelfAdjoint_def.mp hA]
    exact hsym
  have hdense := deficiencySpace_eq_bot_iff_dense.mp
    (deficiencySpace_eq_bot_of_isSymmetric_adjoint hd hadj hc)
  have hclosed := isClosed_range_sub_smul_of_norm_identity hA.isClosed hnorm
  have hset : (LinearMap.range (A.toFun - c • A.domain.subtype) : Set H) = Set.univ := by
    rw [← hclosed.closure_eq]
    exact hdense.closure_eq
  rw [Submodule.eq_top_iff']
  intro z
  show z ∈ LinearMap.range (A.toFun - c • A.domain.subtype)
  rw [← SetLike.mem_coe, hset]
  trivial

/-- **Reverse half of Reed & Simon I, Thm VIII.3**: a densely defined symmetric `A`
with `ran (A + i) = H` and `ran (A - i) = H` is self-adjoint. For `y ∈ D(A†)` solve
`(A - i) x = (A† - i) y`; then `x - y` is an `i`-eigenvector of `A†`, i.e. lies in
`K₊ = (ran (A + i))ᗮ = ⊥`, so `y = x ∈ D(A)` and `A† ≤ A ≤ A†`. -/
theorem isSelfAdjoint_of_range_shift_eq_top {A : H →ₗ.[ℂ] H}
    (hd : Dense (A.domain : Set H)) (hsym : IsSymmetric A)
    (hplus : LinearMap.range (shift A (-Complex.I)).toFun = ⊤)
    (hminus : LinearMap.range (shift A Complex.I).toFun = ⊤) :
    IsSelfAdjoint A := by
  have hle : A ≤ A.adjoint := hsym.le_adjoint hd
  have hbot : deficiencySpace A (-Complex.I) = ⊥ := by
    rw [deficiencySpace_eq_orthogonal_range_shift, hplus, Submodule.top_orthogonal_eq_bot]
  have hdom : A.adjoint.domain ≤ A.domain := by
    intro y hy
    have hmem : A.adjoint ⟨y, hy⟩ - Complex.I • y
        ∈ LinearMap.range (shift A Complex.I).toFun := by
      rw [hminus]; exact Submodule.mem_top
    obtain ⟨x', hx'⟩ := hmem
    have hx'val : A x' - Complex.I • (x' : H) = A.adjoint ⟨y, hy⟩ - Complex.I • y := hx'
    have hx'adj : (x' : H) ∈ A.adjoint.domain := hle.1 x'.2
    have hadjx' : A.adjoint ⟨(x' : H), hx'adj⟩ = A x' :=
      (_root_.LinearPMap.apply_comp_inclusion hle x').symm
    have hzmem : ((x' : H) - y) ∈ A.adjoint.domain := A.adjoint.domain.sub_mem hx'adj hy
    have heigen : A.adjoint ⟨(x' : H) - y, hzmem⟩ = Complex.I • ((x' : H) - y) := by
      have hsub : A.adjoint ⟨(x' : H) - y, hzmem⟩
          = A.adjoint ⟨(x' : H), hx'adj⟩ - A.adjoint ⟨y, hy⟩ := by
        rw [← _root_.LinearPMap.map_sub A.adjoint ⟨(x' : H), hx'adj⟩ ⟨y, hy⟩]
        congr 1
      rw [hsub, hadjx', smul_sub, sub_eq_sub_iff_sub_eq_sub]
      exact hx'val
    have hzdef : ((x' : H) - y) ∈ deficiencySpace A (-Complex.I) := by
      rw [mem_deficiencySpace_iff_mem_adjoint_eigenspace hd]
      exact ⟨hzmem, by rw [heigen]; simp⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hzdef
    rw [← hzdef]
    exact x'.2
  have hle' : A.adjoint ≤ A :=
    ⟨hdom, fun x w hxw => by
      rw [_root_.LinearPMap.apply_comp_inclusion hle w]
      exact congrArg _ (Subtype.ext (hxw.trans (Submodule.coe_inclusion _ _).symm))⟩
  rw [_root_.LinearPMap.isSelfAdjoint_def]
  exact le_antisymm hle' hle

end CompleteSpace

/-! ### The unitary side: `inverseCayley` of a unitary without eigenvalue `1` -/

/-- **Bridge between the two spellings of "`1` is not an eigenvalue"**: the CLM-native
condition `ker (1 - T) = ⊥` of the frozen targets `InverseCayleySelfAdjoint` /
`CayleyInverseCayley` is equivalent to the PMap-native `ker (shift T 1).toFun = ⊥`
consumed by `inverseCayley_apply_eq` (for `T` as the everywhere defined `LinearPMap`;
`1 - T` and `T - 1` have the same kernel). -/
theorem ker_shift_toPMap_one_eq_bot_iff (T : H →L[ℂ] H) :
    LinearMap.ker (shift (((T : H →ₗ[ℂ] H)).toPMap ⊤) 1).toFun = ⊥ ↔ (1 - T).ker = ⊥ := by
  simp only [LinearMap.ker_eq_bot']
  constructor
  · intro h x hx
    have hx' : (T : H →ₗ[ℂ] H) x - (1 : ℂ) • x = 0 := by
      have hs : (x : H) - T x = 0 := hx
      rw [one_smul, ← neg_eq_zero, neg_sub]
      exact hs
    exact congrArg Subtype.val (h ⟨x, Submodule.mem_top⟩ hx')
  · intro h x hx
    have hx' : (T : H →ₗ[ℂ] H) (x : H) - (1 : ℂ) • (x : H) = 0 := hx
    rw [one_smul] at hx'
    have hker : (1 - T : H →L[ℂ] H) (x : H) = 0 := by
      show (x : H) - T (x : H) = 0
      rw [← neg_eq_zero, neg_sub]
      exact hx'
    exact Subtype.ext (h _ hker)

section Unitary

variable [CompleteSpace H] (U : unitary (H →L[ℂ] H))

/-- A unitary is surjective: `U (U† w) = w` (from `U · U† = 1`). -/
private theorem unitary_apply_star_apply (w : H) :
    (U : H →L[ℂ] H) ((star (U : H →L[ℂ] H)) w) = w := by
  calc (U : H →L[ℂ] H) ((star (U : H →L[ℂ] H)) w)
      = ((U : H →L[ℂ] H) * star (U : H →L[ℂ] H)) w := rfl
    _ = (1 : H →L[ℂ] H) w := by rw [(Unitary.mem_iff.mp U.2).2]
    _ = w := rfl

/-- **`inverseCayley U` is symmetric for unitary `U`** (Rudin, *Functional Analysis*,
2nd ed., Thm 13.19; Reed & Simon II, §X.1): on `z = (U - 1) x`, `w = (U - 1) y`, both
`⟪A z, w⟫` and `⟪z, A w⟫` reduce to `i (⟪x, U y⟫ - ⟪U x, y⟫)` using
`⟪U x, U y⟫ = ⟪x, y⟫`. -/
theorem isSymmetric_inverseCayley_unitary (hU : (1 - (U : H →L[ℂ] H)).ker = ⊥) :
    IsSymmetric (inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤)) := by
  have hker := (ker_shift_toPMap_one_eq_bot_iff (U : H →L[ℂ] H)).mpr hU
  intro z w
  obtain ⟨x, hxz⟩ := mem_inverseCayley_domain_iff.mp z.2
  obtain ⟨y, hyw⟩ := mem_inverseCayley_domain_iff.mp w.2
  rw [inverseCayley_apply_eq hker hxz, inverseCayley_apply_eq hker hyw, ← hxz, ← hyw]
  have hxv : (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤) x = (U : H →L[ℂ] H) (x : H) := rfl
  have hyv : (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤) y = (U : H →L[ℂ] H) (y : H) := rfl
  rw [hxv, hyv]
  have huu := Unitary.inner_map_map U (x : H) (y : H)
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, huu, map_neg, Complex.conj_I]
  ring

/-- **`dom (inverseCayley U) = ran (U - 1)` is dense for unitary `U` without
eigenvalue `1`** (Rudin, *Functional Analysis*, 2nd ed., Thm 13.19; Reed & Simon II,
§X.1): `y ⊥ ran (U - 1)` gives `⟪U x, y⟫ = ⟪x, y⟫` for all `x`, hence `U† y = y`,
hence `y = U y` and `y ∈ ker (1 - U) = ⊥`. Density is derived, never hypothesized. -/
theorem dense_domain_inverseCayley_unitary (hU : (1 - (U : H →L[ℂ] H)).ker = ⊥) :
    Dense (((inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤)).domain : Set H)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  have hkey : ∀ a : H, ⟪(U : H →L[ℂ] H) a, y⟫ = ⟪a, y⟫ := by
    intro a
    have hmem : (U : H →L[ℂ] H) a - a
        ∈ (inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤)).domain :=
      mem_inverseCayley_domain_iff.mpr ⟨⟨a, Submodule.mem_top⟩, rfl⟩
    have h0 := hy _ hmem
    rwa [inner_sub_left, sub_eq_zero] at h0
  have hstar : (star (U : H →L[ℂ] H)) y = y := by
    have h1 : ∀ a : H, ⟪a, (star (U : H →L[ℂ] H)) y - y⟫ = 0 := by
      intro a
      rw [inner_sub_right, sub_eq_zero, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
      exact hkey a
    have h2 := h1 ((star (U : H →L[ℂ] H)) y - y)
    rwa [inner_self_eq_zero, sub_eq_zero] at h2
  have hyU : (1 - (U : H →L[ℂ] H)) y = 0 := by
    have h3 : (U : H →L[ℂ] H) y = y := by
      conv_lhs => rw [← hstar]
      exact unitary_apply_star_apply U y
    show y - (U : H →L[ℂ] H) y = 0
    rw [h3, sub_self]
  have h4 : y ∈ (1 - (U : H →L[ℂ] H)).ker := LinearMap.mem_ker.mpr hyU
  rw [hU] at h4
  simpa using h4

/-- **`ran (inverseCayley U + i) = H` for unitary `U` without eigenvalue `1`**:
on `z = (U - 1) x` the value is `A z + i • z = -2i • x`, and `x` ranges over all of
`H` (Reed & Simon I, §VIII.2 / Rudin Thm 13.19: the surjectivity input for
self-adjointness of the inverse transform). -/
theorem range_shift_inverseCayley_unitary_neg_I (hU : (1 - (U : H →L[ℂ] H)).ker = ⊥) :
    LinearMap.range
      (shift (inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤)) (-Complex.I)).toFun
      = ⊤ := by
  have hker := (ker_shift_toPMap_one_eq_bot_iff (U : H →L[ℂ] H)).mpr hU
  rw [LinearMap.range_eq_top]
  intro w
  set a : H := (Complex.I / 2) • w with ha
  have hzmem : (U : H →L[ℂ] H) a - a
      ∈ (inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤)).domain :=
    mem_inverseCayley_domain_iff.mpr ⟨⟨a, Submodule.mem_top⟩, rfl⟩
  refine ⟨⟨_, hzmem⟩, ?_⟩
  have hval : inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤) ⟨_, hzmem⟩
      = -Complex.I • (a + (U : H →L[ℂ] H) a) :=
    inverseCayley_apply_eq hker (x := ⟨a, Submodule.mem_top⟩) rfl
  show inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤) ⟨_, hzmem⟩
      - (-Complex.I) • ((U : H →L[ℂ] H) a - a) = w
  rw [hval]
  have h1 : -Complex.I • (a + (U : H →L[ℂ] H) a)
        - (-Complex.I) • ((U : H →L[ℂ] H) a - a)
      = -(2 * Complex.I) • a := by module
  rw [h1, ha, smul_smul, neg_two_I_mul_I_div_two, one_smul]

/-- **`ran (inverseCayley U - i) = H` for unitary `U` without eigenvalue `1`**:
on `z = (U - 1) x` the value is `A z - i • z = -2i • U x`, and `U` is surjective. -/
theorem range_shift_inverseCayley_unitary_I (hU : (1 - (U : H →L[ℂ] H)).ker = ⊥) :
    LinearMap.range
      (shift (inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤)) Complex.I).toFun
      = ⊤ := by
  have hker := (ker_shift_toPMap_one_eq_bot_iff (U : H →L[ℂ] H)).mpr hU
  rw [LinearMap.range_eq_top]
  intro w
  set a : H := (Complex.I / 2) • (star (U : H →L[ℂ] H)) w with ha
  have hzmem : (U : H →L[ℂ] H) a - a
      ∈ (inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤)).domain :=
    mem_inverseCayley_domain_iff.mpr ⟨⟨a, Submodule.mem_top⟩, rfl⟩
  refine ⟨⟨_, hzmem⟩, ?_⟩
  have hval : inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤) ⟨_, hzmem⟩
      = -Complex.I • (a + (U : H →L[ℂ] H) a) :=
    inverseCayley_apply_eq hker (x := ⟨a, Submodule.mem_top⟩) rfl
  show inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤) ⟨_, hzmem⟩
      - Complex.I • ((U : H →L[ℂ] H) a - a) = w
  rw [hval]
  have h1 : -Complex.I • (a + (U : H →L[ℂ] H) a)
        - Complex.I • ((U : H →L[ℂ] H) a - a)
      = -(2 * Complex.I) • (U : H →L[ℂ] H) a := by module
  have hTa : (U : H →L[ℂ] H) a = (Complex.I / 2) • w := by
    rw [ha, map_smul, unitary_apply_star_apply U w]
  rw [h1, hTa, smul_smul, neg_two_I_mul_I_div_two, one_smul]

/-- **Every unitary without eigenvalue `1` is a Cayley transform**:
`cayley (inverseCayley U) = U` (von Neumann (1930); Rudin, *Functional Analysis*,
2nd ed., Thm 13.19). For `w ∈ H`, put `a = (i/2) • w` and `z = (U - 1) a ∈ dom A`;
then `A z + i • z = -2i • a = w` and the pinning lemma gives
`cayley A w = A z - i • z = -2i • U a = U w`. Fixed-`U` form of the target
`CayleyInverseCayley`. -/
theorem cayley_inverseCayley_unitary (hU : (1 - (U : H →L[ℂ] H)).ker = ⊥) :
    cayley (inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤))
      = ((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤ := by
  have hker := (ker_shift_toPMap_one_eq_bot_iff (U : H →L[ℂ] H)).mpr hU
  have hsym := isSymmetric_inverseCayley_unitary U hU
  have hdom : (cayley (inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤))).domain
      = (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤).domain := by
    rw [cayley_domain, range_shift_inverseCayley_unitary_neg_I U hU]
    rfl
  refine _root_.LinearPMap.ext hdom ?_
  intro w hf hg
  set a : H := (Complex.I / 2) • w with ha
  have hzmem : (U : H →L[ℂ] H) a - a
      ∈ (inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤)).domain :=
    mem_inverseCayley_domain_iff.mpr ⟨⟨a, Submodule.mem_top⟩, rfl⟩
  have hval : inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤) ⟨_, hzmem⟩
      = -Complex.I • (a + (U : H →L[ℂ] H) a) :=
    inverseCayley_apply_eq hker (x := ⟨a, Submodule.mem_top⟩) rfl
  have hxy : inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤) ⟨_, hzmem⟩
      + Complex.I • ((U : H →L[ℂ] H) a - a) = w := by
    rw [hval]
    have h1 : -Complex.I • (a + (U : H →L[ℂ] H) a)
          + Complex.I • ((U : H →L[ℂ] H) a - a)
        = -(2 * Complex.I) • a := by module
    rw [h1, ha, smul_smul, neg_two_I_mul_I_div_two, one_smul]
  rw [hsym.cayley_apply_eq (y := ⟨w, hf⟩) (x := ⟨_, hzmem⟩) hxy, hval]
  show -Complex.I • (a + (U : H →L[ℂ] H) a) - Complex.I • ((U : H →L[ℂ] H) a - a)
      = (U : H →L[ℂ] H) w
  have h1 : -Complex.I • (a + (U : H →L[ℂ] H) a) - Complex.I • ((U : H →L[ℂ] H) a - a)
      = -(2 * Complex.I) • (U : H →L[ℂ] H) a := by module
  rw [h1, ha, map_smul, smul_smul, neg_two_I_mul_I_div_two, one_smul]

end Unitary

end OperatorTheory.LinearPMap

namespace OperatorTheory

/-- **Target — the Cayley transform is isometric** (blueprint node P2.3c): proof of the
frozen `CayleyIsometric` (Rudin, *Functional Analysis*, 2nd ed., Thm 13.19). -/
theorem cayleyIsometric (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    CayleyIsometric H :=
  fun _A hA y => hA.norm_cayley_apply y

/-- **Target — the range of the Cayley transform** (blueprint node P2.3c): proof of the
frozen `CayleyRangeEq` (Rudin, *Functional Analysis*, 2nd ed., Thm 13.19). -/
theorem cayleyRangeEq (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    CayleyRangeEq H :=
  fun _A hA => hA.range_cayley

/-- **Target — `1` is not an eigenvalue of the Cayley transform** (blueprint node
P2.3c): proof of the frozen `CayleyOneNotEigenvalue` (Rudin, *Functional Analysis*,
2nd ed., Thm 13.19). -/
theorem cayleyOneNotEigenvalue (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] : CayleyOneNotEigenvalue H :=
  fun _A hA => hA.ker_shift_cayley_one

/-- **Target — recovery of `A` from its Cayley transform** (blueprint node P2.3c):
proof of the frozen `InverseCayleyCayley` (Rudin, *Functional Analysis*, 2nd ed.,
Thm 13.19; von Neumann (1930)). -/
theorem inverseCayleyCayley (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] : InverseCayleyCayley H :=
  fun _A hA => hA.inverseCayley_cayley

/-- **Target — self-adjointness ⟺ the Cayley transform is a bijection of `H`**
(blueprint node P2.3c, the headliner): proof of the frozen
`CayleySelfAdjointIffBijective` — the basic criterion of Reed & Simon I, §VIII.2,
Thm VIII.3, read through `cayley_domain` and `IsSymmetric.range_cayley`. -/
theorem cayleySelfAdjointIffBijective (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : CayleySelfAdjointIffBijective H := by
  intro A hd hsym
  constructor
  · intro hself
    constructor
    · rw [LinearPMap.cayley_domain]
      exact LinearPMap.range_shift_eq_top_of_isSelfAdjoint hd hself (by simp)
        fun x => by simpa [neg_smul, sub_neg_eq_add] using hsym.norm_add_I_smul_sq x
    · rw [hsym.range_cayley]
      exact LinearPMap.range_shift_eq_top_of_isSelfAdjoint hd hself (by simp)
        fun x => hsym.norm_sub_I_smul_sq x
  · rintro ⟨hdomtop, hrantop⟩
    refine LinearPMap.isSelfAdjoint_of_range_shift_eq_top hd hsym ?_ ?_
    · rw [← LinearPMap.cayley_domain]
      exact hdomtop
    · rw [← hsym.range_cayley]
      exact hrantop

/-- **Target — the inverse transform of a unitary without eigenvalue `1` is
self-adjoint** (blueprint node P2.3c, surjectivity half, part 1): proof of the frozen
`InverseCayleySelfAdjoint` (Rudin, *Functional Analysis*, 2nd ed., Thm 13.19;
von Neumann (1930)). -/
theorem inverseCayleySelfAdjoint (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : InverseCayleySelfAdjoint H :=
  fun U hU =>
    LinearPMap.isSelfAdjoint_of_range_shift_eq_top
      (LinearPMap.dense_domain_inverseCayley_unitary U hU)
      (LinearPMap.isSymmetric_inverseCayley_unitary U hU)
      (LinearPMap.range_shift_inverseCayley_unitary_neg_I U hU)
      (LinearPMap.range_shift_inverseCayley_unitary_I U hU)

/-- **Target — every unitary without eigenvalue `1` is a Cayley transform** (blueprint
node P2.3c, surjectivity half, part 2): proof of the frozen `CayleyInverseCayley`
(Rudin, *Functional Analysis*, 2nd ed., Thm 13.19; von Neumann (1930)). -/
theorem cayleyInverseCayley (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : CayleyInverseCayley H :=
  fun U hU => LinearPMap.cayley_inverseCayley_unitary U hU

end OperatorTheory
