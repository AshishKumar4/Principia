import Mathlib.Tactic.Module
import Atlas.Specs.OperatorTheory.Symmetric

/-!
# P2.3c — The Cayley transform of a symmetric operator

Frozen spec (blueprint node P2.3c): proof sessions must not edit this file; changes
require a spec review and a `[spec-review]` commit (see CLAUDE.md).

## Contents

* `LinearPMap.shift A c`: the operator `A - c·id` on `A.domain`, as a `LinearPMap`. Its
  underlying linear map is *definitionally* the `A.toFun - c • A.domain.subtype` of the
  frozen `deficiencySpace` (`deficiencySpace_eq_orthogonal_range_shift` is `rfl`), so
  the P2.3a/b sign table transfers verbatim.
* Injectivity of `A ∓ i` for symmetric `A`, from the frozen norm identity
  (`ker_shift_eq_bot_of_norm_identity`, `IsSymmetric.ker_shift_I`,
  `IsSymmetric.ker_shift_neg_I`) — proved here since the Cayley transform's
  well-definedness rests on it.
* `LinearPMap.cayley A`: the Cayley transform `U = (A - i)(A + i)⁻¹`, sending
  `(A + i) x ↦ (A - i) x` on the domain `ran (A + i)`, encoded as a `LinearPMap H H`
  via Mathlib's `LinearPMap.inverse` and the resolvent identity `U = 1 - 2i(A + i)⁻¹`.
  Kernel-checked API: `cayley_domain`, `mem_cayley_domain_iff`, `cayley_apply`,
  `cayley_domain_orthogonal` (domain defect = `K₊`), and the pinning computation
  `IsSymmetric.cayley_apply_eq` (`(A + i) x ↦ (A - i) x`, the textbook definition).
* `LinearPMap.inverseCayley U`: the inverse transform `A = i(1 + U)(1 - U)⁻¹`, with the
  analogous API (`inverseCayley_domain`, `mem_inverseCayley_domain_iff`,
  `inverseCayley_apply`, `inverseCayley_apply_eq`).
* Prop-valued target statements for blueprint node P2.3c: `CayleyIsometric`,
  `CayleyRangeEq`, `CayleyOneNotEigenvalue`, `InverseCayleyCayley`,
  `CayleySelfAdjointIffBijective`, `InverseCayleySelfAdjoint`, `CayleyInverseCayley`.

## Conventions

* **Direction of the transform: Rudin's.** The Cayley transform of `A` is
  `U = (A - i)(A + i)⁻¹` with domain `ran (A + i)`, i.e. `(A + i) x ↦ (A - i) x`
  (Rudin, *Functional Analysis*, 2nd ed., Thm 13.19; Reed & Simon II, §X.1;
  von Neumann (1930)). Some authors use the transpose assignment
  `(A + i)(A - i)⁻¹`; every statement in this file follows Rudin's. Under this
  convention the *excluded eigenvalue is `1`*: `U y = y` with `y = (A + i) x` forces
  `(A - i) x = (A + i) x`, i.e. `2i • x = 0`, so `x = 0` and `y = 0`
  (`CayleyOneNotEigenvalue`), and the inverse transform is `A = i(1 + U)(1 - U)⁻¹`
  (`inverseCayley`, `InverseCayleyCayley`). Scalar sanity anchor (kept in mind for the
  witnesses; not stated here): for real `r`, the transform of `r • id` is the Möbius
  scalar `(r - i)/(r + i) • id`, of unit modulus, and `i(1 + μ)/(1 - μ) = r` for
  `μ = (r - i)/(r + i)`.
* **Encoding: a `LinearPMap H H`, built from `LinearPMap.inverse`.** Adjudicated
  against a `LinearIsometry` on the subspace `ran (A + i)` and against a
  partial-isometry `H →L[ℂ] H` (extended by `0` on `ran (A + i)ᗮ`):
  the `LinearPMap` encoding needs *no* completeness of `H` and no closedness of the
  ranges, stays in the type of the frozen P2.3a/b/g stack (so `deficiencySpace`,
  `adjoint`, `IsSelfAdjoint` apply verbatim), and makes the headline totality
  statement literally `(cayley A).domain = ⊤` — which is exactly the range condition
  of the proven deficiency theory (Reed & Simon I, Thm VIII.3). The isometric and
  partial-isometry packagings are *derived data*: they require `CayleyIsometric` plus
  range closedness, and are constructed on the spectral-transfer node (P2.3f), not
  postulated here. For the map itself, `LinearPMap.comp` is unusable as a definition
  (it demands a proof-relevant membership hypothesis, so the composite
  `(A - i) ∘ (A + i)⁻¹` would not be a total function of `A`); instead we use the
  resolvent identity `U z = z - 2i • (A + i)⁻¹ z` — Rudin's own computation `Uz = z - 2ix`
  for `z = Ax + ix` in the proof of Thm 13.19 — with `(A + i)⁻¹ = (shift A (-i)).inverse`
  taken from Mathlib (`LinearPMap.inverse`). This makes `cayley_apply` a `rfl` and the
  textbook rule `(A + i) x ↦ (A - i) x` a ten-line kernel-checked lemma
  (`IsSymmetric.cayley_apply_eq`).
* **Junk values.** `cayley A` is defined for *every* `A`, per Mathlib's junk-value
  philosophy (cf. the `adjoint`/`closure` junk documented in the P2.3a/b spec). Its
  domain is `ran (A + i)` unconditionally (`cayley_domain`, from
  `LinearPMap.inverse_domain`). When `A + i` is not injective — impossible for
  symmetric `A` (`IsSymmetric.ker_shift_neg_I`) — Mathlib's `Submodule.toLinearPMap`
  junk makes `(A + i)⁻¹` the zero map, so `cayley A` degenerates to the inclusion of
  `ran (A + i)`; no statement below evaluates it there without an `IsSymmetric` or
  kernel hypothesis. Same discussion for `inverseCayley U` and `1 - U`.
* **Sign table (deficiency bookkeeping).** With the frozen P2.3a/b conventions
  (`deficiencySpace A c = (ran (A - c))ᗮ`, `K₊ = deficiencySpace A (-I)`,
  `K₋ = deficiencySpace A I` — mind the sign inversion between the parameter and the
  `±` label):
  - `A + i = shift A (-Complex.I)`, and `(cayley A).domain = ran (A + i)`, so the
    *domain* defect is `(cayley A).domainᗮ = deficiencySpace A (-Complex.I) = K₊ =
    ker (A† - i)` — kernel-checked here as `cayley_domain_orthogonal`, unconditionally.
  - `A - i = shift A Complex.I`, and for symmetric `A` the *range* of `cayley A` is
    `ran (A - i)` (target `CayleyRangeEq`), so the range defect is
    `deficiencySpace A Complex.I = K₋ = ker (A† + i)`.
  So `cayley A` maps `ran (A + i)` onto `ran (A - i)` isometrically: initial defect
  `K₊`, final defect `K₋`, exactly von Neumann's picture (Reed & Simon II, §X.1).
* **`1 - U` is spelled through `shift U 1`.** The fixed-point and inverse-transform
  statements use `shift U 1 = U - 1·id` (same primitive as the deficiency bookkeeping)
  rather than a second `1 - U` construction: `ker (U - 1) = ker (1 - U)` *is* the
  "no eigenvalue `1`" condition, and `ran (U - 1) = ran (1 - U)` as submodules. The
  inverse transform on `z = (U - 1) x` accordingly takes the value
  `i(1 + U)(1 - U)⁻¹ z = -i • (x + U x)` (note the sign: `(1 - U)(-x) = z`), which is
  the pinned computation `inverseCayley_apply_eq`.
* **Namespace.** As in the P2.3a/b spec: constructions in `OperatorTheory.LinearPMap`,
  Prop-valued targets in `OperatorTheory`. Dot notation on an operator (`A.cayley`)
  does not resolve from inside `namespace OperatorTheory`; write `LinearPMap.cayley A`
  there (see the P2.3a/b docstring).

## Target statements (not theorems here)

The node-P2.3c theorems are recorded as `Prop`-valued definitions; a stuck proof node
must be decomposed, never allowed to weaken them. The eventual bijection
`cayleyEquiv : {A : H →ₗ.[ℂ] H // IsSelfAdjoint A} ≃ {U : unitary (H →L[ℂ] H) //
(1 - (U : H →L[ℂ] H)).ker = ⊥}` is *data* — its construction (including the
bounded extension of the total isometric `LinearPMap` to a `unitary` element) requires
those proofs, so it is deferred to the proof node and not stated here, exactly as
`stoneEquiv` was handled in the P2.3g spec. The pieces frozen instead:

* `CayleyIsometric` — `‖U y‖ = ‖y‖` on `ran (A + i)`, for symmetric `A`;
* `CayleyRangeEq` — `ran U = ran (A - i)`, for symmetric `A`;
* `CayleyOneNotEigenvalue` — `ker (U - 1) = ⊥`, for symmetric `A`;
* `InverseCayleyCayley` — `A` is recovered: `inverseCayley (cayley A) = A`
  (injectivity of `A ↦ cayley A` on symmetric operators);
* `CayleySelfAdjointIffBijective` — for densely defined symmetric `A`:
  `A` self-adjoint ↔ `cayley A` is everywhere defined and surjective
  (with `CayleyIsometric`, "unitary");
* `InverseCayleySelfAdjoint`, `CayleyInverseCayley` — every unitary without
  eigenvalue `1` arises, from a self-adjoint operator (surjectivity of `A ↦ cayley A`).

## Sources

* W. Rudin, *Functional Analysis*, 2nd ed. (1991), ch. 13, Thm 13.19: the Cayley
  transform of a symmetric operator — defining formula `U = (A - iI)(A + iI)⁻¹` with
  domain `ran (A + iI)`, isometry, closedness transfer, injectivity of `I - U`,
  recovery `A = i(I + U)(I - U)⁻¹`, and the correspondence under which `A` is
  self-adjoint iff `U` is unitary (with `I - U` injective).
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II: Fourier Analysis,
  Self-Adjointness* (1975), §X.1: the Cayley transform as the bridge between the
  deficiency subspaces `K± = ker (A* ∓ i)` and von Neumann's extension theory; the
  unitary-without-eigenvalue-1 correspondence.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised and enlarged edition (1980), §VIII.2, Thm VIII.3: the basic criterion
  (`A` self-adjoint ↔ `ran (A ± i) = H`) — the content of the totality/surjectivity
  leg `CayleySelfAdjointIffBijective`.
* J. von Neumann, "Allgemeine Eigenwerttheorie Hermitescher Funktionaloperatoren",
  *Math. Ann.* 102 (1930), 49–131 (origin of the Cayley-transform method).
-/

namespace OperatorTheory

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The operator `A - c·id` on `A.domain`, as a `LinearPMap`. Its underlying linear
map is definitionally the `A.toFun - c • A.domain.subtype` of the frozen
`LinearPMap.deficiencySpace` (P2.3a/b spec), so the deficiency sign table applies
verbatim: `A + i = shift A (-Complex.I)` and `A - i = shift A Complex.I`
(Reed & Simon I, §VIII.2; Rudin, *Functional Analysis*, 2nd ed., ch. 13). -/
def shift (A : H →ₗ.[ℂ] H) (c : ℂ) : H →ₗ.[ℂ] H :=
  ⟨A.domain, A.toFun - c • A.domain.subtype⟩

/-- Shifting does not move the domain: `dom (A - c) = dom A`. Definitional. -/
theorem shift_domain (A : H →ₗ.[ℂ] H) (c : ℂ) : (shift A c).domain = A.domain :=
  rfl

/-- The shifted operator acts as `x ↦ A x - c • x`. Definitional. -/
theorem shift_apply (A : H →ₗ.[ℂ] H) (c : ℂ) (x : A.domain) :
    shift A c x = A x - c • (x : H) :=
  rfl

/-- The deficiency space of the frozen P2.3a/b spec is the range-orthocomplement of
`shift`: definitional bridge (`rfl`) keeping `shift` and `deficiencySpace` a single
source of truth. -/
theorem deficiencySpace_eq_orthogonal_range_shift (A : H →ₗ.[ℂ] H) (c : ℂ) :
    deficiencySpace A c = (LinearMap.range (shift A c).toFun)ᗮ :=
  rfl

/-- **Injectivity from the norm identity**: if `‖A x - c • x‖² = ‖A x‖² + ‖x‖²` on the
domain, then `A - c` is injective (Reed & Simon I, §VIII.2, proof of Thm VIII.3: the
identity bounds `‖(A - c) x‖` below by `‖x‖`). This is the well-definedness input for
the Cayley transform, feeding Mathlib's `LinearPMap.inverse_apply_eq`. -/
theorem ker_shift_eq_bot_of_norm_identity {A : H →ₗ.[ℂ] H} {c : ℂ}
    (hnorm : ∀ x : A.domain, ‖A x - c • (x : H)‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : H)‖ ^ 2) :
    LinearMap.ker (shift A c).toFun = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have h0 : ‖A x‖ ^ 2 + ‖(x : H)‖ ^ 2 = 0 := by
    rw [← hnorm x, show A x - c • (x : H) = 0 from hx, norm_zero]
    norm_num
  have hx0 : ‖(x : H)‖ = 0 := by
    have : ‖(x : H)‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖A x‖]) (sq_nonneg _)
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  exact Subtype.ext (norm_eq_zero.mp hx0)

/-- `A - i` is injective for symmetric `A` (Reed & Simon I, §VIII.2, proof of
Thm VIII.3), from the frozen norm identity `IsSymmetric.norm_sub_I_smul_sq`. -/
theorem IsSymmetric.ker_shift_I {A : H →ₗ.[ℂ] H} (hA : IsSymmetric A) :
    LinearMap.ker (shift A Complex.I).toFun = ⊥ :=
  ker_shift_eq_bot_of_norm_identity fun x => hA.norm_sub_I_smul_sq x

/-- `A + i = shift A (-i)` is injective for symmetric `A` (Reed & Simon I, §VIII.2,
proof of Thm VIII.3), from the frozen norm identity `IsSymmetric.norm_add_I_smul_sq`. -/
theorem IsSymmetric.ker_shift_neg_I {A : H →ₗ.[ℂ] H} (hA : IsSymmetric A) :
    LinearMap.ker (shift A (-Complex.I)).toFun = ⊥ :=
  ker_shift_eq_bot_of_norm_identity fun x => by
    simpa [neg_smul, sub_neg_eq_add] using hA.norm_add_I_smul_sq x

/-- **The Cayley transform** `U = (A - i)(A + i)⁻¹` of an unbounded operator
`A : H →ₗ.[ℂ] H`: the partial map with domain `ran (A + i)` sending
`(A + i) x ↦ (A - i) x` (Rudin, *Functional Analysis*, 2nd ed., Thm 13.19;
Reed & Simon II, §X.1; von Neumann (1930)).

Encoded through the resolvent identity `U z = z - 2i • (A + i)⁻¹ z` (Rudin's
computation `Uz = z - 2ix` for `z = Ax + ix` in the proof of Thm 13.19), with
`(A + i)⁻¹ = (shift A (-Complex.I)).inverse` from Mathlib. This makes the definition
total in `A` (junk-value philosophy; see the module docstring) with domain
`ran (A + i)` unconditionally (`cayley_domain`). For *symmetric* `A` the map is
honest — `A + i` is injective (`IsSymmetric.ker_shift_neg_I`), and the textbook rule
`(A + i) x ↦ (A - i) x` is the kernel-checked `IsSymmetric.cayley_apply_eq` — and the
node-P2.3c targets state that it is isometric onto `ran (A - i)`, has no eigenvalue
`1`, and is a bijection self-adjoint `A` ↔ unitary `U` without eigenvalue `1`. -/
noncomputable def cayley (A : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H :=
  ⟨((shift A (-Complex.I)).inverse).domain,
    ((shift A (-Complex.I)).inverse).domain.subtype
      - (2 * Complex.I) • ((shift A (-Complex.I)).inverse).toFun⟩

/-- The domain of the Cayley transform is `ran (A + i)`, unconditionally (Rudin,
Thm 13.19; the `shift A (-Complex.I)` spelling is the frozen deficiency convention:
`K₊ = deficiencySpace A (-Complex.I) = (ran (A + i))ᗮ`). -/
theorem cayley_domain (A : H →ₗ.[ℂ] H) :
    (cayley A).domain = LinearMap.range (shift A (-Complex.I)).toFun :=
  _root_.LinearPMap.inverse_domain

/-- **Domain defect of the Cayley transform = `K₊`**: the orthocomplement of
`(cayley A).domain = ran (A + i)` is the deficiency space
`deficiencySpace A (-Complex.I) = K₊ = ker (A† - i)` (Reed & Simon II, §X.1;
frozen sign table of the P2.3a/b spec). Unconditional. The range-side counterpart
(`K₋`) is the target `CayleyRangeEq`. -/
theorem cayley_domain_orthogonal (A : H →ₗ.[ℂ] H) :
    ((cayley A).domain)ᗮ = deficiencySpace A (-Complex.I) := by
  rw [cayley_domain]; rfl

/-- Membership in the Cayley transform's domain, in working form: `y ∈ dom (cayley A)`
iff `y = A x + i • x` for some `x` in the domain of `A` (Rudin, Thm 13.19:
`dom U = ran (A + iI)`). -/
theorem mem_cayley_domain_iff {A : H →ₗ.[ℂ] H} {y : H} :
    y ∈ (cayley A).domain ↔ ∃ x : A.domain, A x + Complex.I • (x : H) = y := by
  rw [cayley_domain]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, by
      show A.toFun x + Complex.I • (x : H) = A.toFun x - (-Complex.I) • (x : H)
      module⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by
      show A.toFun x - (-Complex.I) • (x : H) = A.toFun x + Complex.I • (x : H)
      module⟩

/-- The Cayley transform in resolvent form: `U z = z - 2i • (A + i)⁻¹ z`. Definitional
(`rfl`); the geometric form `(A + i) x ↦ (A - i) x` is `IsSymmetric.cayley_apply_eq`. -/
theorem cayley_apply (A : H →ₗ.[ℂ] H) (y : (cayley A).domain) :
    cayley A y = (y : H) - (2 * Complex.I) • (shift A (-Complex.I)).inverse y :=
  rfl

/-- **The pinning computation** (kernel-checked because it *is* the textbook
definition): for symmetric `A`, the Cayley transform sends `(A + i) x ↦ (A - i) x`
(Rudin, *Functional Analysis*, 2nd ed., Thm 13.19; Reed & Simon II, §X.1). Stated in
the style of `LinearPMap.inverse_apply_eq`: any domain element known to equal
`A x + i • x` is mapped to `A x - i • x`. -/
theorem IsSymmetric.cayley_apply_eq {A : H →ₗ.[ℂ] H} (hA : IsSymmetric A)
    {y : (cayley A).domain} {x : A.domain} (hxy : A x + Complex.I • (x : H) = y) :
    cayley A y = A x - Complex.I • (x : H) := by
  have hinv : (shift A (-Complex.I)).inverse y = x :=
    _root_.LinearPMap.inverse_apply_eq hA.ker_shift_neg_I
      (by rw [shift_apply A (-Complex.I) x, neg_smul, sub_neg_eq_add]; exact hxy)
  rw [cayley_apply, hinv, ← hxy]
  module

/-- **The inverse Cayley transform** `A = i(1 + U)(1 - U)⁻¹` of `U : H →ₗ.[ℂ] H`: the
partial map with domain `ran (U - 1) = ran (1 - U)` recovering the symmetric operator
from its Cayley transform (Rudin, *Functional Analysis*, 2nd ed., Thm 13.19;
Reed & Simon II, §X.1).

Encoded on the primitive `shift U 1 = U - 1·id` (so that the no-eigenvalue-1
condition reads `ker (shift U 1).toFun = ⊥`, and `(U - 1)⁻¹ = (shift U 1).inverse`):
on `z = (U - 1) x` the value is `i(1 + U)(1 - U)⁻¹ z = -i • (x + U x)`, since
`(1 - U)(-x) = z`; in resolvent form, `z ↦ -i • (2 • (U - 1)⁻¹ z + z)`
(`inverseCayley_apply`, definitional). Total in `U` with domain `ran (U - 1)`
unconditionally (`inverseCayley_domain`); honest when `U - 1` is injective, which is
the target `CayleyOneNotEigenvalue` for `U = cayley A`, `A` symmetric. The node-P2.3c
targets state `inverseCayley (cayley A) = A` and, for unitary `U` without eigenvalue
`1`, that `inverseCayley U` is self-adjoint with Cayley transform `U`. -/
noncomputable def inverseCayley (U : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H :=
  ⟨((shift U 1).inverse).domain,
    (-Complex.I) • ((2 : ℂ) • ((shift U 1).inverse).toFun
      + ((shift U 1).inverse).domain.subtype)⟩

/-- The domain of the inverse Cayley transform is `ran (U - 1)` (`= ran (1 - U)` as a
submodule), unconditionally (Rudin, Thm 13.19: `dom A = ran (I - U)`). -/
theorem inverseCayley_domain (U : H →ₗ.[ℂ] H) :
    (inverseCayley U).domain = LinearMap.range (shift U 1).toFun :=
  _root_.LinearPMap.inverse_domain

/-- Membership in the inverse Cayley transform's domain, in working form:
`z ∈ dom (inverseCayley U)` iff `z = U x - x` for some `x` in the domain of `U`. -/
theorem mem_inverseCayley_domain_iff {U : H →ₗ.[ℂ] H} {z : H} :
    z ∈ (inverseCayley U).domain ↔ ∃ x : U.domain, U x - (x : H) = z := by
  rw [inverseCayley_domain]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, by
      show U.toFun x - (x : H) = U.toFun x - (1 : ℂ) • (x : H)
      module⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by
      show U.toFun x - (1 : ℂ) • (x : H) = U.toFun x - (x : H)
      module⟩

/-- The inverse Cayley transform in resolvent form:
`A z = -i • (2 • (U - 1)⁻¹ z + z)`. Definitional (`rfl`); the geometric form
`(U - 1) x ↦ -i • (x + U x)` is `inverseCayley_apply_eq`. -/
theorem inverseCayley_apply (U : H →ₗ.[ℂ] H) (z : (inverseCayley U).domain) :
    inverseCayley U z = -Complex.I • ((2 : ℂ) • (shift U 1).inverse z + (z : H)) :=
  rfl

/-- **The pinning computation for the inverse transform**: when `U - 1` is injective,
`inverseCayley U` sends `(U - 1) x ↦ -i • (x + U x)` — that is,
`i(1 + U)(1 - U)⁻¹` on `(1 - U) x = -(U - 1) x` (Rudin, *Functional Analysis*,
2nd ed., Thm 13.19: `A(I - U) x = i(I + U) x`; mind the sign, see the module
docstring). Sanity: for `U = cayley A` and `z = (U - 1)((A + i) x) = -2i • x` this
gives `-i • ((A + i) x + (A - i) x) = -2i • A x = A z`, which is the recovery target
`InverseCayleyCayley`. -/
theorem inverseCayley_apply_eq {U : H →ₗ.[ℂ] H}
    (hU : LinearMap.ker (shift U 1).toFun = ⊥) {z : (inverseCayley U).domain}
    {x : U.domain} (hxz : U x - (x : H) = z) :
    inverseCayley U z = -Complex.I • ((x : H) + U x) := by
  have hinv : (shift U 1).inverse z = x :=
    _root_.LinearPMap.inverse_apply_eq hU (by rw [shift_apply U 1 x, one_smul]; exact hxz)
  rw [inverseCayley_apply, hinv, ← hxz]
  module

end LinearPMap

/-- **Target statement — the Cayley transform is isometric** (blueprint node P2.3c):
for symmetric `A`, `‖U y‖ = ‖y‖` on `dom U = ran (A + i)` (Rudin, *Functional
Analysis*, 2nd ed., Thm 13.19; Reed & Simon II, §X.1). The proof is the frozen norm
identity of the P2.3a/b spec read twice: `‖(A + i) x‖² = ‖A x‖² + ‖x‖² = ‖(A - i) x‖²`.
No density or completeness is needed.

Stated as a `Prop`-valued definition: the proof is node P2.3c, and per project rules a
stuck proof decomposes into lemmas — it never weakens this statement. -/
def CayleyIsometric (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : Prop :=
  ∀ A : H →ₗ.[ℂ] H, LinearPMap.IsSymmetric A →
    ∀ y : (LinearPMap.cayley A).domain, ‖LinearPMap.cayley A y‖ = ‖(y : H)‖

/-- **Target statement — the range of the Cayley transform** (blueprint node P2.3c):
for symmetric `A`, `ran (cayley A) = ran (A - i)` (Rudin, *Functional Analysis*,
2nd ed., Thm 13.19: `U` maps `ran (A + iI)` onto `ran (A - iI)`). Taking
orthocomplements, the *range defect* is the deficiency space
`deficiencySpace A Complex.I = K₋ = ker (A† + i)` — the codomain half of the sign
table, complementing the kernel-checked domain half `cayley_domain_orthogonal`
(Reed & Simon II, §X.1). -/
def CayleyRangeEq (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : Prop :=
  ∀ A : H →ₗ.[ℂ] H, LinearPMap.IsSymmetric A →
    LinearMap.range (LinearPMap.cayley A).toFun
      = LinearMap.range (LinearPMap.shift A Complex.I).toFun

/-- **Target statement — `1` is not an eigenvalue of the Cayley transform** (blueprint
node P2.3c): for symmetric `A`, `U - 1` is injective on `dom U` (Rudin, *Functional
Analysis*, 2nd ed., Thm 13.19: `I - U` is one-to-one; the fixed-point equation
`U y = y` with `y = (A + i) x` forces `2i • x = 0`). This is what makes the domain of
`inverseCayley (cayley A)` honest and, in the self-adjoint case, pins the codomain of
the eventual bijection: unitaries `U` with `ker (1 - U) = ⊥`. -/
def CayleyOneNotEigenvalue (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] : Prop :=
  ∀ A : H →ₗ.[ℂ] H, LinearPMap.IsSymmetric A →
    LinearMap.ker (LinearPMap.shift (LinearPMap.cayley A) 1).toFun = ⊥

/-- **Target statement — recovery of `A` from its Cayley transform** (blueprint node
P2.3c): for symmetric `A`, `inverseCayley (cayley A) = A` — von Neumann's
`A = i(1 + U)(1 - U)⁻¹` (Rudin, *Functional Analysis*, 2nd ed., Thm 13.19: "`U`
determines `A`"; Reed & Simon II, §X.1). As a `LinearPMap` equality this contains
both `ran ((cayley A) - 1) = dom A` (the domain leg, via `inverseCayley_domain`) and
the value computation; it is the injectivity of `A ↦ cayley A` on symmetric
operators. No density hypothesis is needed: the mechanism is injectivity of `A ± i`,
which symmetry alone provides. -/
def InverseCayleyCayley (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] : Prop :=
  ∀ A : H →ₗ.[ℂ] H, LinearPMap.IsSymmetric A →
    LinearPMap.inverseCayley (LinearPMap.cayley A) = A

/-- **Target statement — self-adjointness ⟺ the Cayley transform is a bijection of
`H`** (blueprint node P2.3c, the headliner): a densely defined symmetric `A` is
self-adjoint iff `cayley A` is everywhere defined (`dom = ⊤`, i.e. `ran (A + i) = H`)
and surjective (`ran = ⊤`, i.e. — via `CayleyRangeEq` — `ran (A - i) = H`). Together
with `CayleyIsometric` this is "`A` self-adjoint iff `U` unitary" (Rudin, *Functional
Analysis*, 2nd ed., Thm 13.19), and it is exactly the basic criterion
`A = A† ↔ ran (A ± i) = H` of Reed & Simon I, §VIII.2, Thm VIII.3 — the totality
clause `(cayley A).domain = ⊤` is the deficiency theory of node P2.3b closing up:
`K₊ = (dom (cayley A))ᗮ` (`cayley_domain_orthogonal`) and `K₋` must vanish *with
closed ranges*. Neither closedness of `A` nor any extra hypothesis is needed: the
forward direction produces it, and the reverse direction of Thm VIII.3 derives
self-adjointness from surjectivity alone. -/
def CayleySelfAdjointIffBijective (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ A : H →ₗ.[ℂ] H, Dense (A.domain : Set H) → LinearPMap.IsSymmetric A →
    (IsSelfAdjoint A ↔
      (LinearPMap.cayley A).domain = ⊤
        ∧ LinearMap.range (LinearPMap.cayley A).toFun = ⊤)

/-- **Target statement — the inverse transform of a unitary without eigenvalue `1` is
self-adjoint** (blueprint node P2.3c, surjectivity half, part 1): for every unitary
`U` on `H` with `ker (1 - U) = ⊥`, the operator `inverseCayley U` (of the everywhere
defined `LinearPMap` underlying `U`) is self-adjoint (Rudin, *Functional Analysis*,
2nd ed., Thm 13.19; Reed & Simon II, §X.1; von Neumann (1930)). Note `dom
(inverseCayley U) = ran (U - 1)` is dense precisely because `ker (1 - U*) =
ker (1 - U⁻¹) = ker (U - 1) = ⊥` for unitary `U` — density is *derived*, not
hypothesized. -/
def InverseCayleySelfAdjoint (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ U : unitary (H →L[ℂ] H), (1 - (U : H →L[ℂ] H)).ker = ⊥ →
    IsSelfAdjoint
      (LinearPMap.inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤))

/-- **Target statement — every unitary without eigenvalue `1` is a Cayley transform**
(blueprint node P2.3c, surjectivity half, part 2): for unitary `U` with
`ker (1 - U) = ⊥`, the Cayley transform of `inverseCayley U` is `U` itself (as the
everywhere defined `LinearPMap`) (Rudin, *Functional Analysis*, 2nd ed., Thm 13.19;
Reed & Simon II, §X.1; von Neumann (1930)). With `InverseCayleySelfAdjoint`,
`CayleySelfAdjointIffBijective`, `CayleyIsometric`, and the injectivity
`InverseCayleyCayley`, this yields the bijection
`{A // IsSelfAdjoint A} ≃ {U : unitary // ker (1 - U) = ⊥}` (`cayleyEquiv`, deferred
to the proof node since constructing it *is* proving these statements). -/
def CayleyInverseCayley (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ U : unitary (H →L[ℂ] H), (1 - (U : H →L[ℂ] H)).ker = ⊥ →
    LinearPMap.cayley
        (LinearPMap.inverseCayley (((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤))
      = ((U : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤

end OperatorTheory
