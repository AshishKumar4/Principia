import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# P2.3a/P2.3b — Symmetric operators, deficiency subspaces, essential self-adjointness

Frozen spec (blueprint nodes P2.3a/P2.3b): proof sessions must not edit this file; changes
require a spec review and a `[spec-review]` commit (see CLAUDE.md).

## Contents

* `LinearPMap.IsSymmetric`: an unbounded operator `A : H →ₗ.[ℂ] H` is symmetric if
  `⟪A x, y⟫ = ⟪x, A y⟫` on its domain, plus basic API: equivalence with
  `LinearPMap.IsFormalAdjoint A A`, equivalence with `A ≤ A.adjoint` (for densely
  defined `A`), self-adjoint → symmetric, symmetric densely defined → closable, and
  reality of the expectation values `⟪A x, x⟫`.
* The norm identity `‖A x ± I • x‖² = ‖A x‖² + ‖x‖²` for symmetric `A`
  (`IsSymmetric.norm_add_I_smul_sq`/`norm_sub_I_smul_sq`), proved here since the
  computation pins the definition.
* `LinearPMap.deficiencySpace A c := (ran (A - c))ᗮ`, with the membership
  characterization and the equivalence `deficiencySpace = ⊥ ↔ Dense (ran (A - c))`.
* `LinearPMap.IsEssentiallySelfAdjoint A := IsSelfAdjoint A.closure`.
* Prop-valued target statements for blueprint node P2.3b:
  `DeficiencySpaceEqKerAdjoint` (deficiency space = eigenspace of the adjoint) and
  `EssentialSelfAdjointnessCriterion` (the Reed–Simon basic criterion).

## Conventions

* **Symmetric does not bake in density.** Reed & Simon (I, §VIII.2) and Rudin define a
  *symmetric* operator to be densely defined with `⟪A x, y⟫ = ⟪x, A y⟫`; Weidmann calls
  the inner-product property alone *hermitian*. Here `LinearPMap.IsSymmetric` is the
  bare inner-product property (Weidmann's hermitian), and density is an explicit
  hypothesis `Dense (A.domain : Set H)` wherever a statement needs it — per project
  rules, physical/analytic assumptions are named hypotheses, never hidden in
  definitions. RS's "symmetric" is always `IsSymmetric` + the density hypothesis.
* **`A ≤ A.adjoint` uses Mathlib's `LinearPMap` order**: `A ≤ B` iff
  `A.domain ≤ B.domain` and `A`, `B` agree on `A.domain` — exactly the operator
  extension relation `A ⊂ B` of the sources. So `IsSymmetric` + density ↔ `A ≤ A†`
  (`isSymmetric_iff_le_adjoint`) is RS's definition of symmetric, verbatim.
* **Junk values.** Mathlib's `LinearPMap.adjoint` of a *non*-densely-defined operator
  is the zero map on its natural domain, and `LinearPMap.closure` of a *non*-closable
  operator is the operator itself (`LinearPMap.closure_def'`). Both junk values are
  benign here: `isSymmetric_of_le_adjoint` holds unconditionally (a non-densely
  defined `A` with `A ≤ A†` is forced to vanish, hence is trivially symmetric), and
  `IsEssentiallySelfAdjoint A = IsSelfAdjoint A.closure` is correctly `False` for
  non-closable `A` because a self-adjoint operator is closed
  (`IsSelfAdjoint.isClosed`), so `A.closure = A` can only be self-adjoint if `A` was
  closable after all. No closability hypothesis is needed.
* **Deficiency parameter.** `deficiencySpace A c := (ran (A - c·id))ᗮ`, encoded as
  `(LinearMap.range (A.toFun - c • A.domain.subtype))ᗮ` — the range-orthocomplement
  form is the definitional primitive because it needs *no* density hypothesis (the
  adjoint-kernel form does, since it goes through `A†`). For densely defined `A` it
  equals the eigenspace `ker (A† - c̄)` — note the **conjugate**:
  `y ⊥ ran (A - c)` iff `⟪A x, y⟫ = ⟪x, c̄ • y⟫` for all `x` — stated as the target
  `DeficiencySpaceEqKerAdjoint`. Consequently the classical deficiency subspaces
  (Reed & Simon II, §X.1; von Neumann (1930)) are
  `K₊ = ker (A† - i) = (ran (A + i))ᗮ = deficiencySpace A (-I)` and
  `K₋ = ker (A† + i) = (ran (A - i))ᗮ = deficiencySpace A I` — mind the sign
  inversion between the parameter `c` and the `±` label.
* **Namespace.** Declarations live in `OperatorTheory.LinearPMap`, parallel to
  `OperatorTheory.OneParameterUnitaryGroup` of the P2.3g spec; on upstreaming to
  Mathlib they would move to the root `LinearPMap` namespace. Beware that dot
  notation on an *operator* (`A.IsSymmetric`) does not resolve from inside
  `namespace OperatorTheory` — write `LinearPMap.IsSymmetric A` there; it does
  resolve under `open OperatorTheory` from outside (probe-verified). Dot
  notation on a *hypothesis* (`hA.le_adjoint`, `hA.norm_add_I_smul_sq`) works as
  usual, since `IsSymmetric`'s full name is the project one.

## Target statements (not theorems here)

The node-P2.3b theorems are recorded as `Prop`-valued definitions
(`DeficiencySpaceEqKerAdjoint`, `EssentialSelfAdjointnessCriterion`); a stuck proof
node must be decomposed, never allowed to weaken them. The classical criterion is a
three-way equivalence (essentially self-adjoint ↔ deficiency spaces vanish ↔ ranges
dense); its third leg is *already kernel-checked here* as
`deficiencySpace_eq_bot_iff_dense`, so the frozen target states only the first
equivalence and the ranges-dense form follows definitionally.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised and enlarged edition (1980), §VIII.2: definitions of symmetric,
  self-adjoint, and essentially self-adjoint operators; Thm VIII.3 (the basic
  criterion for self-adjointness) and its Corollary (the basic criterion for
  *essential* self-adjointness: `A` essentially self-adjoint ↔ `ker (A* ∓ i) = {0}` ↔
  `ran (A ± i)` dense); the norm identity `‖(A ± i)x‖² = ‖Ax‖² + ‖x‖²` is the
  computation opening the proof of Thm VIII.3.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II: Fourier Analysis,
  Self-Adjointness* (1975), §X.1: deficiency subspaces `K± = ker (A* ∓ i)`,
  deficiency indices `n± = dim K±`, von Neumann's extension theory.
* J. von Neumann, "Allgemeine Eigenwerttheorie Hermitescher Funktionaloperatoren",
  *Math. Ann.* 102 (1930), 49–131 (origin of the deficiency theory).
* J. Weidmann, *Linear Operators in Hilbert Spaces*, GTM 68 (1980), ch. 5 (hermitian/
  symmetric/self-adjoint operators; note his "hermitian" = our `IsSymmetric`) and
  ch. 8 (self-adjoint extensions, defect indices). Chapter-level citations: section
  numbers not re-verified against a copy.
* W. Rudin, *Functional Analysis*, 2nd ed. (1991), ch. 13 (symmetric operators,
  deficiency indices, the Cayley transform). Chapter-level citation.
-/

namespace OperatorTheory

open scoped ComplexConjugate

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- An unbounded operator `A` on a complex inner-product space is *symmetric* if
`⟪A x, y⟫ = ⟪x, A y⟫` for all `x`, `y` in its domain.

This is the partial-map analogue of `LinearMap.IsSymmetric` and coincides with
`LinearPMap.IsFormalAdjoint A A` (`isSymmetric_iff_isFormalAdjoint`). Following
Weidmann (ch. 5, his "hermitian") the definition does **not** require a dense domain;
Reed & Simon's "symmetric" (I, §VIII.2) is this property plus the explicit hypothesis
`Dense (A.domain : Set H)`, under which it is equivalent to `A ≤ A.adjoint`
(`isSymmetric_iff_le_adjoint`). -/
def IsSymmetric (A : H →ₗ.[ℂ] H) : Prop :=
  ∀ x y : A.domain, ⟪A x, y⟫ = ⟪(x : H), A y⟫

/-- Symmetry is the statement that `A` is a formal adjoint of itself; this connects
`IsSymmetric` to Mathlib's `LinearPMap.IsFormalAdjoint` API (Reed & Simon I, §VIII.1
for the formal-adjoint relation). -/
theorem isSymmetric_iff_isFormalAdjoint {A : H →ₗ.[ℂ] H} :
    IsSymmetric A ↔ A.IsFormalAdjoint A :=
  Iff.rfl

namespace IsSymmetric

variable {A : H →ₗ.[ℂ] H}

/-- Conjugating flips a symmetric sesquilinear pairing: `conj ⟪A x, y⟫ = ⟪A y, x⟫`.
Partial-map analogue of `LinearMap.IsSymmetric.conj_inner_sym`. -/
theorem conj_inner_sym (hA : IsSymmetric A) (x y : A.domain) :
    conj ⟪A x, (y : H)⟫ = ⟪A y, (x : H)⟫ := by
  rw [hA x y, inner_conj_symm]

/-- Expectation values of a symmetric operator are real: `⟪A x, x⟫` has vanishing
imaginary part (Reed & Simon I, §VIII.2). Partial-map analogue of
`LinearMap.IsSymmetric.im_inner_apply_self`. -/
theorem im_inner_apply_self (hA : IsSymmetric A) (x : A.domain) :
    (⟪A x, (x : H)⟫).im = 0 :=
  Complex.conj_eq_iff_im.mp (hA.conj_inner_sym x x)

/-- **The norm identity, `+` version**: for symmetric `A` and `x` in its domain,
`‖A x + i • x‖² = ‖A x‖² + ‖x‖²`. The cross terms cancel because `⟪A x, x⟫` is real.
This is the computation opening the proof of the basic criterion (Reed & Simon I,
§VIII.2, proof of Thm VIII.3); it makes `A ± i` injective with closed range on a
closed symmetric operator, which is why the deficiency spaces control self-adjointness. -/
theorem norm_add_I_smul_sq (hA : IsSymmetric A) (x : A.domain) :
    ‖A x + Complex.I • (x : H)‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, Complex.norm_I, one_mul,
    ← RCLike.I_to_complex, RCLike.I_mul_re, RCLike.im_to_complex,
    hA.im_inner_apply_self, neg_zero, mul_zero, add_zero]

/-- **The norm identity, `-` version**: for symmetric `A` and `x` in its domain,
`‖A x - i • x‖² = ‖A x‖² + ‖x‖²` (Reed & Simon I, §VIII.2, proof of Thm VIII.3). -/
theorem norm_sub_I_smul_sq (hA : IsSymmetric A) (x : A.domain) :
    ‖A x - Complex.I • (x : H)‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, Complex.norm_I, one_mul,
    ← RCLike.I_to_complex, RCLike.I_mul_re, RCLike.im_to_complex,
    hA.im_inner_apply_self, neg_zero, mul_zero, sub_zero]

end IsSymmetric

section Adjoint

variable [CompleteSpace H] {A : H →ₗ.[ℂ] H}

/-- A densely defined symmetric operator is contained in its adjoint: `A ≤ A†`. This
is Reed & Simon's definition of symmetric (I, §VIII.2, "`A ⊂ A*`"), recovered from the
inner-product form via the maximality of the adjoint among formal adjoints. -/
theorem IsSymmetric.le_adjoint (hA : IsSymmetric A) (hd : Dense (A.domain : Set H)) :
    A ≤ A.adjoint :=
  (isSymmetric_iff_isFormalAdjoint.mp hA).le_adjoint hd

/-- An operator contained in its adjoint is symmetric. No density hypothesis is
needed: for a non-densely defined `A`, the adjoint is the zero map by Mathlib's junk
value, so `A ≤ A†` forces `A` to vanish, and the zero pairing is trivially symmetric. -/
theorem isSymmetric_of_le_adjoint (h : A ≤ A.adjoint) : IsSymmetric A := by
  intro x y
  rw [_root_.LinearPMap.apply_comp_inclusion h x]
  by_cases hd : Dense (A.domain : Set H)
  · exact _root_.LinearPMap.adjoint_isFormalAdjoint hd (Submodule.inclusion h.1 x) y
  · rw [_root_.LinearPMap.adjoint_apply_of_not_dense hd, inner_zero_left,
      _root_.LinearPMap.apply_comp_inclusion h y,
      _root_.LinearPMap.adjoint_apply_of_not_dense hd, inner_zero_right]

/-- **Symmetric ↔ contained in the adjoint**, for densely defined operators
(Reed & Simon I, §VIII.2; Weidmann, ch. 5). -/
theorem isSymmetric_iff_le_adjoint (hd : Dense (A.domain : Set H)) :
    IsSymmetric A ↔ A ≤ A.adjoint :=
  ⟨fun hA => hA.le_adjoint hd, isSymmetric_of_le_adjoint⟩

/-- Every self-adjoint operator is symmetric (Reed & Simon I, §VIII.2: `A = A*`
implies `A ⊂ A*`). The converse fails for unbounded operators — the whole point of
this file; the gap is measured by the deficiency spaces. -/
theorem isSymmetric_of_isSelfAdjoint (hA : IsSelfAdjoint A) : IsSymmetric A :=
  isSymmetric_of_le_adjoint (_root_.LinearPMap.isSelfAdjoint_def.mp hA).ge

/-- A densely defined symmetric operator is closable: `A†` is a closed extension of
`A` (Reed & Simon I, §VIII.2: `A ⊂ A** ⊂ A*`, so the closure exists; Weidmann,
ch. 5). This is what makes `IsEssentiallySelfAdjoint` below contentful for every
densely defined symmetric operator. -/
theorem IsSymmetric.isClosable (hA : IsSymmetric A) (hd : Dense (A.domain : Set H)) :
    A.IsClosable :=
  (_root_.LinearPMap.adjoint_isClosed hd).isClosable.leIsClosable (hA.le_adjoint hd)

end Adjoint

/-- The *deficiency space* of `A : H →ₗ.[ℂ] H` at `c : ℂ`: the orthogonal complement
of the range of `A - c·id` (with domain `A.domain`), encoded as
`(LinearMap.range (A.toFun - c • A.domain.subtype))ᗮ`.

The range-orthocomplement form is the definitional primitive: it requires no density
hypothesis. For densely defined `A` it equals the eigenspace `ker (A† - c̄)` — note
the conjugate — which is the target statement `DeficiencySpaceEqKerAdjoint`. The
classical deficiency subspaces and indices (Reed & Simon II, §X.1; von Neumann
(1930); Weidmann, ch. 8; Rudin, ch. 13) are
`K₊ = ker (A† - i) = deficiencySpace A (-Complex.I)` with `n₊ = dim K₊`, and
`K₋ = ker (A† + i) = deficiencySpace A Complex.I` with `n₋ = dim K₋`. -/
noncomputable def deficiencySpace (A : H →ₗ.[ℂ] H) (c : ℂ) : Submodule ℂ H :=
  (LinearMap.range (A.toFun - c • A.domain.subtype))ᗮ

/-- Membership in the deficiency space is orthogonality to the shifted range:
`y ∈ deficiencySpace A c` iff `⟪A x - c • x, y⟫ = 0` for every `x` in the domain.
This is the working form of the definition (Reed & Simon II, §X.1). -/
theorem mem_deficiencySpace_iff {A : H →ₗ.[ℂ] H} {c : ℂ} {y : H} :
    y ∈ deficiencySpace A c ↔ ∀ x : A.domain, ⟪A x - c • (x : H), y⟫ = 0 := by
  rw [deficiencySpace, Submodule.mem_orthogonal]
  constructor
  · intro hy x
    exact hy _ (LinearMap.mem_range_self _ x)
  · rintro hy u ⟨x, rfl⟩
    exact hy x

/-- The deficiency space at `c` vanishes iff `A - c·id` has dense range. This is the
bridge between conditions (b) and (c) of the basic criterion (Reed & Simon I, §VIII.2,
Corollary to Thm VIII.3): with it, `EssentialSelfAdjointnessCriterion` — stated via
vanishing deficiency spaces — is definitionally also the dense-ranges criterion. -/
theorem deficiencySpace_eq_bot_iff_dense [CompleteSpace H] {A : H →ₗ.[ℂ] H} {c : ℂ} :
    deficiencySpace A c = ⊥ ↔
      Dense ((LinearMap.range (A.toFun - c • A.domain.subtype) : Submodule ℂ H) : Set H) := by
  rw [deficiencySpace, ← Submodule.topologicalClosure_eq_top_iff,
    ← Submodule.dense_iff_topologicalClosure_eq_top]

/-- An unbounded operator is *essentially self-adjoint* if its closure is self-adjoint
(Reed & Simon I, §VIII.2 — their definition verbatim; Weidmann, ch. 5).

No closability hypothesis is needed: for non-closable `A` Mathlib's junk value is
`A.closure = A` (`LinearPMap.closure_def'`), and a self-adjoint operator is closed
(`IsSelfAdjoint.isClosed`) hence closable, so this proposition is correctly `False`
for non-closable `A`. For the operators of interest — densely defined symmetric ones —
closability is automatic (`IsSymmetric.isClosable`). An essentially self-adjoint
operator has a *unique* self-adjoint extension, namely its closure (Reed & Simon I,
§VIII.2) — uniqueness is a node-P2.3b lemma, not part of the definition. -/
def IsEssentiallySelfAdjoint [CompleteSpace H] (A : H →ₗ.[ℂ] H) : Prop :=
  IsSelfAdjoint A.closure

end LinearPMap

/-- **Target statement — deficiency space as adjoint eigenspace** (blueprint node
P2.3b): for densely defined `A`, the deficiency space at `c` is the `c̄`-eigenspace of
the adjoint, `deficiencySpace A c = ker (A† - c̄)`. Note the conjugate: `y ⊥ (A - c) x`
for all `x` unwinds to `⟪A x, y⟫ = ⟪x, c̄ • y⟫`, i.e. `y ∈ D(A†)` with `A† y = c̄ • y`
(Reed & Simon II, §X.1; Weidmann, ch. 8). In particular
`K± = ker (A† ∓ i) = deficiencySpace A (∓Complex.I)`.

Stated as a `Prop`-valued definition: the proof is node P2.3b, and per project rules a
stuck proof decomposes into lemmas — it never weakens this statement. -/
def DeficiencySpaceEqKerAdjoint (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ A : H →ₗ.[ℂ] H, Dense (A.domain : Set H) → ∀ (c : ℂ) (y : H),
    y ∈ LinearPMap.deficiencySpace A c ↔
      ∃ hy : y ∈ A.adjoint.domain, A.adjoint ⟨y, hy⟩ = conj c • y

/-- **Target statement — the basic criterion for essential self-adjointness**
(blueprint node P2.3b): a densely defined symmetric operator is essentially
self-adjoint iff both deficiency spaces at `±i` vanish.

Source: Reed & Simon I, §VIII.2, **Corollary to Thm VIII.3** (Thm VIII.3 itself is the
closed-operator version: `A` self-adjoint ↔ `A` closed and `ker (A* ± i) = {0}` ↔
`ran (A ± i) = H`; the corollary trades closedness for the closure and surjectivity
for density). Also Weidmann, ch. 8; Rudin, ch. 13. The classical statement is a
three-way equivalence — with `ran (A ± i)` dense as the third leg — and that leg is
already available definitionally through `deficiencySpace_eq_bot_iff_dense`, so only
the deficiency-space form is frozen. In the notation of Reed & Simon II §X.1 the
right-hand side reads `K₋ = {0} ∧ K₊ = {0}`, i.e. `n₊ = n₋ = 0`. -/
def EssentialSelfAdjointnessCriterion (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ A : H →ₗ.[ℂ] H, Dense (A.domain : Set H) → LinearPMap.IsSymmetric A →
    (LinearPMap.IsEssentiallySelfAdjoint A ↔
      LinearPMap.deficiencySpace A Complex.I = ⊥ ∧
        LinearPMap.deficiencySpace A (-Complex.I) = ⊥)

end OperatorTheory
