import Atlas.Specs.OperatorTheory.Symmetric

/-!
# P2.3b — The deficiency space as the conjugate eigenspace of the adjoint

Proof of the frozen target `OperatorTheory.DeficiencySpaceEqKerAdjoint`
(`Atlas/Specs/OperatorTheory/Symmetric.lean`): for a densely defined operator `A`, the
deficiency space at `c` is exactly the set of adjoint-domain vectors `y` with
`A† y = c̄ • y`, i.e. the `c̄`-eigenspace `ker (A† - c̄)`.

The proof is the conjugation identity opening §X.1 of Reed & Simon II: unwinding
`y ⊥ ran (A - c)` gives `⟪A x, y⟫ = c̄ ⟪x, y⟫` for all `x` in the domain, whose complex
conjugate `⟪y, A x⟫ = c ⟪y, x⟫` is precisely the defining relation of `y ∈ D(A†)` with
`A† y = c̄ • y` (via `LinearPMap.adjoint_apply_eq` / `adjoint_isFormalAdjoint`).

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. II: Fourier Analysis,
  Self-Adjointness* (1975), §X.1: deficiency subspaces `K± = ker (A* ∓ i)`.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised ed. (1980), §VIII.2 (the adjoint and its formal-adjoint property).
-/

namespace OperatorTheory.LinearPMap

open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

omit [CompleteSpace H] in
/-- A closed operator is its own closure. Mathlib supplies `IsClosable.closure_isClosed`
(the closure is closed) but not the converse fixed-point fact used here. -/
theorem closure_eq_of_isClosed {A : H →ₗ.[ℂ] H} (hA : A.IsClosed) : A.closure = A :=
  _root_.LinearPMap.eq_of_eq_graph <| by
    rw [← hA.isClosable.graph_closure_eq_closure_graph, hA.submodule_topologicalClosure_eq]

/-- Self-adjoint operators are essentially self-adjoint: a self-adjoint operator is closed
(`IsSelfAdjoint.isClosed`), hence equal to its closure. -/
theorem isEssentiallySelfAdjoint_of_isSelfAdjoint {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) : IsEssentiallySelfAdjoint A := by
  show IsSelfAdjoint A.closure
  rw [closure_eq_of_isClosed hA.isClosed]; exact hA

omit [CompleteSpace H] in
/-- **Pointwise conjugation bridge**: for `x` in the domain, orthogonality of `y` to
`(A - c) x` is the complex conjugate of the adjoint defining relation
`⟪c̄ • y, x⟫ = ⟪y, A x⟫`. This is the single computation behind
`DeficiencySpaceEqKerAdjoint`. -/
private theorem inner_sub_smul_eq_zero_iff_adjoint_relation {A : H →ₗ.[ℂ] H} {c : ℂ} {y : H}
    (x : A.domain) :
    ⟪A x - c • (x : H), y⟫ = 0 ↔ ⟪(conj c) • y, (x : H)⟫ = ⟪y, A x⟫ := by
  rw [inner_sub_left, inner_smul_left, sub_eq_zero, inner_smul_left, RCLike.conj_conj]
  rw [← inner_conj_symm (A x) y, ← inner_conj_symm (x : H) y]
  constructor
  · intro h
    have := congrArg conj h
    simpa only [RCLike.conj_conj, map_mul] using this.symm
  · intro h
    have := congrArg conj h
    simpa only [RCLike.conj_conj, map_mul] using this.symm

/-- **Deficiency space = conjugate eigenspace of the adjoint** (working form): for
densely defined `A`, `y ∈ deficiencySpace A c` iff `y ∈ D(A†)` and `A† y = c̄ • y`
(Reed & Simon II, §X.1). This is `DeficiencySpaceEqKerAdjoint` specialized to a fixed
`A`, `c`, `y`. -/
theorem mem_deficiencySpace_iff_mem_adjoint_eigenspace {A : H →ₗ.[ℂ] H}
    (hd : Dense (A.domain : Set H)) (c : ℂ) (y : H) :
    y ∈ deficiencySpace A c ↔
      ∃ hy : y ∈ A.adjoint.domain, A.adjoint ⟨y, hy⟩ = (conj c) • y := by
  rw [mem_deficiencySpace_iff]
  simp only [inner_sub_smul_eq_zero_iff_adjoint_relation]
  constructor
  · intro key
    exact ⟨_root_.LinearPMap.mem_adjoint_domain_of_exists y ⟨(conj c) • y, key⟩,
      _root_.LinearPMap.adjoint_apply_eq hd _ key⟩
  · rintro ⟨hy, heq⟩ x
    have hfa := _root_.LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩ x
    rwa [heq] at hfa

/-! ### Towards the essential self-adjointness criterion (Reed & Simon I, Thm VIII.3) -/

omit [CompleteSpace H] in
open _root_.LinearPMap in
/-- The graph-adjoint of a submodule depends only on the submodule's closure: it is an
orthogonality (hence closed) condition. This is the graph-level fact behind
`adjoint_closure_eq_adjoint`. -/
theorem Submodule.adjoint_topologicalClosure (g : Submodule ℂ (H × H)) :
    (g.topologicalClosure).adjoint = g.adjoint := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [_root_.Submodule.mem_adjoint_iff] at hx ⊢
    exact fun a b hab => hx a b (g.le_topologicalClosure hab)
  · rw [_root_.Submodule.mem_adjoint_iff] at hx ⊢
    have hf : Continuous fun p : H × H => (inner ℂ p.2 x.1 - inner ℂ p.1 x.2 : ℂ) := by
      fun_prop
    have hsub : (g.topologicalClosure : Set (H × H)) ⊆
        {p : H × H | (inner ℂ p.2 x.1 - inner ℂ p.1 x.2 : ℂ) = 0} := by
      rw [_root_.Submodule.topologicalClosure_coe]
      exact closure_minimal (fun p hp => hx p.1 p.2 hp) (isClosed_eq hf continuous_const)
    exact fun a b hab => hsub hab

/-- **Keystone: the adjoint is invariant under closure**, `(Ā)† = A†`
(Reed & Simon I, §VIII.1–2: `A* = A**  *  = Ā*`). The adjoint is a graph-orthogonality
condition, so it only sees the closure of the graph. Not in Mathlib for `LinearPMap`. -/
theorem adjoint_closure_eq_adjoint {A : H →ₗ.[ℂ] H} (hd : Dense (A.domain : Set H))
    (hcl : A.IsClosable) : A.closure.adjoint = A.adjoint := by
  have hdc : Dense (A.closure.domain : Set H) :=
    hd.mono (SetLike.coe_subset_coe.mpr (_root_.LinearPMap.le_closure A).1)
  refine _root_.LinearPMap.eq_of_eq_graph ?_
  rw [_root_.LinearPMap.adjoint_graph_eq_graph_adjoint hdc,
    _root_.LinearPMap.adjoint_graph_eq_graph_adjoint hd,
    ← hcl.graph_closure_eq_closure_graph]
  exact Submodule.adjoint_topologicalClosure A.graph

omit [CompleteSpace H] in
/-- **Symmetric operators have no non-real eigenvalues**: if `A y = μ • y` with `Im μ ≠ 0`
then `y = 0` (Reed & Simon I, §VIII.2). The expectation value `⟪A y, y⟫ = μ̄ ‖y‖²` must be
real, forcing `‖y‖² = 0`. -/
theorem eq_zero_of_isSymmetric_smul {A : H →ₗ.[ℂ] H} (hA : IsSymmetric A) {μ : ℂ}
    (hμ : μ.im ≠ 0) (y : A.domain) (hy : A y = μ • (y : H)) : (y : H) = 0 := by
  have h0 : (inner ℂ (A y) (y : H)).im = 0 := hA.im_inner_apply_self y
  have hyy : inner ℂ (y : H) (y : H) = Complex.ofReal (‖(y : H)‖ ^ 2) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hy, inner_smul_left, hyy, Complex.mul_im, Complex.conj_im, Complex.conj_re,
    Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (neg_eq_zero.mp h) hμ
  · rw [pow_eq_zero_iff (by norm_num)] at h
    exact norm_eq_zero.mp h

/-- The deficiency space at a non-real `c` vanishes once the adjoint is symmetric: its
members are `c̄`-eigenvectors of the (symmetric) adjoint, hence zero. -/
theorem deficiencySpace_eq_bot_of_isSymmetric_adjoint {A : H →ₗ.[ℂ] H}
    (hd : Dense (A.domain : Set H)) (hadj : IsSymmetric A.adjoint) {c : ℂ} (hc : c.im ≠ 0) :
    deficiencySpace A c = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  rw [mem_deficiencySpace_iff_mem_adjoint_eigenspace hd] at hy
  obtain ⟨hyd, hval⟩ := hy
  exact eq_zero_of_isSymmetric_smul hadj (μ := conj c)
    (by rw [Complex.conj_im]; exact neg_ne_zero.mpr hc) ⟨y, hyd⟩ hval

/-- For an essentially self-adjoint operator the adjoint is symmetric: it coincides with
the (self-adjoint) closure, `A† = Ā`. -/
theorem isSymmetric_adjoint_of_isEssentiallySelfAdjoint {A : H →ₗ.[ℂ] H}
    (hd : Dense (A.domain : Set H)) (hsym : IsSymmetric A)
    (hess : IsEssentiallySelfAdjoint A) : IsSymmetric A.adjoint := by
  have heq : A.adjoint = A.closure := by
    rw [← adjoint_closure_eq_adjoint hd (hsym.isClosable hd)]
    exact _root_.LinearPMap.isSelfAdjoint_def.mp hess
  rw [heq]
  exact isSymmetric_of_isSelfAdjoint hess

/-- **Forward direction of the basic criterion**: an essentially self-adjoint operator has
both deficiency spaces at `±i` vanishing (Reed & Simon I, §VIII.2). Its adjoint equals the
self-adjoint closure, hence is symmetric, and a symmetric operator has no non-real
eigenvalues. -/
theorem deficiencySpace_eq_bot_of_isEssentiallySelfAdjoint {A : H →ₗ.[ℂ] H}
    (hd : Dense (A.domain : Set H)) (hsym : IsSymmetric A)
    (hess : IsEssentiallySelfAdjoint A) :
    deficiencySpace A Complex.I = ⊥ ∧ deficiencySpace A (-Complex.I) = ⊥ :=
  let hadj := isSymmetric_adjoint_of_isEssentiallySelfAdjoint hd hsym hess
  ⟨deficiencySpace_eq_bot_of_isSymmetric_adjoint hd hadj (by simp),
    deficiencySpace_eq_bot_of_isSymmetric_adjoint hd hadj (by simp)⟩

/-- The closure of a densely defined symmetric operator is contained in the adjoint,
`Ā ≤ A†` (the closure is the smallest closed extension and `A†` is a closed extension). -/
theorem closure_le_adjoint {A : H →ₗ.[ℂ] H} (hd : Dense (A.domain : Set H))
    (hsym : IsSymmetric A) : A.closure ≤ A.adjoint := by
  have hAcl : A.adjoint.IsClosed := _root_.LinearPMap.adjoint_isClosed hd
  calc A.closure ≤ A.adjoint.closure := hAcl.isClosable.closure_mono (hsym.le_adjoint hd)
    _ = A.adjoint := closure_eq_of_isClosed hAcl

/-- The closure of a densely defined symmetric operator is symmetric: `Ā ≤ Ā† = A†`. -/
theorem isSymmetric_closure {A : H →ₗ.[ℂ] H} (hd : Dense (A.domain : Set H))
    (hsym : IsSymmetric A) : IsSymmetric A.closure := by
  apply isSymmetric_of_le_adjoint
  rw [adjoint_closure_eq_adjoint hd (hsym.isClosable hd)]
  exact closure_le_adjoint hd hsym

/-- **Closed range from the norm identity** (Reed & Simon I, §VIII.2, proof of Thm VIII.3):
if `B` is closed and `‖B x - c • x‖² = ‖B x‖² + ‖x‖²` on its domain, then `ran (B - c)` is
closed. The map `(x, B x) ↦ B x - c • x` from the (complete, since `B` is closed) graph is
bounded below by the graph norm, hence a closed embedding with closed range. -/
theorem isClosed_range_sub_smul_of_norm_identity {B : H →ₗ.[ℂ] H} (hcB : B.IsClosed) {c : ℂ}
    (hnorm : ∀ x : B.domain, ‖B x - c • (x : H)‖ ^ 2 = ‖B x‖ ^ 2 + ‖(x : H)‖ ^ 2) :
    IsClosed (LinearMap.range (B.toFun - c • B.domain.subtype) : Set H) := by
  classical
  set L : (H × H) →L[ℂ] H :=
    ContinuousLinearMap.snd ℂ H H - c • ContinuousLinearMap.fst ℂ H H with hL
  have hLapply : ∀ v : H × H, L v = v.2 - c • v.1 := by
    intro v; simp [hL]
  -- the bounded-below inequality on the graph
  have hkey : ∀ v : H × H, v ∈ B.graph → ‖v‖ ≤ ‖L v‖ := by
    intro v hv
    obtain ⟨y, hy1, hy2⟩ := (_root_.LinearPMap.mem_graph_iff B).mp hv
    have hsq : ‖L v‖ ^ 2 = ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
      rw [hLapply, ← hy1, ← hy2, hnorm y]; ring
    have hLv : ‖L v‖ = Real.sqrt (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) := by
      rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
    rw [Prod.norm_def, hLv]
    apply max_le
    · calc ‖v.1‖ = Real.sqrt (‖v.1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖v.2‖])
    · calc ‖v.2‖ = Real.sqrt (‖v.2‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖v.1‖])
  -- package the map on the graph subtype
  set g : B.graph → H := fun r => L (r : H × H) with hg
  have hanti : AntilipschitzWith 1 g := by
    refine AntilipschitzWith.of_le_mul_dist fun p q => ?_
    have hvmem : ((p : H × H) - (q : H × H)) ∈ B.graph := B.graph.sub_mem p.2 q.2
    rw [Subtype.dist_eq, dist_eq_norm, dist_eq_norm, hg]
    simp only [NNReal.coe_one, one_mul, ← map_sub]
    exact hkey _ hvmem
  have hunif : UniformContinuous g :=
    L.uniformContinuous.comp uniformContinuous_subtype_val
  have : CompleteSpace B.graph := hcB.completeSpace_coe
  have hclosed : IsClosed (Set.range g) := hanti.isClosed_range hunif
  have hrange : Set.range g = (LinearMap.range (B.toFun - c • B.domain.subtype) : Set H) := by
    ext w
    simp only [Set.mem_range, SetLike.mem_coe, LinearMap.mem_range]
    constructor
    · rintro ⟨r, rfl⟩
      obtain ⟨y, hy1, hy2⟩ := (_root_.LinearPMap.mem_graph_iff B).mp r.2
      refine ⟨y, ?_⟩
      show (B.toFun - c • B.domain.subtype) y = L (r : H × H)
      rw [hLapply, LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
        ← hy1, ← hy2]
      rfl
    · rintro ⟨x, rfl⟩
      refine ⟨⟨((x : H), B x), _root_.LinearPMap.mem_graph B x⟩, ?_⟩
      show (B.toFun - c • B.domain.subtype) x = L ((x : H), B x)
      rw [hLapply, LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply]
      rfl
  rwa [hrange] at hclosed

omit [CompleteSpace H] in
/-- Extending the operator enlarges the shifted range: `f ≤ g` gives
`ran (f - c) ≤ ran (g - c)`. -/
theorem range_sub_smul_mono {f g : H →ₗ.[ℂ] H} (h : f ≤ g) (c : ℂ) :
    LinearMap.range (f.toFun - c • f.domain.subtype) ≤
      LinearMap.range (g.toFun - c • g.domain.subtype) := by
  rintro u ⟨x, rfl⟩
  refine ⟨Submodule.inclusion h.1 x, ?_⟩
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
    Submodule.coe_inclusion]
  rw [show g.toFun (Submodule.inclusion h.1 x) = g (Submodule.inclusion h.1 x) from rfl,
    ← _root_.LinearPMap.apply_comp_inclusion h x]
  rfl

/-- **Reverse direction of the basic criterion**: if both deficiency spaces at `±i`
vanish, then `A` is essentially self-adjoint (Reed & Simon I, §VIII.2, proof of
Thm VIII.3). The closure `Ā` is closed symmetric with `ran (Ā - i)` closed (norm identity)
and dense (`ran (A - i)` is), hence `= H`; solving `(Ā - i)x = (A† - i)y` for `y ∈ D(A†)`
puts `x - y` in `ker (A† - i) = deficiencySpace A (-i) = ⊥`, so `D(A†) ⊆ D(Ā)` and
`Ā = A† = Ā†` is self-adjoint. -/
theorem isEssentiallySelfAdjoint_of_deficiencySpace_eq_bot {A : H →ₗ.[ℂ] H}
    (hd : Dense (A.domain : Set H)) (hsym : IsSymmetric A)
    (hI : deficiencySpace A Complex.I = ⊥)
    (hnI : deficiencySpace A (-Complex.I) = ⊥) : IsEssentiallySelfAdjoint A := by
  have hcl := hsym.isClosable hd
  have hĀsym : IsSymmetric A.closure := isSymmetric_closure hd hsym
  have hcĀ : A.closure.IsClosed := hcl.closure_isClosed
  have hĀle : A.closure ≤ A.adjoint := closure_le_adjoint hd hsym
  -- `ran (Ā - i) = ⊤`: closed (norm identity) and dense (contains dense `ran (A - i)`).
  have hRtop : LinearMap.range (A.closure.toFun - Complex.I • A.closure.domain.subtype) = ⊤ := by
    have hclosed := isClosed_range_sub_smul_of_norm_identity hcĀ
      (fun x => hĀsym.norm_sub_I_smul_sq x)
    have hdense := deficiencySpace_eq_bot_iff_dense.mp hI
    rw [Submodule.eq_top_iff']
    intro z
    have hz : z ∈ closure
        ((LinearMap.range (A.toFun - Complex.I • A.domain.subtype) : Submodule ℂ H) : Set H) := by
      rw [hdense.closure_eq]; exact Set.mem_univ z
    exact closure_minimal (fun w hw => range_sub_smul_mono (_root_.LinearPMap.le_closure A)
      Complex.I hw) hclosed hz
  -- `D(A†) ⊆ D(Ā)`, the surjectivity chase.
  have hdom : A.adjoint.domain ≤ A.closure.domain := by
    intro y hy
    have hmem : A.adjoint ⟨y, hy⟩ - Complex.I • y ∈
        LinearMap.range (A.closure.toFun - Complex.I • A.closure.domain.subtype) := by
      rw [hRtop]; exact Submodule.mem_top
    obtain ⟨x', hx'⟩ := hmem
    -- hx' : Ā x' - i • x' = A† y - i • y
    have hx'adj : (x' : H) ∈ A.adjoint.domain := hĀle.1 x'.2
    have hadjx' : A.adjoint ⟨(x' : H), hx'adj⟩ = A.closure x' :=
      (_root_.LinearPMap.apply_comp_inclusion hĀle x').symm
    -- `z := x' - y ∈ ker (A† - i) = deficiencySpace A (-i) = ⊥`
    have hzmem : ((x' : H) - y) ∈ A.adjoint.domain := A.adjoint.domain.sub_mem hx'adj hy
    have heigen : A.adjoint ⟨(x' : H) - y, hzmem⟩ = Complex.I • ((x' : H) - y) := by
      have hsub : A.adjoint ⟨(x' : H) - y, hzmem⟩
          = A.adjoint ⟨(x' : H), hx'adj⟩ - A.adjoint ⟨y, hy⟩ := by
        rw [← _root_.LinearPMap.map_sub A.adjoint ⟨(x' : H), hx'adj⟩ ⟨y, hy⟩]
        congr 1
      have hx'2 : A.closure x' - Complex.I • (x' : H) = A.adjoint ⟨y, hy⟩ - Complex.I • y := by
        rw [← hx']; simp [LinearMap.sub_apply, LinearMap.smul_apply]
      rw [hsub, hadjx', smul_sub, sub_eq_sub_iff_sub_eq_sub]
      exact hx'2
    have hzdef : ((x' : H) - y) ∈ deficiencySpace A (-Complex.I) := by
      rw [mem_deficiencySpace_iff_mem_adjoint_eigenspace hd]
      exact ⟨hzmem, by rw [heigen]; simp⟩
    rw [hnI, Submodule.mem_bot, sub_eq_zero] at hzdef
    rw [← hzdef]; exact x'.2
  -- assemble: `A† ≤ Ā`, then `A† = Ā` and `Ā` is self-adjoint.
  have hle : A.adjoint ≤ A.closure :=
    ⟨hdom, fun x w hxw => by
      rw [_root_.LinearPMap.apply_comp_inclusion hĀle w]
      exact congrArg _ (Subtype.ext (hxw.trans (Submodule.coe_inclusion _ _).symm))⟩
  show IsSelfAdjoint A.closure
  rw [_root_.LinearPMap.isSelfAdjoint_def, adjoint_closure_eq_adjoint hd hcl]
  exact le_antisymm hle hĀle

end OperatorTheory.LinearPMap

namespace OperatorTheory

/-- **Target — deficiency space as adjoint eigenspace** (blueprint node P2.3b): proof of
the frozen `DeficiencySpaceEqKerAdjoint`. -/
theorem deficiencySpaceEqKerAdjoint (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : DeficiencySpaceEqKerAdjoint H :=
  fun _A hd c y => LinearPMap.mem_deficiencySpace_iff_mem_adjoint_eigenspace hd c y

/-- **Target — the basic criterion for essential self-adjointness** (blueprint node P2.3b):
proof of the frozen `EssentialSelfAdjointnessCriterion` (Reed & Simon I, §VIII.2, Corollary
to Thm VIII.3). A densely defined symmetric operator is essentially self-adjoint iff both
deficiency spaces at `±i` vanish. -/
theorem essentialSelfAdjointnessCriterion (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : EssentialSelfAdjointnessCriterion H :=
  fun _A hd hsym =>
    ⟨fun hess => LinearPMap.deficiencySpace_eq_bot_of_isEssentiallySelfAdjoint hd hsym hess,
      fun ⟨hI, hnI⟩ =>
        LinearPMap.isEssentiallySelfAdjoint_of_deficiencySpace_eq_bot hd hsym hI hnI⟩

end OperatorTheory
