import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# P2.3g — One-parameter unitary groups and the Stone generator

Frozen spec (blueprint node P2.3g): proof sessions must not edit this file; changes
require a spec review and a `[spec-review]` commit (see CLAUDE.md).

## Contents

* `OneParameterUnitaryGroup H`: a strongly continuous one-parameter group of unitary
  operators on a complex Hilbert space `H`, bundled as `toFun : ℝ → unitary (H →L[ℂ] H)`
  with the group law and strong continuity, plus a `FunLike` coercion and basic API
  (`map_zero_eq_one`, `map_add_eq_mul`, `map_neg_eq_inv`, `continuous_apply`).
* `OneParameterUnitaryGroup.generator`: the Stone generator of such a group, as an
  unbounded operator `H →ₗ.[ℂ] H` (a `LinearPMap`) with domain the set of vectors `x`
  where `t ↦ U t x` is differentiable at `0`, and value `A x = -I • (d/dt)|₀ (U t x)`.
* Prop-valued target statements for Stone's theorem (blueprint nodes P2.3h/P2.3i):
  `StoneTheoremForward`, `StoneTheoremConverse`, `StoneTheoremUniqueness`.

## Conventions

* **Sign of the generator (physicists' convention).** We follow Reed & Simon and the
  quantum-mechanics literature: a self-adjoint `A` generates `U t = exp(I * t • A)`, so
  that `(d/dt)|₀ (U t x) = I • A x` and the generator is recovered as
  `A x = -I • (d/dt)|₀ (U t x)` (Reed & Simon I, §VIII.4, Thm VIII.7). The *generator* of
  `U` is the (target: self-adjoint) operator `A` itself, **not** the skew-adjoint
  derivative `I • A`; beware that Weidmann, *Linear Operators in Hilbert Spaces*,
  §7.6, calls the skew-adjoint derivative (his `iT`, our `I • A`) the "infinitesimal
  generator". The pinning lemma `hasDerivAt_of_mem_generatorDomain` fixes this
  convention formally: for `x` in the domain, `t ↦ U t x` has derivative
  `I • U.generator x` at `0`.
* **Strong continuity** is stated as the sources state it: `t ↦ U t x` is continuous
  on all of `ℝ` for every `x : H` (Reed & Simon I, §VIII.4; Rudin, *Functional
  Analysis*, 2nd ed., ch. 13). That continuity at a single point plus the group law
  suffices is a theorem (hence a future smart constructor on a proof node), not part
  of the definition.
* **The generator's domain and value use `deriv`, not `Classical.choose`.** The domain
  is carved out by `∃ y, HasDerivAt (fun t ↦ U t x) y 0`; on it the value is
  `-I • deriv (fun t ↦ U t x) 0`. Since `deriv` agrees with any `HasDerivAt` witness
  (`HasDerivAt.deriv`) exactly on the domain, this is equal to the
  `Classical.choose` spelling but rewrites cleanly (`generator_apply_of_hasDerivAt`
  is proved by `HasDerivAt.deriv`, no choice-specification lemmas needed). Off the
  domain, `deriv` takes junk value `0`, which the `LinearPMap` never evaluates.
* **Bundling.** `OneParameterUnitaryGroup` is a standalone structure with a `FunLike`
  instance into `unitary (H →L[ℂ] H)`, following the bundled-hom design of
  `AddChar A M` (which is exactly the algebraic part of this structure: field names
  `map_zero_eq_one'`/`map_add_eq_mul'` match it). We do not `extend AddChar` — the
  extended structure would need its own `FunLike` anyway, so `AddChar`'s lemmas would
  not apply to the coercion without restatement, and none of its multiplicative-
  character API is relevant here. Application to vectors is written
  `(U t : H →L[ℂ] H) x`, the same spelling as Mathlib's `Unitary.norm_map`; the
  coercion chain is `FunLike` then the `Submonoid` subtype coercion.
* **Namespace.** Declarations live in `OperatorTheory`, parallel to the `Spacetime`
  namespace of the P1 specs; on upstreaming to Mathlib they would be de-namespaced
  (Mathlib keeps e.g. `LinearPMap` at root level).

## Target statements (not theorems here)

The Stone halves are recorded as `Prop`-valued definitions, to be proved on blueprint
nodes P2.3h (forward) and P2.3i (converse + uniqueness); a stuck proof node must be
decomposed, never allowed to weaken these statements. The bijection
`stoneEquiv : {A : H →ₗ.[ℂ] H // IsSelfAdjoint A} ≃ OneParameterUnitaryGroup H` is
*data* whose construction requires those proofs, so it is deferred to node P2.3i and
not stated here.

Note that `IsSelfAdjoint` for `LinearPMap`s (star = `LinearPMap.adjoint`,
`Mathlib.Analysis.InnerProductSpace.LinearPMap`) already forces a dense domain
(`IsSelfAdjoint.dense_domain`), so `StoneTheoremForward` correctly asserts, as part of
Stone's theorem, that the differentiability domain is dense — no separate density
clause is needed.

## Sources

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics. I: Functional Analysis*,
  revised and enlarged edition (1980), §VIII.4: Thm VIII.7 (`exp(I * t • A)` is a
  strongly continuous one-parameter unitary group with generator `A`), Thm VIII.8
  (Stone's theorem).
* M. H. Stone, "On one-parameter unitary groups in Hilbert space", *Ann. of Math.* 33
  (1932), 643–648.
* W. Rudin, *Functional Analysis*, 2nd ed. (1991), ch. 13, Thm 13.38 (Stone, in
  semigroup form; unbounded operators;
  semigroups of operators and Stone's theorem).
* J. Weidmann, *Linear Operators in Hilbert Spaces*, GTM 68 (1980), §7.6,
  Thm 7.38 (Stone's theorem; note his opposite "infinitesimal generator" convention,
  see above).
-/

namespace OperatorTheory

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space `H`:
a homomorphism `t ↦ U t` from `(ℝ, +)` to the unitary group of `H →L[ℂ] H` such that
`t ↦ U t x` is norm-continuous for every `x : H`.

This is the classical notion of Stone's theorem: Reed & Simon I, §VIII.4;
Stone (1932); Rudin, *Functional Analysis*, 2nd ed., ch. 13; Weidmann, *Linear
Operators in Hilbert Spaces*, §7.6. Strong continuity is stated on all of `ℝ`, as in
the sources; continuity at `0` (or even weak measurability, von Neumann) suffices,
but that is a theorem about this definition, not part of it.

Elements apply to vectors as `(U t : H →L[ℂ] H) x` (cf. `Unitary.norm_map`,
`Unitary.inner_map_map` for unitarity consequences: each `U t` is an isometry
preserving the inner product). -/
structure OneParameterUnitaryGroup (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The underlying family of unitary operators. Do not use this field directly;
  use the coercion coming from the `FunLike` instance. -/
  toFun : ℝ → unitary (H →L[ℂ] H)
  /-- The group sends `0` to the identity. Do not use this field directly; use
  `OneParameterUnitaryGroup.map_zero_eq_one`. -/
  map_zero_eq_one' : toFun 0 = 1
  /-- The group law `U (s + t) = U s * U t`. Do not use this field directly; use
  `OneParameterUnitaryGroup.map_add_eq_mul`. -/
  map_add_eq_mul' : ∀ s t : ℝ, toFun (s + t) = toFun s * toFun t
  /-- Strong continuity: every orbit map `t ↦ U t x` is continuous. Do not use this
  field directly; use `OneParameterUnitaryGroup.continuous_apply`. -/
  continuous_apply' : ∀ x : H, Continuous fun t : ℝ ↦ (toFun t : H →L[ℂ] H) x

namespace OneParameterUnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance : FunLike (OneParameterUnitaryGroup H) ℝ (unitary (H →L[ℂ] H)) where
  coe := toFun
  coe_injective U V h := by cases U; cases V; congr

@[ext]
theorem ext {U V : OneParameterUnitaryGroup H} (h : ∀ t, U t = V t) : U = V :=
  DFunLike.ext U V h

@[simp]
theorem coe_mk (f : ℝ → unitary (H →L[ℂ] H)) (h0 : f 0 = 1)
    (hadd : ∀ s t : ℝ, f (s + t) = f s * f t)
    (hcont : ∀ x : H, Continuous fun t : ℝ ↦ (f t : H →L[ℂ] H) x) :
    ⇑(mk f h0 hadd hcont) = f :=
  rfl

variable (U : OneParameterUnitaryGroup H)

/-- A one-parameter unitary group sends `0` to the identity (Reed & Simon I, §VIII.4). -/
@[simp]
theorem map_zero_eq_one : U 0 = 1 :=
  U.map_zero_eq_one'

/-- The group law of a one-parameter unitary group (Reed & Simon I, §VIII.4). -/
theorem map_add_eq_mul (s t : ℝ) : U (s + t) = U s * U t :=
  U.map_add_eq_mul' s t

/-- Strong continuity of a one-parameter unitary group: every orbit map `t ↦ U t x`
is continuous (Reed & Simon I, §VIII.4). -/
theorem continuous_apply (x : H) : Continuous fun t : ℝ ↦ (U t : H →L[ℂ] H) x :=
  U.continuous_apply' x

/-- `U (-t)` is the inverse (= adjoint) of `U t`: the group-law consequence pinning
down that `t ↦ U t` is a group homomorphism into the unitary group, not just a
monoid map (Reed & Simon I, §VIII.4; Stone (1932)). -/
theorem map_neg_eq_inv (t : ℝ) : U (-t) = (U t)⁻¹ :=
  eq_inv_of_mul_eq_one_right <| by
    rw [← map_add_eq_mul, add_neg_cancel, map_zero_eq_one]

/-- The domain of the Stone generator of `U`: the set of vectors `x : H` whose orbit
map `t ↦ U t x` is differentiable at `0`. It is a `ℂ`-submodule because
differentiation is linear. Reed & Simon I, §VIII.4 (D(A) in the proof of
Thm VIII.7/VIII.8); Rudin, *Functional Analysis*, 2nd ed., ch. 13.

This definition is needed to construct `OneParameterUnitaryGroup.generator`; the
membership condition is exposed by `mem_generatorDomain` (cf.
`LinearPMap.adjointDomain`). Whether
the derivative is taken at `0` or at any other time is immaterial by the group law
(a future lemma, not part of the spec). -/
def generatorDomain : Submodule ℂ H where
  carrier := {x | ∃ y, HasDerivAt (fun t : ℝ ↦ (U t : H →L[ℂ] H) x) y 0}
  zero_mem' := ⟨0, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
  add_mem' := by
    rintro x y ⟨dx, hdx⟩ ⟨dy, hdy⟩
    exact ⟨dx + dy, by simpa using hdx.fun_add hdy⟩
  smul_mem' := by
    rintro c x ⟨dx, hdx⟩
    exact ⟨c • dx, by simpa using hdx.fun_const_smul c⟩

theorem mem_generatorDomain {U : OneParameterUnitaryGroup H} {x : H} :
    x ∈ U.generatorDomain ↔
      ∃ y, HasDerivAt (fun t : ℝ ↦ (U t : H →L[ℂ] H) x) y 0 :=
  Iff.rfl

/-- The Stone generator of a one-parameter unitary group `U`, as an unbounded operator
(`LinearPMap`): the operator `A` with domain `{x | t ↦ U t x is differentiable at 0}`
and value `A x = -I • (d/dt)|₀ (U t x)`.

Sign convention (physicists', as in Reed & Simon): `A` is normalized so that
`U t = exp(I * t • A)`, i.e. `(d/dt)|₀ (U t x) = I • A x`
(see `hasDerivAt_of_mem_generatorDomain`), and Stone's theorem asserts `A` is
*self-adjoint* — not the skew-adjoint derivative `I • A`, which Weidmann calls the
"infinitesimal generator" (see the module docstring on conventions).

Authoritative sources: Reed & Simon I, §VIII.4, Thms VIII.7–VIII.8 (there
`A x = lim_{t → 0} (U t x - x) / (I * t)` on the set where the limit exists — the
same domain and value as here, since strong differentiability at `0` *is* the
existence of that limit); Stone (1932); Weidmann, Thm 7.38 (up to the factor `I`);
Rudin, *Functional Analysis*, 2nd ed., ch. 13.

The value is spelled with `deriv`; on the domain it agrees with every `HasDerivAt`
witness — use `generator_apply_of_hasDerivAt`. -/
noncomputable def generator : H →ₗ.[ℂ] H where
  domain := U.generatorDomain
  toFun :=
    { toFun := fun x ↦ -Complex.I • deriv (fun t : ℝ ↦ (U t : H →L[ℂ] H) (x : H)) 0
      map_add' := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩
        obtain ⟨dx, hdx⟩ := hx
        obtain ⟨dy, hdy⟩ := hy
        have hxy : HasDerivAt (fun t : ℝ ↦ (U t : H →L[ℂ] H) (x + y)) (dx + dy) 0 := by
          simpa using hdx.fun_add hdy
        simp only [Submodule.coe_add, hxy.deriv, hdx.deriv, hdy.deriv, smul_add]
      map_smul' := by
        rintro c ⟨x, hx⟩
        obtain ⟨dx, hdx⟩ := hx
        have hcx : HasDerivAt (fun t : ℝ ↦ (U t : H →L[ℂ] H) (c • x)) (c • dx) 0 := by
          simpa using hdx.fun_const_smul c
        simp only [Submodule.coe_smul, RingHom.id_apply, hcx.deriv, hdx.deriv]
        rw [smul_comm] }

@[simp]
theorem generator_domain : U.generator.domain = U.generatorDomain :=
  rfl

theorem generator_apply (x : U.generator.domain) :
    U.generator x = -Complex.I • deriv (fun t : ℝ ↦ (U t : H →L[ℂ] H) (x : H)) 0 :=
  rfl

/-- The generator evaluated through a `HasDerivAt` witness: if `t ↦ U t x` has
derivative `y` at `0`, then `x` is in the domain and `A x = -I • y`. This is the
computation rule to use downstream (it hides the `deriv` spelling of
`OneParameterUnitaryGroup.generator`). -/
theorem generator_apply_of_hasDerivAt {x y : H}
    (h : HasDerivAt (fun t : ℝ ↦ (U t : H →L[ℂ] H) x) y 0) :
    U.generator ⟨x, mem_generatorDomain.mpr ⟨y, h⟩⟩ = -Complex.I • y := by
  rw [generator_apply]
  simp [h.deriv]

/-- Round-trip pinning the sign convention: for `x` in the generator's domain, the
orbit map `t ↦ U t x` has derivative `I • A x` at `0` — the differential form of
`U t = exp(I * t • A)` (Reed & Simon I, §VIII.4, Thm VIII.7(c)). -/
theorem hasDerivAt_of_mem_generatorDomain {x : H} (hx : x ∈ U.generatorDomain) :
    HasDerivAt (fun t : ℝ ↦ (U t : H →L[ℂ] H) x)
      (Complex.I • U.generator ⟨x, hx⟩) 0 := by
  obtain ⟨y, hy⟩ := id hx
  have h : U.generator ⟨x, hx⟩ = -Complex.I • y := U.generator_apply_of_hasDerivAt hy
  rw [h, smul_smul]
  simpa [Complex.I_mul_I] using hy

end OneParameterUnitaryGroup

/-- **Target statement — Stone's theorem, forward half** (blueprint node P2.3h): the
generator of every strongly continuous one-parameter unitary group on `H` is
self-adjoint. `IsSelfAdjoint` here is `LinearPMap.adjoint`-self-adjointness
(`Mathlib.Analysis.InnerProductSpace.LinearPMap`); it subsumes density of the
domain (`IsSelfAdjoint.dense_domain`), so this single clause carries the full
content of the forward half.

Reed & Simon I, §VIII.4, Thm VIII.8; Stone (1932); Weidmann, Thm 7.38; Rudin,
*Functional Analysis*, 2nd ed., ch. 13. Stated as a `Prop`-valued definition: the
proof is node P2.3h, and per project rules a stuck proof decomposes into lemmas —
it never weakens this statement. -/
def StoneTheoremForward (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop :=
  ∀ U : OneParameterUnitaryGroup H, IsSelfAdjoint U.generator

/-- **Target statement — Stone's theorem, converse half** (blueprint node P2.3i,
existence part): every self-adjoint operator `A` on `H` is the generator of some
strongly continuous one-parameter unitary group (classically written
`U t = exp(I * t • A)`, constructed via the spectral theorem — nodes P2.3c/P2.3f).

Reed & Simon I, §VIII.4, Thm VIII.7; Stone (1932). Stated as a `Prop`-valued
definition; see `StoneTheoremForward` for the statement discipline. -/
def StoneTheoremConverse (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop :=
  ∀ A : H →ₗ.[ℂ] H, IsSelfAdjoint A → ∃ U : OneParameterUnitaryGroup H, U.generator = A

/-- **Target statement — Stone's theorem, uniqueness half** (blueprint node P2.3i,
injectivity part): a strongly continuous one-parameter unitary group is determined by
its generator. Together with `StoneTheoremForward` and `StoneTheoremConverse` this
yields the bijection `{A // IsSelfAdjoint A} ≃ OneParameterUnitaryGroup H`
(`stoneEquiv`, deferred to node P2.3i since constructing it *is* proving these
statements).

Reed & Simon I, §VIII.4, Thms VIII.7–VIII.8 (uniqueness of the solution of
`(d/dt) u = I • A u`); Weidmann, Thm 7.38. -/
def StoneTheoremUniqueness (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop :=
  Function.Injective (OneParameterUnitaryGroup.generator (H := H))

end OperatorTheory
