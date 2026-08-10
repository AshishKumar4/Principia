import Atlas.Specs.Spacetime.PoincareRep

/-!
# P2.4b adversarial kernel probes — `MonoidHom` consequences and the coercion chain

* `probe_inv_eq_star` / `probe_coe_inv_eq_star` — **adjointness of the inverse is
  reachable**: `U g⁻¹ = star (U g)` both inside the unitary group and after coercion
  to `H →L[ℂ] H` (where `star` is the operator adjoint), via Mathlib's generic
  `map_inv` + `Unitary.star_eq_inv`. This is the S&W `U(g)⁻¹ = U(g)*` content the
  spec deliberately does not restate as a field.
* `probe_norm_map` / `probe_inner_map_map` — unitarity consequences engage on the
  coerced operator (`unitary.norm_map`-style facts the spec docstring advertises).
* Coercion-chain `rfl` probes — `⇑U`, `⇑U.toFun`, the `MonoidHomClass` coe and the
  raw field all agree definitionally: no diamond between the `FunLike` instance,
  the `MonoidHomClass` instance, and the `mk`/`toFun` surface.
* `probe_ext` — extensionality through `DFunLike` works on the frozen structure.

Compiler note (recorded as review evidence): the `noncomputable` on the spec's
`FunLike` instance is *required*, not cosmetic — an identical non-`noncomputable`
definition is rejected because the coercion's type depends on
`ContinuousLinearMap.instStarMulId`, which is noncomputable. This has no kernel
significance (noncomputability never weakens a proof); it only blocks code
generation.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.4b/` only; compiles via
`lake env lean audits/probes/P2.4b/api_coercion_probe.lean`.
-/

open Spacetime.Minkowski

namespace P24bProbe

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Adjointness of the inverse -/

/-- `U g⁻¹ = star (U g)` inside the unitary group: `map_inv` composed with
`Unitary.star_eq_inv`. The group-valued codomain really does carry the adjoint. -/
theorem probe_inv_eq_star (U : PoincareRep H) (g : PoincareGroup) :
    U g⁻¹ = star (U g) := by
  rw [map_inv, Unitary.star_eq_inv]

/-- The same fact after coercion to `H →L[ℂ] H`: the inverse element acts by the
operator adjoint of `U g`. -/
theorem probe_coe_inv_eq_star (U : PoincareRep H) (g : PoincareGroup) :
    ((U g⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
      = star ((U g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
  rw [probe_inv_eq_star, Unitary.coe_star]

/-- Unitarity consequence advertised by the docstring: each `U g` is isometric. -/
theorem probe_norm_map (U : PoincareRep H) (g : PoincareGroup) (x : H) :
    ‖((U g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x‖ = ‖x‖ :=
  Unitary.norm_map (U g) x

/-- Unitarity consequence advertised by the docstring: each `U g` preserves the
inner product. -/
theorem probe_inner_map_map (U : PoincareRep H) (g : PoincareGroup) (x y : H) :
    inner ℂ (((U g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x)
        (((U g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) y)
      = inner ℂ x y :=
  Unitary.inner_map_map (U g) x y

/-! ## Coercion chain: no diamonds -/

example (U : PoincareRep H) (g : PoincareGroup) : U g = U.toFun g := rfl

example (U : PoincareRep H) :
    (DFunLike.coe U : PoincareGroup → unitary (H →L[ℂ] H)) = ⇑U.toFun := rfl

example (f : PoincareGroup →* unitary (H →L[ℂ] H))
    (hf : Continuous fun p : PoincareGroup × H => (f p.1 : H →L[ℂ] H) p.2)
    (g : PoincareGroup) : PoincareRep.mk f hf g = f g := rfl

/-- The generic `MonoidHomClass` coe and the `FunLike` coe agree (single instance
path; a diamond here would make this fail to elaborate as `rfl`). -/
example (U : PoincareRep H) (g : PoincareGroup) :
    (U : PoincareRep H) g * (U g)⁻¹ = 1 := mul_inv_cancel _

example (U : PoincareRep H) : U 1 = 1 := map_one U

/-! ## Extensionality -/

theorem probe_ext (U V : PoincareRep H) (h : ∀ g, U g = V g) : U = V :=
  PoincareRep.ext h

example (U V : PoincareRep H) (h : ⇑U = ⇑V) : U = V :=
  PoincareRep.ext fun g => congrFun h g

end P24bProbe
