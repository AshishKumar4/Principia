import Atlas.Specs.Spacetime.Poincare

/-!
# P2.4a adversarial kernel probes — mass shells and the Poincaré group law

* `massShell`: positive-energy membership/refutations on concrete momenta, and the
  `m = 0` "punctured forward light cone" claim probed at its edge cases (`0 ∉`,
  past-null `∉`, future-null `∈`).
* `PoincareGroup`: the S&W composition law and the affine action, kernel-checked as
  definitional facts and as the generic expansion `(g₁g₂) • x = Λ₁(Λ₂x + a₂) + a₁`
  (the direction in which semidirect conventions break).

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.4a/` only.
-/

open Spacetime.Minkowski

/-! ## Mass shells -/

-- `∂₀ ∈ massShell 1`: `η(e₀, e₀) = -1`, positive energy.
theorem probe_e0_massShell_one : (EuclideanSpace.single 0 1 : M4) ∈ massShell 1 := by
  refine ⟨?_, by simp⟩
  rw [minkowskiForm_eq]
  norm_num [Fin.ext_iff, show ((2 : Fin 4) = 0) = False from by decide,
    show ((3 : Fin 4) = 0) = False from by decide]

-- Future-null momentum is on the `m = 0` shell.
theorem probe_null_massShell_zero :
    (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 : M4) ∈ massShell 0 := by
  refine ⟨?_, by simp⟩
  rw [minkowskiForm_eq]
  norm_num [Fin.ext_iff, show ((2 : Fin 4) = 0) = False from by decide,
    show ((3 : Fin 4) = 0) = False from by decide,
    show ((2 : Fin 4) = 1) = False from by decide,
    show ((3 : Fin 4) = 1) = False from by decide]

-- The `m = 0` shell is PUNCTURED: the origin is excluded (by the energy condition).
theorem probe_zero_not_massShell_zero : (0 : M4) ∉ massShell 0 := fun h => by
  have := h.2; simp at this

-- Positive energy: the past-pointing partner is excluded.
theorem probe_past_not_massShell_one :
    (-(EuclideanSpace.single 0 1) : M4) ∉ massShell 1 := fun h => by
  have := h.2
  simp at this
  exact absurd this (by norm_num)

-- A spacelike momentum is on NO mass shell.
theorem probe_e1_not_massShell (m : ℝ) :
    (EuclideanSpace.single 1 1 : M4) ∉ massShell m := fun h => by
  have hf := h.1
  rw [minkowskiForm_eq] at hf
  norm_num [Fin.ext_iff, show ((2 : Fin 4) = 1) = False from by decide,
    show ((3 : Fin 4) = 1) = False from by decide] at hf
  nlinarith [sq_nonneg m]

/-! ## Poincaré group law and action: the S&W conventions, kernel-checked -/

-- Composition is `(a₁, Λ₁)(a₂, Λ₂) = (a₁ + Λ₁ a₂, Λ₁Λ₂)` — S&W §1-1 / Weinberg
-- (2.3.11) — definitionally.
theorem probe_mul_convention (g₁ g₂ : PoincareGroup) :
    (g₁ * g₂).translation
        = g₁.translation + (g₁.lorentz : M4 ≃L[ℝ] M4) g₂.translation
      ∧ (g₁ * g₂).lorentz = g₁.lorentz * g₂.lorentz :=
  ⟨rfl, rfl⟩

-- The action is `(a, Λ) • x = Λx + a` — definitionally.
theorem probe_smul_convention (g : PoincareGroup) (x : M4) :
    g • x = (g.lorentz : M4 ≃L[ℝ] M4) x + g.translation := rfl

-- The homomorphism expansion `(g₁g₂) • x = Λ₁(Λ₂ x + a₂) + a₁`: this equality is
-- exactly where a wrong semidirect twist (e.g. `a₂ + Λ₂ a₁`) fails; it follows from
-- the proven `MulAction` instance.
theorem probe_action_homomorphism (g₁ g₂ : PoincareGroup) (x : M4) :
    (g₁ * g₂) • x
      = (g₁.lorentz : M4 ≃L[ℝ] M4)
          ((g₂.lorentz : M4 ≃L[ℝ] M4) x + g₂.translation) + g₁.translation := by
  rw [mul_smul, PoincareGroup.smul_def, PoincareGroup.smul_def, map_add]

-- Inverse convention on the translation part, plus `g⁻¹ • (g • x) = x` from the
-- `MulAction`.
theorem probe_inv_smul (g : PoincareGroup) (x : M4) : g⁻¹ • g • x = x :=
  inv_smul_smul g x

-- Concrete translations (`Λ = 1`) compose additively and act by translation.
example :
    ((⟨EuclideanSpace.single 1 1, 1⟩ : PoincareGroup)
        * ⟨EuclideanSpace.single 2 1, 1⟩) • (0 : M4)
      = EuclideanSpace.single 1 1 + EuclideanSpace.single 2 1 := by
  rw [probe_action_homomorphism]
  have h1 : ∀ x : M4, ((1 : RestrictedLorentzGroup) : M4 ≃L[ℝ] M4) x = x := fun _ => rfl
  rw [h1, h1]
  abel
