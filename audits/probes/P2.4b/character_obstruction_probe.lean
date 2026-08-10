import Atlas.Specs.Spacetime.PoincareRep
import Atlas.Witnesses.Poincare

/-!
# P2.4b adversarial kernel probes — the `MonoidHom` field has teeth

The review task suggested probing the "scalar character" `g ↦ e^{i⟨a,k⟩} · 1` (for
fixed `k ≠ 0`) as a cheap nontrivial satisfiability witness for `PoincareRep`.
**That candidate does not exist**: on the semidirect product, `U(g₁g₂) = U(g₁)U(g₂)`
forces `⟨Λa, k⟩ ≡ ⟨a, k⟩ (mod 2π)` for all `Λ ∈ L↑₊`, and by linearity/continuity in
`a` this is exact invariance `⟨Λa, k⟩ = ⟨a, k⟩` — but `L↑₊` fixes no nonzero
functional on `M4`, so `k = 0` and the character collapses to the trivial
representation. (One-dimensional unitary representations of `P↑₊` are trivial;
nontrivial strongly continuous unitary representations are necessarily
infinite-dimensional — Wigner 1939.)

These probes kernel-verify the obstruction at concrete elements, certifying that the
frozen `MonoidHom` field genuinely constrains `toFun` against the frozen P2.4a
semidirect group law (i.e. the field is not satisfied by translation-only
"characters", and the in-spec trivial example is the ONLY cheap model — the
nontrivial-witness obligation on the witness node is real):

* `probe_translation_functional_not_additive` — the coordinate functional
  `g ↦ (g.translation)¹` fails additivity on `P↑₊` (rotation `diag(1,-1,-1,1)`
  conjugated against a spatial translation), i.e. the naive character's exponent is
  not a homomorphism to `(ℝ, +)`;
* `probe_no_character_monoidHom` — no `MonoidHom` into `unitary (ℂ →L[ℂ] ℂ)` has the
  character form `g ↦ e^{i·(g.translation)¹} • 1`: the group law fails at the same
  concrete pair, in the kernel, through `Complex.exp` periodicity (`2 ∉ 2πℤ`).

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.4b/` only; compiles via
`lake env lean audits/probes/P2.4b/character_obstruction_probe.lean`.
-/

open Spacetime.Minkowski Complex

namespace P24bProbe

/-- The spatial basis vector `e₁`, the translation direction of the probe. -/
noncomputable def e1 : M4 := EuclideanSpace.single 1 1

/-- The concrete pair breaking additivity: `g₁ = ⟨0, diag(1,-1,-1,1)⟩`,
`g₂ = ⟨e₁, 1⟩`; then `(g₁ g₂).translation¹ = -1 ≠ 1 = g₁.translation¹ +
g₂.translation¹`. The exponent of the naive character is not additive on `P↑₊`. -/
theorem probe_translation_functional_not_additive :
    ∃ g₁ g₂ : PoincareGroup,
      (g₁ * g₂).translation 1 ≠ g₁.translation 1 + g₂.translation 1 := by
  refine ⟨⟨0, RestrictedLorentzGroup.rotation12⟩, ⟨e1, 1⟩, ?_⟩
  have hL : ((⟨0, RestrictedLorentzGroup.rotation12⟩ * ⟨e1, 1⟩ :
      PoincareGroup)).translation 1 = -1 := by
    rw [PoincareGroup.mul_translation]
    simp [RestrictedLorentzGroup.coe_rotation12, rotation12Equiv_apply_one, e1]
  rw [hL]
  simp [e1]
  norm_num

/-- **The character candidate is not a monoid homomorphism**: there is no
`f : PoincareGroup →* unitary (ℂ →L[ℂ] ℂ)` with `f g = e^{i·(g.translation)¹} • 1`.
Kernel-checked at the concrete pair of `probe_translation_functional_not_additive`,
via `Complex.exp` periodicity: the defect is `e^{-i} ≠ e^{i}`, i.e. `2 ∉ 2πℤ`. -/
theorem probe_no_character_monoidHom :
    ¬ ∃ f : PoincareGroup →* unitary (ℂ →L[ℂ] ℂ),
        ∀ g : PoincareGroup,
          ((f g : unitary (ℂ →L[ℂ] ℂ)) : ℂ →L[ℂ] ℂ)
            = Complex.exp (Complex.I * (g.translation 1 : ℝ)) • (1 : ℂ →L[ℂ] ℂ) := by
  rintro ⟨f, hf⟩
  set g₁ : PoincareGroup := ⟨0, RestrictedLorentzGroup.rotation12⟩ with hg₁
  set g₂ : PoincareGroup := ⟨e1, 1⟩ with hg₂
  have hL : (g₁ * g₂).translation 1 = -1 := by
    rw [hg₁, hg₂, PoincareGroup.mul_translation]
    simp [RestrictedLorentzGroup.coe_rotation12, rotation12Equiv_apply_one, e1]
  have h₁ : g₁.translation 1 = 0 := by simp [hg₁]
  have h₂ : g₂.translation 1 = 1 := by simp [hg₂, e1]
  have happ := congrArg (fun u : unitary (ℂ →L[ℂ] ℂ) => (u : ℂ →L[ℂ] ℂ) 1)
    (f.map_mul g₁ g₂)
  simp only [MulMemClass.coe_mul, mul_apply_eq_comp, hf,
    FunLike.coe_smul, Pi.smul_apply, one_apply_eq_self, smul_eq_mul,
    mul_one, hL, h₁, h₂] at happ
  -- happ : exp (I * -1) = exp (I * 0) * exp (I * 1)
  have hexp : Complex.exp (-Complex.I) = Complex.exp Complex.I := by
    have := happ
    push_cast at this
    simpa [mul_comm, Complex.exp_zero] using this
  rw [Complex.exp_eq_exp_iff_exists_int] at hexp
  obtain ⟨n, hn⟩ := hexp
  -- hn : -I = I + n * (2 * π * I); imaginary parts: -1 = 1 + n * 2π
  have him := congrArg Complex.im hn
  simp [Complex.mul_im, Complex.mul_re] at him
  -- him : -1 = 1 + n * (2 * π)  (up to arrangement)
  have hπ := Real.two_le_pi
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · have hcast : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    nlinarith
  · subst hn0
    norm_num at him
  · have hcast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
    nlinarith

end P24bProbe
