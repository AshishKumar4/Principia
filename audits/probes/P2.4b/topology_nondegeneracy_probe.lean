import Atlas.Specs.Spacetime.PoincareRep

/-!
# P2.4b adversarial kernel probes — non-degeneracy of the `PoincareGroup` topology

The joint-continuity field of `PoincareRep` is stated against the frozen P2.4a
topology on `PoincareGroup` (induced along `g ↦ (g.translation, g.lorentz)` from
`M4 × RestrictedLorentzGroup`, the latter induced from the operator norm). These
probes exclude the degenerate readings under which that field would be trivialized:

* **discrete reading** (every map out of `PoincareGroup` continuous — joint continuity
  would then be free for ANY family of unitaries): refuted by
  `probe_singleton_one_not_isOpen` and, explicitly, `probe_exists_discontinuous`,
  which exhibits a function `PoincareGroup → ℝ` that is NOT continuous;
* **degenerate/indiscrete reading** (continuity constraints collapse): refuted by
  `probe_t2` — the topology is Hausdorff — and `probe_exists_nontrivial_open`;
* the topology is pinned as THE transported product topology:
  `probe_isEmbedding` (the component map is a topological embedding), so the
  "product topology" wording of the spec/dossier is mechanically faithful.

`probe_translationLine_continuous` + `probe_line_injective` +
`probe_singleton_one_not_isOpen` together show a genuine nontrivial convergence:
the translation line `t ↦ ⟨t • e₀, 1⟩` converges to `1` without being eventually
constant, so the joint-continuity field genuinely constrains every `PoincareRep`
along translation directions (this is exactly what the Stone-bridge anchor consumes).

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.4b/` only; compiles via
`lake env lean audits/probes/P2.4b/topology_nondegeneracy_probe.lean`.
-/

open Spacetime.Minkowski Topology

namespace P24bProbe

/-! ## The topology is the transported product topology (an embedding, hence T2) -/

theorem probe_lorentz_isInducing :
    IsInducing (fun Λ : RestrictedLorentzGroup => ((Λ : M4 ≃L[ℝ] M4) : M4 →L[ℝ] M4)) :=
  ⟨rfl⟩

theorem probe_lorentz_injective :
    Function.Injective
      (fun Λ : RestrictedLorentzGroup => ((Λ : M4 ≃L[ℝ] M4) : M4 →L[ℝ] M4)) :=
  ContinuousLinearEquiv.coe_injective.comp Subtype.coe_injective

theorem probe_lorentz_isEmbedding :
    IsEmbedding (fun Λ : RestrictedLorentzGroup => ((Λ : M4 ≃L[ℝ] M4) : M4 →L[ℝ] M4)) :=
  ⟨probe_lorentz_isInducing, probe_lorentz_injective⟩

theorem probe_isInducing :
    IsInducing (fun g : PoincareGroup => (g.translation, g.lorentz)) :=
  ⟨rfl⟩

theorem probe_component_injective :
    Function.Injective (fun g : PoincareGroup => (g.translation, g.lorentz)) := by
  rintro ⟨a, Λ⟩ ⟨b, M⟩ h
  obtain ⟨h₁, h₂⟩ := Prod.mk.injEq .. ▸ h
  exact PoincareGroup.ext h₁ h₂

theorem probe_isEmbedding :
    IsEmbedding (fun g : PoincareGroup => (g.translation, g.lorentz)) :=
  ⟨probe_isInducing, probe_component_injective⟩

/-- `RestrictedLorentzGroup` is Hausdorff (embeds in the operator-norm space). -/
theorem probe_lorentz_t2 : T2Space RestrictedLorentzGroup :=
  probe_lorentz_isEmbedding.t2Space

/-- `PoincareGroup` is Hausdorff: the topology is genuinely separating, not
degenerate. -/
theorem probe_t2 : T2Space PoincareGroup :=
  haveI := probe_lorentz_t2
  probe_isEmbedding.t2Space

/-! ## The topology is not discrete: the translation line converges nontrivially -/

/-- The future time basis vector, as a nonzero direction for the translation line. -/
noncomputable def e0 : M4 := EuclideanSpace.single 0 1

/-- The translation line `t ↦ ⟨t • e₀, 1⟩` is continuous (the same argument the
frozen anchor `PoincareRep.translationGroup` uses). -/
theorem probe_translationLine_continuous :
    Continuous fun t : ℝ => (⟨t • e0, 1⟩ : PoincareGroup) :=
  continuous_induced_rng.2
    ((continuous_id.smul continuous_const).prodMk continuous_const)

theorem probe_line_injective :
    Function.Injective fun t : ℝ => (⟨t • e0, 1⟩ : PoincareGroup) := by
  intro s t h
  have h0 := congrArg (fun g : PoincareGroup => g.translation 0) h
  simpa [e0, PiLp.single_apply] using h0

/-- The singleton `{1}` is NOT open: the frozen topology is not discrete, so the
joint-continuity field of `PoincareRep` is a genuine constraint in the group
variable (under the discrete topology every `toFun` continuous in `x` alone would
satisfy it vacuously). -/
theorem probe_singleton_one_not_isOpen : ¬ IsOpen ({1} : Set PoincareGroup) := by
  intro hopen
  have hpre : (fun t : ℝ => (⟨t • e0, 1⟩ : PoincareGroup)) ⁻¹' {1} = {0} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro ht
      have h1 : (⟨(0 : ℝ) • e0, 1⟩ : PoincareGroup) = 1 :=
        PoincareGroup.ext (by simp) rfl
      exact probe_line_injective (ht.trans h1.symm)
    · rintro rfl
      exact PoincareGroup.ext (by simp) rfl
  have h0open : IsOpen ({0} : Set ℝ) :=
    hpre ▸ hopen.preimage probe_translationLine_continuous
  rw [isOpen_singleton_iff_punctured_nhds] at h0open
  exact absurd h0open (Filter.NeBot.ne inferInstance)

/-- Explicit refutation of the "every map is continuous" reading: the indicator of
`{1}` is a function `PoincareGroup → ℝ` that fails continuity. Joint continuity in
the spec is therefore never satisfiable "for free" in the group variable. -/
theorem probe_exists_discontinuous :
    ∃ f : PoincareGroup → ℝ, ¬ Continuous f := by
  classical
  refine ⟨fun g => if g = 1 then 1 else 0, fun hcont => ?_⟩
  have hpre :
      (fun g : PoincareGroup => if g = 1 then (1 : ℝ) else 0) ⁻¹' Set.Ioi (1 / 2)
        = {1} := by
    ext g
    by_cases hg : g = 1 <;> norm_num [hg]
  exact probe_singleton_one_not_isOpen (hpre ▸ isOpen_Ioi.preimage hcont)

/-! ## The topology is not indiscrete: nontrivial opens exist -/

theorem probe_translation_continuous :
    Continuous fun g : PoincareGroup => g.translation :=
  continuous_fst.comp probe_isInducing.continuous

theorem probe_lorentz_component_continuous :
    Continuous fun g : PoincareGroup => g.lorentz :=
  continuous_snd.comp probe_isInducing.continuous

/-- A nontrivial open set (a translation-norm ball): the topology is not indiscrete —
continuity of orbit maps has actual content in every neighborhood of `1`. -/
theorem probe_exists_nontrivial_open :
    ∃ s : Set PoincareGroup, IsOpen s ∧ (1 : PoincareGroup) ∈ s ∧ s ≠ Set.univ := by
  refine ⟨{g : PoincareGroup | ‖g.translation‖ < 1},
    isOpen_lt (continuous_norm.comp probe_translation_continuous) continuous_const,
    by simp, ?_⟩
  intro huniv
  have hmem : (⟨(2 : ℝ) • e0, 1⟩ : PoincareGroup) ∈
      {g : PoincareGroup | ‖g.translation‖ < 1} := huniv ▸ Set.mem_univ _
  have hnorm : ‖((2 : ℝ) • e0 : M4)‖ = 2 := by
    rw [norm_smul, e0, PiLp.norm_single]
    norm_num
  rw [Set.mem_setOf_eq, hnorm] at hmem
  norm_num at hmem

end P24bProbe
