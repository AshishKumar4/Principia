import Atlas.Witnesses.WightmanUtilities

/-!
# P2.5a adversarial kernel probes — open, punctured, and closed forward cones

The spectrum condition of the Wightman axioms uses the *closed* forward cone `V̄₊`. The
frozen P2.4a spec offers two neighbouring sets and neither of them is `V̄₊`:

* `InFutureCausalCone` — the causal cone *punctured* at the origin (`0 < v⁰`);
* `InFutureTimeCone` — the *open* cone, which drops the whole null boundary.

These probes separate all three sets by kernel arithmetic at two points, the apex `0`
and the null direction `∂₀ + ∂₁`, and then show that the puncture is not a matter of
taste: the punctured cone is not a closed set, so only `closedForwardCone` can carry the
closed-support statement. Physically the apex is the vacuum four-momentum and the null
boundary carries the massless momenta, so each omission changes the axiom.

Reviewer probe file (Workflow v2): lives in `audits/probes/P2.5a/` only.
-/

open Filter
open Spacetime.Minkowski
open scoped Topology

/-! ## The apex: in the closed cone, out of the punctured one -/

theorem probe_apex_mem_closed : (0 : M4) ∈ closedForwardCone :=
  zero_mem_closedForwardCone

theorem probe_apex_notMem_punctured : ¬ InFutureCausalCone (0 : M4) := by
  rintro ⟨-, h0⟩
  simp at h0

theorem probe_closed_ne_punctured :
    closedForwardCone ≠ {v : M4 | InFutureCausalCone v} := by
  intro h
  have hmem : (0 : M4) ∈ {v : M4 | InFutureCausalCone v} := h ▸ probe_apex_mem_closed
  exact probe_apex_notMem_punctured hmem

/-! ## The null boundary: in the closed cone, out of the open one -/

theorem probe_null_mem_closed : (timeUnit + spaceUnit : M4) ∈ closedForwardCone := by
  rw [mem_closedForwardCone_iff]
  norm_num [Fin.ext_iff]

theorem probe_null_notMem_open : ¬ InFutureTimeCone (timeUnit + spaceUnit : M4) := by
  rintro ⟨h1, -⟩
  simp [Fin.ext_iff] at h1

theorem probe_closed_ne_open_with_apex :
    closedForwardCone ≠ insert 0 {v : M4 | InFutureTimeCone v} := by
  intro h
  have hmem : (timeUnit + spaceUnit : M4) ∈ insert 0 {v : M4 | InFutureTimeCone v} :=
    h ▸ probe_null_mem_closed
  rcases hmem with hzero | hopen
  · have h0 := congrArg (fun z : M4 => z 0) hzero
    norm_num [Fin.ext_iff] at h0
  · exact probe_null_notMem_open hopen

/-- A strict coordinate inequality would drop the null boundary: the closed cone does
NOT satisfy `‖v⃗‖² < (v⁰)²`. -/
theorem probe_strict_inequality_wrong :
    ¬ ∀ v : M4, v ∈ closedForwardCone → v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 < v 0 ^ 2 := by
  intro h
  have := h _ probe_null_mem_closed
  norm_num [Fin.ext_iff] at this

/-! ## The puncture is not a matter of taste: the punctured cone is not closed -/

/-- The rays `t ∂₀`, `t > 0`, lie in the punctured causal cone and converge to the apex,
so the punctured cone is not a closed set. This is why the spectrum-condition surface
must adjoin the origin rather than reuse `InFutureCausalCone`. -/
theorem probe_punctured_cone_not_isClosed :
    ¬ IsClosed {v : M4 | InFutureCausalCone v} := by
  intro hclosed
  have htend : Tendsto (fun t : ℝ => t • (timeUnit : M4)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => t • (timeUnit : M4)) (𝓝 (0 : ℝ))
        (𝓝 ((0 : ℝ) • (timeUnit : M4))) := (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (fun t : ℝ => t • (timeUnit : M4)) t ∈ {v : M4 | InFutureCausalCone v} := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨by simpa [Fin.ext_iff] using sq_nonneg t, by simpa using ht⟩
  have hapex := hclosed.mem_of_tendsto htend hmem
  exact probe_apex_notMem_punctured hapex

-- ...whereas the spec's cone is closed.
theorem probe_closed_isClosed : IsClosed (closedForwardCone : Set M4) :=
  isClosed_closedForwardCone

/-! ## The three sets are nested, strictly -/

theorem probe_open_subset_punctured :
    {v : M4 | InFutureTimeCone v} ⊆ {v : M4 | InFutureCausalCone v} :=
  fun _ h => h.inFutureCausalCone

theorem probe_punctured_subset_closed :
    {v : M4 | InFutureCausalCone v} ⊆ closedForwardCone :=
  fun _ h => h.mem_closedForwardCone
