# P2.4/P2.5/P2.6 Design Dossier — Poincaré, Wightman axioms, free field

> This document is edited and maintained by Claude and presented as-is.
> Condensed from the 2026-08-07 Fable design report (physlib cloned+verified at tag
> v4.31.0; pinned-Mathlib API probes run; frozen spec surfaces read).

## Verdicts

1. **physlib dependency: DEFERRED TO P3.** Their v4.31.0 tag is pin-compatible, but
   content buys nothing load-bearing for the scalar-field lane: LorentzGroup matrix
   layer + SL2C→restricted hom exist, but NO surjectivity/kernel/double-cover, NO
   Poincaré group, NO unitary reps, NO Wigner. Carrier friction (their Fin 1 ⊕ Fin 3
   Pi-type vs our M4) would permanently pollute frozen covariance statements. For
   spin-0 the covering group is not load-bearing at all (rep factors through the
   restricted Poincaré group); rep THEORY is load-bearing nowhere on P2.5-P2.7
   (axioms quantify over an arbitrary rep — atlas pattern).
2. **Spectrum condition: distributional support form** (smeared translations vanish
   when the Minkowski-Fourier transform vanishes near the closed forward cone) — NOT
   a joint spectral measure. Kills the joint-PVM/SNAG risk off the critical path
   (deferred post-Stone node; our PVM structure already fits α = M4). P2.7 consumes
   exactly this form via tube analyticity.
3. **Nelson node NOT load-bearing for Wightman** — S&W need dense invariant domain +
   hermiticity (= our proven adjointness). Stays parallel/non-blocking.
4. **Microcausality = one scalar via the proven CCR**: [φ(f),φ(g)] on F₀ reduces to
   ⟪Ef̄,Eg⟫ − ⟪Eḡ,Ef⟫ = Δₘ(h) for one Schwartz h supported spacelike → the
   Pauli-Jordan support lemma H2 is the hard node. Route R1 (recommended): finite
   propagation speed by energy method with smoothed-cone cutoff (avoids Mathlib's
   boxes-only divergence theorem); fixed frame, NO Lorentz-orbit argument, no
   measure invariance. ~4-7 sessions. Fallback R2: Paley-Wiener (absent from
   Mathlib entirely — upstream-valuable, ~4-8).
5. **Layering item for P2.4a spec review**: extract Minkowski DEFINITIONS (carrier,
   form, cones) from Atlas/Witnesses/Minkowski*.lean into
   Atlas/Specs/Spacetime/Minkowski.lean under [spec-review] (lean extraction over
   frozen-by-import).

## Load-bearing inventory (P2.4)

Restricted Lorentz as subgroup of M4 ≃L[ℝ] M4 (form-preserving, det 1,
orthochronous; closure of orthochronicity = cone argument via the P1.W2
InFutureCausalCone toolkit); Poincaré as hand-rolled semidirect structure (Mathlib
SemidirectProduct fails deletion test — physlib EuclideanGroup made the same call);
MulAction on M4; Schwartz action via compCLMOfAntilipschitz (no gap). PoincareRep =
monoid hom into unitary + strong continuity, with the frozen anchor: translation
directions restrict to OneParameterUnitaryGroup (bridges to Stone lane; costless).
NOT needed: connectedness, covers, Lie structure, Wigner, Mackey, Haar.

## Wightman surface (P2.5)

WightmanField structure: rep, vacuum, dense domain D, field : 𝓢(M4,ℂ) →ₗ (D →ₗ H)
(fixed-domain form — avoids LinearPMap composition, lesson of CCROnDomain),
maps_to, tempered (matrix elements continuous in f), hermitian (matrix-element
form ⟺ φ(f)* ⊇ φ(f̄)). Named axiom Props (atlas fence-posts): CovariantField,
MicrocausalField (SpacelikeSeparated supports ⟹ commute on D; freeze WITH the
kernel-checked anchor IsSpacelike(x−y) ↔ ¬x⤳y ∧ ¬y⤳x from minkowski_causal_iff),
SpectrumCondition (distributional form; needs 𝓕η = Schwartz Fourier ∘ time-flip
CLE, closedForwardCone, one integrability lemma), InvariantVacuum, UniqueVacuum
(separable — Haag consumes it), CyclicVacuum. WightmanQFT bundles.

## Free field map (P2.6) — proof engines

hermitian = PROVEN adjointness · microcausality = PROVEN CCR trio + H2 ·
covariance = Γ conjugation + E equivariance · spectrum = sector computation + the
PROVEN P1.W2 InFutureCausalCone.add · unique vacuum = p⁰ ≥ nm > 0 · cyclic = a†
monomials + density. One-particle space: Lp ℂ 2 μₘ with μₘ = pushforward of
d³p/2ω onto M4 (measure on M4, no subtype — Lorentz acts by composition).
Hard nodes: H1 shell-measure invariance (Jacobian det = ω(Λp)/ω(p), ~2-4);
H2 Pauli-Jordan (above); H3 rep strong continuity (~1-2); H4 Γ second quantization
(PiTensorProduct.map isometry — Pi analogue of mapIsometryₕ; lp family-congruence
lemma = upstream candidate; ~3-5).

## DAG / sequencing

P2.4a → P2.4b → P2.5a utilities → P2.5b WIGHTMAN FREEZE → P2.6d assembly.
Parallel lanes: Γ (P2.6a, grindable now), measure/rep (P2.6b, after P2.4a),
Pauli-Jordan (P2.6c, needs only 𝓕η conventions), P2.4W regular-rep witness,
Nelson. First dispatches: P2.4a spec + P2.6c design (+ Γ next). Total to P2.6:
~18-28 sessions; frozen Wightman surface in ~5-8. Risks: H1/H2 (both have
statement-preserving fallbacks).


## Addendum 2026-08-07 (P2.6c design pass side-flag)

The pin contains a 2025-26 Analysis/Distribution suite the sections above did not
account for: TemperedDistribution.lean, Support.lean (Distribution.IsVanishingOn,
dsupport + API), FourierMultiplier.lean (Schwartz and tempered-distribution
multiplier CLMs), Sobolev.lean, TemperateGrowth.lean (fun_prop algebra). P2.5a's
spectrum-condition utilities must be designed against this suite (IsVanishingOn/
dsupport for the vanishing-near-cone hypothesis) rather than hand-rolling. The
P2.6c lemma DAG (KG finite propagation L0-L6) lives in the design-pass report;
key convention: Mathlib's e^(-2pi i x.xi) normalization puts Omega(k) =
sqrt(4pi^2 norm(k)^2 + m^2).

## Recovered P2.6c finite-propagation DAG (2026-08-24)

The full 2026-08-07 design report was recovered from subagent transcript
`adacb72bc388fdeda`. It verified the named Mathlib v4.31 APIs below against the
vendored source.

### Pin inventory

- Distribution tools: `Function.HasTemperateGrowth`, Schwartz
  `smulLeftCLM`/`compCLMOfAntilipschitz`, tempered distributions,
  `fourierMultiplierCLM`, `Distribution.IsVanishingOn`, and `dsupport`.
- Parameter integrals:
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
  `hasFDerivAt_integral_of_dominated_of_fderiv_le`, and
  `MeasureTheory.continuous_of_dominated`.
- Cone cutoff: `Real.smoothTransition` with `contDiff`, `monotone`,
  `one_of_one_le`, `zero_of_nonpos`, and `Monotone.deriv_nonneg`.
- Divergence theorem: boxes only. The missing compact-support corollary
  `integral_div_eq_zero` is an upstream candidate; transfer between Pi and
  EuclideanSpace uses `PiLp.volume_preserving_ofLp`.
- Paley–Wiener, stationary phase, and partial-Fourier splitting are absent.

### Adjudicated route

Use the sharpened smeared statement. The Pauli–Jordan pairing at a fixed slice is
the Klein–Gordon solution with initial data `(0, phi)` evaluated at `(t,0)`:

`u^phi(t,0) = integral k, sin(t*Omega(k))/Omega(k) * Fourier(phi)(k)`.

The target finite-speed theorem is therefore:

`phi = 0 on closedBall x0 R -> |t| <= R -> u^phi(t,x0)=0`.

This removes the cosine branch, arbitrary Cauchy data, distribution-support
machinery, Gronwall, and mollification from the critical path.

### Lemma nodes

1. **L0 symbols — landed 2026-08-23.** `KleinGordon.lean` fixes
   `Omega(k)=sqrt(4*pi^2*||k||^2+m^2)`, bounds/smoothness, the physical
   mass-shell map, and positive KG energy.
2. **L1 propagator — landed through PJ.1e, 2026-08-24.**
   `KGPropagator.lean` proves the integral/dominators, joint continuity, both
   orders of mixed derivatives, the full first/second spatial and time fields,
   initial data, and the pointwise Klein–Gordon equation. Remaining L1 work is
   only API consolidation/upstreaming, not a missing consumer theorem.
3. **L2 cutoff — landed 2026-08-24.** `KGConeCutoff.lean` constructs
   `psi_delta=sqrt(||x-x0||^2+delta^2)` and the smoothTransition cutoff; proves
   support/interior bounds, `dt chi <= 0`, and the load-bearing
   `||grad_x chi|| <= -dt chi`.
4. **L3 integration by parts — landed 2026-08-24.**
   `KGIntegrationByParts.lean` proves the compact-support divergence theorem on
   the Pi carrier, its exact M3 volume-preserving adapter, and the weighted IBP
   identity in general/cutoff-supported/field-supported forms.
5. **L4 local energy.** Differentiate
   `E(t)=integral chi(t,x)*(|dt u|^2+|grad u|^2+m^2|u|^2)`. L3 and L2 give
   `E'<=0`; zero initial local energy and `m>0` give finite speed.
6. **L5 four-dimensional slicing.** Construct the affine Schwartz slice
   `h -> h_t`, partial-Fourier bounds, Fubini splitting, and shell-difference
   sine formula.
7. **L6 assembly/spec.** Smeared Pauli–Jordan support statement, then adapter
   to the shell measure. This depends on frozen P2.5a conventions and P2.6b.

Sources: Reed–Simon II §§IX.1, X.7 (section-level); Evans,
*Partial Differential Equations*, 2nd ed., §2.4.3 (local energy and finite
propagation, section-level); Wald, *General Relativity*, §10.1
(initial-value/energy method, section-level).

## P2.6b shell-measure H1 DAG (2026-08-24)

The direct change-of-variables route is complete. No coarea or
delta-distribution fallback was needed. Important correction to the original
research report: `shellMap` acts on **physical** momentum `p`, not Fourier
frequency `k`. In frequency coordinates the identity-map case is `k ↦ 2πk`,
so the original frequency-coordinate Jacobian formula was false.

1. **N0/N1 — landed.** `MassShellMeasure.lean` defines
   `massShellParam m p=(sqrt(||p||²+m²),p)` and
   `map massShellParam (d³p/(2energy(p)))`; its Fourier-coordinate theorem
   carries the required `(2π)³` factor.
2. **N2/N3 — landed.** `MassShellInvariance.lean` computes the shell-map
   derivative and extracts both row/column Lorentz identities from frozen form
   preservation.
3. **N4/N5 — landed.** An explicit Fin-3 determinant expansion proves
   `|det D F_Lambda(p)|=energy(F_Lambda(p))/energy(p)`; the induced shell map
   is a smooth bijection with inverse from `Lambda⁻¹`.
4. **N6 — landed at measure level.** The real weighted-integral theorem is
   supplemented by `MassShellMeasurePreserving.lean`, which repeats the
   substitution in ENNReal and uses `Measure.ext_of_lintegral`; no invalid
   inference from a nonintegrable Bochner integral occurs.
5. **N7/H3 — landed.** `ShellOneParticle.lean` constructs translations and
   proves their strong continuity. `ShellPoincareRepresentation.lean`
   combines the H1 pullback and phase into the exact Wigner formula, proves
   semidirect representation laws/unitarity, proves full joint strong
   continuity through Mathlib's `Continuous.compMeasurePreservingLp`, and
   packages `shellPoincareRep m hm : PoincareRep (ShellOneParticle m)`.

Primary source: Wigner, *Annals of Mathematics* 40 (1939), §6, eq. (59a)
(the `d^3p/|p0|` inner product and Jacobian-invariance footnote; verified
first-hand). The repository uses the conventional additional factor `1/2`.
Context: Streater–Wightman Chs. 1 and 3; Weinberg QFT I §2.5; Reed–Simon II
§X.7 (all section-level unless a display is named above).