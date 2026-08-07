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
