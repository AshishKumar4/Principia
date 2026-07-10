# P2.3 Design Dossier — Stone's Theorem & Unbounded-Operator Infrastructure

> This document is edited and maintained by Claude and presented as-is.
> Condensed from the 2026-07-09 Fable design report (verified against Mathlib v4.31.0
> source; repo/PR claims spot-checked via gh: SpectralThm pushed 2026-07-01, Doll PR
> #29624 OPEN. physlib SpectralMeasure norm-σ-additivity claim NOT yet re-verified —
> check before relying).

## Verdict

Route: **Cayley transform** (von Neumann/Rudin 13.19) + the in-flight bounded-normal
spectral theorem. Stone's theorem, the unbounded spectral theorem, the Borel functional
calculus, and the Cayley transform have never been formalized in any prover; the
bounded core is actively being built by others. **Our lane: nodes c, f, h, i below.
Contested lane (contribute, don't fork): d, e.**

Rejected routes: Bochner/positive-definite (no infrastructure savings; Bochner exists
only externally — mrdouglasny/bochner, fin-dim, not in Mathlib); Hille-Yosida (large
greenfield, unneeded for unitary groups — Reed-Simon VIII.8's elementary Gårding-domain
argument suffices); multiplication-operator-first (cyclic-decomposition grind Stone
doesn't need; valuable follow-up j).

## Mathlib v4.31.0 state (verified)

HAS: LinearPMap algebra + closure + unbounded adjoint (`LinearPMap.adjoint`,
`IsSelfAdjoint`, graph-adjoint via orthocomplement); mature CFC (17 files, incl.
`cfc_integral`, order, unitary spectrum-in-circle); B(H) is a CStarAlgebra; RMK (real +
NNReal); complex/vector measures + variation; charFun + Lévy continuity; Hölder pairing
(L∞ multiplication on L² free); `IsHilbertSum`; `NormedSpace.exp` +
`selfAdjoint.expUnitary` + `hasDerivAt_exp_smul_const` (bounded-generator Stone nearly
free); L² Plancherel.

MISSING (zero grep hits): symmetric LinearPMaps, essential self-adjointness, deficiency
indices, Cayley transform, PVMs/spectral measures, Borel calculus, spectral theorem
beyond finite-dim/compact, C₀-semigroups/one-parameter groups, positive-definite
functions/Bochner-theorem, unitary representations; von Neumann algebras = definition
only.

## The converging pipelines (coordinate, don't collide)

1. **SpectralThm** (Tanimoto+Butterley, github.com/oliver-butterley/SpectralThm,
   active): bounded-normal spectral theorem per Rudin, `Resolutions.lean` PVMs,
   Mathlib-PR-first. Tanimoto's own in-tree `StandardSubspace.lean` TODO (Tomita/KMS)
   means he NEEDS our f/h/i — natural alliance.
2. **LeanOA** (Loreaux/Bannon/Dedecker): Borel FC for bounded operators, L∞-as-W*.
3. **physlib** (Loges): unbounded basics merged 2026 (IsSymmetric,
   IsEssentiallySelfAdjoint, deficiency numbers, real spectrum, a `SpectralMeasure`
   structure with in-code TODO "move to Mathlib"). RED FLAG to verify: reportedly
   norm-countably-additive (genuine PVMs are only SOT-σ-additive) — flag to Loges.
4. **TauCeti**: C₀-semigroups + Hille-Yosida resolvent (2026-07-08) but does not
   upstream to Mathlib; Stone = stretch goal only. Track, don't depend.
5. **Mathlib**: Doll PR #29624 (LinearPMap resolvent) OPEN — natural reviewer/ally.
6. Other provers: Isabelle bounded-only (Unruh); nothing unbounded anywhere.

## Target statements (abridged; full forms in the session transcript report)

`OneParameterUnitaryGroup H` (toFun : ℝ → unitary (H →L[ℂ] H), map_zero/map_add,
strong continuity) · `generator` (domain = differentiability set at 0, A = −i d/dt|₀)
· Stone halves `isSelfAdjoint_generator` / `IsSelfAdjoint.unitaryGroup` + roundtrips
· `stoneEquiv : {A // IsSelfAdjoint A} ≃ OneParameterUnitaryGroup H` ·
`ProjectionValuedMeasure α H` (**σ-additivity ONLY weak/SOT** — the design decision
three projects are about to make incompatibly) · `PVM.integral` (natural domain via
∫‖f‖²dμ_x < ∞) · unbounded spectral theorem `∃! P, ∫λ dP = A` · `cayleyTransform :
{A // IsSelfAdjoint A} ≃ {U : unitary // 1 not an eigenvalue}` · essential
self-adjointness layer: `LinearPMap.IsSymmetric`, `‖(A±i)x‖² = ‖Ax‖²+‖x‖²`, deficiency
spaces = ker(A†∓i) = range(A±i)ᗮ, RS VIII.3 criterion.

Citations for specs: Reed-Simon II Thm VIII.3/VIII.6/VIII.7-8; Rudin FA 2e ch. 12-13
(Thm 13.19); Weidmann (already Mathlib's LinearPMap reference).

## Sub-node DAG (a→b→c; d→e; c,e→f; g; f,g→h; b,h→i; j stretch)

| Node | Content | Est. | Status |
|---|---|---|---|
| a | Symmetric LinearPMaps (IsSymmetric, closability, norm identity) | ~700 ln, 1-2 wk | ours; coordinate w/ Loges |
| b | Deficiency subspaces + ess. self-adjointness + RS VIII.3 | ~1.2k ln, 2-3 wk | ours, uncontested |
| c | Cayley transform bijection | ~1k ln, 2 wk | ours, world-first |
| d | PVM structure + scalar spectral measures | ~1.5k ln, 3 wk | align w/ SpectralThm |
| e | Bounded-normal spectral thm + Borel calculus | ~3-4k ln, 6-10 wk | CONTESTED — contribute |
| f | Unbounded spectral thm via Cayley pullback | ~2k ln, 3-5 wk | ours, world-first core |
| g | OneParameterUnitaryGroup + bounded-generator case | ~500 ln, 1 wk | ours — **DO FIRST** (freezes atlas-facing spec; unblocks P2.4/P2.5) |
| h | Stone forward | ~800 ln, 2 wk | ours |
| i | Stone converse (Gårding domain) + stoneEquiv | ~1.2k ln, 2-3 wk | ours |
| j | Multiplication-operator form; MeasurableFunctionalCalculus class; C₀-semigroups | stretch | coordinate w/ Loreaux |

Total ≈ 10-12k lines, 4-6 months single-threaded; ~3 if SpectralThm delivers e.

**Witnesses:** multiplication by unbounded real measurable f on L²(μ) self-adjoint;
U_t = mult by e^{itf}; expected-false: symmetric-not-self-adjoint restriction
(IsSelfAdjoint vs IsEssentiallySelfAdjoint distinction exercised).
