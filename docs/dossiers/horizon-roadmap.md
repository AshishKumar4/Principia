# Horizon roadmap — from constraint atlas to an AI-scientist system for physics

> This document is edited and maintained by Claude, with the owner in the loop, and
> presented as-is. Dated 2026-08-23. It distills six read-only research reports
> (landscape, QFT, GR, strings/M-theory, incompatibility engine, governance), each
> grounded in primary sources. Full reports live in the session archive; every
> load-bearing claim below carries its citation. Items no report could verify
> first-hand stay marked UNVERIFIED.

## Mission restated

Principia is one monorepo with four canonical parts: the formal atlas (`Atlas/`),
the evidence ledger (`evidence/`), the candidate registry (`candidates/`,
`CandidateLab/`), and the platform (`principia/`). The goal is a laboratory in
which agents construct candidate physical theories, Lean checks their mathematics,
pinned experimental records test their predictions, and every rejection carries a
machine-checkable certificate. Lean verifies derivations; only experiment verifies
axioms about nature. Finite data never singles out one true theory, so the system
keeps every surviving candidate and searches for experiments that separate them.

## Feasibility verdicts that bound the program

- No general algorithm decides all physical questions: the spectral-gap problem is
  undecidable (Cubitt, Pérez-García, Wolf, Nature 528, 207 (2015); arXiv:1502.04573).
- Yang-Mills existence + mass gap is open mathematics with an official statement
  (Jaffe, Witten, Clay Mathematics Institute). φ⁴ in d=4 is provably trivial
  (Aizenman, Duminil-Copin, Ann. Math. 194, 163 (2021)).
- M-theory has no complete mathematical definition; Witten 1995 (arXiv:hep-th/9503124)
  gives evidence, not a definition; BFSS is a partial candidate. Register M-theory
  as a hypothesis node, never a proof target.
- Derivability-constrained discovery is real prior art: AI-Descartes (Nat. Commun.
  14, 1777 (2023)), AI-Hilbert (Nat. Commun. 15, 5922 (2024)), AI-Noether
  (arXiv:2509.23004). Principia generalizes this pattern from polynomial systems to
  kernel-checked mathematics plus statistical evidence gates.

## Landscape: where Principia stands (2026)

Lean is the only ecosystem holding both a completed physics result and the missing
infrastructure lanes we need. Key external assets and rivals:

- OSforGFF (Douglas, Hoback, Mei, Nissim; arXiv:2603.15770; Apache-2.0): sorry-free
  proof that the 4D Gaussian free field satisfies the Osterwalder-Schrader axioms.
  Composition target: OS→Wightman reconstruction joins their Euclidean result to our
  Lorentzian stack.
- Seiberg-Witten codification (Douglas, arXiv:2607.06379) and DualityCert
  (arXiv:2607.23614): the first proto-incompatibility engines; our X.1 design
  generalizes them.
- Isabelle/AFP owns the only completed Hilbert tensor product (Unruh, AFP 2024) and
  CHSH/Tsirelson entries — concept-portable references, not dependencies.
- Contested lane to coordinate, not fork: unbounded spectral theorem/Stone
  (SpectralThm, LeanOA, Doll #29624, physlib). Geometry lane gates: Mathlib PRs
  #34288 and #36036.
- Ten ownable gaps (ranked in the landscape report): Wightman statement+free field;
  unbounded spectral/Stone; PVM conventions; Fock in Mathlib style; Lorentz/Poincaré
  covering layer; OS reconstruction; von Neumann algebras in Lean; microlocal
  analysis; Lorentzian content on #36036; the mechanized assumption atlas itself.

## Complete-QFT ladder (dependency order, honest walls)

1. Operator infrastructure → 2. Wightman + free fields (current P2) → 3. OS
reconstruction → 4. structural theorems (Haag, Reeh-Schlieder, PCT, spin-statistics)
→ 5. constructive interacting fields in d=2,3 → 6. Haag-Kastler nets + DHR/DR →
7. pAQFT/Epstein-Glaser/BV → 8. BRST/anomalies → 9. KMS/Tomita-Takesaki →
10. WALL: 4D nonperturbative (Clay-status).

- P(φ)₂ is the credible first interacting Wightman theory (Glimm-Jaffe-Spencer,
  Ann. Math. 100, 585 (1974); Nelson, J. Funct. Anal. 12, 97 (1973)): needs Gaussian
  measures on 𝒮′, hypercontractivity, Nelson estimates — multi-year, theorem-level.
- Epstein-Glaser renormalization (Ann. IHP A 19, 211 (1973)) is theorem-level but
  runs on Hörmander wavefront sets; microlocal analysis is absent from every prover
  and is the largest single infrastructure item on the map.
- The Standard Model as a positive-metric Wightman theory is obstructed in principle
  (Strocchi: Gauss law vs locality+positivity); the honest target is
  SM-as-perturbative-AQFT with BRST-quotient observables.

## Complete-GR tracks (from the Phase-1 base)

- Theorem-level after the P1.4 geodesic gate: causality completion (Minguzzi, Living
  Rev. Rel. 22:3), Jacobi/index form (O'Neill ch. 10), Raychaudhuri (Phys. Rev. 98,
  1123 (1955)), Penrose 1965, Hawking 1966, Hawking-Penrose 1970 (Proc. Roy. Soc. A
  314, 529), FLRW cosmology (cheapest post-P1.7 win).
- Statement-freeze now, proofs deferred to dedicated infrastructure programs:
  Choquet-Bruhat local EVFE (Acta Math. 88, 141 (1952)) needs a quasilinear
  hyperbolic PDE + Sobolev shelf Mathlib entirely lacks; positive mass
  (Schoen-Yau CMP 65, 45; Witten CMP 80, 381) needs spin geometry or GMT; GW
  asymptotics/memory (Christodoulou PRL 67, 1486) needs stability-of-Minkowski
  machinery.
- Open mathematics, never roadmap items: cosmic censorship, Kerr stability
  (sub-extremal Schwarzschild only: arXiv:1710.01755), non-analytic rigidity, BKL.

## Strings and M-theory

- Theorem-level today: no-ghost theorem (Goddard-Thorn, Phys. Lett. B 40, 235
  (1972); Brower, Phys. Rev. D 6, 1655 (1972)) on our Fock/Virasoro assets
  (Virasoro in Lean: arXiv:2510.21741); Green-Schwarz anomaly-polynomial identity
  (Phys. Lett. B 149, 117 (1984)); partition-function-level T-duality on Mathlib's
  modular forms; HLS supersymmetric extension of Coleman-Mandula (Nucl. Phys. B 88,
  257 (1975)) after P3.3.
- Critical dimension D=26 needs the Kac determinant formula (Feigin-Fuchs 1983) —
  substantial, finite.
- VOA axioms: coordinate with Carnahan's in-flight Mathlib work; do not duplicate.
- Definitionally open, hypothesis nodes only: S-duality, M-theory, AdS/CFT (GKPW),
  mirror symmetry, moduli of curves.

## Incompatibility engine (X.1 upgrade)

Design (packed-classes lineage: Garillot et al. TPHOLs 2009; Spitters-van der
Weegen arXiv:1102.1323; corrected prior art for FOL packaging: Forster-Kirst
arXiv:2006.04399 — the "Bauer" lead was misattributed):

1. Every named physical assumption becomes one Prop-valued class with its source
   docstring (`HasNEC`, `HasMicrocausality`, `HasSpectrumCondition`, ...).
2. A candidate theory extends exactly the classes it assumes; a dropped assumption
   is a missing instance, visible syntactically.
3. No-go theorems take hypothesis classes as instance arguments; a `#atlas_check`
   MetaM command walks a theorem's instance binders and reports which hypotheses a
   candidate satisfies.
4. Independence witnesses join non-vacuity witnesses: for each hypothesis of a
   no-go, a committed model satisfying the others and violating it. Finite cases run
   through Mathlib ModelTheory structures discharged by kernel `decide`; infinite
   cases are proved lemmas.
5. Candidate gates before any grind: randomized testing on decidable projections,
   proof-producing refutation attempts (Duper, ITP 2024), finite-model search.
   Gate outcomes land in `audits/probes/<candidate>/`.

Boundaries stated plainly: instance-synthesis failure proves nothing by itself;
the engine detects stated clashes between registered hypotheses, and unstated
assumptions remain spec-review's job.

## Discovery automation: what the evidence supports

Proof-grinding on frozen statements is industrial (AlphaProof, Nature 2025;
Aristotle, arXiv:2510.01346; DeepSeek-Prover-V2, arXiv:2504.21801). Responsible
axiom/definition discovery is not (autoformalization surveys arXiv:2505.23486;
definition-mismatch dominance: Wu et al. NeurIPS 2022). Consequence for the
platform: agents propose and repair candidates inside the sandbox, evaluators and
evidence gates decide, humans own semantics of canonical definitions. "Cyan
Helmet" does not exist; Trinity (Morph Labs) is real but vendor-published —
treat vendor pipelines as unreviewed.

## Governance practices adopted or queued

From Mathlib/LTE/FLT/PNT+LeanArchitect studies (Baanen et al. arXiv:2508.21593;
LeanArchitect arXiv:2601.22554; Lean Atlas arXiv:2604.16347): blueprint-driven
dependency graphs (our BLUEPRINT), green-main enforcement (our CI + branch
protection), committed review evidence (audits/), dated deprecations, and
scope-laundering vigilance (15-53% rates reported: arXiv:2606.16118). Queued:
review-cone tooling for spec freezes, weekly debt metrics in CI.

## Sequencing (single source of truth stays BLUEPRINT.md)

Now → P2.5 Wightman freeze → P2.6 free-field flagship → P2.7 Haag. Then, in
parallel lanes: Phase 3 no-gos (+HLS extension); GR tracks D/H after P1.4-P1.7;
Phase 5 strings (no-ghost → Kac determinant → D=26); X.1 engine upgrade with the
first candidate-gate loop on the Bell pilot pattern; evidence ledger growth one
vertical slice at a time (next: one GR observable, one collider likelihood).
Statement-freezes for EVFE, positive mass, and GW memory enter the atlas as named
hypotheses so the engine can reason about them long before proofs exist.
