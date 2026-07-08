# Formalizing QFT in Lean 4 — state of the field (2026-07)

> This document is edited and maintained by Claude and presented as-is.

Consolidated research (3 independent deep-research passes, cross-corroborated) answering:
*how much of QFT can be derived from first principles, formally provable, in Lean 4?*

## The one-line answer

**Not all of it — and the ceiling is mathematics, not Lean.** Everything through free
fields, the axiomatic frameworks and their structural theorems, d = 2, 3 interacting
(constructive) QFT, perturbative renormalization as formal-power-series mathematics, and
2D Yang-Mills is theorem-level rigorous and formalizable in principle. Every nontrivial
interacting theory in d = 4 (Yang-Mills existence + mass gap, QED, QCD, the Standard
Model) is **open mathematics** — no proof exists for anyone to formalize. φ⁴₄ is worse
than open: it is **provably trivial** (Aizenman & Duminil-Copin, Annals 194 (2021)).

## Tier 1 — already formalized (don't reinvent)

- **physlib** (`github.com/leanprover-community/physlib`; HepLean → PhysLean → merged
  with Lean-QuantumInfo → Physlib; lead: Joseph Tooby-Smith). Lean `v4.31.0`, Mathlib
  pinned `v4.31.0`, sorry-free CI.
  - **Wick's theorem, fully proved, 3 forms** (static / time-ordered / normal-ordered):
    `Physlib/QFT/PerturbationTheory/` — `WickAlgebra` (CCR+CAR unified via
    super-commutators, quotient of free algebra), `WickContraction` with fermionic signs,
    normal/time ordering. 52 files, 193 defs, 929 lemmas (arXiv:2505.07939).
  - Lorentz group / SL(2,ℂ) / index-notation `TensorSpecies` (arXiv:2411.07667),
    Higgs potential, anomaly cancellation (SM, MSSM, Pati-Salam, Spin(10), …),
    QM (harmonic oscillator etc.), `FeynmanDiagrams/` nascent.
  - **No Fock space** — approach is purely algebraic; Hilbert-space representation is
    explicitly future work.
- **OSforGFF** (`github.com/mrdouglasny/OSforGFF`; Douglas, Hoback, Mei, Nissim,
  arXiv:2603.15770, ~32k lines, sorry- and axiom-free): **free bosonic QFT in 4D
  Euclidean space proved to satisfy all Osterwalder-Schrader/Glimm-Jaffe axioms** —
  Gaussian Free Field measure on 𝒮′(ℝ⁴) via Minlos. Companion external libs (all
  axiom-free, none upstreamed to Mathlib): `mrdouglasny/bochner` (Minlos theorem),
  `mrdouglasny/gaussian-field` (nuclearity of Schwartz space via Hermite/Dynin-Mityagin),
  `RemyDegenne/kolmogorov_extension4`.
- Adjacent: Virasoro/Sugawara in Lean (arXiv:2510.21741), generalized quantum Stein's
  lemma (arXiv:2510.08672), continuous functional calculus in Mathlib
  (arXiv:2501.15639), tempered distributions in Mathlib (Doll, arXiv:2510.24060).
- **Nobody, in any prover, has formalized the Wightman axioms or Haag-Kastler AQFT**
  (confirmed gap, not merely unfound). OS→Wightman reconstruction: not formalized.

## Tier 2 — theorem-level mathematics, formalizable in principle (the real frontier)

| Target | Math status | Blockers in Mathlib |
|---|---|---|
| Wightman axioms (statement) + free scalar/Dirac verification | Streater-Wightman, Reed-Simon II | Fock space (needs completed Hilbert ⊗), unbounded operator theory |
| OS reconstruction theorem (Euclidean → Wightman) | OS 1973/75 | unbounded spectral theorem, Stone's theorem |
| PCT, spin-statistics, Reeh-Schlieder, Haag's theorem | classic theorems | Wightman framework first; analytic continuation machinery |
| P(φ)₂ / φ⁴₂ interacting construction | Nelson, Glimm-Jaffe-Spencer, Simon | Gaussian + interacting measures on 𝒮′; hypercontractivity |
| φ⁴₃ (incl. via regularity structures) | Glimm-Jaffe; Gubinelli-Hofmanová CMP 2021 | SPDE theory absent from Mathlib entirely |
| Epstein-Glaser / BPHZ perturbative renormalization, pAQFT | rigorous per-order (formal power series) | wavefront sets / microlocal analysis, distribution extension |
| GN₂, sine-Gordon (β²<8π), Yukawa₂,₃ | constructed 1970s–80s | as above, harder |
| 2D Yang-Mills measure, Makeenko-Migdal, master field | Lévy, Chevyrev, Dahlqvist | stochastic analysis on groups |
| φ⁴₄ triviality (negative theorem) | Aizenman-Duminil-Copin 2021 | lattice/random-current machinery |
| Haag-Kastler nets, DHR superselection, Tomita-Takesaki | Haag, Doplicher-Roberts | von Neumann algebras missing from Mathlib |

## Tier 3 — open mathematics (cannot be formalized by anyone)

- 4D Yang-Mills existence + mass gap (Clay Millennium; claimed proofs keep getting
  withdrawn, e.g. arXiv:2506.00284 withdrawn by arXiv admins).
- Any nontrivial interacting 4D theory: QED₄ (believed trivial — Landau pole — but
  unproven), QCD₄, electroweak, Standard Model, 4D Higgs.
- 3D Yang-Mills continuum measure + mass gap (rigorous lattice progress:
  Cao-Chatterjee; CCHS stochastic quantization is local-in-time only,
  Inventiones 2024; Chevyrev-Shen 2025 uniqueness of renormalization).
- Non-perturbative meaning of the 4D perturbation series (Borel summability proven
  only in d = 2, 3 super-renormalizable cases).

So "all of QFT" in the physicist's sense (the Standard Model, computed to all orders and
non-perturbatively) is not formalizable this decade by anyone — deriving it would mean
first solving multiple Millennium-class open problems.

## Mathlib infrastructure map (mid-2026)

**Solid:** Hilbert spaces (`InnerProductSpace` + `CompleteSpace`, `HilbertBasis`),
bounded operators + adjoints, C*-algebras (mature), continuous functional calculus,
spectrum/Gelfand, Schwartz space, tempered distributions + Fourier (𝓢/L²/𝓢′), Bochner
integral, measure theory/kernels, martingales, algebraic tensor/symmetric/exterior/
Clifford algebras, Lie algebras + root systems.

**Partial:** unbounded operators (`LinearPMap` + adjoint; no essential self-adjointness,
no von Neumann extension theory), spectral theorem (finite-dim/compact only; no PVMs),
GNS (`GelfandNaimarkSegal` exists; cyclic vector TODO), Gaussian measures (abstract
Banach `IsGaussian`; 𝒮′-Gaussians external), Kolmogorov extension (Ionescu-Tulcea in;
full theorem external).

**Missing:** unbounded spectral theorem (biggest single gap), Stone's theorem /
one-parameter unitary groups / C₀-semigroups, Borel functional calculus + spectral
measures, von Neumann algebras (bicommutant exists only as an AI-prover benchmark),
nuclear spaces, Minlos (external only), completed/Hilbert tensor products (**hard
blocker for Fock space**), Wiener measure (external, upstreaming:
`RemyDegenne/brownian-motion`), Itô calculus (external: arXiv:2606.15089), SDE/SPDE
(absent everywhere), concrete Lie groups / Lorentz-Poincaré in Mathlib proper,
universal covers as groups, unitary representations, Peter-Weyl, Mackey machine /
Wigner classification.

## Candidate world-first targets for this sandbox (ranked by leverage/feasibility)

1. **Fock space + free scalar field satisfying the Wightman axioms** — no prover has
   the Wightman axioms at all. Requires building completed Hilbert tensor products +
   symmetric Fock space + enough unbounded-operator theory (a Mathlib-grade
   contribution in itself). The single most cited gap by both physlib and OSforGFF.
2. **Stone's theorem + unbounded spectral theorem** — pure Mathlib infrastructure that
   unblocks everything operator-theoretic (Hamiltonians, dynamics, OS reconstruction);
   highest upstream value.
3. **OS reconstruction theorem** — composes with OSforGFF's existing result to yield
   the first fully formal Lorentzian QFT. Depends on (2).
4. **P(φ)₂ interacting construction** — first formalized interacting QFT ever;
   large (Nelson estimates, hypercontractivity) but genuinely theorem-level.
5. **Haag's theorem / PCT / spin-statistics** — high-prestige structural theorems once
   (1) exists.

## Toolchain state (this machine)

- elan 4.2.3 installed at `~/.elan` (toolchain manager; no default toolchain yet —
  pin per-project via `lean-toolchain`).
- physlib targets `leanprover/lean4:v4.31.0` + Mathlib `v4.31.0`.

## Key references

- physlib: https://github.com/leanprover-community/physlib · https://physlib.io
- HepLean paper arXiv:2405.08863 (CPC 308 (2025) 109457) · index notation
  arXiv:2411.07667 · Wick's theorem arXiv:2505.07939
- OSforGFF / "Formalization of QFT" arXiv:2603.15770
- Aizenman & Duminil-Copin, Annals 194 (2021) 163-235 (φ⁴₄ triviality)
- Gubinelli & Hofmanová, CMP 2021 (φ⁴₃ PDE construction)
- Chandra-Chevyrev-Hairer-Shen, Inventiones 2024 (3D YMH stochastic quantization)
- Streater & Wightman, *PCT, Spin and Statistics, and All That*; Glimm & Jaffe,
  *Quantum Physics*; Simon, *The P(φ)₂ Euclidean QFT*; Haag, *Local Quantum Physics*;
  Rejzner, *Perturbative Algebraic QFT*
