# Incompatibility ledger

> This document is edited and maintained by Claude, with the owner in the loop, and
> presented as-is. Every entry names its formal certificate in this repository and
> the original research it comes from. Statuses:
> `kernel-certified` — a Lean proof or kernel probe in this repo carries the claim;
> `evidence-certified` — a pinned experimental record plus a recomputed statistical
> test rejects the assumption set (certificate = archived evaluation bundle);
> `statement-registered` — the clash is established in the literature and recorded
> here with sources, pending formalization in the atlas.

## 1. Local realism vs. quantum experiment — evidence-certified

Assumption set: outcome determinism + locality (response functions independent of
the remote setting) + measurement independence (one hidden-variable distribution
for all settings pairs).
Formal side: `CandidateLab.Bell.LocalRealism.chEberhard_expectation_nonpos` (every
local model keeps the CH-Eberhard functional at or below zero; the CHSH bound is
Mathlib's `CHSH_inequality_of_comm`, applied not restated).
Empirical side: `evidence/records/shalm-2015-ch-eberhard.json`; the martingale
binomial test recomputed from Table S-II sufficient statistics rejects the set at
p = 2.287×10⁻⁷ (excess predictability 3×10⁻³); null-control run correctly not
rejected (p = 0.5637). Certificate bundle:
`e98512f5e104ee27d36a0e11efaafcec7e84bc0d7e3219e91bb747cb926c5421`.
Sources: Bell, Physics 1, 195 (1964); Clauser, Horne, Shimony, Holt, PRL 23, 880
(1969); Clauser, Horne, PRD 10, 526 (1974); Eberhard, PRA 47, R747 (1993); Fine,
PRL 48, 291 (1982); Shalm et al., PRL 115, 250402 (2015), arXiv:1511.03189.
Independence (each assumption individually load-bearing, kernel-certified):
`CandidateLab.Bell.Independence.signalingResponse_breaks_bound` (locality dropped
only at Alice → functional reaches 1 > 0) and
`settingsCorrelated_breaks_bound` (measurement independence dropped only in the
hidden-variable weights → 1 > 0), with faithfulness lemmas (`signalingCH_ofLocal`
is `rfl`) proving the countermodels break the frozen functional, not a restated
one.

## 2. Classical vs. quantum correlation bounds (CHSH 2 vs 2√2) — kernel-certified

Commuting (classical) CHSH tuples obey S ≤ 2; arbitrary *-algebra tuples obey
S ≤ 2√2. Both bounds live in the pinned Mathlib
(`Mathlib/Algebra/Star/CHSH.lean`: `CHSH_inequality_of_comm`,
`tsirelson_inequality`) and are consumed by the local-realism candidate. The gap
between the two constants is the machine-checked boundary the Bell evidence
exploits.
Sources: Cirel'son (Tsirelson), Lett. Math. Phys. 4, 93 (1980); CHSH 1969 as above.

## 3. No nontrivial one-dimensional unitary Poincaré representation — kernel-certified

A strongly continuous unitary representation of the restricted Poincaré group on ℂ
is trivial; the "cheap character rep" a wrong spec would admit is impossible.
Certificate: `audits/probes/P2.4b/character_obstruction_probe.lean` (committed
kernel probe, recompiled by gate 9 on every run).
Source: Wigner, Ann. Math. 40, 149 (1939).

## 4. Gauss law vs. locality + positivity in gauge theories — statement-registered

In a gauge quantum field theory with a Gauss law, locality, positivity of the
metric, and manifest covariance cannot hold together; the physical state space
lives in an indefinite-metric quotient (why the Standard Model is not a
positive-metric Wightman theory as such). Formalization target: Phase 6 (pAQFT
lane) hypothesis node.
Sources: Strocchi, CMP 56, 57 (1977); Strocchi, *An Introduction to
Non-Perturbative Foundations of Quantum Field Theory*, OUP (2013); Morchio,
Strocchi indefinite-metric axioms (context: arXiv:math-ph/0501034).

## 5. φ⁴ triviality in four dimensions — statement-registered

The 4D nearest-neighbour Ising/φ⁴ scaling limits are Gaussian: the textbook φ⁴₄
interacting continuum limit does not exist. Registered as a wall for any
candidate relying on a nontrivial 4D φ⁴ fixed point.
Source: Aizenman, Duminil-Copin, Ann. Math. 194, 163 (2021).

## 6. Spectral-gap undecidability — statement-registered

No algorithm decides gappedness for general translationally invariant
nearest-neighbour 2D Hamiltonians; a bound on what any evaluation gate can ever
promise about candidate theories with unrestricted Hamiltonian families.
Sources: Cubitt, Pérez-García, Wolf, Nature 528, 207 (2015); full version
arXiv:1502.04573; 1D extension: Bausch, Cubitt, Lucia, Pérez-García, PRX 10,
031038 (2020).

## 7. Pending formalization targets (statement-registered, blueprint-scheduled)

- Weinberg-Witten: no composite massless spin-2 with a Lorentz-covariant conserved
  stress tensor — Weinberg, Witten, Phys. Lett. B 96, 59 (1980). Blueprint P3.2.
- Coleman-Mandula: no nontrivial mixing of spacetime and internal symmetries —
  Coleman, Mandula, Phys. Rev. 159, 1251 (1967). Blueprint P3.3; supersymmetric
  loophole: Haag, Łopuszański, Sohnius, Nucl. Phys. B 88, 257 (1975), Phase 5.
- Haag's theorem: the interaction picture does not exist as claimed — Haag, Dan.
  Mat. Fys. Medd. 29, 12 (1955); Streater-Wightman Thm 4-16 form. Blueprint P2.7.
- Penrose singularity theorem: classical GR predicts its own incompleteness —
  Penrose, PRL 14, 57 (1965). Blueprint P1.7.
