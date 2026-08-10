# QG Constraint Atlas — project rules

> This document is edited and maintained by Claude and presented as-is.
> Binding for every agent and session working in this repository.

## What this project is

A machine-checked constraint atlas for quantum gravity: formalize, in Lean 4 + Mathlib,
the theorems that fence in any unification of quantum theory and general relativity
(singularity theorems, Haag's theorem, Weinberg-Witten, Coleman-Mandula, QFT on curved
spacetime), with every physical assumption as an explicit, named hypothesis. Read
`RESEARCH.md` (state of the field, what exists, what is open) and `BLUEPRINT.md` (phased
plan and DAG) before starting any work.

We are NOT attempting to prove a theory of everything. Lean verifies derivations;
only experiment verifies axioms about nature. Never claim otherwise.

## Foundational soundness (mechanical, non-negotiable)

- Allowed axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. Never write
  `axiom`. The audit (`scripts/check.sh`) enforces this on every declaration.
- Physics axioms enter as `structure`/`class` definitions plus explicit theorem
  hypotheses. We quantify over models satisfying them; we never postulate.
- No `sorry`/`admit` on `main`. `sorry` is allowed only on work branches as scaffolding
  for stated-but-unproven blueprint nodes.
- No `native_decide`, no `unsafe`, no kernel-bypassing metaprogram tricks.
- `scripts/check.sh` must pass before any merge to `main`.

## Spec/grind separation (the anti-slop core)

- `Atlas/Specs/**` holds frozen definitions and target theorem statements. Proof
  (grind) sessions must never edit them — not to fix a proof, not to "clean up". If a
  spec looks wrong, STOP and escalate to a spec review; do not edit-and-proceed.
- Spec changes require `[spec-review]` in the commit message (enforced by the
  `commit-msg` hook) and re-verification of all dependent witnesses and proofs.
- Weakening a statement to make a proof pass is the formal equivalent of hacking a test
  harness. Never do it. A stuck lemma is decomposed into sub-lemmas, not weakened.
- Every spec cites its authoritative source in its docstring: book or paper, theorem
  number, edition (e.g. "Wald, *General Relativity*, Thm 9.5.1"). Statements are
  reviewed against the source, not against convenience.

## Non-vacuity witnesses

- No spec may be used by downstream proofs until `Atlas/Witnesses/` contains a
  nontrivial model instantiating it (e.g. Minkowski space for spacetime structures)
  plus expected-true and expected-false `example`s exercising the definitions.
- A theorem about structures nothing satisfies is worthless; witnesses are how we know
  our fences enclose something.

## Working style

- Blueprint-driven: every work item is a node in `BLUEPRINT.md`. Claim a node, prove
  it, commit, update the node status. New lemmas discovered mid-proof become new nodes.
- Commit per kernel-verified lemma: small, logical, frequent. The kernel accepting a
  build is the "tests pass" criterion.
- Mathlib conventions throughout: naming, style, docstrings, `autoImplicit` stays off.
  Everything should be upstreamable — analysis/geometry infrastructure toward Mathlib,
  physics content toward physlib.
- Once per clone, run: `git config core.hooksPath .githooks`

## Workflow v2 (2026-08-07, response to external cross-model audit)

- **Remote is the source of truth**: `origin` = github.com/AshishKumar4/Principia.
  Push `main` after every merge; CI (`.github/workflows/ci.yml`) runs the gates on
  every push — enforcement no longer depends on the orchestrator's discipline alone.
- **Cross-model review is mandatory for every spec freeze**: in addition to the
  Fable adversarial review, a Codex (GPT-family, `gpt-5.6-sol`, xhigh reasoning)
  review of the spec surface runs before `[spec-review]` freeze. Two model families
  must independently fail to break a spec. Codex verdicts are audit artifacts.
- **Audit artifacts are committed, not ephemeral**: every adversarial review's
  kernel-probe files land in `audits/probes/<node>/` (reviewers may write ONLY
  there and never to Specs/Proofs/Witnesses), and each review verdict is summarized
  in `audits/reviews/<node>.md`. Reviews that leave no committed evidence did not
  happen, as far as the repo is concerned.
- **Frozen-import closure is mechanical**: `scripts/frozen-imports.txt` is the
  single source of truth consumed by BOTH the commit-msg hook and gate 4
  (`scripts/check_frozen_closure.py`), which computes the transitive Atlas-import
  closure of `Atlas/Specs/**` and fails on any unlisted load-bearing file.
- **External kernel re-verification**: gate 5 runs `lean4checker` when installed
  (install: clone leanprover/lean4checker at the pinned toolchain tag, `lake build`,
  symlink to ~/.local/bin). Until installed the gate is advisory and says so.
- **Status vocabulary** (BLUEPRINT statuses are exactly these): `designed` (dossier
  exists) → `spec` (statement frozen, unproven) → `witnessed` (non-vacuity landed)
  → `proving` → `done` (proven AS the frozen Props + witnessed + merged + gates
  green). Never conflate them in reports. Novelty claims are always phrased
  "to our knowledge, first in any prover" — they rest on dated research sweeps,
  not external verification, until published.

## Autonomous operation (owner's standing orders, 2026-07-08)

The owner is away for several months; the orchestrator session runs the project
autonomously through the whole blueprint. Rules:

- **Guard files** — `scripts/**`, `.githooks/**`, `CLAUDE.md`, `lakefile.toml`,
  `lean-toolchain` — may be modified only by the orchestrator, never by subagents.
  Any subagent diff touching a guard file is rejected wholesale, no matter how good
  the rest of the work is.
- **Model policy**: Fable 5 subagents for hard/planning/sensitive work (spec drafting,
  adversarial spec review vs. sources, proof strategy, audits). Opus 4.8 subagents only
  for well-specified mechanical grinding inside frozen boundaries (proving stated
  lemmas, churn). Never give an Opus grinder spec-writing or guard-adjacent work.
- **Audit before merge**: subagent output is untrusted until independently audited —
  guard-file and spec diff review, `scripts/check.sh` reproduced by the auditor (not
  taken from the worker's report), witnesses re-checked. Enforce the rules; assume
  clever tricks and look for them.
- **PROGRESS.md is the durable journal**: dated entries for every milestone, blocker,
  and decision — written so the owner can catch up months later, and updated before
  any context compaction could lose state. Honest status only; walls are reported as
  walls, with evidence.
- Work on phase branches; merge to main only with gates green and audit complete.

## Toolchain

- Lean `leanprover/lean4:v4.31.0` + Mathlib `v4.31.0`, pinned to match physlib for
  later interop. Do not bump versions without a spec-review-level decision.
- First setup: `~/.elan/bin/lake exe cache get` (fetch Mathlib oleans) before building.
- physlib is intentionally NOT yet a dependency; add it only when a blueprint node
  concretely needs it (expected: Lorentz/SL(2,ℂ) work in Phase 2).
