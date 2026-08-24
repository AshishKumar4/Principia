# Principia — project rules

> This document is edited and maintained by Claude and presented as-is.
> Binding for every agent and session working in this repository.

## What this project is

Principia is a monorepo building an open-source AI-scientist system for physics. It has
four canonical parts, and nothing else is a source of truth:

- **Formal atlas** (`Atlas/`): machine-checked physics in Lean 4 + Mathlib — the
  constraint theorems that fence in any unification of quantum theory and general
  relativity (singularity theorems, Haag, Weinberg-Witten, Coleman-Mandula, Wightman
  QFT, QFT on curved spacetime), with every physical assumption an explicit, named
  hypothesis. This is the agents' physics library.
- **Evidence ledger** (`evidence/`): immutable, hash-pinned experimental records with
  primary-source provenance, uncertainty models, and statistical gates.
- **Candidate registry** (`candidates/`, `CandidateLab/`): agent-proposed theory
  manifests bound to Lean modules, evaluated against the atlas and the evidence gates.
- **Platform** (`principia/`): the stdlib-only Python orchestration layer — artifact
  schemas, evidence/candidate verification, sandboxed agent execution, evaluation, and
  the discovery loop.

Read `RESEARCH.md` (state of the field), `BLUEPRINT.md` (phased plan and DAG), and
`docs/` before starting any work.

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
- **Dependency integrity is mechanical**: gate 4 (`scripts/check_frozen_closure.py`)
  enforces three manifests — the transitive Atlas-import closure of `Atlas/Specs/**`
  may leave Specs only through `scripts/frozen-imports.txt` (also consumed by the
  commit-msg hook); the full witness-reachable closure must equal
  `scripts/witness-closure.txt` exactly; and frozen entries must stay reachable
  (staleness fails the gate).
- **External kernel re-verification is mandatory**: gate 5 runs `lean4checker` and
  FAILS when it is missing. Install: clone leanprover/lean4checker at commit
  `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` (builds clean on the v4.31.0 toolchain),
  `lake build`, symlink the binary to `~/.local/bin/lean4checker`. CI installs the
  same pinned commit.
- **Status vocabulary** (BLUEPRINT statuses are exactly these): `designed` (dossier
  exists) → `spec` (statement frozen, unproven) → `witnessed` (non-vacuity landed)
  → `proving` → `done` (proven AS the frozen Props + witnessed + merged + gates
  green). Never conflate them in reports. Novelty claims are always phrased
  "to our knowledge, first in any prover" — they rest on dated research sweeps,
  not external verification, until published.

## Workflow v3 (2026-08-21, monorepo + enforcement completion)

- **Ten gates** (`scripts/check.sh`, mirrored exactly by CI which calls the same
  script): 1 `lake build` of Atlas plus every committed CandidateLab module; 2
  Atlas axiom audit; 3 forbidden-token scan over Atlas and CandidateLab; 4
  frozen-spec + witness dependency integrity; 5 lean4checker (mandatory); 6 Atlas
  orphan-source detector (`scripts/check_no_orphans.py` — every
  `Atlas/**/*.lean` must be reachable from `Atlas.lean`); 7 citation-debt manifest
  (`scripts/check_citation_flags.py` + `scripts/citation-debt.txt` — unresolved
  "quoted from memory"/"not (re-)verified against a copy" flags are tracked
  line-hashes, added or cleared only in reviewed changes); 8 witness audit
  (`scripts/WitnessAudit.lean` — classical-trio check plus
  concrete-construction reporting over `Atlas.Witnesses.*`); 9 committed probe
  recompilation (`scripts/check_probes.py` — every `audits/probes/**/*.lean` must
  still compile); 10 sandboxed formal evaluation of every committed candidate
  (compile, generated checker, and classical-trio audit through `principia`).
- **Platform tests are a gate**: `python3 -m unittest discover -s tests` runs in CI
  and in the pre-push hook alongside `scripts/check.sh`.
- **Spec-review evidence is linked server-side**: CI runs
  `scripts/check_spec_review_evidence.py` over the pushed range — changes to the
  frozen surface require a `[spec-review]` commit AND a touched
  `audits/reviews/<node>.md` in the same range.
- **Hooks**: `pre-commit` (token scan), `commit-msg` (spec-review tag), and
  `pre-push` (full gates + tests over the outgoing tree). Hooks remain client-side
  convenience; CI + branch protection are the enforcement. `.github/CODEOWNERS` and
  `.github/branch-protection.json` are the committed protection policy; the live
  GitHub setting must match the JSON (owner action when it drifts).
- **Platform rules**: Lean is the semantic source of truth — JSON manifests carry
  identity/provenance/config and reference Lean symbols, never restate theorem
  content. `principia/` is Python >= 3.11 standard library only. Evidence records are
  immutable and hash-pinned; corrections create new versions, never edits in place.
  Candidate theories enter as structures/hypotheses with concrete witnesses — never
  Lean `axiom`s — and are evaluated by kernel + evidence gates, not by reviewer
  opinion. An agent whose candidate is under evaluation may never modify the atlas,
  the gates, or the evidence; repairs to canonical files go through a separate
  reviewed lane and trigger re-evaluation of affected candidates.
- **Rejection semantics**: a candidate is rejected only by kernel contradiction,
  formal countermodel, or reproducible statistical mismatch with pinned evidence
  under its documented assumptions. Empirically indistinguishable candidates are
  archived as survivors, never deleted for unfamiliarity.

## Autonomous operation (owner's standing orders, 2026-07-08)

The owner is away for several months; the orchestrator session runs the project
autonomously through the whole blueprint. Rules:

- **Guard files** — `scripts/**`, `.githooks/**`, `.github/**`, `CLAUDE.md`,
  `lakefile.toml`, `lean-toolchain` — may be modified only by the orchestrator, never
  by subagents.
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
