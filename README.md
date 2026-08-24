> This repository's documentation is edited and maintained by Claude, with me in the
> loop, and presented as-is.

# Principia

An open-source AI-scientist system for physics: a machine-checked physics library,
an experimental-evidence ledger, and a sandboxed laboratory where AI agents build
candidate theories that the Lean kernel and real data judge.

I have always wanted to work on the hardest problems in physics, and the one I keep
coming back to is the unification of quantum theory with general relativity. I am a
systems engineer and ML researcher, not a physicist, so I am approaching this the
way I know how: with machines that cannot lie to me.

This project has three goals that carry equal weight.

**The library.** A machine-checked constraint atlas for quantum gravity: the
theorems that fence in any unification of quantum theory and general relativity
(singularity theorems, Haag's theorem, Weinberg-Witten, Coleman-Mandula, the
Wightman axioms, QFT on curved spacetime), formalized with every physical
assumption as an explicit, named hypothesis. Nobody can formally derive a theory of
everything today, because the required mathematics does not exist yet. What can be
done, and largely has never been done in any proof assistant, is to formalize the
fence around the problem. So far this repository holds (to our knowledge, first in
any prover, pending external verification): Lorentzian causality theory with
Minkowski witnesses, essential self-adjointness and the Reed-Simon VIII.3
criterion, the von Neumann Cayley correspondence, projection-valued measures,
symmetric Fock space, and the canonical commutation relations proven in their Fock
representation. The current summit is the free scalar quantum field proven to
satisfy the Wightman axioms.

**The workflow.** Just as important as the theorems is the machinery that produces
them: a multi-agent pipeline designed so that AI mistakes, hallucinations, and
convention errors cannot survive into the record. The Lean kernel makes wrong
proofs impossible, so all danger lives in the statements. The pipeline attacks
that surface with frozen spec files under mechanical git-hook enforcement, source
dossiers with epistemic tags, adversarial reviews by one model family plus
cross-model reviews by another, kernel probes that arithmetically refute
wrong-convention variants before freezing, mandatory non-vacuity witnesses with
expected-true and expected-false examples, an axiom audit that pins every
declaration to classical mathematics and nothing else, and committed audit
artifacts so the review record is reproducible from Git alone. The honest
threat-model of this workflow, including what it cannot catch, lives in
PROGRESS.md.

**The laboratory.** The monorepo now also holds the first vertical slice of the
system the library exists for: `principia/` (a dependency-free Python layer for
immutable evidence records, candidate-theory manifests, a bubblewrap-sandboxed
evaluator and agent runner, and a discovery loop), `evidence/` (hash-pinned
experimental records with primary-source provenance), and `candidates/` +
`CandidateLab/` (agent-proposed theories as Lean modules). The pilot is real
physics end to end: local realism stated as a Lean candidate over Mathlib's CHSH
inequality, evaluated against the NIST loophole-free Bell test (Shalm et al.,
PRL 115, 250402 (2015)) with the martingale p-value recomputed independently from
the published sufficient statistics — the kernel accepts the candidate's
mathematics, and the data refutes it at p = 2.3×10⁻⁷. Rejection semantics are
strict: a candidate dies only by kernel contradiction, formal countermodel, or a
reproducible statistical mismatch with pinned evidence. Empirically
indistinguishable candidates survive in the archive, whatever their ontology.

## Ground rules and layout

See `CLAUDE.md` for the binding rules, `RESEARCH.md` for the state of the field,
`BLUEPRINT.md` for the dependency DAG of every work item,
`docs/dossiers/horizon-roadmap.md` for the sourced long-horizon map (complete QFT,
GR, strings, and the incompatibility engine, with honest walls), `PROGRESS.md` for
the dated honest journal, `docs/dossiers/` for design-decision records, and
`audits/` for review evidence.

## Building

```sh
git config core.hooksPath .githooks   # once per clone
lake exe cache get                    # fetch Mathlib oleans (Lean v4.31.0)
lake build
scripts/check.sh                      # full verification gate (9 gates)
python3 -m unittest discover -s tests # platform behavior tests (stdlib only)

# evaluate a candidate theory against Lean and pinned evidence
python3 -m principia --repo . evaluate candidates/local-realism \
  --evidence evidence/records/shalm-2015-ch-eberhard.json
```
