> This repository's documentation is edited and maintained by Claude, with me in the
> loop, and presented as-is.

# QG Constraint Atlas

I have always wanted to work on some of the hardest problems in physics, and the one I
keep coming back to is the unification of quantum theory with general relativity. I am
a systems engineer and ML researcher, not a physicist, so I am approaching this the way
I know how: with machines that cannot lie to me.

This project builds a machine-checked constraint atlas for quantum gravity in Lean 4.
The honest framing matters: nobody can formally derive a theory of everything today,
because the required mathematics does not exist yet (no interacting 4D QFT has ever
been constructed, and the Yang-Mills mass gap is a Millennium Prize problem). What CAN
be done, and has never been done in any proof assistant, is to formalize the fence
around the problem: the no-go theorems and structural results that any candidate
unification must evade. Penrose's singularity theorem. Haag's theorem. Weinberg-Witten.
Coleman-Mandula. The Wightman axioms themselves, with QFT on curved spacetime as the
one place where the two theories rigorously coexist.

Every physical assumption becomes an explicit, named hypothesis in Lean. The endgame is
an atlas where "which axiom does string theory drop, and which does loop quantum
gravity drop" is a formal query instead of a philosophy debate.

## Ground rules

The anti-slop machinery is the point, so it is mechanical, not aspirational. Proofs are
verified by the Lean kernel and re-checkable externally. No axioms beyond Mathlib's
classical trio, no `sorry` on main, enforced by `scripts/check.sh` on every merge.
Definitions and theorem statements live in frozen spec files that proof sessions cannot
touch, every spec cites its textbook source, and no definition may be used until a
nontrivial witness proves it is not vacuous. See `CLAUDE.md` for the binding rules,
`RESEARCH.md` for the state of the field, and `BLUEPRINT.md` for the plan.

## Building

```sh
git config core.hooksPath .githooks   # once per clone
lake exe cache get                    # fetch Mathlib oleans (Lean v4.31.0)
lake build
scripts/check.sh                      # full verification gate
```
