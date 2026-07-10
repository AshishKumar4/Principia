import Atlas.Witnesses.Minkowski
import Atlas.Witnesses.MinkowskiCausal
import Atlas.Witnesses.UnitaryGroups
import Atlas.Witnesses.SymmetricOperators
import Atlas.Witnesses.CayleyScalar

/-!
# Atlas.Witnesses — non-vacuity witnesses

Every spec in `Atlas.Specs` must be instantiated here by a nontrivial model (e.g.
Minkowski space for spacetime structures) together with expected-true and
expected-false `example`s, before any downstream proof may consume it (see CLAUDE.md).

Populated from Phase 1 of BLUEPRINT.md onward.
-/
