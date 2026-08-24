import Atlas.Specs
import Atlas.Witnesses
import Atlas.Proofs
import Atlas.Meta

/-!
# QG Constraint Atlas — root module

Imports the whole atlas. Layout:
- `Atlas.Specs` — frozen definitions and target theorem statements (spec-review only)
- `Atlas.Witnesses` — non-vacuity witnesses and sanity examples for every spec
- `Atlas.Proofs` — proof developments toward blueprint targets
- `Atlas.Meta` — audit metaprograms (`#atlas_check` hypothesis inventories)
-/
