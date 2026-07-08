import Lean
import Atlas

/-!
# Axiom audit

Walks every declaration living in an `Atlas.*` module and collects its transitive
axiom dependencies. Fails unless they are within Mathlib's classical trio
(`propext`, `Classical.choice`, `Quot.sound`). `sorry` surfaces here as `sorryAx`,
so this also catches any sorry that slipped past the token scan.

Run via: `lake env lean scripts/AxiomAudit.lean`
-/

open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  let mut violations : Array (Name × Name) := #[]
  for (name, _) in env.constants.toList do
    let some modIdx := env.getModuleIdxFor? name | continue
    let some modName := env.header.moduleNames[modIdx.toNat]? | continue
    unless (`Atlas).isPrefixOf modName do continue
    checked := checked + 1
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowedAxioms.contains ax do
        violations := violations.push (name, ax)
  for (name, ax) in violations do
    logError m!"forbidden axiom: {name} depends on {ax}"
  unless violations.isEmpty do
    throwError "Axiom audit FAILED: {violations.size} violation(s)"
  logInfo m!"Axiom audit passed ({checked} Atlas declarations checked)"
