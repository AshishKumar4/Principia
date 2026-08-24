import Lean
import Atlas

/-!
# Witness audit

Checks every declaration in `Atlas.Witnesses.*` against the classical axiom trio and
requires the imported witness surface to contain value definitions. It also reports
how many value definitions transitively use `Classical.choice`; that dependency is not
a failure because concrete Mathlib constructions routinely use classical machinery.

Run via: `lake env lean scripts/WitnessAudit.lean`
-/

open Lean

private def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]


private def isValueDefinition : ConstantInfo → Bool
  | .defnInfo _ => true
  | .opaqueInfo _ => true
  | _ => false

open Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  let mut valueDefinitions := 0
  let mut forbidden : Array (Name × Name) := #[]
  let mut choiceDefinitions := 0
  for (name, info) in env.constants.toList do
    let some modIdx := env.getModuleIdxFor? name | continue
    let some modName := env.header.moduleNames[modIdx.toNat]? | continue
    unless (`Atlas.Witnesses).isPrefixOf modName do continue
    checked := checked + 1
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowedAxioms.contains ax do
        forbidden := forbidden.push (name, ax)
    if isValueDefinition info then
      valueDefinitions := valueDefinitions + 1
      if axioms.contains ``Classical.choice then
        choiceDefinitions := choiceDefinitions + 1
  for (name, ax) in forbidden do
    logError m!"forbidden axiom: {name} depends on {ax}"
  unless forbidden.isEmpty do
    throwError "Witness audit FAILED: {forbidden.size} forbidden axiom(s)"
  if valueDefinitions = 0 then
    throwError "Witness audit FAILED: no value definitions found"
  logInfo m!"Witness audit passed ({checked} declarations, {valueDefinitions} value definitions, {choiceDefinitions} using Classical.choice)"
