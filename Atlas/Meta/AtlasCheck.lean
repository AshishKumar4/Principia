import Lean
import Atlas.Proofs.CayleyTheory

/-!
# `#atlas_check` — the hypothesis inventory of an atlas theorem

Applying a no-go theorem to a candidate theory starts with a boring question: what
exactly does the theorem assume? `#atlas_check thm` answers that question mechanically.
It reads the type of `thm` and lists every hypothesis binder, explicit or
instance-implicit, with the binder name, the pretty-printed binder type, and whether
that type is a `Prop`.

The `Prop`-valued rows are the assumptions a candidate has to meet. The other rows are
the data a model must supply before those assumptions can even be stated.

## How it works

`getConstInfo` gives `ConstantInfo.type`. `Lean.Meta.forallTelescope` walks the `∀`
prefix of that type. Each binder is reported with `Lean.Meta.ppExpr` of its type and
`Lean.Meta.isProp` of the same type. Lean core `Meta` API only, as of the pinned
toolchain `leanprover/lean4:v4.31.0`. A binder written without a name, as
`[NormedAddCommGroup H]` is, prints as `_`.

## What it does NOT do

* No semantic matching. It never compares a candidate against a row, and never decides
  whether a model satisfies one.
* No instance synthesis. An `instance` row records that the theorem needs such an
  instance at its call site, not that one exists.
* No unfolding. `forallTelescope` sees the binders as written, so an assumption packed
  into a structure is one row, not its fields: `IsSelfAdjoint A` prints as one row.
* No ranking. The count is a count.

Every claim a report makes is therefore syntactic. Reading applicability out of it stays
a human job, and the printed row is the whole of the evidence.
-/

namespace Atlas.Meta

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

/-- The binders a user of the theorem has to discharge: explicit arguments, and the
instances Lean synthesises at the call site. Implicit and strict-implicit binders are
inferred from the others, so they are indices rather than assumptions. -/
private def isHypothesisBinder : BinderInfo → Bool
  | .default => true
  | .instImplicit => true
  | .implicit => false
  | .strictImplicit => false

private def binderKind : BinderInfo → String
  | .instImplicit => "instance"
  | _ => "explicit"

/-- An instance binder written `[Foo H]` carries no accessible name, only a hygienic
one. Such a binder prints as `_`, which is what it is. -/
private def binderName (name : Name) : String :=
  if name.hasMacroScopes then "_" else toString name

/-- One row per explicit or instance-implicit binder of `declName`'s type, closed by the
row count and how many rows are `Prop`-valued. The module docstring states the exact
limits of what a row claims. -/
def hypothesisInventory (declName : Name) : MetaM MessageData := do
  let info ← getConstInfo declName
  forallTelescope info.type fun binders _ => do
    let mut rows : Array MessageData := #[]
    let mut propRows : Nat := 0
    for binder in binders do
      let decl ← binder.fvarId!.getDecl
      unless isHypothesisBinder decl.binderInfo do continue
      let prop ← isProp decl.type
      if prop then propRows := propRows + 1
      let type ← ppExpr decl.type
      rows := rows.push m!"{binderName decl.userName} : {MessageData.ofFormat type}  \
        [{binderKind decl.binderInfo}, {if prop then "Prop" else "data"}]"
    let header := m!"hypothesis inventory of {declName}"
    let footer := m!"{rows.size} hypothesis binder(s), {propRows} Prop-valued"
    return MessageData.joinSep (header :: rows.toList ++ [footer]) "\n"

/-- `#atlas_check thm` prints the hypothesis inventory of the theorem `thm`: every
explicit and instance-implicit binder of its type, with the pretty-printed binder type
and whether that type is a `Prop`. Syntactic only; see the module docstring. -/
elab "#atlas_check " declId:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverload declId
  logInfo (← liftTermElabM (hypothesisInventory declName))

/-! ### Demo

The forward half of Reed & Simon I, Thm VIII.3, proved in `Atlas.Proofs.CayleyTheory`.
Its inventory is why `#atlas_check` exists. The theorem needs three instances on `H`,
two of them data (`NormedAddCommGroup`, `InnerProductSpace`) and one a `Prop`
(`CompleteSpace`), plus four explicit `Prop` hypotheses. No reader should have to take
that split on trust. -/

#atlas_check OperatorTheory.LinearPMap.range_shift_eq_top_of_isSelfAdjoint

end Atlas.Meta
