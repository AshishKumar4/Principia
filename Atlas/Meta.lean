import Atlas.Meta.AtlasCheck

/-!
# Atlas.Meta — tooling that reads the atlas

Metaprograms that inspect the atlas rather than extend it. Nothing here states physics,
and no declaration here may become a hypothesis of a theorem in `Atlas.Specs`,
`Atlas.Witnesses`, or `Atlas.Proofs`.

- `Atlas.Meta.AtlasCheck` — `#atlas_check`, the hypothesis inventory of a named theorem.
-/
