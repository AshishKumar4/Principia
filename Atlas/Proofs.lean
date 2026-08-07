import Atlas.Proofs.CausalLemmas
import Atlas.Proofs.BoundedGenerator
import Atlas.Proofs.DeficiencyTheory
import Atlas.Proofs.CayleyTheory
import Atlas.Proofs.HilbertTensorMaps
import Atlas.Proofs.HilbertTensorBasis
import Atlas.Proofs.PiTensorSemilinear
import Atlas.Proofs.PiTensorInner
import Atlas.Proofs.FockBridge
import Atlas.Proofs.CCRTheory

/-!
# Atlas.Proofs — proof developments

Proofs of blueprint targets. Statements consumed here live frozen in `Atlas.Specs`;
a stuck lemma is decomposed into sub-lemmas (new blueprint nodes), never weakened.

Populated from Phase 1 of BLUEPRINT.md onward.
-/
