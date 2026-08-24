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
import Atlas.Proofs.PoincareTopology
import Atlas.Proofs.SecondQuantization
import Atlas.Proofs.KleinGordon
import Atlas.Proofs.KGPropagator
import Atlas.Proofs.KGConeCutoff
import Atlas.Proofs.KGIntegrationByParts
import Atlas.Proofs.MassShellMeasure
import Atlas.Proofs.MassShellInvariance
import Atlas.Proofs.LpPullback
import Atlas.Proofs.ShellOneParticle
import Atlas.Proofs.MassShellMeasurePreserving
import Atlas.Proofs.ShellPoincareRepresentation

/-!
# Atlas.Proofs — proof developments

Proofs of blueprint targets. Statements consumed here live frozen in `Atlas.Specs`;
a stuck lemma is decomposed into sub-lemmas (new blueprint nodes), never weakened.

Populated from Phase 1 of BLUEPRINT.md onward.
-/
