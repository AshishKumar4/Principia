"""Behaviour tests for `principia.models`.

The models are a trust boundary: everything downstream assumes that an instance which
exists is well formed. So the tests drive the public surface only — `from_dict`,
`to_dict`, direct construction and `dataclasses.replace` — and assert three things.
Round-trips lose nothing. Malformed input fails with a message naming the field. And
the checks the models deliberately do *not* own, Lean names and path containment, stay
loadable so that `verify_candidate` and `verify_evidence` can report them.
"""

from __future__ import annotations

import dataclasses
import unittest
from types import MappingProxyType

from principia.models import (
    SCHEMA_VERSION,
    AgentSpec,
    ArtifactError,
    Assumption,
    CandidateManifest,
    ClaimRef,
    CommandResult,
    DatasetRef,
    EvaluationResult,
    EvaluationStatus,
    EvidenceGate,
    EvidencePrediction,
    EvidenceRecord,
    ExceptionRecord,
    LeanSpec,
    Parameter,
    SourceRef,
    validate_artifact_id,
    validate_evaluator_id,
    validate_sha256_hex,
    validate_timestamp,
)

_TIMESTAMP = "2026-08-23T12:00:00.000000Z"
_DIGEST = "3b1f2a" + "0" * 58
_NAMESPACE = "CandidateLab.Demo.Theory"


def source() -> dict:
    return {
        "title": "Experimental Test of Bell's Inequalities Using Time-Varying Analyzers",
        "authors": ["Alain Aspect", "Jean Dalibard", "Gerard Roger"],
        "url": "https://doi.org/10.1103/PhysRevLett.49.1804",
        "doi": "10.1103/PhysRevLett.49.1804",
        "published": "1982-12-20",
    }


def dataset() -> dict:
    return {
        "url": "https://example.org/chsh/coincidences.json",
        "sha256": _DIGEST,
        "license": "CC0-1.0",
        "format": "application/json",
        "local_path": "evidence/data/chsh.json",
    }


def gate() -> dict:
    return {
        "evaluator": "principia.evaluators.bell_ch",
        "required_claims": ["chsh.violation"],
        "inputs": {"window_ns": 100, "settings": [{"angle": 0.0}, {"angle": 1.5}]},
        "decision": {"alpha": 0.05},
    }


def evidence() -> dict:
    return {
        "schema_version": SCHEMA_VERSION,
        "id": "bell.chsh.test",
        "version": 1,
        "title": "CHSH violation, committed sufficient statistics",
        "source": source(),
        "dataset": dataset(),
        "gate": gate(),
    }


def lean() -> dict:
    return {
        "module": _NAMESPACE,
        "entrypoint": "CandidateLab/Demo/Theory.lean",
        "namespace": _NAMESPACE,
        "witnesses": [f"{_NAMESPACE}.demoWitness"],
        "claims": [f"{_NAMESPACE}.demo_bound"],
    }


def candidate() -> dict:
    return {
        "schema_version": SCHEMA_VERSION,
        "id": "demo-theory",
        "version": 2,
        "parent": "demo-theory.v1",
        "title": "Demo candidate theory",
        "lean": lean(),
        "assumptions": [
            {"id": "locality", "lean_symbol": f"{_NAMESPACE}.Locality", "source": source()}
        ],
        "claims": [{"id": "demo-bound", "lean_symbol": f"{_NAMESPACE}.demo_bound"}],
        "parameters": [{"id": "alpha", "value": 0.05, "unit": None}],
        "exceptions": [{"id": "detector.efficiency", "description": "no fair sampling"}],
        "evidence": [{"id": "bell.chsh.test", "prediction": {"chsh": 2.7}}],
    }


def result() -> dict:
    return {
        "schema_version": SCHEMA_VERSION,
        "candidate_id": "demo-theory",
        "evidence_id": "bell.chsh.test",
        "status": "pass",
        "summary": "CHSH S = 2.70 exceeds the local bound",
        "metrics": {"chsh": 2.7, "trials": 4000, "violated": True, "note": "recomputed", "p": None},
        "artifacts": {"checker": _DIGEST},
        "timestamp": _TIMESTAMP,
    }


def spec() -> dict:
    return {
        "command": ["python3", "-I", "-c", "pass"],
        "network": False,
        "timeout_seconds": 30.0,
        "env_allowlist": ["PATH", "LANG"],
        "read_only_binds": ["/usr/lib", "/opt/elan"],
    }


def command() -> dict:
    return {
        "command": ["/usr/bin/env", "-i", "-i"],
        "exit_code": 0,
        "signal": None,
        "timed_out": False,
        "stdout": "",
        "stderr": "boom\n",
        "stdout_sha256": _DIGEST,
        "stderr_sha256": _DIGEST,
        "request_sha256": _DIGEST,
        "duration_seconds": 0.5,
        "timestamp": _TIMESTAMP,
    }


#: Every public model with a canonical document: one place to add the next one.
MODELS: tuple[tuple[type, dict], ...] = (
    (SourceRef, source()),
    (DatasetRef, dataset()),
    (LeanSpec, lean()),
    (EvidenceGate, gate()),
    (EvidenceRecord, evidence()),
    (Assumption, candidate()["assumptions"][0]),
    (ClaimRef, candidate()["claims"][0]),
    (Parameter, candidate()["parameters"][0]),
    (ExceptionRecord, candidate()["exceptions"][0]),
    (EvidencePrediction, candidate()["evidence"][0]),
    (CandidateManifest, candidate()),
    (EvaluationResult, result()),
    (AgentSpec, spec()),
    (CommandResult, command()),
)


class ModelCase(unittest.TestCase):
    def rejects(self, model: type, document: dict, *fragments: str) -> str:
        """Assert *document* is rejected, and return the message for further checks."""
        with self.assertRaises(ArtifactError) as caught:
            model.from_dict(document)
        message = str(caught.exception)
        for fragment in fragments:
            self.assertIn(fragment, message)
        return message

    def altered(self, document: dict, **overrides: object) -> dict:
        return {**document, **overrides}


class RoundTripTest(ModelCase):
    def test_every_model_round_trips_through_json_and_back(self) -> None:
        for model, document in MODELS:
            with self.subTest(model=model.__name__):
                loaded = model.from_dict(document)
                self.assertEqual(document, loaded.to_dict())
                self.assertEqual(loaded, model.from_dict(loaded.to_dict()))

    def test_to_dict_emits_exactly_the_declared_fields(self) -> None:
        for model, document in MODELS:
            with self.subTest(model=model.__name__):
                names = tuple(field.name for field in dataclasses.fields(model))
                self.assertEqual(list(names), list(model.from_dict(document).to_dict()))
                self.assertEqual((), tuple(set(model._NULLABLE) - set(names)))

    def test_to_dict_is_plain_json_data(self) -> None:
        document = EvidenceRecord.from_dict(evidence()).to_dict()

        self.assertIsInstance(document["gate"]["inputs"], dict)
        self.assertIsInstance(document["gate"]["inputs"]["settings"], list)
        self.assertIsInstance(document["gate"]["required_claims"], list)
        self.assertEqual("pass", EvaluationResult.from_dict(result()).to_dict()["status"])

    def test_to_dict_hands_back_a_detached_copy(self) -> None:
        record = EvidenceRecord.from_dict(evidence())
        document = record.to_dict()
        document["gate"]["inputs"]["window_ns"] = 999

        self.assertEqual(100, record.gate.inputs["window_ns"])

    def test_the_source_document_is_copied_not_captured(self) -> None:
        document = evidence()
        record = EvidenceRecord.from_dict(document)
        document["gate"]["inputs"]["window_ns"] = 999
        document["gate"]["required_claims"].append("other.claim")

        self.assertEqual(100, record.gate.inputs["window_ns"])
        self.assertEqual(("chsh.violation",), record.gate.required_claims)

    def test_models_accept_already_built_children(self) -> None:
        built = EvidenceRecord(
            schema_version=SCHEMA_VERSION,
            id="bell.chsh.test",
            version=1,
            title="CHSH violation, committed sufficient statistics",
            source=SourceRef.from_dict(source()),
            dataset=DatasetRef.from_dict(dataset()),
            gate=EvidenceGate.from_dict(gate()),
        )

        self.assertEqual(EvidenceRecord.from_dict(evidence()), built)

    def test_sequences_and_mappings_are_normalised_on_construction(self) -> None:
        built = AgentSpec(
            command=["python3", "-I", "-c", "pass"],
            network=False,
            timeout_seconds=30,
            env_allowlist=["PATH", "LANG"],
            read_only_binds=["/usr/lib", "/opt/elan"],
        )

        self.assertEqual(("python3", "-I", "-c", "pass"), built.command)
        self.assertIsInstance(built.timeout_seconds, float)
        self.assertEqual(AgentSpec.from_dict(spec()), built)


class StrictSchemaTest(ModelCase):
    def test_unknown_key_is_rejected_with_the_allowed_keys(self) -> None:
        message = self.rejects(
            DatasetRef, self.altered(dataset(), bytes=32), "DatasetRef", "unknown key(s) bytes"
        )

        self.assertIn("allowed keys are url, sha256, license, format, local_path", message)

    def test_unknown_key_is_rejected_inside_a_nested_object(self) -> None:
        document = evidence()
        document["dataset"]["upstream"] = []

        self.rejects(EvidenceRecord, document, "DatasetRef", "unknown key(s) upstream")

    def test_every_unknown_key_is_reported_at_once(self) -> None:
        self.rejects(
            ClaimRef,
            self.altered(candidate()["claims"][0], statement="prose", weight=1),
            "unknown key(s) statement, weight",
        )

    def test_missing_required_key_is_named(self) -> None:
        document = evidence()
        del document["gate"]

        self.rejects(EvidenceRecord, document, "EvidenceRecord", "missing required key(s) gate")

    def test_nullable_key_may_be_absent_or_null(self) -> None:
        absent = dataset()
        del absent["local_path"]
        nulled = self.altered(dataset(), local_path=None)

        self.assertIsNone(DatasetRef.from_dict(absent).local_path)
        self.assertEqual(DatasetRef.from_dict(nulled), DatasetRef.from_dict(absent))

    def test_non_object_input_is_rejected(self) -> None:
        for document in ([], "record", 7, None):
            with self.subTest(document=document):
                with self.assertRaises(ArtifactError) as caught:
                    EvidenceRecord.from_dict(document)
                self.assertIn("EvidenceRecord: expected a JSON object", str(caught.exception))

    def test_non_string_keys_are_rejected(self) -> None:
        self.rejects(ClaimRef, {"id": "x", "lean_symbol": "A.b", 3: "junk"}, "string object keys")

    def test_nested_array_entry_reports_its_position(self) -> None:
        document = candidate()
        document["claims"] = [candidate()["claims"][0], "not-an-object"]

        self.rejects(CandidateManifest, document, "claims[1]", "expected a ClaimRef")

    def test_wrong_container_kind_is_rejected(self) -> None:
        self.rejects(LeanSpec, self.altered(lean(), witnesses="A.b"), "expected an array of strings")
        self.rejects(EvidenceGate, self.altered(gate(), inputs=[]), "expected a JSON object")
        self.rejects(EvidenceRecord, self.altered(evidence(), source=[source()]), "expected a SourceRef")


class IdentityTest(ModelCase):
    def test_artifact_ids_follow_the_contract_pattern(self) -> None:
        for good in ("a", "0", "bell.chsh.test", "demo-theory", "x" * 128):
            with self.subTest(id=good):
                self.assertEqual(good, validate_artifact_id(good))
        for bad in ("", "Bell", "under_score", ".leading", "-lead", "x" * 129, "a b", 7, None):
            with self.subTest(id=bad):
                with self.assertRaises(ArtifactError) as caught:
                    validate_artifact_id(bad)
                self.assertIn("[a-z0-9][a-z0-9.-]{0,127}", str(caught.exception))

    def test_a_bad_id_names_its_own_field(self) -> None:
        self.rejects(EvidenceRecord, self.altered(evidence(), id="Bell"), "EvidenceRecord.id")
        self.rejects(
            EvaluationResult, self.altered(result(), candidate_id="Bad"), "EvaluationResult.candidate_id"
        )

    def test_evaluator_ids_are_exempt_from_the_artifact_id_pattern(self) -> None:
        underscored = "principia.evaluators.bell_ch"

        self.assertEqual(underscored, validate_evaluator_id(underscored))
        self.assertEqual(underscored, EvidenceGate.from_dict(gate()).evaluator)
        with self.assertRaises(ArtifactError):
            validate_artifact_id(underscored)

    def test_evaluator_ids_must_be_dotted_lowercase_identifiers(self) -> None:
        for bad in ("", "Bell", "principia.evaluators.", ".bell", "bell ch", "bell-ch", "9bell", "a..b"):
            with self.subTest(evaluator=bad):
                self.rejects(EvidenceGate, self.altered(gate(), evaluator=bad), "EvidenceGate.evaluator")

    def test_required_claims_are_candidate_claim_ids(self) -> None:
        self.rejects(EvidenceGate, self.altered(gate(), required_claims=["Chsh"]), "required_claims[0]")
        self.rejects(
            EvidenceGate,
            self.altered(gate(), required_claims=["a.b", "a.b"]),
            "required_claims",
            "unique",
        )
        self.assertEqual((), EvidenceGate.from_dict(self.altered(gate(), required_claims=[])).required_claims)

    def test_digests_must_be_lowercase_hexadecimal(self) -> None:
        self.assertEqual(_DIGEST, validate_sha256_hex(_DIGEST))
        for bad in ("", _DIGEST.upper(), _DIGEST[:-1], f"{_DIGEST}0", "zz" + _DIGEST[2:], None):
            with self.subTest(digest=bad):
                self.rejects(DatasetRef, self.altered(dataset(), sha256=bad), "DatasetRef.sha256")

    def test_artifact_digest_map_is_checked_per_entry(self) -> None:
        self.rejects(EvaluationResult, self.altered(result(), artifacts={"checker": "nope"}), "artifacts.checker")
        self.rejects(EvaluationResult, self.altered(result(), artifacts={"": _DIGEST}), "non-empty string keys")

    def test_source_must_carry_a_real_publication(self) -> None:
        self.rejects(SourceRef, self.altered(source(), authors=[]), "at least 1")
        self.rejects(SourceRef, self.altered(source(), authors=["  "]), "authors[0]")
        self.rejects(SourceRef, self.altered(source(), url="ftp://example.org/x"), "https")
        self.rejects(SourceRef, self.altered(source(), url="doi.org/10.1/x"), "https")
        self.rejects(SourceRef, self.altered(source(), doi="https://doi.org/10.1/x"), "bare DOI")
        self.rejects(SourceRef, self.altered(source(), published="1982-13-45"), "calendar date")
        self.rejects(SourceRef, self.altered(source(), published="1982"), "YYYY-MM-DD")
        self.assertIsNone(SourceRef.from_dict(self.altered(source(), doi=None)).doi)


class ScalarTest(ModelCase):
    def test_a_boolean_is_not_an_integer(self) -> None:
        self.rejects(EvidenceRecord, self.altered(evidence(), version=True), "EvidenceRecord.version")
        self.rejects(EvidenceRecord, self.altered(evidence(), schema_version=True), "schema_version")
        self.rejects(CommandResult, self.altered(command(), exit_code=True), "CommandResult.exit_code")
        self.rejects(AgentSpec, self.altered(spec(), timeout_seconds=True), "expected a number")

    def test_a_boolean_is_a_legitimate_json_scalar(self) -> None:
        self.assertIs(True, EvaluationResult.from_dict(result()).metrics["violated"])
        self.assertIs(False, Parameter.from_dict({"id": "flag", "value": False, "unit": None}).value)

    def test_only_the_current_schema_version_is_accepted(self) -> None:
        for bad in (0, SCHEMA_VERSION + 1, "1", 1.0):
            with self.subTest(version=bad):
                self.rejects(CandidateManifest, self.altered(candidate(), schema_version=bad), "schema_version")

    def test_versions_start_at_one(self) -> None:
        self.rejects(CandidateManifest, self.altered(candidate(), version=0), "expected an integer >= 1")

    def test_timeout_must_be_a_positive_finite_number(self) -> None:
        for bad in (0, -1, float("inf"), float("nan"), "30"):
            with self.subTest(timeout=bad):
                self.rejects(AgentSpec, self.altered(spec(), timeout_seconds=bad), "timeout_seconds")
        self.assertEqual(0.5, AgentSpec.from_dict(self.altered(spec(), timeout_seconds=0.5)).timeout_seconds)

    def test_metrics_hold_scalars_only(self) -> None:
        self.rejects(EvaluationResult, self.altered(result(), metrics={"m": {"nested": 1}}), "metrics.m")
        self.rejects(EvaluationResult, self.altered(result(), metrics={"m": [1]}), "metrics.m")
        self.rejects(EvaluationResult, self.altered(result(), metrics={"m": float("nan")}), "finite")

    def test_evaluator_payloads_take_any_json_depth_but_no_infinities(self) -> None:
        deep = {"a": [{"b": {"c": [1, 2.5, "x", True, None]}}]}
        loaded = EvidenceGate.from_dict(self.altered(gate(), inputs=deep))

        self.assertEqual((1, 2.5, "x", True, None), loaded.inputs["a"][0]["b"]["c"])
        self.rejects(EvidenceGate, self.altered(gate(), inputs={"a": float("inf")}), "finite")
        self.rejects(EvidenceGate, self.altered(gate(), inputs={"a": {1: "x"}}), "string object keys")
        self.rejects(EvidenceGate, self.altered(gate(), inputs={"a": object()}), "expected JSON data")

    def test_prose_fields_reject_blank_strings(self) -> None:
        for blank in ("", "   ", "\n"):
            with self.subTest(value=blank):
                self.rejects(EvidenceRecord, self.altered(evidence(), title=blank), "EvidenceRecord.title")
                self.rejects(EvaluationResult, self.altered(result(), summary=blank), "summary")


class TimestampTest(ModelCase):
    def test_utc_timestamps_are_accepted_and_kept_verbatim(self) -> None:
        for good in (
            "2026-08-23T12:00:00.000000Z",
            "2026-08-23T12:00:00Z",
            "2026-08-23T12:00:00+00:00",
            "2026-08-23 12:00:00+00:00",
        ):
            with self.subTest(timestamp=good):
                self.assertEqual(good, validate_timestamp(good))
                self.assertEqual(good, EvaluationResult.from_dict(self.altered(result(), timestamp=good)).timestamp)

    def test_naive_and_offset_timestamps_are_rejected(self) -> None:
        for bad in ("2026-08-23T12:00:00", "2026-08-23", "2026-08-23T12:00:00+05:30", "yesterday", "", 7):
            with self.subTest(timestamp=bad):
                self.rejects(EvaluationResult, self.altered(result(), timestamp=bad), "timestamp")

    def test_the_models_never_invent_a_timestamp(self) -> None:
        document = result()
        del document["timestamp"]

        self.rejects(EvaluationResult, document, "missing required key(s) timestamp")


class ImmutabilityTest(ModelCase):
    def test_fields_cannot_be_reassigned(self) -> None:
        record = EvidenceRecord.from_dict(evidence())

        with self.assertRaises(dataclasses.FrozenInstanceError):
            record.id = "other"

    def test_nested_payloads_are_read_only(self) -> None:
        loaded = EvidenceGate.from_dict(gate())

        self.assertIsInstance(loaded.inputs, MappingProxyType)
        with self.assertRaises(TypeError):
            loaded.inputs["window_ns"] = 1
        with self.assertRaises(TypeError):
            loaded.inputs["settings"][0]["angle"] = 1.0

    def test_replace_revalidates_the_whole_object(self) -> None:
        loaded = EvaluationResult.from_dict(result())

        self.assertEqual(EvaluationStatus.FAIL, dataclasses.replace(loaded, status="fail").status)
        with self.assertRaises(ArtifactError):
            dataclasses.replace(loaded, timestamp="2026-08-23T12:00:00")

    def test_direct_construction_is_validated_too(self) -> None:
        with self.assertRaises(ArtifactError) as caught:
            ClaimRef(id="Bad", lean_symbol="A.b")

        self.assertIn("ClaimRef.id", str(caught.exception))


class StatusTest(ModelCase):
    def test_the_five_contract_values(self) -> None:
        self.assertEqual(
            ["pass", "fail", "inconclusive", "not_applicable", "error"],
            [status.value for status in EvaluationStatus],
        )

    def test_status_accepts_a_member_or_its_value(self) -> None:
        from_value = EvaluationResult.from_dict(self.altered(result(), status="inconclusive"))
        from_member = EvaluationResult.from_dict(self.altered(result(), status=EvaluationStatus.INCONCLUSIVE))

        self.assertEqual(from_member, from_value)
        self.assertIs(EvaluationStatus.INCONCLUSIVE, from_value.status)
        self.assertEqual("inconclusive", from_value.to_dict()["status"])

    def test_an_unknown_status_lists_the_allowed_ones(self) -> None:
        message = self.rejects(EvaluationResult, self.altered(result(), status="passed"), "status")

        self.assertIn("pass, fail, inconclusive, not_applicable, error", message)


class CommandResultTest(ModelCase):
    def test_exactly_one_of_exit_code_and_signal_is_set(self) -> None:
        killed = CommandResult.from_dict(self.altered(command(), exit_code=None, signal=9))

        self.assertEqual(9, killed.signal)
        self.rejects(CommandResult, self.altered(command(), signal=9), "exactly one of")
        self.rejects(CommandResult, self.altered(command(), exit_code=None), "exactly one of")

    def test_a_zero_exit_code_counts_as_present(self) -> None:
        self.assertEqual(0, CommandResult.from_dict(command()).exit_code)

    def test_exit_codes_and_signals_stay_in_range(self) -> None:
        self.rejects(CommandResult, self.altered(command(), exit_code=256), "expected an integer <= 255")
        self.rejects(CommandResult, self.altered(command(), exit_code=-1), "expected an integer >= 0")
        self.rejects(CommandResult, self.altered(command(), exit_code=None, signal=0), "expected an integer >= 1")

    def test_argv_may_repeat_a_word_but_never_be_empty(self) -> None:
        self.assertEqual(("/usr/bin/env", "-i", "-i"), CommandResult.from_dict(command()).command)
        self.rejects(CommandResult, self.altered(command(), command=[]), "at least 1")
        self.rejects(CommandResult, self.altered(command(), command=["ls", ""]), "command[1]")

    def test_captured_output_may_be_empty_but_must_be_text(self) -> None:
        self.assertEqual("", CommandResult.from_dict(command()).stdout)
        self.rejects(CommandResult, self.altered(command(), stdout=None), "expected a string")

    def test_duration_is_a_non_negative_finite_number(self) -> None:
        self.assertEqual(0.0, CommandResult.from_dict(self.altered(command(), duration_seconds=0)).duration_seconds)
        self.rejects(CommandResult, self.altered(command(), duration_seconds=-0.1), "duration_seconds")


class AgentSpecTest(ModelCase):
    def test_read_only_binds_are_absolute_host_paths(self) -> None:
        self.rejects(AgentSpec, self.altered(spec(), read_only_binds=["opt/elan"]), "absolute path")
        self.rejects(AgentSpec, self.altered(spec(), read_only_binds=["/opt/../etc"]), "'..'")
        self.rejects(AgentSpec, self.altered(spec(), read_only_binds=["/opt/elan/"]), "normalised")
        self.rejects(AgentSpec, self.altered(spec(), read_only_binds=["/opt", "/opt"]), "unique")
        self.assertEqual((), AgentSpec.from_dict(self.altered(spec(), read_only_binds=[])).read_only_binds)

    def test_environment_names_are_checked_but_not_looked_up(self) -> None:
        loaded = AgentSpec.from_dict(self.altered(spec(), env_allowlist=["PRINCIPIA_NOT_IN_THIS_PROCESS"]))

        self.assertEqual(("PRINCIPIA_NOT_IN_THIS_PROCESS",), loaded.env_allowlist)
        self.rejects(AgentSpec, self.altered(spec(), env_allowlist=["9BAD"]), "env_allowlist[0]")
        self.rejects(AgentSpec, self.altered(spec(), env_allowlist=["A=B"]), "env_allowlist[0]")

    def test_network_is_an_explicit_boolean(self) -> None:
        self.rejects(AgentSpec, self.altered(spec(), network="false"), "expected a boolean")
        self.rejects(AgentSpec, self.altered(spec(), network=0), "expected a boolean")


class OwnershipBoundaryTest(ModelCase):
    """What the models deliberately leave to `verify_candidate` and `verify_evidence`.

    A record naming an escaping path or an illegal Lean name must still load, or the
    verifiers could never report it and a bad artifact would be unreadable instead of
    diagnosable.
    """

    def test_escaping_dataset_paths_load_and_stay_verbatim(self) -> None:
        for path in ("../outside/escape.json", "/etc/hostname", "a/./b.json"):
            with self.subTest(path=path):
                self.assertEqual(path, DatasetRef.from_dict(self.altered(dataset(), local_path=path)).local_path)

    def test_a_dataset_with_neither_path_nor_url_loads(self) -> None:
        loaded = DatasetRef.from_dict(self.altered(dataset(), local_path=None, url=None))

        self.assertIsNone(loaded.local_path)
        self.assertIsNone(loaded.url)

    def test_illegal_lean_names_and_paths_load(self) -> None:
        broken = {
            "module": "CandidateLab..Demo",
            "entrypoint": "/etc/passwd",
            "namespace": "1Bad",
            "witnesses": ["axiom", "axiom"],
            "claims": ["not a name"],
        }

        loaded = LeanSpec.from_dict(broken)

        self.assertEqual("1Bad", loaded.namespace)
        self.assertEqual(("axiom", "axiom"), loaded.witnesses)

    def test_degenerate_manifests_load_so_verification_can_report_them(self) -> None:
        manifest = CandidateManifest.from_dict(candidate())
        stripped = dataclasses.replace(
            manifest, lean=dataclasses.replace(manifest.lean, witnesses=(), claims=())
        )
        blank = dataclasses.replace(manifest.evidence[0], prediction={})

        self.assertEqual((), stripped.lean.witnesses)
        self.assertEqual({}, dict(blank.prediction))

    def test_duplicate_reference_ids_load(self) -> None:
        document = candidate()
        document["claims"] = [document["claims"][0], dict(document["claims"][0])]

        self.assertEqual(2, len(CandidateManifest.from_dict(document).claims))

    def test_a_candidate_may_declare_no_parent(self) -> None:
        self.assertIsNone(CandidateManifest.from_dict(self.altered(candidate(), parent=None)).parent)


if __name__ == "__main__":
    unittest.main()
