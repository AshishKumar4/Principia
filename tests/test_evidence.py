"""Behaviour tests for `principia.evidence`.

Every test builds a throwaway repository, so path containment and checksum rules are
exercised against a real filesystem instead of a mock. Test evaluators are registered
through the public function and dropped again in cleanup; the registry is private to
the module under test, and reaching into it here keeps the tests hermetic without an
unregister function that production code would never call.
"""

from __future__ import annotations

import json
import shutil
import tempfile
import unittest
from hashlib import sha256
from pathlib import Path

from principia import evidence
from principia.evidence import (
    evaluate_evidence,
    load_evidence,
    register_evaluator,
    verify_evidence,
)
from principia.models import (
    SCHEMA_VERSION,
    ArtifactError,
    CandidateManifest,
    EvaluationResult,
    EvaluationStatus,
    EvidenceRecord,
)

_TIMESTAMP = "2026-08-23T12:00:00.000000Z"
_EVALUATOR = "test.evaluator"
_BUILTIN = "principia.evaluators.bell_ch"
_RECORD_ID = "bell.chsh.test"
_CANDIDATE_ID = "chsh-candidate"
_CLAIM = "chsh.violation"
_LOCAL_PATH = "evidence/data/chsh.json"
_DATA_URL = "https://example.org/chsh/coincidences.json"
_DATA_BYTES = b'{"minus":[10,20],"plus":[30,40]}\n'
_INVALID_IDS = ("", "Bell", "principia.evaluators.", ".bell", "bell ch", "bell-ch", "9bell", 1)


def _source_document() -> dict:
    return {
        "title": "Experimental Test of Bell's Inequalities Using Time-Varying Analyzers",
        "authors": ["Alain Aspect", "Jean Dalibard", "Gerard Roger"],
        "url": "https://doi.org/10.1103/PhysRevLett.49.1804",
        "doi": "10.1103/PhysRevLett.49.1804",
        "published": "1982-12-20",
    }


def _candidate_document(claims: list[str]) -> dict:
    return {
        "schema_version": SCHEMA_VERSION,
        "id": _CANDIDATE_ID,
        "version": 1,
        "parent": None,
        "title": "Local hidden variable candidate",
        "lean": {
            "module": "Atlas.Specs.Bell",
            "entrypoint": "Atlas.Specs.Bell.chshBound",
            "namespace": "Atlas.Bell",
            "witnesses": ["Atlas.Bell.minkowskiWitness"],
            "claims": ["Atlas.Bell.chshViolation"],
        },
        "assumptions": [
            {
                "id": "locality",
                "lean_symbol": "Atlas.Bell.Locality",
                "source": _source_document(),
            }
        ],
        "claims": [{"id": claim, "lean_symbol": "Atlas.Bell.chshViolation"} for claim in claims],
        "parameters": [{"id": "alpha", "value": 0.05, "unit": None}],
        "exceptions": [{"id": "detector.efficiency", "description": "no fair sampling"}],
        "evidence": [{"id": _RECORD_ID, "prediction": {"chsh": 2.7}}],
    }


class EvidenceCase(unittest.TestCase):
    """A temporary repository holding one evidence record and its data file."""

    def setUp(self) -> None:
        base = Path(tempfile.mkdtemp(prefix="principia-")).resolve()
        self.addCleanup(shutil.rmtree, base, ignore_errors=True)
        self.repo = base / "repo"
        self.outside = base / "outside"
        self.repo.mkdir()
        self.outside.mkdir()
        self.digest = sha256(_DATA_BYTES).hexdigest()
        self.calls: list[tuple[str, str]] = []

    # --- fixtures ----------------------------------------------------------

    def write_data(self, content: bytes = _DATA_BYTES, name: str = _LOCAL_PATH) -> Path:
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        return path

    def dataset_document(self, **overrides: object) -> dict:
        document: dict = {
            "url": _DATA_URL,
            "sha256": self.digest,
            "license": "CC0-1.0",
            "format": "application/json",
            "local_path": _LOCAL_PATH,
        }
        document.update(overrides)
        return document

    def gate_document(self, **overrides: object) -> dict:
        document: dict = {
            "evaluator": _EVALUATOR,
            "required_claims": [_CLAIM],
            "inputs": {"coincidence_window_ns": 100},
            "decision": {"alpha": 0.05},
        }
        document.update(overrides)
        return document

    def evidence_document(self, **overrides: object) -> dict:
        document: dict = {
            "schema_version": SCHEMA_VERSION,
            "id": _RECORD_ID,
            "version": 1,
            "title": "CHSH violation, committed sufficient statistics",
            "source": _source_document(),
            "dataset": self.dataset_document(),
            "gate": self.gate_document(),
        }
        document.update(overrides)
        return document

    def write_document(self, document: dict) -> Path:
        path = self.repo / "evidence/records/chsh.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(document) + "\n", encoding="utf-8")
        return path

    def write_record(self, **overrides: object) -> Path:
        return self.write_document(self.evidence_document(**overrides))

    def record(self, **overrides: object) -> EvidenceRecord:
        return load_evidence(self.write_record(**overrides))

    def candidate(self, claims: list[str] | None = None) -> CandidateManifest:
        return CandidateManifest.from_dict(
            _candidate_document([_CLAIM] if claims is None else claims)
        )

    # --- evaluators --------------------------------------------------------

    def register(self, function: object, name: str = _EVALUATOR) -> str:
        register_evaluator(name, function)
        self.addCleanup(evidence._EVALUATORS.pop, name, None)
        return name

    def register_returning(self, result: object) -> None:
        def evaluator(record, candidate, repo_root, timestamp):
            self.calls.append((record.id, candidate.id))
            return result

        self.register(evaluator)

    def result(self, **overrides: object) -> EvaluationResult:
        fields: dict = {
            "schema_version": SCHEMA_VERSION,
            "candidate_id": _CANDIDATE_ID,
            "evidence_id": _RECORD_ID,
            "status": EvaluationStatus.PASS,
            "summary": "CHSH S = 2.70 exceeds the local bound",
            "metrics": {"chsh": 2.7},
            "artifacts": {},
            "timestamp": _TIMESTAMP,
        }
        fields.update(overrides)
        return EvaluationResult(**fields)

    def evaluate(
        self, record: EvidenceRecord, claims: list[str] | None = None
    ) -> EvaluationResult:
        return evaluate_evidence(record, self.candidate(claims), self.repo, _TIMESTAMP)


class LoadEvidenceTest(EvidenceCase):
    def test_local_record_loads_and_verifies(self) -> None:
        self.write_data()
        self.register(lambda *_: None)
        record = load_evidence(self.write_record())
        self.assertEqual(record.id, _RECORD_ID)
        self.assertEqual(record.gate.evaluator, _EVALUATOR)
        self.assertEqual(tuple(record.gate.required_claims), (_CLAIM,))
        self.assertEqual(record.dataset.local_path, _LOCAL_PATH)
        self.assertEqual(record.dataset.sha256, self.digest)
        self.assertEqual(verify_evidence(record, self.repo), [])

    def test_checksum_pinned_remote_record_verifies(self) -> None:
        self.register(lambda *_: None)
        record = self.record(dataset=self.dataset_document(local_path=None))
        self.assertIsNone(record.dataset.local_path)
        self.assertEqual(record.dataset.url, _DATA_URL)
        self.assertEqual(verify_evidence(record, self.repo), [])

    def test_unknown_key_is_rejected(self) -> None:
        with self.assertRaises(ArtifactError):
            load_evidence(self.write_record(notes="unexpected"))

    def test_unknown_gate_key_is_rejected(self) -> None:
        with self.assertRaises(ArtifactError):
            load_evidence(self.write_record(gate=self.gate_document(command="rm -rf /")))

    def test_missing_required_key_is_rejected(self) -> None:
        document = self.evidence_document()
        del document["gate"]
        with self.assertRaises(ArtifactError):
            load_evidence(self.write_document(document))


class VerifyEvidenceTest(EvidenceCase):
    def setUp(self) -> None:
        super().setUp()
        self.register(lambda *_: None)

    def test_parent_traversal_is_rejected(self) -> None:
        (self.outside / "escape.json").write_bytes(_DATA_BYTES)
        record = self.record(dataset=self.dataset_document(local_path="../outside/escape.json"))
        problems = verify_evidence(record, self.repo)
        self.assertEqual(len(problems), 1)
        self.assertIn("../outside/escape.json", problems[0])

    def test_absolute_path_is_rejected(self) -> None:
        record = self.record(dataset=self.dataset_document(local_path="/etc/hostname"))
        problems = verify_evidence(record, self.repo)
        self.assertEqual(len(problems), 1)
        self.assertIn("/etc/hostname", problems[0])

    def test_symlink_escape_is_rejected(self) -> None:
        target = self.outside / "chsh.json"
        target.write_bytes(_DATA_BYTES)
        link = self.repo / _LOCAL_PATH
        link.parent.mkdir(parents=True, exist_ok=True)
        link.symlink_to(target)
        problems = verify_evidence(self.record(), self.repo)
        self.assertEqual(len(problems), 1)
        self.assertIn(_LOCAL_PATH, problems[0])

    def test_symlink_inside_the_repository_is_accepted(self) -> None:
        self.write_data(name="evidence/data/store/chsh.json")
        (self.repo / _LOCAL_PATH).symlink_to(Path("store/chsh.json"))
        self.assertEqual(verify_evidence(self.record(), self.repo), [])

    def test_missing_data_is_reported(self) -> None:
        problems = verify_evidence(self.record(), self.repo)
        self.assertEqual(len(problems), 1)
        self.assertIn(_LOCAL_PATH, problems[0])

    def test_directory_instead_of_a_file_is_reported(self) -> None:
        (self.repo / _LOCAL_PATH).mkdir(parents=True)
        problems = verify_evidence(self.record(), self.repo)
        self.assertEqual(len(problems), 1)
        self.assertIn(_LOCAL_PATH, problems[0])

    def test_checksum_mismatch_is_reported(self) -> None:
        tampered = _DATA_BYTES.replace(b"10", b"11")
        self.assertEqual(len(tampered), len(_DATA_BYTES))
        self.write_data(tampered)
        problems = verify_evidence(self.record(), self.repo)
        self.assertEqual(len(problems), 1)
        self.assertIn("checksum", problems[0])

    def test_dataset_without_local_path_or_url_is_reported(self) -> None:
        record = self.record(dataset=self.dataset_document(local_path=None, url=None))
        problems = verify_evidence(record, self.repo)
        self.assertEqual(len(problems), 1)
        self.assertIn("neither a repo-relative local_path nor a url", problems[0])

    def test_unregistered_evaluator_is_reported(self) -> None:
        self.write_data()
        record = self.record(gate=self.gate_document(evaluator="test.absent"))
        problems = verify_evidence(record, self.repo)
        self.assertEqual(len(problems), 1)
        self.assertIn("test.absent", problems[0])
        self.assertIn(_BUILTIN, problems[0])

    def test_problems_are_reported_in_a_fixed_order(self) -> None:
        record = self.record(gate=self.gate_document(evaluator="test.absent"))
        problems = verify_evidence(record, self.repo)
        self.assertEqual(len(problems), 2)
        self.assertIn("test.absent", problems[0])
        self.assertIn(_LOCAL_PATH, problems[1])
        self.assertEqual(problems, verify_evidence(record, self.repo))


class RegisterEvaluatorTest(EvidenceCase):
    def test_duplicate_registration_is_rejected(self) -> None:
        self.register(lambda *_: None)
        with self.assertRaises(ArtifactError) as caught:
            register_evaluator(_EVALUATOR, lambda *_: None)
        self.assertIn("already registered", str(caught.exception))

    def test_builtin_evaluator_is_registered_once(self) -> None:
        with self.assertRaises(ArtifactError) as caught:
            register_evaluator(_BUILTIN, lambda *_: None)
        self.assertIn("already registered", str(caught.exception))

    def test_invalid_ids_are_rejected(self) -> None:
        for name in _INVALID_IDS:
            with self.subTest(name=name), self.assertRaises(ArtifactError):
                register_evaluator(name, lambda *_: None)

    def test_non_callable_evaluator_is_rejected(self) -> None:
        with self.assertRaises(ArtifactError):
            register_evaluator("test.not.callable", _BUILTIN)

    def test_a_rejected_registration_adds_nothing(self) -> None:
        before = sorted(evidence._EVALUATORS)
        self.assertIn(_BUILTIN, before)
        for name in _INVALID_IDS:
            with self.subTest(name=name), self.assertRaises(ArtifactError):
                register_evaluator(name, lambda *_: None)
        self.assertEqual(sorted(evidence._EVALUATORS), before)


class EvaluateEvidenceTest(EvidenceCase):
    def setUp(self) -> None:
        super().setUp()
        self.write_data()

    def test_evaluator_result_passes_through_unchanged(self) -> None:
        expected = self.result()
        self.register_returning(expected)
        self.assertIs(self.evaluate(self.record()), expected)
        self.assertEqual(self.calls, [(_RECORD_ID, _CANDIDATE_ID)])

    def test_evaluator_receives_record_candidate_repo_and_timestamp(self) -> None:
        seen: dict = {}

        def evaluator(record, candidate, repo_root, timestamp):
            seen.update(
                record=record.id, candidate=candidate.id, repo=repo_root, timestamp=timestamp
            )
            return self.result()

        self.register(evaluator)
        self.evaluate(self.record())
        self.assertEqual(
            seen,
            {
                "record": _RECORD_ID,
                "candidate": _CANDIDATE_ID,
                "repo": self.repo,
                "timestamp": _TIMESTAMP,
            },
        )

    def test_missing_claim_is_not_applicable(self) -> None:
        self.register_returning(self.result())
        result = self.evaluate(self.record(), claims=["other.claim"])
        self.assertEqual(result.status, EvaluationStatus.NOT_APPLICABLE)
        self.assertEqual(result.summary, f"the candidate does not claim {_CLAIM}")
        self.assertEqual(result.candidate_id, _CANDIDATE_ID)
        self.assertEqual(result.evidence_id, _RECORD_ID)
        self.assertEqual(result.timestamp, _TIMESTAMP)
        self.assertEqual(dict(result.metrics), {})
        self.assertEqual(dict(result.artifacts), {})
        self.assertEqual(self.calls, [])

    def test_every_required_claim_must_be_present(self) -> None:
        self.register_returning(self.result())
        record = self.record(gate=self.gate_document(required_claims=[_CLAIM, "second.claim"]))
        result = self.evaluate(record)
        self.assertEqual(result.status, EvaluationStatus.NOT_APPLICABLE)
        self.assertEqual(result.summary, "the candidate does not claim second.claim")
        self.assertEqual(self.calls, [])

    def test_unusable_evidence_is_never_evaluated(self) -> None:
        (self.repo / _LOCAL_PATH).unlink()
        self.register_returning(self.result())
        result = self.evaluate(self.record())
        self.assertEqual(result.status, EvaluationStatus.ERROR)
        self.assertIn("not usable", result.summary)
        self.assertIn(_LOCAL_PATH, result.summary)
        self.assertEqual(self.calls, [])

    def test_unregistered_evaluator_is_an_error_result(self) -> None:
        record = self.record(gate=self.gate_document(evaluator="test.absent"))
        result = evaluate_evidence(record, self.candidate(), self.repo, _TIMESTAMP)
        self.assertEqual(result.status, EvaluationStatus.ERROR)
        self.assertIn("test.absent", result.summary)

    def test_evaluator_exception_becomes_a_deterministic_error_result(self) -> None:
        def evaluator(record, candidate, repo_root, timestamp):
            raise ValueError("column 'coincidences' is missing")

        self.register(evaluator)
        record = self.record()
        first = self.evaluate(record)
        second = self.evaluate(record)
        self.assertEqual(first.status, EvaluationStatus.ERROR)
        self.assertIn(_EVALUATOR, first.summary)
        self.assertIn("ValueError", first.summary)
        self.assertIn("column 'coincidences' is missing", first.summary)
        self.assertEqual(first.summary, second.summary)
        self.assertEqual(dict(first.metrics), {})

    def test_keyboard_interrupt_is_not_swallowed(self) -> None:
        def evaluator(record, candidate, repo_root, timestamp):
            raise KeyboardInterrupt

        self.register(evaluator)
        with self.assertRaises(KeyboardInterrupt):
            self.evaluate(self.record())

    def test_mislabelled_result_becomes_an_error_result(self) -> None:
        self.register_returning(self.result(candidate_id="other-candidate"))
        result = self.evaluate(self.record())
        self.assertEqual(result.status, EvaluationStatus.ERROR)
        self.assertIn("candidate_id", result.summary)
        self.assertEqual(result.candidate_id, _CANDIDATE_ID)

    def test_result_for_another_record_becomes_an_error_result(self) -> None:
        self.register_returning(self.result(evidence_id="bell.other"))
        result = self.evaluate(self.record())
        self.assertEqual(result.status, EvaluationStatus.ERROR)
        self.assertIn("evidence_id", result.summary)

    def test_non_result_return_becomes_an_error_result(self) -> None:
        self.register_returning({"status": "pass"})
        result = self.evaluate(self.record())
        self.assertEqual(result.status, EvaluationStatus.ERROR)
        self.assertIn("EvaluationResult", result.summary)

    def test_failing_verdicts_pass_through_untouched(self) -> None:
        verdicts: list[EvaluationResult] = []

        def evaluator(record, candidate, repo_root, timestamp):
            return verdicts[-1]

        self.register(evaluator)
        record = self.record()
        for status in (EvaluationStatus.FAIL, EvaluationStatus.INCONCLUSIVE):
            with self.subTest(status=status):
                verdicts.append(self.result(status=status, summary="the local bound holds"))
                self.assertIs(self.evaluate(record), verdicts[-1])


if __name__ == "__main__":
    unittest.main()
