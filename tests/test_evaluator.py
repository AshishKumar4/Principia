"""Behaviour tests for `principia.evaluator`.

The filesystem is real: every test builds a small repository in a temporary
directory and reads back the archived bundle. Only the external Lean process is
doubled, at the `subprocess.Popen` boundary, so the generated checker source, the
argument vectors, the hashes and the archive are all exercised for real.
"""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import tempfile
import unittest
from dataclasses import dataclass, field
from pathlib import Path
from unittest import mock

from principia import evaluator
from principia.artifacts import sha256_json
from principia.evidence import register_evaluator
from principia.models import (
    SCHEMA_VERSION,
    ArtifactError,
    CandidateManifest,
    EvaluationResult,
    EvaluationStatus,
    EvidenceRecord,
)

_TIMESTAMP = "2026-08-23T09:00:00.000000Z"
_OTHER_TIMESTAMP = "2026-08-23T10:00:00.000000Z"
_TOOLCHAIN = "leanprover/lean4:v4.31.0"
_CLAIM_SYMBOL = "CandidateLab.Demo.chsh_bound"
_WITNESS_SYMBOL = "CandidateLab.Demo.singletWitness"
_GATE_EVALUATOR = "principia.tests.demo_gate"
_UNREGISTERED_EVALUATOR = "principia.tests.absent_gate"

_ENTRYPOINT_SOURCE = """import Mathlib.Analysis.CStarAlgebra.CStarMatrix

namespace CandidateLab.Demo

/-- Hypotheses of the demo candidate, as a structure rather than an axiom. -/
structure Locality where
  factorises : True

/-- Demo claim: bounded by the Tsirelson value under the stated hypotheses. -/
theorem chsh_bound (h : Locality) : (0 : ℝ) ≤ 2 := by norm_num

/-- Non-vacuity witness for `Locality`. -/
def singletWitness : Locality := ⟨trivial⟩

end CandidateLab.Demo
"""

_SOURCE_REF = {
    "title": "Proposed Experiment to Test Local Hidden-Variable Theories",
    "authors": [
        "John F. Clauser",
        "Michael A. Horne",
        "Abner Shimony",
        "Richard A. Holt",
    ],
    "url": "https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.23.880",
    "doi": "10.1103/PhysRevLett.23.880",
    "published": "1969-10-13",
}

_DATA_CSV = "setting_a,setting_b,coincidences\n0,0,1024\n0,1,64\n"


def _candidate_document() -> dict[str, object]:
    return {
        "schema_version": SCHEMA_VERSION,
        "id": "demo",
        "version": 1,
        "parent": None,
        "title": "Demo candidate exercising the evaluator",
        "lean": {
            "module": "CandidateLab.Demo",
            "entrypoint": "CandidateLab/Demo.lean",
            "namespace": "CandidateLab.Demo",
            "claims": [_CLAIM_SYMBOL],
            "witnesses": [_WITNESS_SYMBOL],
        },
        "assumptions": [
            {
                "id": "locality",
                "lean_symbol": "CandidateLab.Demo.Locality",
                "source": dict(_SOURCE_REF),
            }
        ],
        "claims": [{"id": "chsh-bound", "lean_symbol": _CLAIM_SYMBOL}],
        "parameters": [{"id": "detector-efficiency", "value": 0.9, "unit": None}],
        "exceptions": [
            {"id": "postselection", "description": "coincidence windows are postselected"}
        ],
        "evidence": [{"id": "demo-bell", "prediction": {"violates_chsh": True}}],
    }


def _evidence_document(sha256: str, *, evaluator_id: str, required: list[str]) -> dict[str, object]:
    return {
        "schema_version": SCHEMA_VERSION,
        "id": "demo-bell",
        "version": 1,
        "title": "Demo Bell coincidence counts",
        "source": dict(_SOURCE_REF),
        "dataset": {
            "url": "https://journals.aps.org/prl/supplemental/10.1103/PhysRevLett.23.880",
            "sha256": sha256,
            "license": "CC-BY-4.0",
            "format": "csv",
            "local_path": "evidence/data/demo-bell.csv",
        },
        "gate": {
            "evaluator": evaluator_id,
            "required_claims": required,
            "inputs": {"coincidence_column": "coincidences"},
            "decision": {"tsirelson_bound": 2.0},
        },
    }


def _demo_gate(
    record: EvidenceRecord,
    candidate: CandidateManifest,
    repo_root: Path,
    timestamp: str,
) -> EvaluationResult:
    """Test-only built-in gate, registered through the public extension point."""
    return EvaluationResult(
        schema_version=SCHEMA_VERSION,
        candidate_id=candidate.id,
        evidence_id=record.id,
        status=EvaluationStatus.PASS,
        summary=f"the demo gate accepted {candidate.id}",
        metrics={"observed": 2.7},
        artifacts={},
        timestamp=timestamp,
    )


register_evaluator(_GATE_EVALUATOR, _demo_gate)


@dataclass
class _Reply:
    """Scripted behaviour of one external Lean invocation."""

    exit_code: int = 0
    stdout: bytes = b""
    stderr: bytes = b""
    timeout: bool = False


@dataclass
class _Call:
    argv: tuple[str, ...]
    full_argv: tuple[str, ...]
    cwd: Path
    kwargs: dict[str, object]
    timeout: float | None = None


class _FakeProcess:
    """Stand-in for a `lake` child process."""

    # No such process, so group termination can never reach the test runner.
    pid = 2**31 - 1

    def __init__(self, reply: _Reply, call: _Call) -> None:
        self._reply = reply
        self._call = call
        self._raised = False
        self.returncode = reply.exit_code
        self.killed = False

    def communicate(self, timeout: float | None = None) -> tuple[bytes, bytes]:
        if timeout is not None:
            self._call.timeout = timeout
        if self._reply.timeout and not self._raised:
            self._raised = True
            raise subprocess.TimeoutExpired(cmd=list(self._call.argv), timeout=timeout)
        if self._reply.timeout:
            self.returncode = -9
        return self._reply.stdout, self._reply.stderr

    def kill(self) -> None:
        self.killed = True

    def wait(self, timeout: float | None = None) -> int:
        return self.returncode


@dataclass
class _FakeLean:
    """Boundary double for the external Lean toolchain."""

    build: _Reply = field(default_factory=_Reply)
    compile: _Reply = field(default_factory=_Reply)
    check: _Reply = field(default_factory=_Reply)
    spawn_error: OSError | None = None
    calls: list[_Call] = field(default_factory=list)
    checker_sources: list[str] = field(default_factory=list)

    def __call__(self, argv: object, **kwargs: object) -> _FakeProcess:
        full = tuple(argv)  # type: ignore[call-overload]
        # The evaluator wraps every Lean step in a bubblewrap prefix that ends
        # with a literal `--` separator; the inner command is the boundary.
        vector = full[full.index("--") + 1 :] if "--" in full else full
        cwd = Path(str(kwargs["cwd"]))
        call = _Call(argv=vector, full_argv=full, cwd=cwd, kwargs=dict(kwargs))
        self.calls.append(call)
        if self.spawn_error is not None:
            raise self.spawn_error
        if vector[1] == "build":
            return _FakeProcess(self.build, call)
        if vector[-1].endswith(evaluator._CHECKER_FILENAME):
            self.checker_sources.append((cwd / vector[-1]).read_text(encoding="utf-8"))
            return _FakeProcess(self.check, call)
        return _FakeProcess(self.compile, call)

    @property
    def argvs(self) -> list[tuple[str, ...]]:
        return [call.argv for call in self.calls]


def _audit_line(
    *, checked: int = 4, claims: int = 1, witnesses: int = 1, violations: int = 0
) -> bytes:
    """The summary line as `lake env lean` prints it: info messages carry no prefix."""
    return (
        f"PRINCIPIA_AUDIT checked={checked} claims={claims} "
        f"witnesses={witnesses} violations={violations}\n"
    ).encode()


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class EvaluatorTestCase(unittest.TestCase):
    """Shared temporary repository and Lean double."""

    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.repo = Path(temporary.name).resolve() / "repo"
        self.candidate_dir = self.repo / "candidates" / "demo"
        self.entrypoint = self.repo / "CandidateLab" / "Demo.lean"
        self.output = self.repo / ".principia" / "evaluations"
        self.data_path = self.repo / "evidence" / "data" / "demo-bell.csv"
        self.record_path = self.repo / "evidence" / "records" / "demo-bell.json"

        self._write(self.repo / "lean-toolchain", f"{_TOOLCHAIN}\n")
        self._write(self.entrypoint, _ENTRYPOINT_SOURCE)
        self._write_json(self.candidate_dir / "candidate.json", _candidate_document())
        self._write(self.data_path, _DATA_CSV)
        self._write_json(
            self.record_path,
            _evidence_document(
                _sha256(_DATA_CSV.encode()),
                evaluator_id=_GATE_EVALUATOR,
                required=["chsh-bound"],
            ),
        )

        self.lean = _FakeLean(check=_Reply(stdout=_audit_line()))
        popen = mock.patch.object(evaluator.subprocess, "Popen", self.lean)
        popen.start()
        self.addCleanup(popen.stop)
        which = mock.patch.object(evaluator.shutil, "which", lambda name: f"/usr/bin/{name}")
        which.start()
        self.addCleanup(which.stop)

    # --- helpers ------------------------------------------------------------

    @staticmethod
    def _write(path: Path, text: str) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    @staticmethod
    def _write_json(path: Path, document: object) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    def _evaluate(
        self,
        *,
        evidence: list[Path] | None = None,
        timestamp: str = _TIMESTAMP,
        output: Path | None = None,
    ) -> list[EvaluationResult]:
        return evaluator.evaluate_candidate(
            self.candidate_dir,
            evidence or [],
            self.repo,
            output or self.output,
            timestamp,
        )

    def _status(self, result: EvaluationResult) -> EvaluationStatus:
        return EvaluationStatus(result.status)

    def _bundle_dir(self, output: Path | None = None) -> Path:
        root = output or self.output
        directories = sorted(path for path in root.iterdir() if path.is_dir())
        self.assertEqual(1, len(directories), f"expected one bundle in {root}, got {directories}")
        return directories[0]

    def _bundle(self, output: Path | None = None) -> dict[str, object]:
        path = self._bundle_dir(output) / evaluator.BUNDLE_FILENAME
        return json.loads(path.read_text(encoding="utf-8"))


class FormalStageTests(EvaluatorTestCase):
    def test_passing_candidate_reports_pass_with_audit_metrics(self) -> None:
        results = self._evaluate()

        self.assertEqual(1, len(results))
        result = results[0]
        self.assertIs(EvaluationStatus.PASS, self._status(result))
        self.assertIsNone(result.evidence_id)
        self.assertEqual("demo", result.candidate_id)
        self.assertEqual(_TIMESTAMP, result.timestamp)
        self.assertEqual(4, result.metrics["declarations_audited"])
        self.assertEqual(0, result.metrics["axiom_violations"])
        self.assertEqual(1, result.metrics["claim_symbols"])
        self.assertEqual(1, result.metrics["witness_symbols"])
        self.assertEqual(len(_ENTRYPOINT_SOURCE.encode()), result.metrics["source_bytes"])
        self.assertEqual(1, result.metrics["assumption_count"])
        self.assertEqual(1, result.metrics["parameter_count"])
        self.assertEqual(1, result.metrics["exception_count"])
        self.assertIn("CandidateLab.Demo", result.summary)

    def test_processes_are_argv_only_from_the_repo_root_with_timeouts(self) -> None:
        self._evaluate()

        checker_path = self._bundle()["paths"]["lean_checker"]
        self.assertEqual(
            [
                ("lake", "build", "CandidateLab.Demo"),
                ("lake", "env", "lean", "CandidateLab/Demo.lean"),
                ("lake", "env", "lean", checker_path),
            ],
            self.lean.argvs,
        )
        for call in self.lean.calls:
            self.assertEqual(self.repo, call.cwd)
            self.assertNotIn("shell", call.kwargs)
            self.assertIs(True, call.kwargs["start_new_session"])
            self.assertEqual(subprocess.DEVNULL, call.kwargs["stdin"])
            self.assertIsNotNone(call.timeout)
            self.assertGreater(call.timeout, 0)

    def test_generated_checker_elaborates_symbols_and_audits_the_classical_trio(self) -> None:
        self._evaluate()

        self.assertEqual(1, len(self.lean.checker_sources))
        source = self.lean.checker_sources[0]
        self.assertIn("import CandidateLab.Demo", source)
        self.assertIn(f"#check @{_CLAIM_SYMBOL}", source)
        self.assertIn(f"#check @{_WITNESS_SYMBOL}", source)
        self.assertIn("run_cmd do", source)
        self.assertIn("Lean.collectAxioms", source)
        self.assertIn("root.isPrefixOf name", source)
        self.assertIn("let root : Name := `CandidateLab.Demo", source)
        self.assertIn(f"let claims : List Name := [``{_CLAIM_SYMBOL}]", source)
        self.assertIn(f"let witnesses : List Name := [``{_WITNESS_SYMBOL}]", source)
        self.assertIn(
            "let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]", source
        )
        self.assertIn("PRINCIPIA_AXIOM_VIOLATION", source)
        self.assertIn("PRINCIPIA_CLAIM_NOT_THEOREM", source)
        self.assertIn("PRINCIPIA_AUDIT_EMPTY", source)
        declarations = [
            line
            for line in source.splitlines()
            if line.startswith(("axiom ", "sorry", "unsafe ", "native_decide"))
        ]
        self.assertEqual([], declarations)

    def test_checker_is_content_addressed_and_removed_afterwards(self) -> None:
        self._evaluate()

        bundle = self._bundle()
        digest = bundle["hashes"]["lean_checker"]
        self.assertEqual(_sha256(self.lean.checker_sources[0].encode()), digest)
        self.assertEqual(
            f".principia/tmp/checker-{digest[:16]}/PrincipiaChecker.lean",
            bundle["paths"]["lean_checker"],
        )
        self.assertEqual([], list((self.repo / ".principia" / "tmp").glob("checker-*")))

    def test_compile_failure_is_a_candidate_fail_and_skips_the_checker(self) -> None:
        self.lean.compile = _Reply(
            exit_code=1,
            stdout=b"CandidateLab/Demo.lean:12:8: error: unsolved goals\n",
        )

        results = self._evaluate()

        self.assertIs(EvaluationStatus.FAIL, self._status(results[0]))
        self.assertIn("does not compile", results[0].summary)
        self.assertIn("unsolved goals", results[0].summary)
        self.assertEqual(2, len(self.lean.calls))
        self.assertEqual([], self.lean.checker_sources)

    def test_build_failure_after_a_clean_compile_is_an_infrastructure_error(self) -> None:
        self.lean.build = _Reply(exit_code=1, stderr=b"error: unknown module CandidateLab.Demo\n")

        results = self._evaluate()

        self.assertIs(EvaluationStatus.ERROR, self._status(results[0]))
        self.assertIn("lake build CandidateLab.Demo", results[0].summary)
        self.assertEqual([], self.lean.checker_sources)

    def test_forbidden_axiom_is_a_candidate_fail(self) -> None:
        self.lean.check = _Reply(
            exit_code=1,
            stdout=_audit_line(violations=1),
            stderr=(
                b"PrincipiaChecker.lean:20:4: error: PRINCIPIA_AXIOM_VIOLATION "
                b"CandidateLab.Demo.chsh_bound CandidateLab.Demo.bellAx\n"
                b"PrincipiaChecker.lean:30:2: error: PRINCIPIA_AUDIT_FAILED: 1 forbidden"
                b" axiom dependency(ies)\n"
            ),
        )

        results = self._evaluate()

        self.assertIs(EvaluationStatus.FAIL, self._status(results[0]))
        self.assertIn("forbidden axiom", results[0].summary)
        self.assertIn("CandidateLab.Demo.chsh_bound depends on CandidateLab.Demo.bellAx", results[0].summary)
        self.assertEqual(1, results[0].metrics["axiom_violations"])

    def test_sorry_surfaces_as_a_forbidden_axiom_fail(self) -> None:
        self.lean.check = _Reply(
            exit_code=1,
            stdout=_audit_line(violations=1),
            stderr=(
                b"PrincipiaChecker.lean:20:4: error: PRINCIPIA_AXIOM_VIOLATION "
                b"CandidateLab.Demo.chsh_bound sorryAx\n"
            ),
        )

        results = self._evaluate()

        self.assertIs(EvaluationStatus.FAIL, self._status(results[0]))
        self.assertIn("sorryAx", results[0].summary)

    def test_claim_symbol_that_is_not_a_theorem_is_a_candidate_fail(self) -> None:
        self.lean.check = _Reply(
            exit_code=1,
            stdout=_audit_line(),
            stderr=(
                b"PrincipiaChecker.lean:26:4: error: PRINCIPIA_CLAIM_NOT_THEOREM "
                b"CandidateLab.Demo.chsh_bound\n"
            ),
        )

        results = self._evaluate()

        self.assertIs(EvaluationStatus.FAIL, self._status(results[0]))
        self.assertIn("not theorems", results[0].summary)
        self.assertIn(_CLAIM_SYMBOL, results[0].summary)

    def test_missing_symbol_is_a_candidate_fail_with_lean_diagnostics(self) -> None:
        self.lean.check = _Reply(
            exit_code=1,
            stdout=(
                b"PrincipiaChecker.lean:17:8: error(lean.unknownIdentifier): Unknown "
                b"identifier `CandidateLab.Demo.chsh_bound`\n"
                b"PrincipiaChecker.lean:23:31: error(lean.unknownIdentifier): Unknown "
                b"constant `CandidateLab.Demo.chsh_bound`\n"
            ),
        )

        results = self._evaluate()

        self.assertIs(EvaluationStatus.FAIL, self._status(results[0]))
        self.assertIn("rejected the candidate", results[0].summary)
        self.assertIn("Unknown identifier", results[0].summary)
        self.assertNotIn("declarations_audited", results[0].metrics)

    def test_checker_without_an_audit_summary_is_an_infrastructure_error(self) -> None:
        self.lean.check = _Reply(stdout=b"")

        results = self._evaluate()

        self.assertIs(EvaluationStatus.ERROR, self._status(results[0]))
        self.assertIn("no audit summary", results[0].summary)

    def test_timeout_is_an_infrastructure_error_and_kills_the_process(self) -> None:
        self.lean.compile = _Reply(timeout=True)

        results = self._evaluate()

        self.assertIs(EvaluationStatus.ERROR, self._status(results[0]))
        self.assertIn("timed out", results[0].summary)
        self.assertIn("lean.compile", results[0].summary)
        commands = self._bundle()["commands"]
        self.assertEqual(
            [False, True], [command["timed_out"] for command in commands]
        )

    def test_missing_lake_is_an_infrastructure_error_without_processes(self) -> None:
        with (
            mock.patch.object(evaluator.shutil, "which", lambda _: None),
            mock.patch.object(evaluator.os, "access", lambda *_: False),
        ):
            results = self._evaluate()

        self.assertIs(EvaluationStatus.ERROR, self._status(results[0]))
        self.assertIn("lake", results[0].summary)
        self.assertEqual([], self.lean.calls)

    def test_unstartable_lean_process_is_an_infrastructure_error(self) -> None:
        self.lean.spawn_error = OSError(13, "Permission denied")

        results = self._evaluate()

        self.assertIs(EvaluationStatus.ERROR, self._status(results[0]))
        self.assertIn("could not be started", results[0].summary)
        self.assertEqual([], self._bundle()["commands"])

    def test_silent_compile_failure_reports_the_exit_code(self) -> None:
        self.lean.compile = _Reply(exit_code=2)

        results = self._evaluate()

        self.assertIs(EvaluationStatus.FAIL, self._status(results[0]))
        self.assertIn("no diagnostics, exit code 2", results[0].summary)


class CandidateVerificationTests(EvaluatorTestCase):
    def test_missing_manifest_is_an_infrastructure_error(self) -> None:
        (self.candidate_dir / "candidate.json").unlink()

        results = self._evaluate()

        self.assertEqual(1, len(results))
        self.assertIs(EvaluationStatus.ERROR, self._status(results[0]))
        self.assertIn("candidates/demo/candidate.json", results[0].summary)
        self.assertEqual([], self.lean.calls)

    @unittest.skipIf(os.geteuid() == 0, "root ignores file permissions")
    def test_unreadable_manifest_is_an_infrastructure_error(self) -> None:
        manifest = self.candidate_dir / "candidate.json"
        manifest.chmod(0o000)
        self.addCleanup(manifest.chmod, 0o600)

        results = self._evaluate()

        self.assertIs(EvaluationStatus.ERROR, self._status(results[0]))
        self.assertIn("cannot be read", results[0].summary)
        self.assertEqual([], self.lean.calls)

    def test_invalid_manifest_is_a_candidate_fail(self) -> None:
        document = _candidate_document()
        document["unexpected"] = "key"
        self._write_json(self.candidate_dir / "candidate.json", document)

        results = self._evaluate()

        self.assertIs(EvaluationStatus.FAIL, self._status(results[0]))
        self.assertIn("is invalid", results[0].summary)
        self.assertEqual([], self.lean.calls)

    def test_verification_problems_are_a_candidate_fail(self) -> None:
        self.entrypoint.unlink()

        results = self._evaluate()

        self.assertIs(EvaluationStatus.FAIL, self._status(results[0]))
        self.assertIn("does not verify", results[0].summary)
        self.assertGreaterEqual(results[0].metrics["manifest_problems"], 1)
        self.assertEqual([], self.lean.calls)

    def test_candidate_directory_outside_the_repository_is_rejected(self) -> None:
        outside = self.repo.parent / "outside"
        outside.mkdir()

        with self.assertRaises(ArtifactError):
            evaluator.evaluate_candidate(outside, [], self.repo, self.output, _TIMESTAMP)

    def test_absent_candidate_directory_is_rejected(self) -> None:
        with self.assertRaises(ArtifactError):
            evaluator.evaluate_candidate(
                self.repo / "candidates" / "ghost", [], self.repo, self.output, _TIMESTAMP
            )


class EvidenceStageTests(EvaluatorTestCase):
    def test_evidence_results_follow_the_formal_result(self) -> None:
        results = self._evaluate(evidence=[self.record_path])

        self.assertEqual(2, len(results))
        self.assertIs(EvaluationStatus.PASS, self._status(results[0]))
        self.assertIsNone(results[0].evidence_id)
        self.assertIs(EvaluationStatus.PASS, self._status(results[1]))
        self.assertEqual("demo-bell", results[1].evidence_id)
        self.assertEqual("demo", results[1].candidate_id)

        hashes = self._bundle()["hashes"]
        self.assertEqual(_sha256(self.record_path.read_bytes()), hashes["evidence.0.file"])
        self.assertIn("evidence.0.record", hashes)

    def test_unusable_evidence_record_is_an_infrastructure_error(self) -> None:
        missing = self.repo / "evidence" / "records" / "absent.json"

        results = self._evaluate(evidence=[missing])

        self.assertEqual(2, len(results))
        self.assertIs(EvaluationStatus.ERROR, self._status(results[1]))
        self.assertIsNone(results[1].evidence_id)
        self.assertIn("evidence/records/absent.json", results[1].summary)
        hashes = self._bundle()["hashes"]
        self.assertNotIn("evidence.0.record", hashes)
        self.assertNotIn("evidence.0.file", hashes)

    def test_unknown_gate_evaluator_is_reported_per_record(self) -> None:
        self._write_json(
            self.record_path,
            _evidence_document(
                _sha256(_DATA_CSV.encode()),
                evaluator_id=_UNREGISTERED_EVALUATOR,
                required=["chsh-bound"],
            ),
        )

        results = self._evaluate(evidence=[self.record_path])

        self.assertEqual(2, len(results))
        self.assertIs(EvaluationStatus.ERROR, self._status(results[1]))

    def test_inapplicable_gate_is_recorded_without_failing_the_candidate(self) -> None:
        self._write_json(
            self.record_path,
            _evidence_document(
                _sha256(_DATA_CSV.encode()),
                evaluator_id=_GATE_EVALUATOR,
                required=["claim-the-candidate-does-not-make"],
            ),
        )

        results = self._evaluate(evidence=[self.record_path])

        self.assertIs(EvaluationStatus.PASS, self._status(results[0]))
        self.assertIs(EvaluationStatus.NOT_APPLICABLE, self._status(results[1]))
        self.assertEqual("demo-bell", results[1].evidence_id)
        self.assertIn("evidence.0.record", self._bundle()["hashes"])

    def test_evidence_is_not_evaluated_when_the_formal_verdict_fails(self) -> None:
        self.lean.compile = _Reply(exit_code=1, stdout=b"Demo.lean:1:1: error: boom\n")

        results = self._evaluate(evidence=[self.record_path])

        self.assertEqual(1, len(results))
        self.assertIs(EvaluationStatus.FAIL, self._status(results[0]))
        self.assertNotIn("evidence.0.file", self._bundle()["hashes"])

    def test_every_evidence_record_is_evaluated_in_order(self) -> None:
        second = self.repo / "evidence" / "records" / "absent.json"

        results = self._evaluate(evidence=[self.record_path, second])

        self.assertEqual(3, len(results))
        self.assertEqual("demo-bell", results[1].evidence_id)
        self.assertIs(EvaluationStatus.ERROR, self._status(results[2]))
        self.assertIn("evidence.1", self._bundle()["paths"])


class ArchiveTests(EvaluatorTestCase):
    def test_bundle_records_inputs_commands_and_results(self) -> None:
        self.lean.build = _Reply(stdout=b"info: [2/2] Built CandidateLab.Demo\n")
        self.lean.compile = _Reply(stdout=b"")
        self.lean.check = _Reply(stdout=_audit_line(checked=6))

        results = self._evaluate(evidence=[self.record_path])
        bundle = self._bundle()

        self.assertEqual(evaluator.BUNDLE_SCHEMA_VERSION, bundle["schema_version"])
        self.assertEqual(_TIMESTAMP, bundle["timestamp"])
        self.assertEqual(_TOOLCHAIN, bundle["toolchain"])
        self.assertEqual(
            {"dir": "candidates/demo", "id": "demo"},
            bundle["candidate"],
        )
        self.assertEqual([result.to_dict() for result in results], bundle["results"])

        hashes = bundle["hashes"]
        manifest_path = self.candidate_dir / "candidate.json"
        self.assertEqual(_sha256(manifest_path.read_bytes()), hashes["candidate_manifest_file"])
        self.assertEqual(_sha256(self.entrypoint.read_bytes()), hashes["lean_entrypoint"])
        self.assertEqual(
            _sha256(self.lean.checker_sources[0].encode()), hashes["lean_checker"]
        )
        self.assertIn("candidate_manifest", hashes)
        self.assertEqual(
            {
                "candidate_manifest": "candidates/demo/candidate.json",
                "lean_entrypoint": "CandidateLab/Demo.lean",
                "lean_checker": bundle["paths"]["lean_checker"],
                "evidence.0": "evidence/records/demo-bell.json",
            },
            bundle["paths"],
        )

        commands = bundle["commands"]
        self.assertEqual(
            ["lean.build", "lean.compile", "lean.check"],
            [command["name"] for command in commands],
        )
        self.assertEqual([0, 0, 0], [command["exit_code"] for command in commands])
        self.assertEqual(_sha256(_audit_line(checked=6)), commands[2]["stdout_sha256"])
        self.assertEqual(_sha256(b""), commands[1]["stdout_sha256"])
        self.assertNotIn("stdout_sha256", commands[0])
        self.assertNotIn("stderr_sha256", commands[0])
        self.assertNotIn("outputs", bundle)

    def test_bundle_digest_and_logs_are_archived(self) -> None:
        self.lean.build = _Reply(stdout=b"info: [2/2] Built CandidateLab.Demo\n")
        self._evaluate()

        directory = self._bundle_dir()
        digest = (directory / evaluator.BUNDLE_DIGEST_FILENAME).read_text(encoding="utf-8")
        self.assertEqual(sha256_json(self._bundle()), digest.strip())

        logs = directory / evaluator.LOG_DIRNAME
        self.assertEqual(
            b"info: [2/2] Built CandidateLab.Demo\n",
            (logs / "lean.build.stdout").read_bytes(),
        )
        self.assertEqual(_audit_line(), (logs / "lean.check.stdout").read_bytes())
        self.assertEqual(b"", (logs / "lean.check.stderr").read_bytes())

    def test_result_artifacts_cover_every_hashed_input_and_output(self) -> None:
        results = self._evaluate()

        artifacts = results[0].artifacts
        self.assertEqual(
            {
                "candidate_manifest",
                "candidate_manifest_file",
                "lean_entrypoint",
                "lean_checker",
                "lean.compile.stdout",
                "lean.compile.stderr",
                "lean.check.stdout",
                "lean.check.stderr",
            },
            set(artifacts),
        )
        for name, digest in artifacts.items():
            self.assertRegex(digest, r"^[0-9a-f]{64}$", name)

    def test_identical_rerun_keeps_the_archived_bundle(self) -> None:
        first = self._evaluate()
        directory = self._bundle_dir()
        archived = (directory / evaluator.BUNDLE_FILENAME).read_bytes()

        second = self._evaluate()

        self.assertEqual([1, 1], [len(first), len(second)])
        self.assertEqual(directory, self._bundle_dir())
        self.assertEqual(archived, (directory / evaluator.BUNDLE_FILENAME).read_bytes())
        self.assertEqual(first[0].to_dict(), second[0].to_dict())

    def test_differing_bytes_under_the_same_bundle_id_are_refused(self) -> None:
        self._evaluate()
        archived = self._bundle_dir() / evaluator.BUNDLE_FILENAME
        tampered = b'{"tampered":true}\n'
        archived.write_bytes(tampered)

        with self.assertRaises(ArtifactError) as caught:
            self._evaluate()

        self.assertIn("immutable", str(caught.exception))
        self.assertEqual(tampered, archived.read_bytes())

    def test_bundle_identity_follows_the_timestamp(self) -> None:
        self._evaluate()
        first = self._bundle_dir().name

        self._evaluate(timestamp=_OTHER_TIMESTAMP)

        names = sorted(path.name for path in self.output.iterdir() if path.is_dir())
        self.assertEqual(2, len(names))
        self.assertIn(first, names)

    def test_bundle_identity_follows_the_candidate_bytes(self) -> None:
        self._evaluate()
        first = self._bundle_dir().name
        self._write(self.entrypoint, _ENTRYPOINT_SOURCE + "\n-- edited\n")

        self._evaluate()

        names = sorted(path.name for path in self.output.iterdir() if path.is_dir())
        self.assertEqual(2, len(names))
        self.assertNotEqual(names[0], names[1])
        self.assertIn(first, names)

    def test_bundle_id_starts_with_the_candidate_id(self) -> None:
        self._evaluate()

        self.assertRegex(self._bundle_dir().name, r"^demo-[0-9a-f]{16}$")

    def test_output_directory_is_created_and_left_without_staging_dirs(self) -> None:
        output = self.repo / ".principia" / "nested" / "evaluations"

        self._evaluate(output=output)

        self.assertTrue(output.is_dir())
        self.assertEqual([], [path.name for path in output.iterdir() if path.name.startswith(".")])

    def test_archive_path_occupied_by_a_foreign_directory_is_refused(self) -> None:
        self._evaluate()
        directory = self._bundle_dir()
        (directory / evaluator.BUNDLE_FILENAME).unlink()

        with self.assertRaises(ArtifactError) as caught:
            self._evaluate()

        self.assertIn(evaluator.BUNDLE_FILENAME, str(caught.exception))




class SandboxContractTests(EvaluatorTestCase):
    """The mocked boundary locks in containment; no unsandboxed regression can pass."""

    def test_every_lean_process_is_isolated_and_the_repo_is_read_only(self) -> None:
        self._evaluate()

        self.assertEqual(3, len(self.lean.calls))
        uppers: list[str] = []
        for call in self.lean.calls:
            full = call.full_argv
            self.assertEqual("bwrap", Path(str(full[0])).name)
            self.assertIn("--unshare-all", full)
            self.assertNotIn("--share-net", full)
            self.assertIn("--clearenv", full)
            self.assertIn("--new-session", full)
            self.assertEqual({"PATH": os.defpath}, call.kwargs["env"])
            self.assertEqual(self.repo, call.cwd)
            pairs = list(zip(full, full[1:]))
            self.assertIn(("--chdir", str(self.repo)), pairs)
            ro_triples = list(zip(full, full[1:], full[2:]))
            self.assertIn(("--ro-bind", str(self.repo), str(self.repo)), ro_triples)
            overlay = full.index("--overlay")
            upper, work, destination = map(str, full[overlay + 1 : overlay + 4])
            self.assertEqual(str(self.repo / ".lake"), destination)
            self.assertNotEqual(upper, work)
            uppers.append(upper)
        self.assertEqual(3, len(set(uppers)))
        self.assertIn(uppers[0], self.lean.calls[1].full_argv)
        self.assertIn(uppers[0], self.lean.calls[2].full_argv)
        self.assertIn(uppers[1], self.lean.calls[2].full_argv)

    def test_bwrap_setup_failure_is_infrastructure_error_not_candidate_failure(self) -> None:
        self.lean.compile = _Reply(exit_code=1, stderr=b"bwrap: namespace setup failed\n")

        result = self._evaluate()[0]

        self.assertIs(EvaluationStatus.ERROR, self._status(result))
        self.assertIn("sandbox failed", result.summary)
        self.assertIn("namespace setup failed", result.summary)


class RealSandboxIsolationTests(unittest.TestCase):
    """One real bwrap process proves the evaluator's mount contract, not a mock."""

    @classmethod
    def setUpClass(cls) -> None:
        bwrap = evaluator.shutil.which(evaluator._BWRAP)
        if bwrap is None:
            raise unittest.SkipTest("bubblewrap is not installed")
        vector = [bwrap, "--unshare-all", "--die-with-parent"]
        for path in evaluator._runner._system_read_only():
            vector += ["--ro-bind", str(path), str(path)]
        vector += ["--proc", "/proc", "--dev", "/dev", "--", "/bin/true"]
        probe = subprocess.run(
            vector,
            check=False,
            capture_output=True,
        )
        if probe.returncode != 0:
            raise unittest.SkipTest(
                "bubblewrap namespaces unavailable: "
                + probe.stderr.decode("utf-8", "replace").strip()
            )
        cls.bwrap = bwrap

    def test_repo_is_read_only_and_lake_writes_land_only_in_overlay(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            repo = root / "repo"
            lake = repo / ".lake"
            scratch = root / "scratch"
            lake.mkdir(parents=True)
            scratch.mkdir()
            (repo / "canonical.txt").write_text("unchanged\n", encoding="utf-8")
            (lake / "host.txt").write_text("host\n", encoding="utf-8")
            sandbox = evaluator._Sandbox(
                bwrap=self.bwrap,
                repo_root=repo,
                lake_bin=Path("/usr/bin"),
                scratch=scratch,
                elan_home=None,
            )

            outcome = evaluator._run_process(
                "isolation.probe",
                (
                    "/bin/sh",
                    "-c",
                    "printf test > canonical.txt 2>/dev/null || printf 'repo-ro\\n'; "
                    "printf overlay > .lake/new.txt; "
                    "printf 'home=%s\\n' \"$HOME\"; cat .lake/host.txt",
                ),
                sandbox,
                10.0,
            )

            self.assertTrue(outcome.ok, outcome.text)
            self.assertIn("repo-ro", outcome.text)
            self.assertIn("home=/sandbox/home", outcome.text)
            self.assertIn("host", outcome.text)
            self.assertEqual("unchanged\n", (repo / "canonical.txt").read_text())
            self.assertFalse((lake / "new.txt").exists())
            self.assertEqual(1, len(sandbox.uppers))
            self.assertEqual("overlay", (sandbox.uppers[0] / "new.txt").read_text())


if __name__ == "__main__":
    unittest.main()
