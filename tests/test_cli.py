"""Behavior tests for the Principia command line interface.

Each test drives `cli.main` and patches only the public boundary functions that
the CLI calls. The tests check the arguments handed to those boundaries, the
single canonical JSON object on stdout, the diagnostics on stderr, and the exit
status.
"""

import dataclasses
import io
import json
import unittest
from contextlib import redirect_stderr, redirect_stdout
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import Any
from unittest.mock import patch

from principia import __version__, cli, runner
from principia.artifacts import canonical_json
from principia.models import (
    AgentSpec,
    ArtifactError,
    CandidateManifest,
    CommandResult,
    EvaluationResult,
    EvaluationStatus,
    EvidenceRecord,
)

TIMESTAMP = "2026-08-23T05:06:07.000000Z"
LOCAL_TIMESTAMP = "2026-08-23T07:06:07+02:00"


@dataclass(frozen=True)
class _Artifact:
    """Stand-in for a loaded record or manifest. The CLI reads only `id`."""

    id: str


@dataclass(frozen=True)
class _Result:
    """Stand-in for EvaluationResult. The CLI reads status, summary and to_dict."""

    status: EvaluationStatus
    summary: str = "checked"

    def to_dict(self) -> dict[str, Any]:
        return {"status": self.status.value, "summary": self.summary}


@dataclass(frozen=True)
class _Command:
    """Stand-in for CommandResult. The CLI reads exit_code, timed_out, signal, to_dict."""

    exit_code: int | None = 0
    timed_out: bool = False
    signal: int | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "exit_code": self.exit_code,
            "signal": self.signal,
            "timed_out": self.timed_out,
        }


def _status(value: str) -> EvaluationStatus:
    return EvaluationStatus(value)


def _invoke(*argv: str) -> tuple[int, str, str]:
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        exit_code = cli.main(list(argv))
    return exit_code, out.getvalue(), err.getvalue()


def _exits(argv: list[str]) -> int:
    with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
        try:
            cli.main(argv)
        except SystemExit as stop:
            return int(stop.code or 0)
    raise AssertionError(f"{argv} did not exit")


class _CliTest(unittest.TestCase):
    def setUp(self) -> None:
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.repo = Path(temporary.name).resolve()
        self.workspace = self.repo / "workspace"
        self.candidate_dir = self.repo / "candidates" / "toy-theory"

    def run_cli(self, *argv: str) -> tuple[int, dict[str, Any], str]:
        """Run one command and assert stdout is one canonical JSON line."""
        exit_code, out, err = _invoke("--repo", str(self.repo), *argv)
        document = json.loads(out)
        self.assertEqual(out, canonical_json(document).decode("utf-8") + "\n")
        return exit_code, document, err


class EvidenceVerifyTest(_CliTest):
    def setUp(self) -> None:
        super().setUp()
        self.path = self.repo / "evidence" / "records" / "bell.json"
        self.record = _Artifact("bell.hensen-2015")

    def test_valid_record_passes(self) -> None:
        with (
            patch("principia.evidence.load_evidence", return_value=self.record) as load,
            patch("principia.evidence.verify_evidence", return_value=[]) as verify,
        ):
            exit_code, document, err = self.run_cli("evidence", "verify", str(self.path))

        load.assert_called_once_with(self.path)
        verify.assert_called_once_with(self.record, self.repo)
        self.assertEqual(exit_code, 0)
        self.assertEqual(
            document,
            {
                "command": "evidence verify",
                "errors": [],
                "id": "bell.hensen-2015",
                "ok": True,
                "path": "evidence/records/bell.json",
            },
        )
        self.assertEqual(err, "")

    def test_invalid_record_reports_every_error(self) -> None:
        errors = ["dataset sha256 mismatch", "source url is missing"]
        with (
            patch("principia.evidence.load_evidence", return_value=self.record),
            patch("principia.evidence.verify_evidence", return_value=errors),
        ):
            exit_code, document, err = self.run_cli("evidence", "verify", str(self.path))

        self.assertEqual(exit_code, 1)
        self.assertFalse(document["ok"])
        self.assertEqual(document["errors"], errors)
        self.assertEqual(
            err,
            "principia: evidence verify: dataset sha256 mismatch\n"
            "principia: evidence verify: source url is missing\n",
        )

    def test_unreadable_record_is_a_validation_verdict(self) -> None:
        with patch(
            "principia.evidence.load_evidence",
            side_effect=ArtifactError("unknown key 'gates'"),
        ):
            exit_code, document, err = self.run_cli("evidence", "verify", str(self.path))

        self.assertEqual(exit_code, 1)
        self.assertEqual(document["errors"], ["unknown key 'gates'"])
        self.assertIn("unknown key 'gates'", err)


class CandidateVerifyTest(_CliTest):
    def setUp(self) -> None:
        super().setUp()
        self.manifest = _Artifact("toy-theory")
        self.complexity = {"assumptions": 2, "exceptions": 0, "parameters": 1, "source_bytes": 512}

    def test_valid_candidate_reports_complexity_and_lineage(self) -> None:
        with (
            patch("principia.candidates.load_candidate", return_value=self.manifest) as load,
            patch("principia.candidates.verify_candidate", return_value=[]) as verify,
            patch(
                "principia.candidates.candidate_complexity", return_value=self.complexity
            ) as measure,
            patch(
                "principia.candidates.candidate_lineage", return_value=["root", "toy-theory"]
            ) as lineage,
        ):
            exit_code, document, err = self.run_cli(
                "candidate", "verify", str(self.candidate_dir)
            )

        load.assert_called_once_with(self.candidate_dir)
        verify.assert_called_once_with(self.manifest, self.candidate_dir, self.repo)
        measure.assert_called_once_with(self.manifest, self.repo)
        lineage.assert_called_once_with(self.candidate_dir.parent, "toy-theory")
        self.assertEqual(exit_code, 0)
        self.assertEqual(
            document,
            {
                "command": "candidate verify",
                "complexity": self.complexity,
                "errors": [],
                "id": "toy-theory",
                "lineage": ["root", "toy-theory"],
                "ok": True,
                "path": "candidates/toy-theory",
            },
        )
        self.assertEqual(err, "")

    def test_invalid_candidate_skips_complexity_and_lineage(self) -> None:
        with (
            patch("principia.candidates.load_candidate", return_value=self.manifest),
            patch(
                "principia.candidates.verify_candidate",
                return_value=["claim 'chsh' has no lean symbol"],
            ),
            patch("principia.candidates.candidate_complexity") as measure,
            patch("principia.candidates.candidate_lineage") as lineage,
        ):
            exit_code, document, err = self.run_cli(
                "candidate", "verify", str(self.candidate_dir)
            )

        measure.assert_not_called()
        lineage.assert_not_called()
        self.assertEqual(exit_code, 1)
        self.assertEqual(document["complexity"], {})
        self.assertEqual(document["lineage"], [])
        self.assertEqual(document["errors"], ["claim 'chsh' has no lean symbol"])
        self.assertIn("claim 'chsh' has no lean symbol", err)

    def test_broken_lineage_becomes_an_error(self) -> None:
        with (
            patch("principia.candidates.load_candidate", return_value=self.manifest),
            patch("principia.candidates.verify_candidate", return_value=[]),
            patch("principia.candidates.candidate_complexity", return_value=self.complexity),
            patch(
                "principia.candidates.candidate_lineage",
                side_effect=ArtifactError("parent 'ghost' is missing"),
            ),
        ):
            exit_code, document, err = self.run_cli(
                "candidate", "verify", str(self.candidate_dir)
            )

        self.assertEqual(exit_code, 1)
        self.assertEqual(document["errors"], ["parent 'ghost' is missing"])
        self.assertEqual(document["complexity"], self.complexity)
        self.assertEqual(document["lineage"], [])
        self.assertIn("parent 'ghost' is missing", err)


class EvaluateTest(_CliTest):
    def test_arguments_reach_the_evaluator(self) -> None:
        first = self.repo / "evidence" / "records" / "bell.json"
        second = self.repo / "evidence" / "records" / "gw.json"
        with patch(
            "principia.evaluator.evaluate_candidate", return_value=[_Result(_status("pass"))]
        ) as evaluate:
            exit_code, document, err = self.run_cli(
                "evaluate",
                str(self.candidate_dir),
                "--evidence",
                str(first),
                "--evidence",
                str(second),
                "--timestamp",
                LOCAL_TIMESTAMP,
            )

        evaluate.assert_called_once_with(
            self.candidate_dir,
            [first, second],
            self.repo,
            self.repo / ".principia" / "evaluations",
            TIMESTAMP,
        )
        self.assertEqual(exit_code, 0)
        self.assertEqual(document["candidate"], "candidates/toy-theory")
        self.assertEqual(document["output"], ".principia/evaluations")
        self.assertEqual(document["results"], [{"status": "pass", "summary": "checked"}])
        self.assertEqual(document["status"], "pass")
        self.assertEqual(document["timestamp"], TIMESTAMP)
        self.assertEqual(err, "")

    def test_no_evidence_option_evaluates_nothing_but_lean(self) -> None:
        with patch(
            "principia.evaluator.evaluate_candidate", return_value=[_Result(_status("pass"))]
        ) as evaluate:
            self.run_cli("evaluate", str(self.candidate_dir), "--timestamp", TIMESTAMP)

        self.assertEqual(evaluate.call_args.args[1], [])

    def test_output_option_overrides_the_archive_directory(self) -> None:
        output = self.repo / "bundles"
        with patch(
            "principia.evaluator.evaluate_candidate", return_value=[_Result(_status("pass"))]
        ) as evaluate:
            _, document, _ = self.run_cli(
                "evaluate",
                str(self.candidate_dir),
                "--output",
                str(output),
                "--timestamp",
                TIMESTAMP,
            )

        self.assertEqual(evaluate.call_args.args[3], output)
        self.assertEqual(document["output"], "bundles")

    def test_status_decides_the_exit_code(self) -> None:
        for status, expected in (
            ("pass", 0),
            ("not_applicable", 0),
            ("inconclusive", 1),
            ("fail", 1),
            ("error", 2),
        ):
            with self.subTest(status=status):
                with patch(
                    "principia.evaluator.evaluate_candidate",
                    return_value=[_Result(_status(status))],
                ):
                    exit_code, document, err = self.run_cli(
                        "evaluate", str(self.candidate_dir), "--timestamp", TIMESTAMP
                    )

                self.assertEqual(exit_code, expected)
                self.assertEqual(document["status"], status)
                self.assertIs(document["ok"], expected == 0)
                if expected == 0:
                    self.assertEqual(err, "")
                else:
                    self.assertIn(f"{status}: checked", err)

    def test_the_worst_status_decides_the_whole_run(self) -> None:
        results = [
            _Result(_status("pass"), "lean checks passed"),
            _Result(_status("fail"), "chsh bound violated"),
            _Result(_status("error"), "lake is missing"),
        ]
        with patch("principia.evaluator.evaluate_candidate", return_value=results):
            exit_code, document, err = self.run_cli(
                "evaluate", str(self.candidate_dir), "--timestamp", TIMESTAMP
            )

        self.assertEqual(exit_code, 2)
        self.assertEqual(document["status"], "error")
        self.assertEqual(len(document["results"]), 3)
        self.assertIn("fail: chsh bound violated", err)
        self.assertIn("error: lake is missing", err)
        self.assertNotIn("lean checks passed", err)

    def test_an_empty_result_set_establishes_nothing(self) -> None:
        with patch("principia.evaluator.evaluate_candidate", return_value=[]):
            exit_code, document, err = self.run_cli(
                "evaluate", str(self.candidate_dir), "--timestamp", TIMESTAMP
            )

        self.assertEqual(exit_code, 1)
        self.assertEqual(document["status"], "inconclusive")
        self.assertEqual(document["results"], [])
        self.assertIn("no evaluation result was produced", err)

    def test_rejected_candidate_directory_is_an_infrastructure_error(self) -> None:
        with patch(
            "principia.evaluator.evaluate_candidate",
            side_effect=ArtifactError("candidate directory escapes the repository"),
        ):
            exit_code, document, err = self.run_cli(
                "evaluate", str(self.candidate_dir), "--timestamp", TIMESTAMP
            )

        self.assertEqual(exit_code, 2)
        self.assertEqual(document["errors"], ["candidate directory escapes the repository"])
        self.assertIn("candidate directory escapes the repository", err)


class AgentRunTest(_CliTest):
    def setUp(self) -> None:
        super().setUp()
        self.spec_path = self.repo / "agents" / "theorist.json"
        self.request_path = self.repo / "request.json"
        self.spec_document = {"command": ["/usr/bin/true"], "network": False}
        self.request_document = {"iteration": 1}
        self.spec = object()

    def _run(self, result: _Command, *extra: str):
        with (
            patch(
                "principia.artifacts.load_json",
                side_effect=[self.spec_document, self.request_document],
            ) as load,
            patch.object(AgentSpec, "from_dict", return_value=self.spec) as from_dict,
            patch("principia.runner.run_agent", return_value=result) as run,
        ):
            outcome = self.run_cli(
                "agent",
                "run",
                str(self.spec_path),
                "--workspace",
                str(self.workspace),
                *extra,
                "--timestamp",
                TIMESTAMP,
            )
        return outcome, load, from_dict, run

    def test_spec_request_and_timestamp_reach_the_runner(self) -> None:
        (exit_code, document, err), load, from_dict, run = self._run(
            _Command(), "--request", str(self.request_path)
        )

        self.assertEqual(
            [call.args for call in load.call_args_list],
            [(self.spec_path,), (self.request_path,)],
        )
        from_dict.assert_called_once_with(self.spec_document)
        run.assert_called_once_with(
            self.spec, self.workspace, self.request_document, self.repo, TIMESTAMP
        )
        self.assertEqual(exit_code, 0)
        self.assertEqual(
            document,
            {
                "command": "agent run",
                "ok": True,
                "result": {"exit_code": 0, "signal": None, "timed_out": False},
                "spec": "agents/theorist.json",
                "timestamp": TIMESTAMP,
                "workspace": "workspace",
            },
        )
        self.assertEqual(err, "")

    def test_without_a_request_file_the_agent_gets_an_empty_request(self) -> None:
        _, load, _, run = self._run(_Command())

        load.assert_called_once_with(self.spec_path)
        self.assertEqual(run.call_args.args[2], {})

    def test_failed_runs_exit_one_and_explain_themselves(self) -> None:
        for result, message in (
            (_Command(exit_code=3), "the agent exited with status 3"),
            (_Command(exit_code=None, timed_out=True, signal=9), "the agent timed out"),
            (_Command(exit_code=None, signal=11), "the agent died from signal 11"),
        ):
            with self.subTest(message=message):
                (exit_code, document, err), _, _, _ = self._run(result)

                self.assertEqual(exit_code, 1)
                self.assertFalse(document["ok"])
                self.assertEqual(document["result"], result.to_dict())
                self.assertEqual(err, f"principia: agent run: {message}\n")

    def test_an_unusable_sandbox_is_an_infrastructure_error(self) -> None:
        with (
            patch("principia.artifacts.load_json", return_value=self.spec_document),
            patch.object(AgentSpec, "from_dict", return_value=self.spec),
            patch(
                "principia.runner.run_agent",
                side_effect=RuntimeError("bwrap is not installed"),
            ),
        ):
            exit_code, document, err = self.run_cli(
                "agent",
                "run",
                str(self.spec_path),
                "--workspace",
                str(self.workspace),
                "--timestamp",
                TIMESTAMP,
            )

        self.assertEqual(exit_code, 2)
        self.assertEqual(document["errors"], ["bwrap is not installed"])
        self.assertIn("bwrap is not installed", err)

    def test_an_invalid_spec_is_an_infrastructure_error(self) -> None:
        with (
            patch("principia.artifacts.load_json", return_value=self.spec_document),
            patch.object(
                AgentSpec, "from_dict", side_effect=ArtifactError("command must be a list")
            ),
            patch("principia.runner.run_agent") as run,
        ):
            exit_code, document, _ = self.run_cli(
                "agent",
                "run",
                str(self.spec_path),
                "--workspace",
                str(self.workspace),
                "--timestamp",
                TIMESTAMP,
            )

        run.assert_not_called()
        self.assertEqual(exit_code, 2)
        self.assertEqual(document["errors"], ["command must be a list"])


class DiscoverTest(_CliTest):
    def setUp(self) -> None:
        super().setUp()
        self.config_path = self.repo / "discovery" / "bell.json"

    def _report(self, status: str, error: dict[str, Any] | None = None) -> dict[str, Any]:
        return {
            "accepted": status == "accepted",
            "error": error,
            "iterations": [],
            "status": status,
        }

    def test_arguments_and_a_fixed_timestamp_reach_the_loop(self) -> None:
        report = self._report("accepted")
        with patch("principia.discovery.run_discovery", return_value=report) as run:
            exit_code, document, err = self.run_cli(
                "discover",
                str(self.config_path),
                "--workspace",
                str(self.workspace),
                "--timestamp",
                LOCAL_TIMESTAMP,
            )

        config, workspace, repo_root, output_root, factory = run.call_args.args
        self.assertEqual(config, self.config_path)
        self.assertEqual(workspace, self.workspace)
        self.assertEqual(repo_root, self.repo)
        self.assertEqual(output_root, self.repo / ".principia" / "discovery")
        self.assertEqual([factory(), factory()], [TIMESTAMP, TIMESTAMP])
        self.assertEqual(exit_code, 0)
        self.assertEqual(document["config"], "discovery/bell.json")
        self.assertEqual(document["output"], ".principia/discovery")
        self.assertEqual(document["report"], report)
        self.assertEqual(document["workspace"], "workspace")
        self.assertEqual(err, "")

    def test_the_default_factory_stamps_the_current_utc_time(self) -> None:
        with patch(
            "principia.discovery.run_discovery", return_value=self._report("accepted")
        ) as run:
            self.run_cli("discover", str(self.config_path), "--workspace", str(self.workspace))

        stamped = run.call_args.args[4]()
        self.assertRegex(stamped, r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d{6}Z$")
        self.assertIsInstance(datetime.strptime(stamped, "%Y-%m-%dT%H:%M:%S.%fZ"), datetime)

    def test_status_decides_the_exit_code(self) -> None:
        for status, expected in (
            ("accepted", 0),
            ("max_iterations", 1),
            ("agent_error", 2),
            ("reviewer_mutation", 2),
            ("something_new", 2),
        ):
            with self.subTest(status=status):
                with patch(
                    "principia.discovery.run_discovery", return_value=self._report(status)
                ):
                    exit_code, document, err = self.run_cli(
                        "discover",
                        str(self.config_path),
                        "--workspace",
                        str(self.workspace),
                    )

                self.assertEqual(exit_code, expected)
                self.assertIs(document["ok"], expected == 0)
                if expected == 0:
                    self.assertEqual(err, "")
                else:
                    self.assertIn(status, err)

    def test_the_error_object_becomes_the_diagnostic(self) -> None:
        failure = {
            "iteration": 2,
            "reason": "the theorist wrote no candidate",
            "stage": "theorist",
        }
        report = self._report("agent_error", failure)
        with patch("principia.discovery.run_discovery", return_value=report):
            exit_code, _, err = self.run_cli(
                "discover", str(self.config_path), "--workspace", str(self.workspace)
            )

        self.assertEqual(exit_code, 2)
        self.assertEqual(
            err, "principia: discover: theorist: the theorist wrote no candidate\n"
        )

    def test_an_invalid_config_is_an_infrastructure_error(self) -> None:
        with patch(
            "principia.discovery.run_discovery",
            side_effect=ArtifactError("max_iterations must be at least 1"),
        ):
            exit_code, document, err = self.run_cli(
                "discover", str(self.config_path), "--workspace", str(self.workspace)
            )

        self.assertEqual(exit_code, 2)
        self.assertEqual(document["errors"], ["max_iterations must be at least 1"])
        self.assertIn("max_iterations must be at least 1", err)


class UsageTest(_CliTest):
    def test_help_lists_every_command(self) -> None:
        out = io.StringIO()
        with redirect_stdout(out), self.assertRaises(SystemExit) as stop:
            cli.main(["--help"])

        self.assertEqual(stop.exception.code, 0)
        text = out.getvalue()
        for command in ("evidence", "candidate", "evaluate", "agent", "discover", "--repo"):
            self.assertIn(command, text)

    def test_every_command_has_help(self) -> None:
        for argv in (
            ["evidence", "verify", "--help"],
            ["candidate", "verify", "--help"],
            ["evaluate", "--help"],
            ["agent", "run", "--help"],
            ["discover", "--help"],
        ):
            with self.subTest(argv=argv):
                self.assertEqual(_exits(argv), 0)

    def test_version_reports_the_package_version(self) -> None:
        out = io.StringIO()
        with redirect_stdout(out), self.assertRaises(SystemExit) as stop:
            cli.main(["--version"])

        self.assertEqual(stop.exception.code, 0)
        self.assertEqual(out.getvalue().strip(), f"principia {__version__}")

    def test_usage_errors_exit_two(self) -> None:
        for argv in (
            [],
            ["bogus"],
            ["evidence"],
            ["candidate"],
            ["agent"],
            ["evidence", "verify"],
            ["agent", "run", "spec.json"],
            ["discover", "config.json"],
            ["evaluate", "candidates/toy", "--timestamp", "yesterday"],
            ["evaluate", "candidates/toy", "--timestamp", "2026-08-23T05:06:07"],
        ):
            with self.subTest(argv=argv):
                self.assertEqual(_exits(argv), 2)

    def test_a_missing_repository_root_stops_before_the_command(self) -> None:
        missing = self.repo / "gone"
        with patch("principia.evidence.load_evidence") as load:
            exit_code, out, err = _invoke(
                "--repo", str(missing), "evidence", "verify", "bell.json"
            )

        load.assert_not_called()
        document = json.loads(out)
        self.assertEqual(exit_code, 2)
        self.assertFalse(document["ok"])
        self.assertRegex(document["errors"][0], r"^repository root is not a directory: ")
        self.assertIn("repository root is not a directory", err)

    def test_the_repository_root_defaults_to_the_current_directory(self) -> None:
        record = _Artifact("bell")
        with (
            patch("principia.evidence.load_evidence", return_value=record),
            patch("principia.evidence.verify_evidence", return_value=[]) as verify,
        ):
            exit_code, _, _ = _invoke("evidence", "verify", "bell.json")

        self.assertEqual(exit_code, 0)
        verify.assert_called_once_with(record, Path.cwd().resolve())

    def test_paths_outside_the_repository_stay_absolute(self) -> None:
        outside = Path("/etc/principia/bell.json")
        with (
            patch("principia.evidence.load_evidence", return_value=_Artifact("bell")),
            patch("principia.evidence.verify_evidence", return_value=[]),
        ):
            _, document, _ = self.run_cli("evidence", "verify", str(outside))

        self.assertEqual(document["path"], "/etc/principia/bell.json")


class ModelContractTest(unittest.TestCase):
    """The CLI reads these names off objects that the other modules return."""

    def test_models_expose_what_the_cli_uses(self) -> None:
        for model, attributes in (
            (EvidenceRecord, {"id"}),
            (CandidateManifest, {"id"}),
            (EvaluationResult, {"status", "summary"}),
            (CommandResult, {"exit_code", "timed_out", "signal"}),
        ):
            with self.subTest(model=model.__name__):
                names = {field.name for field in dataclasses.fields(model)}
                self.assertLessEqual(attributes, names)
                self.assertTrue(callable(model.to_dict))
        self.assertTrue(callable(AgentSpec.from_dict))

    def test_evaluation_statuses_match_the_exit_table(self) -> None:
        self.assertEqual(
            {status.value for status in EvaluationStatus},
            {"pass", "fail", "inconclusive", "not_applicable", "error"},
        )

    def test_an_unusable_sandbox_raises_a_runtime_error(self) -> None:
        self.assertTrue(issubclass(runner.SandboxUnavailableError, RuntimeError))

    def test_artifact_errors_are_value_errors(self) -> None:
        self.assertTrue(issubclass(ArtifactError, ValueError))


if __name__ == "__main__":
    unittest.main()
