"""Behavior tests for the discovery loop, driven through fake boundary functions.

The loop has exactly two boundaries: the agent runner and the candidate evaluator.
The fakes below stand in for both. They are scripted per iteration, they record
every call, and they edit the workspace the way real agents would, which is what
lets these tests check archiving, feedback and mutation detection without a
sandbox, without Lean and without a network.

`_touch` deliberately writes outside the workspace it was handed. The real sandbox
forbids that; the fake performs the breach so the loop's own detection is tested
rather than assumed.
"""

from __future__ import annotations

import hashlib
import json
import shutil
import unittest
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from tempfile import TemporaryDirectory

from principia.artifacts import canonical_json, load_json, sha256_json
from principia.discovery import (
    STATUS_ACCEPTED,
    STATUS_AGENT_ERROR,
    STATUS_MAX_ITERATIONS,
    STATUS_REVIEWER_MUTATION,
    DiscoveryConfig,
    run_discovery,
)
from principia.models import (
    SCHEMA_VERSION,
    AgentSpec,
    ArtifactError,
    CommandResult,
    EvaluationResult,
    EvaluationStatus,
)

_CANDIDATE_ID = "bell-chsh"
_EVIDENCE_ID = "aspect-1982-chsh"
_EVIDENCE_PATH = "evidence/records/aspect-1982-chsh.json"
_THEORY_FILE = f"{_CANDIDATE_ID}/Theory.lean"

_Step = Callable[[Path, Mapping[str, object]], "dict[str, object]"]


def _spec(role: str) -> dict[str, object]:
    return {
        "command": ["/usr/bin/env", role],
        "network": False,
        "timeout_seconds": 60.0,
        "env_allowlist": [],
        "read_only_binds": [],
    }


def _config(
    *, reviewer: bool = True, max_iterations: int = 2, **overrides: object
) -> dict[str, object]:
    config: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "theorist": _spec("theorist"),
        "max_iterations": max_iterations,
        "candidate_dir": _CANDIDATE_ID,
        "evidence_paths": [_EVIDENCE_PATH],
    }
    if reviewer:
        config["reviewer"] = _spec("reviewer")
    config.update(overrides)
    return config


class _Clock:
    """One timestamp per call, in order, so a run is reproducible."""

    def __init__(self) -> None:
        self.issued: list[str] = []

    def __call__(self) -> str:
        index = len(self.issued)
        self.issued.append(f"2026-08-23T00:{index // 60:02d}:{index % 60:02d}.000000Z")
        return self.issued[-1]


@dataclass(frozen=True, slots=True)
class _AgentCall:
    """One recorded agent invocation."""

    role: str
    spec: AgentSpec
    workspace: Path
    repo_root: Path
    request: Mapping[str, object]
    timestamp: str


@dataclass(frozen=True, slots=True)
class _EvaluationCall:
    """One recorded evaluator invocation."""

    candidate_dir: Path
    evidence_paths: tuple[Path, ...]
    output_dir: Path
    timestamp: str


class _Agents:
    """Scripted stand-in for `principia.runner.run_agent`.

    Step N of a role's script serves call N of that role; the last step repeats, so
    a one-step script describes an agent that always behaves the same way.
    """

    def __init__(self, theorist: Sequence[_Step], reviewer: Sequence[_Step] = ()) -> None:
        self.scripts = {"theorist": list(theorist), "reviewer": list(reviewer)}
        self.calls: list[_AgentCall] = []

    def __call__(
        self,
        spec: AgentSpec,
        workspace: Path,
        request: Mapping[str, object],
        repo_root: Path,
        timestamp: str,
    ) -> CommandResult:
        role = str(request["role"])
        script = self.scripts[role]
        if not script:
            raise AssertionError(f"the {role} was invoked but has no scripted step")
        index = sum(1 for call in self.calls if call.role == role)
        self.calls.append(
            _AgentCall(
                role=role,
                spec=spec,
                workspace=Path(workspace),
                repo_root=Path(repo_root),
                request=request,
                timestamp=timestamp,
            )
        )
        reply = script[min(index, len(script) - 1)](Path(workspace), request)
        return _command(timestamp, request, **reply)

    def roles(self) -> list[str]:
        return [call.role for call in self.calls]

    def requests(self, role: str) -> list[Mapping[str, object]]:
        return [call.request for call in self.calls if call.role == role]


class _Evaluations:
    """Scripted stand-in for `principia.evaluator.evaluate_candidate`."""

    def __init__(self, rounds: Sequence[Sequence[str]]) -> None:
        self.rounds = [list(statuses) for statuses in rounds]
        self.calls: list[_EvaluationCall] = []

    def __call__(
        self,
        candidate_dir: Path,
        evidence_paths: Sequence[Path],
        repo_root: Path,
        output_dir: Path,
        timestamp: str,
    ) -> list[EvaluationResult]:
        index = len(self.calls)
        self.calls.append(
            _EvaluationCall(
                candidate_dir=Path(candidate_dir),
                evidence_paths=tuple(Path(path) for path in evidence_paths),
                output_dir=Path(output_dir),
                timestamp=timestamp,
            )
        )
        statuses = self.rounds[min(index, len(self.rounds) - 1)]
        bundle = Path(output_dir)
        bundle.mkdir(parents=True, exist_ok=True)
        (bundle / "bundle.json").write_text(json.dumps(statuses), encoding="utf-8")
        return [_result(status, timestamp, position) for position, status in enumerate(statuses)]


def _result(status: str, timestamp: str, position: int) -> EvaluationResult:
    """A formal result carries no evidence id; evidence results carry one."""
    return EvaluationResult(
        schema_version=SCHEMA_VERSION,
        candidate_id=_CANDIDATE_ID,
        evidence_id=None if position == 0 else _EVIDENCE_ID,
        status=EvaluationStatus(status),
        summary=f"scripted {status}",
        metrics={},
        artifacts={},
        timestamp=timestamp,
    )


def _command(
    timestamp: str,
    request: Mapping[str, object],
    *,
    exit_code: int | None = 0,
    stdout: str = "",
    stderr: str = "",
    timed_out: bool = False,
    signal: int | None = None,
) -> CommandResult:
    return CommandResult(
        command=("/usr/bin/env", "agent"),
        exit_code=exit_code,
        signal=signal,
        timed_out=timed_out,
        stdout=stdout,
        stderr=stderr,
        stdout_sha256=_sha256(stdout),
        stderr_sha256=_sha256(stderr),
        request_sha256=hashlib.sha256(canonical_json(request)).hexdigest(),
        duration_seconds=0.125,
        timestamp=timestamp,
    )


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _edit(
    files: Mapping[str, str] | None = None, *, remove: Sequence[str] = (), **reply: object
) -> _Step:
    """A scripted agent step: write files in its workspace, drop paths, then exit."""

    def step(workspace: Path, request: Mapping[str, object]) -> dict[str, object]:
        for name, text in (files or {}).items():
            path = workspace / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        for name in remove:
            shutil.rmtree(workspace / name)
        return dict(reply)

    return step


def _touch(path: Path, text: str) -> _Step:
    """A step that writes outside its own workspace, then accepts anyway."""

    def step(workspace: Path, request: Mapping[str, object]) -> dict[str, object]:
        path.write_text(text, encoding="utf-8")
        return {"stdout": _verdict("accept")}

    return step


def _verdict(decision: str, *, summary: str = "reviewed", findings: Sequence[str] = ()) -> str:
    payload: dict[str, object] = {"decision": decision, "summary": summary}
    if findings:
        payload["findings"] = list(findings)
    return json.dumps(payload)


def _accepts() -> list[_Step]:
    """A reviewer that accepts whatever it is shown."""
    return [_edit(stdout=_verdict("accept"))]


class _LoopTest(unittest.TestCase):
    """A throwaway repository holding a workspace, a seeded candidate and a config."""

    def setUp(self) -> None:
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.workspace = self.root / ".principia" / "work"
        self.candidate = self.workspace / _CANDIDATE_ID
        self.candidate.mkdir(parents=True)
        (self.candidate / "candidate.json").write_text(
            json.dumps({"id": _CANDIDATE_ID}), encoding="utf-8"
        )
        evidence = self.root / _EVIDENCE_PATH
        evidence.parent.mkdir(parents=True)
        evidence.write_text(json.dumps({"id": _EVIDENCE_ID}), encoding="utf-8")
        self.output = self.root / ".principia" / "discovery"
        self.config_path = self.root / "discovery.json"
        self.write_config()
        self.clock = _Clock()

    def write_config(self, **overrides: object) -> None:
        self.config_path.write_text(json.dumps(_config(**overrides)), encoding="utf-8")

    def discover(
        self,
        agents: _Agents,
        evaluations: _Evaluations,
        *,
        workspace: Path | None = None,
        output: Path | None = None,
        clock: Callable[[], str] | None = None,
    ) -> dict[str, object]:
        return run_discovery(
            self.config_path,
            self.workspace if workspace is None else workspace,
            self.root,
            self.output if output is None else output,
            self.clock if clock is None else clock,
            agent_runner=agents,
            candidate_evaluator=evaluations,
        )

    def archive(self, report: Mapping[str, object]) -> Path:
        return Path(str(report["archive_root"]))


class DiscoveryLoopTest(_LoopTest):
    def test_accepts_on_the_first_pass(self) -> None:
        theory = _edit({_THEORY_FILE: "theorem chsh : True := trivial\n"})
        agents = _Agents([theory], _accepts())
        evaluations = _Evaluations([["pass", "pass"]])

        report = self.discover(agents, evaluations)

        self.assertEqual(report["status"], STATUS_ACCEPTED)
        self.assertIs(report["accepted"], True)
        self.assertIsNone(report["error"])
        self.assertEqual(agents.roles(), ["theorist", "reviewer"])
        self.assertEqual(len(evaluations.calls), 1)
        records = report["iterations"]
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["outcome"], STATUS_ACCEPTED)
        self.assertEqual(records[0]["evaluations"]["statuses"], ["pass", "pass"])
        self.assertEqual(records[0]["review"]["decision"], "accept")

    def test_repairs_after_evaluator_feedback(self) -> None:
        agents = _Agents(
            [_edit({_THEORY_FILE: "first attempt\n"}), _edit({_THEORY_FILE: "repaired\n"})],
            _accepts(),
        )
        evaluations = _Evaluations([["pass", "fail"], ["pass", "pass"]])

        report = self.discover(agents, evaluations)

        self.assertEqual(report["status"], STATUS_ACCEPTED)
        first, second = report["iterations"]
        self.assertEqual(first["outcome"], "evaluator_feedback")
        self.assertEqual(first["evaluations"]["statuses"], ["pass", "fail"])
        self.assertEqual(second["outcome"], STATUS_ACCEPTED)
        self.assertNotEqual(
            first["candidate_snapshot"]["sha256"], second["candidate_snapshot"]["sha256"]
        )
        requests = agents.requests("theorist")
        self.assertIsNone(requests[0]["prior_evaluations"])
        self.assertEqual(
            [entry["status"] for entry in requests[1]["prior_evaluations"]], ["pass", "fail"]
        )
        self.assertEqual(
            [entry["summary"] for entry in requests[1]["prior_evaluations"]],
            ["scripted pass", "scripted fail"],
        )
        self.assertIsNone(requests[1]["prior_review"])
        self.assertEqual(agents.roles(), ["theorist", "theorist", "reviewer"])

    def test_stops_at_the_iteration_limit(self) -> None:
        agents = _Agents([_edit({_THEORY_FILE: "still wrong\n"})], _accepts())
        evaluations = _Evaluations([["fail"]])

        report = self.discover(agents, evaluations)

        self.assertEqual(report["status"], STATUS_MAX_ITERATIONS)
        self.assertIs(report["accepted"], False)
        self.assertIsNone(report["error"])
        self.assertEqual(len(report["iterations"]), 2)
        self.assertEqual(report["max_iterations"], 2)
        self.assertEqual(agents.roles(), ["theorist", "theorist"])
        self.assertEqual(len(evaluations.calls), 2)
        self.assertEqual(
            [record["outcome"] for record in report["iterations"]],
            ["evaluator_feedback", "evaluator_feedback"],
        )

    def test_theorist_command_error_ends_the_run(self) -> None:
        agents = _Agents([_edit(exit_code=3, stderr="traceback\n")], _accepts())
        evaluations = _Evaluations([["pass"]])

        report = self.discover(agents, evaluations)

        self.assertEqual(report["status"], STATUS_AGENT_ERROR)
        self.assertEqual(
            report["error"], {"stage": "theorist", "iteration": 1, "reason": "exit code 3"}
        )
        self.assertEqual(agents.roles(), ["theorist"])
        self.assertEqual(evaluations.calls, [])
        record = report["iterations"][0]
        self.assertEqual(len(report["iterations"]), 1)
        self.assertEqual(record["outcome"], STATUS_AGENT_ERROR)
        self.assertNotIn("candidate_snapshot", record)
        self.assertNotIn("evaluations", record)
        archived = load_json(self.archive(report) / "iteration-001" / "theorist-command.json")
        self.assertEqual(archived["exit_code"], 3)
        self.assertEqual(archived["stderr"], "traceback\n")

    def test_theorist_timeout_ends_the_run(self) -> None:
        # A timeout reaches the loop the way the runner reports it: killed, so no exit code.
        agents = _Agents([_edit(exit_code=None, signal=9, timed_out=True)])
        evaluations = _Evaluations([["pass"]])

        report = self.discover(agents, evaluations)

        self.assertEqual(report["status"], STATUS_AGENT_ERROR)
        self.assertEqual(report["error"]["stage"], "theorist")
        self.assertIn("timed out", str(report["error"]["reason"]))
        self.assertEqual(report["iterations"][0]["theorist"]["timed_out"], True)
        self.assertEqual(evaluations.calls, [])

    def test_theorist_deleting_the_candidate_ends_the_run(self) -> None:
        agents = _Agents([_edit(remove=[_CANDIDATE_ID])])
        evaluations = _Evaluations([["pass"]])

        report = self.discover(agents, evaluations)

        self.assertEqual(report["status"], STATUS_AGENT_ERROR)
        self.assertEqual(report["error"]["stage"], "theorist")
        self.assertIn("candidate directory is gone", str(report["error"]["reason"]))
        self.assertEqual(evaluations.calls, [])

    def test_an_empty_evaluation_set_is_not_an_acceptance(self) -> None:
        agents = _Agents([_edit({_THEORY_FILE: "unchecked\n"})], _accepts())
        evaluations = _Evaluations([[]])

        report = self.discover(agents, evaluations)

        self.assertEqual(report["status"], STATUS_AGENT_ERROR)
        self.assertEqual(report["error"]["stage"], "evaluator")
        self.assertIs(report["accepted"], False)
        self.assertEqual(agents.roles(), ["theorist"])
        self.assertEqual(report["iterations"][0]["evaluations"]["statuses"], [])

    def test_reviewer_rejection_returns_to_the_theorist(self) -> None:
        rejection = _verdict(
            "reject",
            summary="assumption 2 has no source",
            findings=["assumptions[1].source is missing"],
        )
        agents = _Agents(
            [_edit({_THEORY_FILE: "first\n"}), _edit({_THEORY_FILE: "second\n"})],
            [_edit(stdout=rejection), *_accepts()],
        )
        evaluations = _Evaluations([["pass"], ["pass"]])

        report = self.discover(agents, evaluations)

        self.assertEqual(report["status"], STATUS_ACCEPTED)
        self.assertEqual(agents.roles(), ["theorist", "reviewer", "theorist", "reviewer"])
        first, second = report["iterations"]
        self.assertEqual(first["outcome"], "review_rejected")
        self.assertEqual(first["review"]["decision"], "reject")
        self.assertEqual(second["review"]["decision"], "accept")
        request = agents.requests("theorist")[1]
        self.assertEqual(
            request["prior_review"],
            {
                "decision": "reject",
                "summary": "assumption 2 has no source",
                "findings": ["assumptions[1].source is missing"],
            },
        )
        self.assertEqual([entry["status"] for entry in request["prior_evaluations"]], ["pass"])
        archived = load_json(self.archive(report) / "iteration-001" / "review.json")
        self.assertEqual(archived["decision"], "reject")
        self.assertEqual(archived["findings"], ["assumptions[1].source is missing"])

    def test_reviewer_mutation_beats_acceptance(self) -> None:
        agents = _Agents(
            [_edit({_THEORY_FILE: "reviewed version\n"})],
            [_touch(self.candidate / "Theory.lean", "the reviewer rewrote this\n")],
        )
        evaluations = _Evaluations([["pass"]])

        report = self.discover(agents, evaluations)

        self.assertEqual(report["status"], STATUS_REVIEWER_MUTATION)
        self.assertIs(report["accepted"], False)
        self.assertEqual(report["error"]["stage"], "reviewer")
        self.assertEqual(report["error"]["iteration"], 1)
        review = report["iterations"][0]["review"]
        self.assertEqual(review["changes"], [{"path": _THEORY_FILE, "change": "modified"}])
        self.assertNotEqual(review["workspace_sha256_before"], review["workspace_sha256_after"])
        self.assertNotIn("decision", review)
        self.assertEqual(len(report["iterations"]), 1)

    def test_reviewer_additions_to_the_workspace_are_mutations(self) -> None:
        agents = _Agents(
            [_edit({_THEORY_FILE: "reviewed version\n"})],
            [_touch(self.candidate / "notes.md", "reviewer notes\n")],
        )
        evaluations = _Evaluations([["pass"]])

        report = self.discover(agents, evaluations)

        self.assertEqual(report["status"], STATUS_REVIEWER_MUTATION)
        self.assertEqual(
            report["iterations"][0]["review"]["changes"],
            [{"path": f"{_CANDIDATE_ID}/notes.md", "change": "added"}],
        )

    def test_an_unreadable_verdict_is_never_an_acceptance(self) -> None:
        for stdout, fragment in (
            ("looks good to me", "not JSON"),
            ("[]", "must be a JSON object"),
            (json.dumps({"decision": "maybe", "summary": "unsure"}), "'accept' or 'reject'"),
            (json.dumps({"decision": "accept"}), "non-empty summary"),
            (json.dumps({"decision": "accept", "summary": "ok", "verdict": 1}), "unknown keys"),
            (json.dumps({"decision": "accept", "summary": "ok", "findings": [2]}), "findings"),
        ):
            with self.subTest(stdout=stdout):
                agents = _Agents([_edit({_THEORY_FILE: "candidate\n"})], [_edit(stdout=stdout)])
                report = self.discover(agents, _Evaluations([["pass"]]))
                self.assertEqual(report["status"], STATUS_AGENT_ERROR)
                self.assertEqual(report["error"]["stage"], "reviewer")
                self.assertIn(fragment, str(report["error"]["reason"]))
                self.assertNotIn("decision", report["iterations"][0]["review"])

    def test_reviewer_reviews_a_snapshot_from_its_own_workspace(self) -> None:
        agents = _Agents([_edit({_THEORY_FILE: "candidate\n"})], _accepts())
        evaluations = _Evaluations([["pass"]])

        report = self.discover(agents, evaluations)

        theorist, reviewer = agents.calls
        self.assertEqual(theorist.workspace, self.workspace)
        self.assertFalse(reviewer.workspace.is_relative_to(self.workspace))
        self.assertTrue(reviewer.workspace.is_dir())
        self.assertEqual(list(theorist.spec.command), ["/usr/bin/env", "theorist"])
        self.assertEqual(list(reviewer.spec.command), ["/usr/bin/env", "reviewer"])
        request = reviewer.request
        self.assertIs(request["candidate_writable"], False)
        self.assertEqual(request["candidate_dir"], str(self.candidate))
        snapshot = request["candidate_snapshot"]
        self.assertIn("Theory.lean", snapshot)
        self.assertIn("candidate.json", snapshot)
        self.assertEqual(
            sha256_json(snapshot), report["iterations"][0]["candidate_snapshot"]["sha256"]
        )
        self.assertEqual([entry["status"] for entry in request["evaluations"]], ["pass"])
        self.assertEqual(evaluations.calls[0].evidence_paths, (self.root / _EVIDENCE_PATH,))
        self.assertEqual(evaluations.calls[0].candidate_dir, self.candidate)

    def test_theorist_request_points_at_the_writable_candidate(self) -> None:
        agents = _Agents([_edit({_THEORY_FILE: "candidate\n"})], _accepts())

        self.discover(agents, _Evaluations([["pass"]]))

        request = agents.requests("theorist")[0]
        self.assertEqual(request["role"], "theorist")
        self.assertEqual(request["iteration"], 1)
        self.assertEqual(request["max_iterations"], 2)
        self.assertEqual(request["candidate_dir"], _CANDIDATE_ID)
        self.assertEqual(request["repo_root"], str(self.root))
        self.assertEqual(request["evidence_paths"], [str(self.root / _EVIDENCE_PATH)])
        self.assertTrue((self.workspace / str(request["candidate_dir"])).is_dir())

    def test_archive_holds_the_whole_lineage(self) -> None:
        agents = _Agents(
            [_edit({_THEORY_FILE: "first\n"}), _edit({_THEORY_FILE: "second\n"})],
            _accepts(),
        )
        evaluations = _Evaluations([["fail"], ["pass"]])

        report = self.discover(agents, evaluations)
        archive = self.archive(report)

        self.assertEqual(load_json(archive / "run.json"), report)
        config = load_json(archive / "config.json")
        self.assertEqual(config["sha256"], report["config"]["sha256"])
        self.assertEqual(config["sha256"], sha256_json(load_json(self.config_path)))
        self.assertEqual(config["config"], DiscoveryConfig.from_dict(_config()).to_dict())
        self.assertEqual(config["candidate_dir"], str(self.candidate))

        for index, record in enumerate(report["iterations"], start=1):
            iteration_dir = archive / f"iteration-{index:03d}"
            with self.subTest(iteration=index):
                self.assertEqual(load_json(iteration_dir / "iteration.json"), record)
                command = load_json(iteration_dir / "theorist-command.json")
                self.assertEqual(
                    sha256_json(load_json(iteration_dir / "request.json")),
                    record["request_sha256"],
                )
                self.assertEqual(command["request_sha256"], record["request_sha256"])
                self.assertEqual(sha256_json(command), record["theorist"]["command_sha256"])
                self.assertEqual(
                    sha256_json(load_json(iteration_dir / "candidate-snapshot.json")),
                    record["candidate_snapshot"]["sha256"],
                )
                self.assertEqual(
                    sha256_json(load_json(iteration_dir / "evaluations.json")),
                    record["evaluations"]["sha256"],
                )
                self.assertTrue((iteration_dir / "evaluation" / "bundle.json").is_file())

        self.assertIsNone(report["iterations"][0]["previous_sha256"])
        self.assertEqual(
            report["iterations"][1]["previous_sha256"],
            sha256_json(load_json(archive / "iteration-001" / "iteration.json")),
        )
        self.assertFalse((archive / "iteration-001" / "review.json").exists())
        self.assertEqual(
            sha256_json(load_json(archive / "iteration-002" / "review-request.json")),
            report["iterations"][1]["review_request_sha256"],
        )
        review = report["iterations"][1]["review"]
        self.assertEqual(
            sha256_json(load_json(archive / "iteration-002" / "review-command.json")),
            review["command_sha256"],
        )
        self.assertEqual(
            sha256_json(load_json(archive / "iteration-002" / "review.json")),
            review["decision_sha256"],
        )

        self.assertEqual(report["started"], self.clock.issued[0])
        self.assertEqual(report["finished"], self.clock.issued[-1])
        stamped = {report["started"], report["finished"]}
        for record in report["iterations"]:
            stamped.add(record["theorist"]["timestamp"])
            stamped.add(record["evaluations"]["timestamp"])
        stamped.add(review["timestamp"])
        self.assertLessEqual(stamped, set(self.clock.issued))
        self.assertEqual(len(stamped), len(self.clock.issued))


class DiscoveryGuardTest(_LoopTest):
    def test_refuses_to_overwrite_a_run_archive(self) -> None:
        def fixed() -> str:
            return "2026-08-23T00:00:00.000000Z"

        first = self.discover(
            _Agents([_edit({_THEORY_FILE: "one\n"})], _accepts()),
            _Evaluations([["pass"]]),
            clock=fixed,
        )
        self.assertEqual(first["status"], STATUS_ACCEPTED)

        with self.assertRaises(ArtifactError) as caught:
            self.discover(
                _Agents([_edit({_THEORY_FILE: "two\n"})], _accepts()),
                _Evaluations([["pass"]]),
                clock=fixed,
            )
        self.assertIn("already archived", str(caught.exception))
        self.assertEqual(load_json(self.archive(first) / "run.json"), first)

    def test_refuses_a_candidate_reached_through_a_symlink_out_of_the_workspace(self) -> None:
        outside = self.root / "outside" / _CANDIDATE_ID
        outside.mkdir(parents=True)
        (self.workspace / "escape").symlink_to(outside, target_is_directory=True)
        self.write_config(candidate_dir="escape")
        agents = _Agents([_edit()])

        with self.assertRaises(ArtifactError):
            self.discover(agents, _Evaluations([["pass"]]))
        self.assertEqual(agents.calls, [])

    def test_refuses_an_archive_that_overlaps_the_workspace(self) -> None:
        with self.assertRaises(ArtifactError) as caught:
            self.discover(
                _Agents([_edit()]), _Evaluations([["pass"]]), output=self.workspace / "archive"
            )
        self.assertIn("overlap", str(caught.exception))

    def test_refuses_a_missing_evidence_record(self) -> None:
        self.write_config(evidence_paths=["evidence/records/absent.json"])

        with self.assertRaises(ArtifactError):
            self.discover(_Agents([_edit()]), _Evaluations([["pass"]]))

    def test_refuses_a_missing_config(self) -> None:
        self.config_path.unlink()

        with self.assertRaises(ArtifactError) as caught:
            self.discover(_Agents([_edit()]), _Evaluations([["pass"]]))
        self.assertIn("discovery config not found", str(caught.exception))

    def test_refuses_a_workspace_outside_the_repository(self) -> None:
        with TemporaryDirectory() as elsewhere:
            with self.assertRaises(ArtifactError) as caught:
                self.discover(
                    _Agents([_edit()]), _Evaluations([["pass"]]), workspace=Path(elsewhere)
                )
        self.assertIn("workspace must be a subdirectory", str(caught.exception))


class DiscoveryConfigTest(unittest.TestCase):
    def test_rejects_unknown_keys(self) -> None:
        with self.assertRaises(ArtifactError) as caught:
            DiscoveryConfig.from_dict({**_config(), "reviewers": {}})
        self.assertIn("reviewers", str(caught.exception))

    def test_requires_every_key_but_the_reviewer(self) -> None:
        base = _config()
        required = ("schema_version", "theorist", "max_iterations", "candidate_dir", "evidence_paths")
        for key in required:
            partial = {name: value for name, value in base.items() if name != key}
            with self.subTest(key=key), self.assertRaises(ArtifactError) as caught:
                DiscoveryConfig.from_dict(partial)
            self.assertIn(key, str(caught.exception))

    def test_reviewer_is_optional(self) -> None:
        self.assertIsNone(DiscoveryConfig.from_dict(_config(reviewer=False)).reviewer)
        self.assertIsNone(DiscoveryConfig.from_dict({**_config(), "reviewer": None}).reviewer)
        configured = DiscoveryConfig.from_dict(_config())
        self.assertIsNotNone(configured.reviewer)
        self.assertEqual(list(configured.reviewer.command), ["/usr/bin/env", "reviewer"])

    def test_rejects_unusable_values(self) -> None:
        for override, fragment in (
            ({"max_iterations": 0}, "positive integer"),
            ({"max_iterations": True}, "positive integer"),
            ({"max_iterations": "2"}, "positive integer"),
            ({"schema_version": SCHEMA_VERSION + 1}, "schema_version"),
            ({"candidate_dir": "../escape"}, "'..'"),
            ({"candidate_dir": "/absolute"}, "relative path"),
            ({"candidate_dir": ""}, "non-empty string"),
            ({"evidence_paths": _EVIDENCE_PATH}, "must be a list"),
            ({"evidence_paths": [_EVIDENCE_PATH, _EVIDENCE_PATH]}, "duplicates"),
            ({"evidence_paths": [17]}, "non-empty string"),
        ):
            with self.subTest(override=override), self.assertRaises(ArtifactError) as caught:
                DiscoveryConfig.from_dict({**_config(), **override})
            self.assertIn(fragment, str(caught.exception))

    def test_round_trips_through_to_dict(self) -> None:
        config = DiscoveryConfig.from_dict(_config())
        self.assertEqual(DiscoveryConfig.from_dict(config.to_dict()).to_dict(), config.to_dict())
        self.assertEqual(config.evidence_paths, (_EVIDENCE_PATH,))
        self.assertEqual(config.candidate_dir, _CANDIDATE_ID)


if __name__ == "__main__":
    unittest.main()
