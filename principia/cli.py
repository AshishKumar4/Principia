"""Command line interface for Principia.

Every command prints exactly one canonical JSON object on stdout and keeps human
readable diagnostics on stderr. Exit status is 0 for success, 1 for a validation
or evaluation failure, and 2 for a usage or infrastructure error.

Invalid input maps to a different exit status per command, because the commands
answer different questions. `evidence verify` and `candidate verify` exist to
render a validity verdict, so an unparseable artifact is that verdict and exits
1. `evaluate`, `agent run` and `discover` need their inputs to start a run, so
invalid input leaves no verdict at all and exits 2.
"""

from __future__ import annotations

import argparse
import sys
from collections.abc import Sequence
from datetime import datetime, timezone
from pathlib import Path
from typing import NamedTuple, TextIO

from . import __version__, artifacts, candidates, discovery, evaluator, evidence, runner
from .models import AgentSpec, ArtifactError, EvaluationResult, EvaluationStatus

_PROG = "principia"
_TIMESTAMP_FORMAT = "%Y-%m-%dT%H:%M:%S.%fZ"
_EVALUATION_DIR = ".principia/evaluations"
_DISCOVERY_DIR = ".principia/discovery"

_EXIT_OK = 0
_EXIT_FAIL = 1
_EXIT_ERROR = 2

# Worst status first. The status of a result set is the worst status in it, and
# that status decides the exit code. Members come from their contract values, so
# a renamed enum member cannot silently change the mapping.
_EVALUATION_EXITS: tuple[tuple[EvaluationStatus, int], ...] = (
    (EvaluationStatus("error"), _EXIT_ERROR),
    (EvaluationStatus("fail"), _EXIT_FAIL),
    (EvaluationStatus("inconclusive"), _EXIT_FAIL),
    (EvaluationStatus("not_applicable"), _EXIT_OK),
    (EvaluationStatus("pass"), _EXIT_OK),
)
_EXIT_BY_EVALUATION = dict(_EVALUATION_EXITS)
_NO_EVALUATION = EvaluationStatus("inconclusive")

_EXIT_BY_DISCOVERY = {
    "accepted": _EXIT_OK,
    "max_iterations": _EXIT_FAIL,
    "agent_error": _EXIT_ERROR,
    "reviewer_mutation": _EXIT_ERROR,
}


class _Outcome(NamedTuple):
    """One command result: exit status, stdout payload, stderr diagnostics."""

    exit_code: int
    payload: dict[str, object]
    diagnostics: tuple[str, ...] = ()


def main(argv: Sequence[str] | None = None) -> int:
    """Run one command and return its exit status."""
    args = _build_parser().parse_args(argv)
    repo_root = Path(args.repo).resolve()
    if not repo_root.is_dir():
        outcome = _failed(_EXIT_ERROR, f"repository root is not a directory: {repo_root}")
    else:
        try:
            outcome = args.handler(args, repo_root)
        except ArtifactError as error:
            outcome = _failed(args.invalid_exit, str(error))
        except (OSError, RuntimeError) as error:
            outcome = _failed(_EXIT_ERROR, str(error) or type(error).__name__)
    return _report(args.command, outcome, sys.stdout, sys.stderr)


def _report(command: str, outcome: _Outcome, stdout: TextIO, stderr: TextIO) -> int:
    document = {"command": command, "ok": outcome.exit_code == _EXIT_OK, **outcome.payload}
    stdout.write(artifacts.canonical_json(document).decode("utf-8") + "\n")
    for message in outcome.diagnostics:
        stderr.write(f"{_PROG}: {command}: {message}\n")
    return outcome.exit_code


def _failed(exit_code: int, message: str) -> _Outcome:
    return _Outcome(exit_code, {"errors": [message]}, (message,))


# --- commands ---------------------------------------------------------------


def _verify_evidence(args: argparse.Namespace, repo_root: Path) -> _Outcome:
    path = Path(args.path).resolve()
    record = evidence.load_evidence(path)
    errors = list(evidence.verify_evidence(record, repo_root))
    payload: dict[str, object] = {
        "errors": errors,
        "id": record.id,
        "path": _relative(path, repo_root),
    }
    return _Outcome(_EXIT_FAIL if errors else _EXIT_OK, payload, tuple(errors))


def _verify_candidate(args: argparse.Namespace, repo_root: Path) -> _Outcome:
    candidate_dir = Path(args.path).resolve()
    manifest = candidates.load_candidate(candidate_dir)
    errors = list(candidates.verify_candidate(manifest, candidate_dir, repo_root))
    complexity: dict[str, int] = {}
    lineage: list[str] = []
    if not errors:
        complexity = dict(candidates.candidate_complexity(manifest, repo_root))
        try:
            lineage = list(candidates.candidate_lineage(candidate_dir.parent, manifest.id))
        except ArtifactError as error:
            errors.append(str(error))
    payload: dict[str, object] = {
        "complexity": complexity,
        "errors": errors,
        "id": manifest.id,
        "lineage": lineage,
        "path": _relative(candidate_dir, repo_root),
    }
    return _Outcome(_EXIT_FAIL if errors else _EXIT_OK, payload, tuple(errors))


def _evaluate(args: argparse.Namespace, repo_root: Path) -> _Outcome:
    candidate_dir = Path(args.candidate).resolve()
    evidence_paths = [Path(item).resolve() for item in args.evidence or ()]
    output_dir = _output_dir(args.output, repo_root, _EVALUATION_DIR)
    timestamp = args.timestamp or _utc_now()
    results = evaluator.evaluate_candidate(
        candidate_dir, evidence_paths, repo_root, output_dir, timestamp
    )
    status = _worst_status(results)
    payload: dict[str, object] = {
        "candidate": _relative(candidate_dir, repo_root),
        "output": _relative(output_dir, repo_root),
        "results": [result.to_dict() for result in results],
        "status": status.value,
        "timestamp": timestamp,
    }
    exit_code = _EXIT_BY_EVALUATION[status]
    diagnostics = () if exit_code == _EXIT_OK else _evaluation_diagnostics(results)
    return _Outcome(exit_code, payload, diagnostics)


def _run_agent(args: argparse.Namespace, repo_root: Path) -> _Outcome:
    spec_path = Path(args.spec).resolve()
    workspace = Path(args.workspace).resolve()
    spec = AgentSpec.from_dict(artifacts.load_json(spec_path))
    request = artifacts.load_json(Path(args.request).resolve()) if args.request else {}
    timestamp = args.timestamp or _utc_now()
    result = runner.run_agent(spec, workspace, request, repo_root, timestamp)
    payload: dict[str, object] = {
        "result": result.to_dict(),
        "spec": _relative(spec_path, repo_root),
        "timestamp": timestamp,
        "workspace": _relative(workspace, repo_root),
    }
    if result.timed_out:
        return _Outcome(_EXIT_FAIL, payload, ("the agent timed out",))
    if result.exit_code is None:
        return _Outcome(
            _EXIT_FAIL, payload, (f"the agent died from signal {result.signal}",)
        )
    if result.exit_code != 0:
        return _Outcome(
            _EXIT_FAIL, payload, (f"the agent exited with status {result.exit_code}",)
        )
    return _Outcome(_EXIT_OK, payload)


def _discover(args: argparse.Namespace, repo_root: Path) -> _Outcome:
    config_path = Path(args.config).resolve()
    workspace = Path(args.workspace).resolve()
    output_root = _output_dir(args.output, repo_root, _DISCOVERY_DIR)
    fixed = args.timestamp
    report = discovery.run_discovery(
        config_path,
        workspace,
        repo_root,
        output_root,
        (lambda: fixed) if fixed else _utc_now,
    )
    status = str(report.get("status", ""))
    exit_code = _EXIT_BY_DISCOVERY.get(status, _EXIT_ERROR)
    payload: dict[str, object] = {
        "config": _relative(config_path, repo_root),
        "output": _relative(output_root, repo_root),
        "report": report,
        "workspace": _relative(workspace, repo_root),
    }
    diagnostics = () if exit_code == _EXIT_OK else _discovery_diagnostics(report, status)
    return _Outcome(exit_code, payload, diagnostics)


# --- helpers ----------------------------------------------------------------


def _status_of(result: EvaluationResult) -> EvaluationStatus:
    return EvaluationStatus(result.status)


def _worst_status(results: Sequence[EvaluationResult]) -> EvaluationStatus:
    """Return the worst status in the set; an empty set establishes nothing."""
    seen = {_status_of(result) for result in results}
    return next(
        (status for status, _ in _EVALUATION_EXITS if status in seen), _NO_EVALUATION
    )


def _evaluation_diagnostics(results: Sequence[EvaluationResult]) -> tuple[str, ...]:
    if not results:
        return ("no evaluation result was produced",)
    return tuple(
        f"{_status_of(result).value}: {result.summary}"
        for result in results
        if _EXIT_BY_EVALUATION[_status_of(result)] != _EXIT_OK
    )


def _discovery_diagnostics(report: dict, status: str) -> tuple[str, ...]:
    failure = report.get("error")
    if isinstance(failure, dict):
        return (f"{failure.get('stage')}: {failure.get('reason')}",)
    return (f"the discovery loop stopped with status {status!r}",)


def _output_dir(value: str | None, repo_root: Path, default: str) -> Path:
    return Path(value).resolve() if value else repo_root / default


def _relative(path: Path, repo_root: Path) -> str:
    inside = path.is_relative_to(repo_root)
    return (path.relative_to(repo_root) if inside else path).as_posix()


def _utc_now() -> str:
    return datetime.now(timezone.utc).strftime(_TIMESTAMP_FORMAT)


def _utc_timestamp(value: str) -> str:
    try:
        moment = datetime.fromisoformat(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError(f"not an ISO-8601 timestamp: {value!r}") from error
    if moment.tzinfo is None:
        raise argparse.ArgumentTypeError(f"timestamp needs a UTC offset: {value!r}")
    return moment.astimezone(timezone.utc).strftime(_TIMESTAMP_FORMAT)


# --- parser -----------------------------------------------------------------


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog=_PROG,
        description=(
            "Verify evidence records and candidate theories, and run sandboxed "
            "discovery agents against the Lean atlas."
        ),
    )
    parser.add_argument("--version", action="version", version=f"{_PROG} {__version__}")
    parser.add_argument(
        "--repo",
        default=".",
        metavar="PATH",
        help="repository root that holds the Lean library and the artifacts "
        "(default: the current directory)",
    )
    commands = parser.add_subparsers(dest="group", metavar="COMMAND", required=True)

    evidence_group = commands.add_parser("evidence", help="work with evidence records")
    evidence_actions = evidence_group.add_subparsers(
        dest="action", metavar="ACTION", required=True
    )
    verify_evidence = evidence_actions.add_parser(
        "verify", help="validate one evidence record"
    )
    verify_evidence.add_argument("path", metavar="PATH", help="evidence record JSON file")
    verify_evidence.set_defaults(
        command="evidence verify", handler=_verify_evidence, invalid_exit=_EXIT_FAIL
    )

    candidate_group = commands.add_parser("candidate", help="work with candidate theories")
    candidate_actions = candidate_group.add_subparsers(
        dest="action", metavar="ACTION", required=True
    )
    verify_candidate = candidate_actions.add_parser(
        "verify", help="validate one candidate manifest and report its complexity"
    )
    verify_candidate.add_argument(
        "path", metavar="PATH", help="candidate directory that holds candidate.json"
    )
    verify_candidate.set_defaults(
        command="candidate verify", handler=_verify_candidate, invalid_exit=_EXIT_FAIL
    )

    evaluate = commands.add_parser(
        "evaluate", help="check one candidate against Lean and evidence records"
    )
    evaluate.add_argument(
        "candidate", metavar="PATH", help="candidate directory that holds candidate.json"
    )
    evaluate.add_argument(
        "--evidence",
        action="append",
        metavar="PATH",
        help="evidence record to evaluate; repeat the option for more records, "
        "omit it to run the Lean checks only",
    )
    evaluate.add_argument(
        "--output",
        metavar="PATH",
        help=f"archive directory for the result bundle (default: <repo>/{_EVALUATION_DIR})",
    )
    _add_timestamp(evaluate)
    evaluate.set_defaults(command="evaluate", handler=_evaluate, invalid_exit=_EXIT_ERROR)

    agent_group = commands.add_parser("agent", help="run agents inside the sandbox")
    agent_actions = agent_group.add_subparsers(dest="action", metavar="ACTION", required=True)
    run = agent_actions.add_parser("run", help="run one agent inside the sandbox")
    run.add_argument("spec", metavar="PATH", help="agent spec JSON file")
    run.add_argument(
        "--workspace",
        metavar="PATH",
        required=True,
        help="writable workspace directory for the agent",
    )
    run.add_argument(
        "--request", metavar="PATH", help="JSON file handed to the agent as its request"
    )
    _add_timestamp(run)
    run.set_defaults(command="agent run", handler=_run_agent, invalid_exit=_EXIT_ERROR)

    discover = commands.add_parser("discover", help="run the iterative discovery loop")
    discover.add_argument("config", metavar="PATH", help="discovery config JSON file")
    discover.add_argument(
        "--workspace",
        metavar="PATH",
        required=True,
        help="writable workspace directory for the agents",
    )
    discover.add_argument(
        "--output",
        metavar="PATH",
        help=f"archive directory for the run (default: <repo>/{_DISCOVERY_DIR})",
    )
    _add_timestamp(discover)
    discover.set_defaults(command="discover", handler=_discover, invalid_exit=_EXIT_ERROR)

    return parser


def _add_timestamp(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--timestamp",
        type=_utc_timestamp,
        metavar="ISO8601",
        help="UTC timestamp stamped on the produced artifacts (default: the current time)",
    )
