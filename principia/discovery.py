"""Iterative theory discovery: theorist, evaluator, then independent reviewer.

The loop holds no opinion of its own. A theorist agent edits the workspace, the
evaluator judges the candidate, and an optional reviewer accepts or rejects a
read-only snapshot of it. Every request, command result, snapshot hash, evaluation
and review is archived before the loop advances, and each iteration record carries
the hash of the previous record, so the archive is a chain an auditor can replay.

Two rules keep the loop honest.

A failing iteration is never retried in silence. It is archived, its evaluations
become the next theorist request, and the iteration counter advances. The run stops
on an evaluation set free of `fail` and `error` plus reviewer acceptance, on the
configured iteration limit, or on a boundary failure. Nothing else.

The reviewer cannot touch what it reviews, by construction and then by check. The
runner binds the whole repository read-only and makes writable only the workspace it
is handed, so a reviewer given its own scratch workspace cannot write a candidate
that lives in the theorist workspace. The theorist workspace is hashed before and
after the review as well: any change ends the run as `reviewer_mutation`, which is
checked before the reviewer's own exit status, so a mutating reviewer can never
review a candidate into acceptance.

Agent protocol, as provided by `principia.runner`: the request is canonical JSON on
stdin and cwd is the agent workspace. A theorist reads `candidate_dir` relative to
that cwd and edits it. A reviewer reads `candidate_dir` as an absolute read-only
path and writes one JSON object to stdout: `decision` (`accept` or `reject`),
`summary`, and optional `findings`.
"""

from __future__ import annotations

import hashlib
import json
import os
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from itertools import chain
from pathlib import Path, PurePosixPath

from .artifacts import load_json, resolve_repo_path, sha256_json, write_json_atomic
from .evaluator import evaluate_candidate
from .models import (
    SCHEMA_VERSION,
    AgentSpec,
    ArtifactError,
    CommandResult,
    EvaluationResult,
    EvaluationStatus,
)
from .runner import run_agent

STATUS_ACCEPTED = "accepted"
STATUS_MAX_ITERATIONS = "max_iterations"
STATUS_AGENT_ERROR = "agent_error"
STATUS_REVIEWER_MUTATION = "reviewer_mutation"

OUTCOME_EVALUATOR_FEEDBACK = "evaluator_feedback"
OUTCOME_REVIEW_REJECTED = "review_rejected"

AgentRunner = Callable[[AgentSpec, Path, Mapping[str, object], Path, str], CommandResult]
CandidateEvaluation = Callable[[Path, Sequence[Path], Path, Path, str], Sequence[EvaluationResult]]

_CONFIG_KEYS = frozenset(
    {"schema_version", "theorist", "reviewer", "max_iterations", "candidate_dir", "evidence_paths"}
)
_REQUIRED_CONFIG_KEYS = _CONFIG_KEYS - {"reviewer"}
_REVIEW_KEYS = frozenset({"decision", "summary", "findings"})
_REVIEW_DECISIONS = ("accept", "reject")
_BLOCKING_STATUSES = frozenset({EvaluationStatus.FAIL, EvaluationStatus.ERROR})

__all__ = [
    "STATUS_ACCEPTED",
    "STATUS_AGENT_ERROR",
    "STATUS_MAX_ITERATIONS",
    "STATUS_REVIEWER_MUTATION",
    "DiscoveryConfig",
    "run_discovery",
]


@dataclass(frozen=True, slots=True)
class DiscoveryConfig:
    """Who proposes, who reviews, what is judged, and for how many rounds.

    `candidate_dir` is relative to the discovery workspace, because the theorist may
    edit nothing else; `evidence_paths` are repo-relative, because evidence records
    are immutable repository artifacts.
    """

    schema_version: int
    theorist: AgentSpec
    reviewer: AgentSpec | None
    max_iterations: int
    candidate_dir: str
    evidence_paths: tuple[str, ...]

    @classmethod
    def from_dict(cls, value: object) -> DiscoveryConfig:
        payload = _require_mapping("discovery config", value)
        unknown = sorted(set(payload) - _CONFIG_KEYS)
        if unknown:
            raise ArtifactError(f"discovery config has unknown keys: {', '.join(unknown)}")
        missing = sorted(_REQUIRED_CONFIG_KEYS - set(payload))
        if missing:
            raise ArtifactError(f"discovery config is missing keys: {', '.join(missing)}")
        schema_version = payload["schema_version"]
        if schema_version != SCHEMA_VERSION:
            raise ArtifactError(f"unsupported discovery config schema_version: {schema_version!r}")
        max_iterations = payload["max_iterations"]
        if (
            not isinstance(max_iterations, int)
            or isinstance(max_iterations, bool)
            or max_iterations < 1
        ):
            raise ArtifactError(f"max_iterations must be a positive integer: {max_iterations!r}")
        evidence = payload["evidence_paths"]
        if not isinstance(evidence, list):
            raise ArtifactError("evidence_paths must be a list")
        evidence_paths = tuple(
            _require_relative(f"evidence_paths[{index}]", entry)
            for index, entry in enumerate(evidence)
        )
        if len(set(evidence_paths)) != len(evidence_paths):
            raise ArtifactError("evidence_paths contains duplicates")
        reviewer = payload.get("reviewer")
        return cls(
            schema_version=schema_version,
            theorist=AgentSpec.from_dict(payload["theorist"]),
            reviewer=None if reviewer is None else AgentSpec.from_dict(reviewer),
            max_iterations=max_iterations,
            candidate_dir=_require_relative("candidate_dir", payload["candidate_dir"]),
            evidence_paths=evidence_paths,
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": self.schema_version,
            "theorist": self.theorist.to_dict(),
            "reviewer": None if self.reviewer is None else self.reviewer.to_dict(),
            "max_iterations": self.max_iterations,
            "candidate_dir": self.candidate_dir,
            "evidence_paths": list(self.evidence_paths),
        }


@dataclass(frozen=True, slots=True)
class _Context:
    """Fixed inputs of one discovery run, threaded through every stage."""

    config: DiscoveryConfig
    workspace: Path
    repo_root: Path
    candidate_dir: Path
    candidate_in_workspace: str
    evidence_paths: tuple[Path, ...]
    timestamp_factory: Callable[[], str]
    agent_runner: AgentRunner
    candidate_evaluator: CandidateEvaluation


@dataclass(frozen=True, slots=True)
class _Iteration:
    """One archived iteration: its record, whether the run ends, and the feedback."""

    record: dict[str, object]
    status: str | None
    error: dict[str, object] | None
    evaluations: list[dict[str, object]] | None
    review: dict[str, object] | None


def run_discovery(
    config_path: str | Path,
    workspace: str | Path,
    repo_root: str | Path,
    output_root: str | Path,
    timestamp_factory: Callable[[], str],
    *,
    agent_runner: AgentRunner = run_agent,
    candidate_evaluator: CandidateEvaluation = evaluate_candidate,
) -> dict[str, object]:
    """Run the theorist/evaluator/reviewer loop; archive and return its audit summary.

    `timestamp_factory` supplies every UTC ISO-8601 stamp, so a caller can make a run
    reproducible. The first stamp names the archive directory, which is write-once:
    `<output_root>/run-<stamp>/`, holding the config, one directory per iteration and
    the returned summary as `run.json`.

    Raises `ArtifactError` for an unusable config, workspace, archive or evidence path.
    Boundary failures are reported in the summary, never raised, and never retried.
    """
    repo = _require_directory("repo_root", repo_root)
    work = _require_directory("workspace", workspace)
    if work == repo or not work.is_relative_to(repo):
        raise ArtifactError(f"workspace must be a subdirectory of the repo root: {work}")
    output_parent = Path(output_root).resolve()
    if output_parent == repo or not output_parent.is_relative_to(repo):
        raise ArtifactError(f"output root must be a subdirectory of the repo root: {output_parent}")
    if output_parent.is_relative_to(work) or work.is_relative_to(output_parent):
        raise ArtifactError(f"output root must not overlap the workspace: {output_parent}")

    config_path = Path(config_path)
    if not config_path.is_file():
        raise ArtifactError(f"discovery config not found: {config_path}")
    raw_config = load_json(config_path)
    config = DiscoveryConfig.from_dict(raw_config)
    work_in_repo = work.relative_to(repo).as_posix()
    candidate_dir = resolve_repo_path(
        repo, f"{work_in_repo}/{config.candidate_dir}", must_exist=True
    )
    if candidate_dir == work or not candidate_dir.is_relative_to(work):
        raise ArtifactError(
            f"candidate_dir must sit inside the workspace: {config.candidate_dir!r}"
        )
    if not candidate_dir.is_dir():
        raise ArtifactError(f"candidate_dir is not a directory: {candidate_dir}")
    evidence_paths = tuple(
        resolve_repo_path(repo, path, must_exist=True) for path in config.evidence_paths
    )

    started = timestamp_factory()
    if not isinstance(started, str) or not started:
        raise ArtifactError(f"timestamp_factory must return a non-empty string: {started!r}")
    archive_root = output_parent / f"run-{_slug(started)}"
    if archive_root.exists():
        raise ArtifactError(f"this run is already archived: {archive_root}")

    context = _Context(
        config=config,
        workspace=work,
        repo_root=repo,
        candidate_dir=candidate_dir,
        candidate_in_workspace=candidate_dir.relative_to(work).as_posix(),
        evidence_paths=evidence_paths,
        timestamp_factory=timestamp_factory,
        agent_runner=agent_runner,
        candidate_evaluator=candidate_evaluator,
    )

    config_sha256 = sha256_json(raw_config)
    _archive(
        archive_root / "config.json",
        {
            "schema_version": SCHEMA_VERSION,
            "source": str(config_path),
            "sha256": config_sha256,
            "config": config.to_dict(),
            "repo_root": str(repo),
            "workspace": str(work),
            "candidate_dir": str(candidate_dir),
            "evidence_paths": [str(path) for path in evidence_paths],
        },
    )

    iterations: list[dict[str, object]] = []
    previous_sha256: str | None = None
    prior_evaluations: list[dict[str, object]] | None = None
    prior_review: dict[str, object] | None = None
    status = STATUS_MAX_ITERATIONS
    error: dict[str, object] | None = None

    for index in range(1, config.max_iterations + 1):
        iteration_dir = archive_root / f"iteration-{index:03d}"
        outcome = _run_iteration(
            context, index, iteration_dir, previous_sha256, prior_evaluations, prior_review
        )
        iterations.append(outcome.record)
        previous_sha256 = _archive(iteration_dir / "iteration.json", outcome.record)
        if outcome.status is not None:
            status = outcome.status
            error = outcome.error
            break
        prior_evaluations = outcome.evaluations
        prior_review = outcome.review

    summary: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "status": status,
        "accepted": status == STATUS_ACCEPTED,
        "started": started,
        "finished": timestamp_factory(),
        "config": {"path": str(config_path), "sha256": config_sha256},
        "candidate_dir": config.candidate_dir,
        "evidence_paths": list(config.evidence_paths),
        "max_iterations": config.max_iterations,
        "reviewed": config.reviewer is not None,
        "iterations": iterations,
        "error": error,
        "archive_root": str(archive_root),
    }
    _archive(archive_root / "run.json", summary)
    return summary


def _run_iteration(
    context: _Context,
    iteration: int,
    iteration_dir: Path,
    previous_sha256: str | None,
    prior_evaluations: list[dict[str, object]] | None,
    prior_review: dict[str, object] | None,
) -> _Iteration:
    config = context.config
    record: dict[str, object] = {"iteration": iteration, "previous_sha256": previous_sha256}

    request: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "role": "theorist",
        "iteration": iteration,
        "max_iterations": config.max_iterations,
        "repo_root": str(context.repo_root),
        "candidate_dir": context.candidate_in_workspace,
        "evidence_paths": [str(path) for path in context.evidence_paths],
        "prior_evaluations": prior_evaluations,
        "prior_review": prior_review,
    }
    record["request_sha256"] = _archive(iteration_dir / "request.json", request)

    timestamp = context.timestamp_factory()
    command = context.agent_runner(
        config.theorist, context.workspace, request, context.repo_root, timestamp
    )
    record["theorist"] = _agent_record(
        timestamp, _archive(iteration_dir / "theorist-command.json", command.to_dict()), command
    )
    failure = _command_failure(command)
    if failure is not None:
        return _terminal(record, STATUS_AGENT_ERROR, "theorist", iteration, failure)
    if not context.candidate_dir.is_dir():
        return _terminal(
            record,
            STATUS_AGENT_ERROR,
            "theorist",
            iteration,
            f"candidate directory is gone after the theorist ran: {context.candidate_in_workspace}",
        )

    snapshot = _snapshot(context.candidate_dir)
    record["candidate_snapshot"] = {
        "sha256": _archive(iteration_dir / "candidate-snapshot.json", snapshot),
        "entry_count": len(snapshot),
    }

    timestamp = context.timestamp_factory()
    evaluations = [
        result.to_dict()
        for result in context.candidate_evaluator(
            context.candidate_dir,
            context.evidence_paths,
            context.repo_root,
            iteration_dir / "evaluation",
            timestamp,
        )
    ]
    statuses = [EvaluationStatus(entry["status"]) for entry in evaluations]
    record["evaluations"] = {
        "timestamp": timestamp,
        "sha256": _archive(iteration_dir / "evaluations.json", evaluations),
        "statuses": [status.value for status in statuses],
    }
    if not evaluations:
        return _terminal(
            record, STATUS_AGENT_ERROR, "evaluator", iteration, "evaluator produced no results"
        )
    if any(status in _BLOCKING_STATUSES for status in statuses):
        return _feedback(record, OUTCOME_EVALUATOR_FEEDBACK, evaluations, None)

    if config.reviewer is None:
        return _accepted(record)
    return _review(
        context, config.reviewer, iteration, iteration_dir, record, snapshot, evaluations
    )


def _review(
    context: _Context,
    reviewer: AgentSpec,
    iteration: int,
    iteration_dir: Path,
    record: dict[str, object],
    snapshot: dict[str, str],
    evaluations: list[dict[str, object]],
) -> _Iteration:
    """Run the independent reviewer against a read-only candidate and police the workspace."""
    review_workspace = iteration_dir / "review-workspace"
    review_workspace.mkdir(parents=True, exist_ok=True)

    request: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "role": "reviewer",
        "iteration": iteration,
        "repo_root": str(context.repo_root),
        "candidate_dir": str(context.candidate_dir),
        "candidate_writable": False,
        "candidate_snapshot": snapshot,
        "evidence_paths": [str(path) for path in context.evidence_paths],
        "evaluations": evaluations,
    }
    record["review_request_sha256"] = _archive(iteration_dir / "review-request.json", request)

    before = _snapshot(context.workspace)
    timestamp = context.timestamp_factory()
    command = context.agent_runner(
        reviewer, review_workspace, request, context.repo_root, timestamp
    )
    review = _agent_record(
        timestamp, _archive(iteration_dir / "review-command.json", command.to_dict()), command
    )
    after = _snapshot(context.workspace)
    review["workspace_sha256_before"] = sha256_json(before)
    review["workspace_sha256_after"] = sha256_json(after)
    record["review"] = review

    changes = _changes(before, after)
    if changes:
        review["changes"] = changes
        return _terminal(
            record,
            STATUS_REVIEWER_MUTATION,
            "reviewer",
            iteration,
            f"reviewer changed the workspace ({len(changes)} entries)",
        )
    failure = _command_failure(command)
    if failure is not None:
        return _terminal(record, STATUS_AGENT_ERROR, "reviewer", iteration, failure)
    try:
        decision = _parse_review(command.stdout)
    except ArtifactError as exc:
        return _terminal(record, STATUS_AGENT_ERROR, "reviewer", iteration, str(exc))

    review["decision"] = decision["decision"]
    review["decision_sha256"] = _archive(iteration_dir / "review.json", decision)
    if decision["decision"] == "accept":
        return _accepted(record)
    return _feedback(record, OUTCOME_REVIEW_REJECTED, evaluations, decision)


def _terminal(
    record: dict[str, object], status: str, stage: str, iteration: int, reason: str
) -> _Iteration:
    record["outcome"] = status
    return _Iteration(
        record=record,
        status=status,
        error={"stage": stage, "iteration": iteration, "reason": reason},
        evaluations=None,
        review=None,
    )


def _accepted(record: dict[str, object]) -> _Iteration:
    record["outcome"] = STATUS_ACCEPTED
    return _Iteration(
        record=record, status=STATUS_ACCEPTED, error=None, evaluations=None, review=None
    )


def _feedback(
    record: dict[str, object],
    outcome: str,
    evaluations: list[dict[str, object]],
    review: dict[str, object] | None,
) -> _Iteration:
    """Carry an unfinished iteration's evaluations, and any rejection, into the next one."""
    record["outcome"] = outcome
    return _Iteration(
        record=record, status=None, error=None, evaluations=evaluations, review=review
    )


def _agent_record(
    timestamp: str, command_sha256: str, command: CommandResult
) -> dict[str, object]:
    return {
        "timestamp": timestamp,
        "command_sha256": command_sha256,
        "exit_code": command.exit_code,
        "signal": command.signal,
        "timed_out": command.timed_out,
    }


def _command_failure(command: CommandResult) -> str | None:
    """Describe why a boundary command failed, or None when it succeeded."""
    if command.timed_out:
        return f"timed out after {command.duration_seconds} s"
    if command.signal is not None:
        return f"killed by signal {command.signal}"
    if command.exit_code != 0:
        return f"exit code {command.exit_code}"
    return None


def _parse_review(stdout: str) -> dict[str, object]:
    """Read the reviewer verdict from stdout; an unreadable verdict is never an acceptance."""
    try:
        payload = json.loads(stdout)
    except json.JSONDecodeError as exc:
        raise ArtifactError(f"reviewer verdict is not JSON: {exc}") from exc
    if not isinstance(payload, dict):
        raise ArtifactError("reviewer verdict must be a JSON object")
    unknown = sorted(set(payload) - _REVIEW_KEYS)
    if unknown:
        raise ArtifactError(f"reviewer verdict has unknown keys: {', '.join(unknown)}")
    decision = payload.get("decision")
    if decision not in _REVIEW_DECISIONS:
        raise ArtifactError(f"reviewer decision must be 'accept' or 'reject': {decision!r}")
    summary = payload.get("summary")
    if not isinstance(summary, str) or not summary:
        raise ArtifactError("reviewer verdict needs a non-empty summary")
    findings = payload.get("findings", [])
    if not isinstance(findings, list) or any(
        not isinstance(item, str) or not item for item in findings
    ):
        raise ArtifactError("reviewer findings must be a list of non-empty strings")
    return {"decision": decision, "summary": summary, "findings": list(findings)}


def _snapshot(root: Path) -> dict[str, str]:
    """Digest every entry beneath `root`: files by content, directories and links by kind.

    Key order is irrelevant, because the snapshot is hashed as canonical JSON, which
    sorts keys. Symlinks are recorded by target and never followed, so a link cannot
    smuggle a change past the comparison or walk out of the tree.
    """
    entries: dict[str, str] = {}
    for directory, dirnames, filenames in os.walk(root, followlinks=False):
        base = Path(directory)
        for name in chain(dirnames, filenames):
            path = base / name
            entries[path.relative_to(root).as_posix()] = _entry_digest(path)
    return entries


def _entry_digest(path: Path) -> str:
    if path.is_symlink():
        return f"link:{os.readlink(path)}"
    if path.is_dir():
        return "dir:"
    if not path.is_file():
        return "other:"
    with path.open("rb") as handle:
        return f"file:{hashlib.file_digest(handle, 'sha256').hexdigest()}"


def _changes(before: Mapping[str, str], after: Mapping[str, str]) -> list[dict[str, str]]:
    changes: list[dict[str, str]] = []
    for key in sorted(set(before) | set(after)):
        old = before.get(key)
        new = after.get(key)
        if old == new:
            continue
        change = "added" if old is None else "removed" if new is None else "modified"
        changes.append({"path": key, "change": change})
    return changes


def _archive(path: Path, value: object) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    return write_json_atomic(path, value)


def _slug(timestamp: str) -> str:
    """Reduce a timestamp to one path component, so every run archive is write-once."""
    return "".join(
        character if character.isalnum() or character in "._-" else "-" for character in timestamp
    )


def _require_directory(field: str, value: str | Path) -> Path:
    path = Path(value)
    if not path.is_dir():
        raise ArtifactError(f"{field} is not a directory: {path}")
    return path.resolve()


def _require_mapping(label: str, value: object) -> Mapping[str, object]:
    if not isinstance(value, dict):
        raise ArtifactError(f"{label} must be a JSON object")
    return value


def _require_relative(field: str, value: object) -> str:
    if not isinstance(value, str) or not value:
        raise ArtifactError(f"{field} must be a non-empty string")
    parts = PurePosixPath(value).parts
    if value.startswith("/") or not parts or any(part in (".", "..") for part in parts):
        raise ArtifactError(f"{field} must be a relative path without '.' or '..': {value!r}")
    return "/".join(parts)
