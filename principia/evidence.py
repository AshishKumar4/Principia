"""Evidence records: strict loading, containment checks and gated evaluation.

An evidence record names one experiment, its provenance, its data and the gate that
turns the data into a verdict about a candidate theory. The gate names a built-in
evaluator by id. A record can therefore never introduce code: it selects from the
functions registered at import time and nothing else.

Verification and evaluation are deterministic. `verify_evidence` reports problems in a
fixed order, and `evaluate_evidence` never raises: unusable evidence, an inapplicable
candidate and a crashing evaluator all become an `EvaluationResult`.
"""

from __future__ import annotations

from collections.abc import Callable
from pathlib import Path

from .artifacts import load_json, resolve_repo_path, verify_file_sha256
from .evaluators import BUILTIN_EVALUATORS
from .models import (
    SCHEMA_VERSION,
    ArtifactError,
    CandidateManifest,
    DatasetRef,
    EvaluationResult,
    EvaluationStatus,
    EvidenceRecord,
    validate_evaluator_id,
)

__all__ = [
    "Evaluator",
    "evaluate_evidence",
    "load_evidence",
    "register_evaluator",
    "verify_evidence",
]

Evaluator = Callable[[EvidenceRecord, CandidateManifest, Path, str], EvaluationResult]

_EVALUATORS: dict[str, Evaluator] = {}


def load_evidence(path: Path) -> EvidenceRecord:
    """Read one evidence record. Unknown keys and malformed values are rejected."""
    return EvidenceRecord.from_dict(load_json(path))


def register_evaluator(name: str, function: Evaluator) -> None:
    """Bind evaluator id `name` to `function`.

    Ids are bound once per process. Re-binding is a programming error, not a
    configuration option, so it raises instead of silently replacing an evaluator.
    """
    validate_evaluator_id(name, "evaluator id")
    if not callable(function):
        raise ArtifactError(f"evaluator {name!r} is not callable")
    if name in _EVALUATORS:
        raise ArtifactError(f"evaluator {name!r} is already registered")
    _EVALUATORS[name] = function


def verify_evidence(record: EvidenceRecord, repo_root: Path) -> list[str]:
    """Return every problem that makes `record` unusable. An empty list means usable."""
    problems: list[str] = []
    evaluator = record.gate.evaluator
    if evaluator not in _EVALUATORS:
        known = ", ".join(sorted(_EVALUATORS)) or "none"
        problems.append(f"gate evaluator {evaluator!r} is not registered (registered: {known})")
    problems.extend(_dataset_problems(record.dataset, repo_root))
    return problems


def evaluate_evidence(
    record: EvidenceRecord,
    candidate: CandidateManifest,
    repo_root: Path,
    timestamp: str,
) -> EvaluationResult:
    """Run the gate of `record` against `candidate` and return its result.

    The record is verified first, so an evaluator only ever sees data whose bytes match
    the record. A candidate that does not declare every required claim is outside the
    reach of this experiment and gets `not_applicable`, which is not a failure.
    """
    problems = verify_evidence(record, repo_root)
    if problems:
        return _result(
            record,
            candidate,
            timestamp,
            EvaluationStatus.ERROR,
            "the evidence record is not usable: " + "; ".join(problems),
        )
    missing = _missing_claims(record, candidate)
    if missing:
        return _result(
            record,
            candidate,
            timestamp,
            EvaluationStatus.NOT_APPLICABLE,
            "the candidate does not claim " + ", ".join(missing),
        )
    name = record.gate.evaluator
    try:
        result = _EVALUATORS[name](record, candidate, repo_root, timestamp)
    except Exception as exc:
        return _result(
            record,
            candidate,
            timestamp,
            EvaluationStatus.ERROR,
            f"evaluator {name!r} raised {type(exc).__name__}: {exc}",
        )
    return _labelled(result, record, candidate, timestamp)


def _missing_claims(record: EvidenceRecord, candidate: CandidateManifest) -> list[str]:
    claimed = {claim.id for claim in candidate.claims}
    return [claim for claim in record.gate.required_claims if claim not in claimed]


def _dataset_problems(dataset: DatasetRef, repo_root: Path) -> list[str]:
    if dataset.local_path is None:
        if dataset.url is None:
            return ["the dataset gives neither a repo-relative local_path nor a url"]
        return []
    try:
        data = resolve_repo_path(repo_root, dataset.local_path, must_exist=True)
    except (ArtifactError, OSError) as exc:
        return [f"dataset path {dataset.local_path!r} is unusable: {exc}"]
    if not data.is_file():
        return [f"dataset path {dataset.local_path!r} is not a regular file"]
    try:
        verify_file_sha256(data, dataset.sha256)
    except (ArtifactError, OSError) as exc:
        return [f"dataset {dataset.local_path!r} does not match its checksum: {exc}"]
    return []


def _labelled(
    result: object,
    record: EvidenceRecord,
    candidate: CandidateManifest,
    timestamp: str,
) -> EvaluationResult:
    """Pass an evaluator result through once it is labelled with the right identities.

    Results are archived by candidate and evidence id, so a mislabelled result would
    corrupt the archive. That is an error, never a silent relabel.
    """
    name = record.gate.evaluator
    if not isinstance(result, EvaluationResult):
        return _result(
            record,
            candidate,
            timestamp,
            EvaluationStatus.ERROR,
            f"evaluator {name!r} returned {type(result).__name__}, not an EvaluationResult",
        )
    wrong = [
        f"{field} {value!r} instead of {expected!r}"
        for field, value, expected in (
            ("candidate_id", result.candidate_id, candidate.id),
            ("evidence_id", result.evidence_id, record.id),
        )
        if value != expected
    ]
    if wrong:
        return _result(
            record,
            candidate,
            timestamp,
            EvaluationStatus.ERROR,
            f"evaluator {name!r} returned " + " and ".join(wrong),
        )
    return result


def _result(
    record: EvidenceRecord,
    candidate: CandidateManifest,
    timestamp: str,
    status: EvaluationStatus,
    summary: str,
) -> EvaluationResult:
    return EvaluationResult(
        schema_version=SCHEMA_VERSION,
        candidate_id=candidate.id,
        evidence_id=record.id,
        status=status,
        summary=summary,
        metrics={},
        artifacts={},
        timestamp=timestamp,
    )


def _register_builtins() -> None:
    for name, function in BUILTIN_EVALUATORS.items():
        register_evaluator(name, function)


_register_builtins()
