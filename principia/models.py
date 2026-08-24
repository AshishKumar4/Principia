"""Frozen, strictly validated artifact models.

Validation lives in ``__post_init__``, so direct construction, ``dataclasses.replace``
and :meth:`from_dict` share one path: every instance that exists is well formed. It
rejects wrong *kinds* of data, never merely degenerate data, so a manifest with an
empty witness list still loads and is reported by ``candidates.verify_candidate``.

The models own JSON shape, artifact identity, digests and timestamps. They do not own
filesystem or Lean semantics: a repo-relative path is resolved by
``artifacts.resolve_repo_path`` where the file is opened, and Lean names are judged by
``candidates.verify_candidate``, which reports problems instead of raising. Keeping
those checks at their point of use is what lets a bad path be reported rather than
make a whole record unreadable.

Nothing here reads the clock or the filesystem. Timestamps arrive from callers.
"""

from __future__ import annotations

import math
import re
from collections.abc import Mapping
from dataclasses import dataclass, fields
from datetime import date, datetime, timedelta
from enum import StrEnum
from types import MappingProxyType
from typing import Callable, ClassVar, NoReturn, Self
from urllib.parse import urlsplit

__all__ = [
    "SCHEMA_VERSION",
    "JsonScalar",
    "ArtifactError",
    "EvaluationStatus",
    "validate_artifact_id",
    "validate_evaluator_id",
    "validate_sha256_hex",
    "validate_timestamp",
    "SourceRef",
    "DatasetRef",
    "LeanSpec",
    "EvidenceGate",
    "EvidenceRecord",
    "Assumption",
    "ClaimRef",
    "Parameter",
    "ExceptionRecord",
    "EvidencePrediction",
    "CandidateManifest",
    "EvaluationResult",
    "AgentSpec",
    "CommandResult",
]

#: Version of every artifact schema in this module. A record carrying another version
#: is rejected rather than guessed at.
SCHEMA_VERSION = 1

JsonScalar = str | int | float | bool | None

_ARTIFACT_ID = re.compile(r"[a-z0-9][a-z0-9.-]{0,127}")
_EVALUATOR_ID = re.compile(r"[a-z][a-z0-9_]*(?:\.[a-z][a-z0-9_]*)*")
_SHA256 = re.compile(r"[0-9a-f]{64}")
_DOI = re.compile(r"10\.[0-9]{4,9}/[^\s\"']+")
_ENV_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_DATE = re.compile(r"[0-9]{4}-[0-9]{2}-[0-9]{2}")


class ArtifactError(ValueError):
    """Raised for every schema, identity, digest or value violation."""


class EvaluationStatus(StrEnum):
    """Verdict of one evidence gate on one candidate theory."""

    PASS = "pass"
    FAIL = "fail"
    INCONCLUSIVE = "inconclusive"
    NOT_APPLICABLE = "not_applicable"
    ERROR = "error"


def _show(value: object) -> str:
    text = repr(value)
    return text if len(text) <= 72 else f"{text[:69]}..."


def _fail(field: str, expectation: str, value: object) -> NoReturn:
    raise ArtifactError(f"{field}: {expectation}, got {_show(value)}")


def validate_artifact_id(value: object, field: str = "id") -> str:
    """Accept an artifact id: ``[a-z0-9][a-z0-9.-]{0,127}``."""
    if not isinstance(value, str) or not _ARTIFACT_ID.fullmatch(value):
        _fail(field, "expected an artifact id matching [a-z0-9][a-z0-9.-]{0,127}", value)
    return value


def validate_sha256_hex(value: object, field: str = "sha256") -> str:
    """Accept a lowercase hexadecimal SHA-256 digest."""
    if not isinstance(value, str) or not _SHA256.fullmatch(value):
        _fail(field, "expected 64 lowercase hexadecimal SHA-256 characters", value)
    return value


def validate_timestamp(value: object, field: str = "timestamp") -> str:
    """Accept a timezone-aware ISO-8601 timestamp at UTC. Never generates one."""
    if not isinstance(value, str):
        _fail(field, "expected an ISO-8601 UTC timestamp string", value)
    try:
        parsed = datetime.fromisoformat(value)
    except ValueError:
        _fail(field, "expected an ISO-8601 timestamp such as 2026-08-23T10:15:00Z", value)
    if parsed.tzinfo is None or parsed.utcoffset() != timedelta(0):
        _fail(field, "expected a timezone-aware timestamp at UTC offset +00:00", value)
    return value


def validate_evaluator_id(value: object, field: str = "evaluator") -> str:
    """Accept a built-in evaluator id: dotted lowercase identifiers with underscores.

    This is the whole namespace an evidence record can name, so the registry and the
    ``gate.evaluator`` key are checked by this one rule.
    """
    if not isinstance(value, str) or len(value) > 256 or not _EVALUATOR_ID.fullmatch(value):
        _fail(field, "expected a dotted lowercase identifier such as principia.evaluators.bell_ch", value)
    return value


def _env_name(value: object, field: str) -> str:
    if not isinstance(value, str) or not _ENV_NAME.fullmatch(value):
        _fail(field, "expected an environment variable name matching [A-Za-z_][A-Za-z0-9_]*", value)
    return value


def _absolute_path(value: object, field: str) -> str:
    """A sandbox bind grants access outside the repo, so it is an absolute host path."""
    if not isinstance(value, str) or not value or "\x00" in value:
        _fail(field, "expected a non-empty absolute path", value)
    if not value.startswith("/"):
        _fail(field, "expected an absolute path starting with '/'", value)
    if value != "/" and (
        value.endswith("/") or any(part in ("", ".", "..") for part in value[1:].split("/"))
    ):
        _fail(field, "expected a normalised absolute path without empty, '.' or '..' segments", value)
    return value


def _date(value: object, field: str) -> str:
    if not isinstance(value, str) or not _DATE.fullmatch(value):
        _fail(field, "expected an ISO-8601 calendar date (YYYY-MM-DD)", value)
    try:
        date.fromisoformat(value)
    except ValueError:
        _fail(field, "expected a real calendar date (YYYY-MM-DD)", value)
    return value


def _doi(value: object, field: str) -> str:
    if not isinstance(value, str) or not _DOI.fullmatch(value):
        _fail(field, "expected a bare DOI such as 10.1103/PhysRevLett.49.1804", value)
    return value


def _https_url(value: object, field: str) -> str:
    if not isinstance(value, str) or not value or value.strip() != value:
        _fail(field, "expected an absolute https URL", value)
    parts = urlsplit(value)
    if parts.scheme != "https" or not parts.netloc:
        _fail(field, "expected an absolute https URL", value)
    return value


def _text(value: object, field: str) -> str:
    if not isinstance(value, str) or not value.strip() or "\x00" in value:
        _fail(field, "expected a non-empty string", value)
    return value


def _free_text(value: object, field: str) -> str:
    if not isinstance(value, str):
        _fail(field, "expected a string", value)
    return value


def _argv_word(value: object, field: str) -> str:
    if not isinstance(value, str) or not value or "\x00" in value:
        _fail(field, "expected a non-empty string without NUL", value)
    return value


def _flag(value: object, field: str) -> bool:
    if not isinstance(value, bool):
        _fail(field, "expected a boolean", value)
    return value


def _integer(
    value: object, field: str, *, minimum: int | None = None, maximum: int | None = None
) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        _fail(field, "expected an integer", value)
    if minimum is not None and value < minimum:
        _fail(field, f"expected an integer >= {minimum}", value)
    if maximum is not None and value > maximum:
        _fail(field, f"expected an integer <= {maximum}", value)
    return value


def _number(
    value: object, field: str, *, minimum: float | None = None, exclusive: bool = False
) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        _fail(field, "expected a number", value)
    number = float(value)
    if not math.isfinite(number):
        _fail(field, "expected a finite number", value)
    if minimum is not None and (number <= minimum if exclusive else number < minimum):
        _fail(field, f"expected a number {'>' if exclusive else '>='} {minimum}", value)
    return number


def _schema_version(value: object, field: str) -> int:
    version = _integer(value, field, minimum=1)
    if version != SCHEMA_VERSION:
        _fail(field, f"expected schema version {SCHEMA_VERSION}", value)
    return version


def _scalar(value: object, field: str) -> JsonScalar:
    if value is None or isinstance(value, (bool, str, int)):
        return value
    if isinstance(value, float):
        if not math.isfinite(value):
            _fail(field, "expected a finite number", value)
        return value
    _fail(field, "expected a JSON scalar (string, number, boolean or null)", value)


def _strings(
    value: object,
    field: str,
    validator: Callable[[object, str], str],
    *,
    minimum: int = 0,
    unique: bool = True,
) -> tuple[str, ...]:
    if isinstance(value, (str, bytes)) or not isinstance(value, (list, tuple)):
        _fail(field, "expected an array of strings", value)
    items = tuple(validator(item, f"{field}[{index}]") for index, item in enumerate(value))
    if len(items) < minimum:
        _fail(field, f"expected at least {minimum} entry/entries", value)
    if unique and len(set(items)) != len(items):
        _fail(field, "expected unique entries", value)
    return items


def _child(value: object, field: str, model: type[_Artifact]) -> _Artifact:
    if isinstance(value, model):
        return value
    if isinstance(value, Mapping):
        return model.from_dict(value)
    _fail(field, f"expected a {model.__name__} or a JSON object", value)


def _children(value: object, field: str, model: type[_Artifact]) -> tuple[_Artifact, ...]:
    if isinstance(value, (str, bytes)) or not isinstance(value, (list, tuple)):
        _fail(field, f"expected an array of {model.__name__} objects", value)
    return tuple(_child(item, f"{field}[{index}]", model) for index, item in enumerate(value))


def _freeze_json(value: object, field: str) -> object:
    """Deep-freeze evaluator-defined JSON: objects become read-only, arrays become tuples."""
    if value is None or isinstance(value, (bool, str, int)):
        return value
    if isinstance(value, float):
        if not math.isfinite(value):
            _fail(field, "expected a finite number", value)
        return value
    if isinstance(value, Mapping):
        frozen: dict[str, object] = {}
        for key, item in value.items():
            if not isinstance(key, str):
                _fail(field, "expected string object keys", key)
            frozen[key] = _freeze_json(item, f"{field}.{key}")
        return MappingProxyType(frozen)
    if isinstance(value, (list, tuple)):
        return tuple(_freeze_json(item, f"{field}[{index}]") for index, item in enumerate(value))
    _fail(field, "expected JSON data (object, array, string, number, boolean or null)", value)


def _json_object(value: object, field: str) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        _fail(field, "expected a JSON object", value)
    frozen = _freeze_json(value, field)
    if not isinstance(frozen, MappingProxyType):
        _fail(field, "expected a JSON object", value)
    return frozen


def _scalar_map(value: object, field: str) -> Mapping[str, JsonScalar]:
    if not isinstance(value, Mapping):
        _fail(field, "expected a JSON object of scalar values", value)
    frozen: dict[str, JsonScalar] = {}
    for key, item in value.items():
        if not isinstance(key, str) or not key:
            _fail(field, "expected non-empty string keys", key)
        frozen[key] = _scalar(item, f"{field}.{key}")
    return MappingProxyType(frozen)


def _hash_map(value: object, field: str) -> Mapping[str, str]:
    if not isinstance(value, Mapping):
        _fail(field, "expected a JSON object mapping names to SHA-256 digests", value)
    frozen: dict[str, str] = {}
    for key, item in value.items():
        if not isinstance(key, str) or not key:
            _fail(field, "expected non-empty string keys", key)
        frozen[key] = validate_sha256_hex(item, f"{field}.{key}")
    return MappingProxyType(frozen)


def _status(value: object, field: str) -> EvaluationStatus:
    if isinstance(value, EvaluationStatus):
        return value
    if isinstance(value, str):
        try:
            return EvaluationStatus(value)
        except ValueError:
            pass
    allowed = ", ".join(status.value for status in EvaluationStatus)
    _fail(field, f"expected one of {allowed}", value)


def _to_json(value: object) -> object:
    if isinstance(value, _Artifact):
        return value.to_dict()
    if isinstance(value, StrEnum):
        return value.value
    if isinstance(value, Mapping):
        return {key: _to_json(item) for key, item in value.items()}
    if isinstance(value, tuple):
        return [_to_json(item) for item in value]
    return value


def _read_object(
    value: object, label: str, names: tuple[str, ...], nullable: tuple[str, ...]
) -> dict[str, object]:
    if not isinstance(value, Mapping):
        _fail(label, "expected a JSON object", value)
    for key in value:
        if not isinstance(key, str):
            _fail(label, "expected string object keys", key)
    unknown = sorted(key for key in value if key not in names)
    if unknown:
        raise ArtifactError(
            f"{label}: unknown key(s) {', '.join(unknown)}; "
            f"allowed keys are {', '.join(names)}"
        )
    missing = [name for name in names if name not in nullable and name not in value]
    if missing:
        raise ArtifactError(f"{label}: missing required key(s) {', '.join(missing)}")
    return {name: value.get(name) for name in names}


class _Artifact:
    """Strict JSON parsing and canonical dict emission for frozen models.

    Keys named in ``_NULLABLE`` may be ``null`` or absent; every other declared key
    must be present. Unknown keys are rejected at every level. :meth:`to_dict` always
    emits every key, so ``from_dict(to_dict(x)) == x`` holds.
    """

    __slots__ = ()
    _NULLABLE: ClassVar[tuple[str, ...]] = ()

    @classmethod
    def from_dict(cls, data: object) -> Self:
        names = tuple(field.name for field in fields(cls))
        return cls(**_read_object(data, cls.__name__, names, cls._NULLABLE))

    def to_dict(self) -> dict[str, object]:
        return {field.name: _to_json(getattr(self, field.name)) for field in fields(self)}

    def _put(
        self,
        name: str,
        validator: Callable[..., object],
        *args: object,
        optional: bool = False,
        **kwargs: object,
    ) -> None:
        value = getattr(self, name)
        if optional and value is None:
            return
        label = f"{type(self).__name__}.{name}"
        object.__setattr__(self, name, validator(value, label, *args, **kwargs))


@dataclass(frozen=True, slots=True)
class SourceRef(_Artifact):
    """The publication an artifact rests on."""

    title: str
    authors: tuple[str, ...]
    url: str
    doi: str | None
    published: str

    _NULLABLE = ("doi",)

    def __post_init__(self) -> None:
        self._put("title", _text)
        self._put("authors", _strings, _text, minimum=1, unique=False)
        self._put("url", _https_url)
        self._put("doi", _doi, optional=True)
        self._put("published", _date)


@dataclass(frozen=True, slots=True)
class DatasetRef(_Artifact):
    """Data pinned by digest: committed at ``local_path``, fetched from ``url``, or both.

    ``local_path`` is resolved where the file is opened, so a record naming an escaping
    path still loads and is reported as a problem by ``evidence.verify_evidence``.
    """

    url: str | None
    sha256: str
    license: str
    format: str
    local_path: str | None

    _NULLABLE = ("url", "local_path")

    def __post_init__(self) -> None:
        self._put("url", _https_url, optional=True)
        self._put("sha256", validate_sha256_hex)
        self._put("license", _text)
        self._put("format", _text)
        self._put("local_path", _text, optional=True)


@dataclass(frozen=True, slots=True)
class LeanSpec(_Artifact):
    """Where a candidate theory lives in Lean and which declarations carry its content.

    Names and paths are strings here. ``candidates.verify_candidate`` judges whether
    they are legal Lean names inside the declared namespace, and whether the entrypoint
    resolves to a file inside the candidate Lean tree.
    """

    module: str
    entrypoint: str
    namespace: str
    witnesses: tuple[str, ...]
    claims: tuple[str, ...]

    def __post_init__(self) -> None:
        self._put("module", _text)
        self._put("entrypoint", _text)
        self._put("namespace", _text)
        self._put("witnesses", _strings, _text, unique=False)
        self._put("claims", _strings, _text, unique=False)


@dataclass(frozen=True, slots=True)
class EvidenceGate(_Artifact):
    """The evaluator that judges this evidence, the claims it needs, and its configuration.

    ``inputs`` and ``decision`` are evaluator-defined JSON of any depth. Their keys
    belong to the named evaluator, not to this schema, so they are validated as JSON
    data and frozen rather than key-checked.
    """

    evaluator: str
    required_claims: tuple[str, ...]
    inputs: Mapping[str, object]
    decision: Mapping[str, object]

    def __post_init__(self) -> None:
        self._put("evaluator", validate_evaluator_id)
        self._put("required_claims", _strings, validate_artifact_id)
        self._put("inputs", _json_object)
        self._put("decision", _json_object)


@dataclass(frozen=True, slots=True)
class EvidenceRecord(_Artifact):
    """One experiment, its provenance, its data, and the gate it imposes on candidates."""

    schema_version: int
    id: str
    version: int
    title: str
    source: SourceRef
    dataset: DatasetRef
    gate: EvidenceGate

    def __post_init__(self) -> None:
        self._put("schema_version", _schema_version)
        self._put("id", validate_artifact_id)
        self._put("version", _integer, minimum=1)
        self._put("title", _text)
        self._put("source", _child, SourceRef)
        self._put("dataset", _child, DatasetRef)
        self._put("gate", _child, EvidenceGate)


@dataclass(frozen=True, slots=True)
class Assumption(_Artifact):
    """A hypothesis the candidate takes on, encoded in Lean and cited to a source."""

    id: str
    lean_symbol: str
    source: SourceRef

    def __post_init__(self) -> None:
        self._put("id", validate_artifact_id)
        self._put("lean_symbol", _text)
        self._put("source", _child, SourceRef)


@dataclass(frozen=True, slots=True)
class ClaimRef(_Artifact):
    """A prediction of the candidate, tied to the Lean declaration that states it."""

    id: str
    lean_symbol: str

    def __post_init__(self) -> None:
        self._put("id", validate_artifact_id)
        self._put("lean_symbol", _text)


@dataclass(frozen=True, slots=True)
class Parameter(_Artifact):
    """A free parameter of the candidate theory."""

    id: str
    value: JsonScalar
    unit: str | None

    _NULLABLE = ("value", "unit")

    def __post_init__(self) -> None:
        self._put("id", validate_artifact_id)
        self._put("value", _scalar, optional=True)
        self._put("unit", _text, optional=True)


@dataclass(frozen=True, slots=True)
class ExceptionRecord(_Artifact):
    """A regime the candidate does not cover, or a known conflict."""

    id: str
    description: str

    def __post_init__(self) -> None:
        self._put("id", validate_artifact_id)
        self._put("description", _text)


@dataclass(frozen=True, slots=True)
class EvidencePrediction(_Artifact):
    """What the candidate predicts for one evidence record, in the evaluator's own terms."""

    id: str
    prediction: Mapping[str, object]

    def __post_init__(self) -> None:
        self._put("id", validate_artifact_id)
        self._put("prediction", _json_object)


@dataclass(frozen=True, slots=True)
class CandidateManifest(_Artifact):
    """Identity, lineage, Lean anchors and commitments of one candidate theory."""

    schema_version: int
    id: str
    version: int
    parent: str | None
    title: str
    lean: LeanSpec
    assumptions: tuple[Assumption, ...]
    claims: tuple[ClaimRef, ...]
    parameters: tuple[Parameter, ...]
    exceptions: tuple[ExceptionRecord, ...]
    evidence: tuple[EvidencePrediction, ...]

    _NULLABLE = ("parent",)

    def __post_init__(self) -> None:
        self._put("schema_version", _schema_version)
        self._put("id", validate_artifact_id)
        self._put("version", _integer, minimum=1)
        self._put("parent", validate_artifact_id, optional=True)
        self._put("title", _text)
        self._put("lean", _child, LeanSpec)
        self._put("assumptions", _children, Assumption)
        self._put("claims", _children, ClaimRef)
        self._put("parameters", _children, Parameter)
        self._put("exceptions", _children, ExceptionRecord)
        self._put("evidence", _children, EvidencePrediction)


@dataclass(frozen=True, slots=True)
class EvaluationResult(_Artifact):
    """Verdict of one gate on one candidate, with recomputed metrics and input digests."""

    schema_version: int
    candidate_id: str
    evidence_id: str | None
    status: EvaluationStatus
    summary: str
    metrics: Mapping[str, JsonScalar]
    artifacts: Mapping[str, str]
    timestamp: str

    _NULLABLE = ("evidence_id",)

    def __post_init__(self) -> None:
        self._put("schema_version", _schema_version)
        self._put("candidate_id", validate_artifact_id)
        self._put("evidence_id", validate_artifact_id, optional=True)
        self._put("status", _status)
        self._put("summary", _text)
        self._put("metrics", _scalar_map)
        self._put("artifacts", _hash_map)
        self._put("timestamp", validate_timestamp)


@dataclass(frozen=True, slots=True)
class AgentSpec(_Artifact):
    """How to run one agent under the sandbox. ``command`` is argv; there is no shell.

    ``read_only_binds`` are absolute host paths: they grant capabilities from outside
    the repository, which is already bound read-only.
    """

    command: tuple[str, ...]
    network: bool
    timeout_seconds: float
    env_allowlist: tuple[str, ...]
    read_only_binds: tuple[str, ...]

    def __post_init__(self) -> None:
        self._put("command", _strings, _argv_word, minimum=1, unique=False)
        self._put("network", _flag)
        self._put("timeout_seconds", _number, minimum=0.0, exclusive=True)
        self._put("env_allowlist", _strings, _env_name)
        self._put("read_only_binds", _strings, _absolute_path)


@dataclass(frozen=True, slots=True)
class CommandResult(_Artifact):
    """What one sandboxed agent run did. Exactly one of ``exit_code``/``signal`` is set."""

    command: tuple[str, ...]
    exit_code: int | None
    signal: int | None
    timed_out: bool
    stdout: str
    stderr: str
    stdout_sha256: str
    stderr_sha256: str
    request_sha256: str
    duration_seconds: float
    timestamp: str

    _NULLABLE = ("exit_code", "signal")

    def __post_init__(self) -> None:
        self._put("command", _strings, _argv_word, minimum=1, unique=False)
        self._put("exit_code", _integer, minimum=0, maximum=255, optional=True)
        self._put("signal", _integer, minimum=1, maximum=64, optional=True)
        self._put("timed_out", _flag)
        self._put("stdout", _free_text)
        self._put("stderr", _free_text)
        self._put("stdout_sha256", validate_sha256_hex)
        self._put("stderr_sha256", validate_sha256_hex)
        self._put("request_sha256", validate_sha256_hex)
        self._put("duration_seconds", _number, minimum=0.0)
        self._put("timestamp", validate_timestamp)
        if (self.exit_code is None) == (self.signal is None):
            raise ArtifactError(
                "CommandResult: expected exactly one of 'exit_code' or 'signal', got "
                f"exit_code={self.exit_code!r} and signal={self.signal!r}"
            )
