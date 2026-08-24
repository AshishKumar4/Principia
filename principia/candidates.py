"""Candidate theory manifests: load, verify, measure and trace lineage.

A candidate lives in its own directory. The directory name is the candidate id, so
identity cannot drift from location. The directory holds ``candidate.json``; the Lean
sources it points at live in the candidate Lean tree ``CandidateLab/`` so that Lean can
import them by module name.

Verification never interprets physics. It covers identity, path containment, Lean name
sanity and cross-field agreement, so the Lean toolchain and the axiom audit downstream
see exactly the declarations the manifest promised. Two containment rules carry the
weight: an entrypoint must stay inside ``CandidateLab/`` and every declared symbol must
sit inside the candidate namespace. Without them a candidate could point at the frozen
atlas and claim theorems it did not prove.
"""

from __future__ import annotations

import os
import re
from collections import Counter
from collections.abc import Iterable, Sequence
from pathlib import Path
from typing import Protocol

from .artifacts import load_json, resolve_repo_path
from .models import ArtifactError, CandidateManifest, ClaimRef, EvidencePrediction

__all__ = [
    "CANDIDATE_LEAN_ROOT",
    "CANDIDATE_MANIFEST_NAME",
    "candidate_complexity",
    "candidate_lineage",
    "load_candidate",
    "verify_candidate",
]

StrPath = str | os.PathLike[str]

CANDIDATE_MANIFEST_NAME = "candidate.json"

#: Repo-relative Lean source tree that holds candidate theories. Candidate Lean files
#: live here and nowhere else, which keeps the frozen atlas out of reach.
CANDIDATE_LEAN_ROOT = "CandidateLab"

# A Lean 4 name is dot-separated components, each an ASCII identifier. Declared symbols
# are spliced into generated Lean checker source downstream, so a name outside this
# grammar is rejected here rather than escaped later.
_LEAN_COMPONENT = r"[A-Za-z_][A-Za-z0-9_'!?]*"
_LEAN_NAME_RE = re.compile(rf"{_LEAN_COMPONENT}(?:\.{_LEAN_COMPONENT})*")

# Reserved Lean tokens cannot be a bare name component: `Foo.axiom` does not parse.
_LEAN_KEYWORDS = frozenset(
    {
        "at",
        "attribute",
        "axiom",
        "by",
        "class",
        "def",
        "deriving",
        "do",
        "else",
        "end",
        "example",
        "forall",
        "from",
        "fun",
        "have",
        "if",
        "import",
        "in",
        "inductive",
        "instance",
        "let",
        "macro",
        "match",
        "mutual",
        "namespace",
        "noncomputable",
        "open",
        "partial",
        "private",
        "protected",
        "section",
        "set_option",
        "show",
        "sorry",
        "structure",
        "syntax",
        "then",
        "theorem",
        "universe",
        "unsafe",
        "variable",
        "where",
        "with",
    }
)


class _Identified(Protocol):
    """Any manifest reference carrying an artifact id."""

    @property
    def id(self) -> str: ...


def load_candidate(candidate_dir: StrPath) -> CandidateManifest:
    """Load ``candidate.json`` from *candidate_dir*.

    Raises ``ArtifactError`` when the manifest is absent, is not a JSON object, fails
    schema validation, or declares an id other than the directory name.
    """
    directory = Path(candidate_dir)
    manifest_path = directory / CANDIDATE_MANIFEST_NAME
    if not manifest_path.is_file():
        raise ArtifactError(f"candidate manifest not found: {manifest_path}")
    payload = load_json(manifest_path)
    if not isinstance(payload, dict):
        raise ArtifactError(
            f"{manifest_path}: candidate manifest must be a JSON object, "
            f"got {type(payload).__name__}"
        )
    manifest = CandidateManifest.from_dict(payload)
    directory_name = _directory_name(directory)
    if manifest.id != directory_name:
        raise ArtifactError(
            f"{manifest_path}: manifest id {manifest.id!r} does not match candidate "
            f"directory name {directory_name!r}"
        )
    return manifest


def verify_candidate(
    manifest: CandidateManifest, candidate_dir: StrPath, repo_root: StrPath
) -> list[str]:
    """Report every problem with *manifest* as stored in *candidate_dir*.

    An empty list means the candidate is well formed. Problems come back in a fixed
    order: identity, location, Lean declarations, then the nested reference arrays.
    """
    directory = Path(candidate_dir)
    repo = Path(repo_root)
    lean = manifest.lean
    problems: list[str] = []

    directory_name = _directory_name(directory)
    if manifest.id != directory_name:
        problems.append(
            f"id: {manifest.id!r} does not match candidate directory name "
            f"{directory_name!r}"
        )

    if not _inside(repo, directory):
        problems.append(
            f"candidate directory {directory.resolve()} is not inside repo root "
            f"{repo.resolve()}"
        )

    if manifest.parent == manifest.id:
        problems.append(f"parent: {manifest.parent!r} is the candidate itself")

    module_problem = _lean_name_problem("lean.module", lean.module)
    if module_problem is not None:
        problems.append(module_problem)

    namespace_problem = _lean_name_problem("lean.namespace", lean.namespace)
    if namespace_problem is not None:
        problems.append(namespace_problem)
    namespace = None if namespace_problem is not None else lean.namespace

    problems.extend(_entrypoint_problems(lean.module, lean.entrypoint, repo))

    problems.extend(_symbol_problems("lean.witnesses", lean.witnesses, namespace))
    problems.extend(_symbol_problems("lean.claims", lean.claims, namespace))
    problems.extend(
        f"lean: {symbol!r} is declared as both a witness and a claim"
        for symbol in sorted(set(lean.witnesses) & set(lean.claims))
    )
    if not lean.witnesses:
        problems.append(
            "lean.witnesses: empty; a candidate must name at least one non-vacuity "
            "witness declaration"
        )
    if not lean.claims:
        problems.append(
            "lean.claims: empty; a candidate must name at least one claim declaration "
            "to check"
        )

    problems.extend(_duplicate_id_problems("assumptions", manifest.assumptions))
    problems.extend(
        _symbol_problems(
            "assumptions.lean_symbol",
            [assumption.lean_symbol for assumption in manifest.assumptions],
            namespace,
        )
    )

    problems.extend(_duplicate_id_problems("claims", manifest.claims))
    problems.extend(_claim_symbol_problems(manifest.claims, lean.claims))

    problems.extend(_duplicate_id_problems("parameters", manifest.parameters))
    problems.extend(_duplicate_id_problems("exceptions", manifest.exceptions))
    problems.extend(_duplicate_id_problems("evidence", manifest.evidence))
    problems.extend(_prediction_problems(manifest.evidence))

    return problems


def candidate_complexity(
    manifest: CandidateManifest, repo_root: StrPath
) -> dict[str, int]:
    """Measure candidate complexity from the artifacts themselves.

    Every number is computed: ``source_bytes`` is the size of the Lean entrypoint on
    disk, the counts are the lengths of the manifest reference arrays. A manifest can
    never report its own complexity.

    Raises ``ArtifactError`` when the entrypoint is missing, escapes the repo, or is
    not a regular file.
    """
    entrypoint = resolve_repo_path(repo_root, manifest.lean.entrypoint, must_exist=True)
    if not entrypoint.is_file():
        raise ArtifactError(
            f"lean entrypoint {manifest.lean.entrypoint!r} is not a regular file: "
            f"{entrypoint}"
        )
    return {
        "source_bytes": entrypoint.stat().st_size,
        "assumption_count": len(manifest.assumptions),
        "parameter_count": len(manifest.parameters),
        "exception_count": len(manifest.exceptions),
    }


def candidate_lineage(candidates_root: StrPath, candidate_id: str) -> list[str]:
    """Walk the parent chain of *candidate_id*.

    Returns the ids from the earliest ancestor to *candidate_id* inclusive. Raises
    ``ArtifactError`` on an id that is not a plain directory name, an unknown
    candidate, a parent that does not exist, or a cycle.
    """
    _require_directory_name(candidate_id)
    root = Path(candidates_root)
    chain: list[str] = []
    child: str | None = None
    current: str | None = candidate_id

    while current is not None:
        if current in chain:
            cycle = " -> ".join([*chain[chain.index(current) :], current])
            raise ArtifactError(f"candidate lineage cycle: {cycle}")
        directory = root / current
        if not directory.is_dir():
            raise ArtifactError(
                f"candidate {current!r} not found under {root}"
                if child is None
                else f"parent {current!r} of candidate {child!r} not found under {root}"
            )
        manifest = load_candidate(directory)
        chain.append(current)
        child = current
        current = manifest.parent

    chain.reverse()
    return chain


def _directory_name(candidate_dir: Path) -> str:
    # abspath normalises `.`, `..` and trailing separators without resolving symlinks,
    # so the id is compared against the directory as addressed.
    return os.path.basename(os.path.abspath(candidate_dir))


def _inside(root: StrPath, target: StrPath) -> bool:
    return Path(root).resolve() in Path(target).resolve().parents


def _entrypoint_problems(module: str, entrypoint: str, repo_root: Path) -> list[str]:
    problems: list[str] = []

    lean_root = f"{CANDIDATE_LEAN_ROOT}/"
    declared_inside = entrypoint.startswith(lean_root)
    if not declared_inside:
        problems.append(
            f"lean.entrypoint: {entrypoint!r} is outside the candidate Lean tree "
            f"{lean_root!r}"
        )

    if not entrypoint.endswith(".lean"):
        problems.append(f"lean.entrypoint: {entrypoint!r} is not a .lean file")
    elif _LEAN_NAME_RE.fullmatch(module):
        module_path = f"{module.replace('.', '/')}.lean"
        if entrypoint != module_path and not entrypoint.endswith(f"/{module_path}"):
            problems.append(
                f"lean.entrypoint: {entrypoint!r} cannot provide module {module!r}; "
                f"the path must end with {module_path!r}"
            )

    try:
        resolved = resolve_repo_path(repo_root, entrypoint, must_exist=True)
    except ArtifactError as error:
        problems.append(f"lean.entrypoint: {error}")
        return problems

    if not resolved.is_file():
        problems.append(
            f"lean.entrypoint: {entrypoint!r} is not a regular file: {resolved}"
        )
    elif declared_inside and not _inside(repo_root / CANDIDATE_LEAN_ROOT, resolved):
        problems.append(
            f"lean.entrypoint: {entrypoint!r} resolves to {resolved}, outside the "
            f"candidate Lean tree {lean_root!r}"
        )
    return problems


def _lean_name_problem(field: str, name: str) -> str | None:
    if not _LEAN_NAME_RE.fullmatch(name):
        return f"{field}: {name!r} is not a dotted ASCII Lean name"
    reserved = sorted({part for part in name.split(".") if part in _LEAN_KEYWORDS})
    if reserved:
        return f"{field}: {name!r} uses reserved Lean token(s) {', '.join(reserved)}"
    return None


def _symbol_problems(
    field: str, symbols: Sequence[str], namespace: str | None
) -> list[str]:
    problems: list[str] = []
    seen: set[str] = set()
    for index, symbol in enumerate(symbols):
        where = f"{field}[{index}]"
        name_problem = _lean_name_problem(where, symbol)
        if name_problem is not None:
            problems.append(name_problem)
            continue
        if namespace is not None and not symbol.startswith(f"{namespace}."):
            problems.append(
                f"{where}: {symbol!r} is not a declaration inside namespace "
                f"{namespace!r}"
            )
        if symbol in seen:
            problems.append(f"{where}: {symbol!r} is listed more than once")
        seen.add(symbol)
    return problems


def _claim_symbol_problems(
    claims: Sequence[ClaimRef], declared: Sequence[str]
) -> list[str]:
    named = {claim.lean_symbol for claim in claims}
    declared_symbols = set(declared)
    return [
        *(
            f"claims: lean symbol {symbol!r} is missing from lean.claims, so it would "
            "never be checked"
            for symbol in sorted(named - declared_symbols)
        ),
        *(
            f"lean.claims: {symbol!r} is not named by any claim entry"
            for symbol in sorted(declared_symbols - named)
        ),
    ]


def _prediction_problems(references: Sequence[EvidencePrediction]) -> list[str]:
    problems: list[str] = []
    for index, reference in enumerate(references):
        where = f"evidence[{index}]"
        if not reference.prediction:
            problems.append(
                f"{where}: prediction is empty; an evidence reference must state what "
                "the candidate predicts"
            )
            continue
        problems.extend(
            f"{where}: prediction key {key!r} must be a non-blank string without "
            "surrounding whitespace"
            for key in sorted(reference.prediction)
            if not key or key.strip() != key
        )
    return problems


def _duplicate_id_problems(field: str, references: Iterable[_Identified]) -> list[str]:
    counts = Counter(reference.id for reference in references)
    return [
        f"{field}: id {value!r} is used {count} times"
        for value, count in sorted(counts.items())
        if count > 1
    ]


def _require_directory_name(candidate_id: str) -> None:
    """A caller-supplied id addresses a directory, so it must be one path component."""
    if (
        not candidate_id
        or candidate_id in {".", ".."}
        or os.path.basename(candidate_id) != candidate_id
    ):
        raise ArtifactError(
            f"candidate id {candidate_id!r} is not a plain directory name"
        )
