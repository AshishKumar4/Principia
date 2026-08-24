"""Candidate evaluation: Lean verification, evidence gates and an immutable archive.

`evaluate_candidate` is the only public entry point. It verifies the candidate
manifest, builds and compiles the declared Lean entrypoint, elaborates every
declared claim and witness symbol through a generated checker, audits the kernel
axiom dependencies of the candidate namespace, evaluates the requested evidence
records and archives one canonical result bundle.

The two failure kinds stay separate. `fail` means the candidate is wrong: an
invalid manifest, Lean source that does not compile, a missing symbol, a
forbidden axiom, or a claim symbol that is not a theorem. `error` means the
evaluation could not be carried out: no manifest, no Lean toolchain, a process
timeout, or an unreadable evidence record. The archive is immutable. An
identical re-run keeps the archived bundle, and different bytes under the same
bundle id raise `ArtifactError`.
"""

from __future__ import annotations

import hashlib
import os
import re
import shutil
import signal
import subprocess
import tempfile
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path

from . import runner as _runner
from .artifacts import resolve_repo_path, sha256_json, write_json_atomic
from .candidates import (
    CANDIDATE_MANIFEST_NAME,
    candidate_complexity,
    load_candidate,
    verify_candidate,
)
from .evidence import evaluate_evidence, load_evidence
from .models import (
    SCHEMA_VERSION,
    ArtifactError,
    CandidateManifest,
    EvaluationResult,
    EvaluationStatus,
    LeanSpec,
)

__all__ = [
    "ALLOWED_AXIOMS",
    "BUNDLE_DIGEST_FILENAME",
    "BUNDLE_FILENAME",
    "BUNDLE_SCHEMA_VERSION",
    "LOG_DIRNAME",
    "evaluate_candidate",
]

ALLOWED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
BUNDLE_SCHEMA_VERSION = 1
BUNDLE_FILENAME = "bundle.json"
BUNDLE_DIGEST_FILENAME = "bundle.sha256"
LOG_DIRNAME = "logs"

_TOOLCHAIN_FILENAME = "lean-toolchain"
_CHECKER_FILENAME = "PrincipiaChecker.lean"
_CHECKER_ROOT = ".principia/tmp"
_CHECKER_SECTION = "PrincipiaCheck"

_BUILD_COMMAND = "lean.build"
_COMPILE_COMMAND = "lean.compile"
_CHECK_COMMAND = "lean.check"
_LAKE = "lake"
_BWRAP = "bwrap"
_LAKE_STATE_DIRNAME = ".lake"
_SANDBOX_STDERR_PREFIX = b"bwrap:"
_XDG_CACHE = "/tmp/xdg-cache"

_BUILD_TIMEOUT_SECONDS = 3600.0
_COMPILE_TIMEOUT_SECONDS = 900.0
_CHECK_TIMEOUT_SECONDS = 900.0
_TERMINATE_GRACE_SECONDS = 5.0

_DIAGNOSTIC_LIMIT = 5
_ID_DIGEST_LENGTH = 16
_ID_PREFIX_LENGTH = 96

_AUDIT_RE = re.compile(
    r"PRINCIPIA_AUDIT checked=(\d+) claims=(\d+) witnesses=(\d+) violations=(\d+)"
)
_VIOLATION_RE = re.compile(r"PRINCIPIA_AXIOM_VIOLATION (\S+) (\S+)")
_NOT_THEOREM_RE = re.compile(r"PRINCIPIA_CLAIM_NOT_THEOREM (\S+)")


@dataclass(frozen=True)
class _Audit:
    """Counters reported by the generated checker."""

    checked: int
    claims: int
    witnesses: int
    violations: int



@dataclass
class _Sandbox:
    """Containment for candidate Lean elaboration, which is untrusted code."""

    bwrap: str
    repo_root: Path
    lake_bin: Path
    scratch: Path
    elan_home: Path | None
    uppers: list[Path] = field(default_factory=list)

    def allocate_layer(self) -> tuple[Path, Path]:
        """A fresh writable layer: kernel overlayfs refuses to reuse an upper."""
        index = len(self.uppers)
        upper = self.scratch / f"upper-{index}"
        work = self.scratch / f"work-{index}"
        upper.mkdir()
        work.mkdir()
        return upper, work


def _sandbox_argv(
    sandbox: _Sandbox, argv: Sequence[str], upper: Path, work: Path
) -> list[str]:
    """Assemble the bubblewrap command line for one Lean invocation.

    The mount plan mirrors `runner._sandbox_argv`: allowlisted system
    directories, the repository read-only, a private HOME and /tmp, and no
    network. On top of that, `<repo>/.lake` becomes an overlay: every step gets
    a fresh writable upper layer, earlier steps' layers stack read-only above
    the real Lake state (later `--overlay-src` entries are higher layers), so
    the module olean built in step one is visible to the checker while the
    repository itself never changes.
    """
    environment = {
        "HOME": _runner.SANDBOX_HOME,
        "TMPDIR": _runner.SANDBOX_TMP,
        "LANG": _runner.SANDBOX_LOCALE,
        "LC_ALL": _runner.SANDBOX_LOCALE,
        "XDG_CACHE_HOME": _XDG_CACHE,
        "PATH": f"{sandbox.lake_bin}:{_runner.SANDBOX_PATH}",
    }
    if sandbox.elan_home is not None:
        environment["ELAN_HOME"] = str(sandbox.elan_home)
    vector = [sandbox.bwrap, "--unshare-all", "--die-with-parent", "--new-session", "--clearenv"]
    for name in sorted(environment):
        vector += ["--setenv", name, environment[name]]
    for path in _runner._system_read_only():
        vector += ["--ro-bind", str(path), str(path)]
    vector += ["--proc", "/proc", "--dev", "/dev"]
    vector += ["--tmpfs", _runner.SANDBOX_TMP, "--tmpfs", _runner.SANDBOX_HOME]
    if sandbox.elan_home is not None:
        vector += ["--ro-bind", str(sandbox.elan_home), str(sandbox.elan_home)]
    vector += ["--ro-bind", str(sandbox.repo_root), str(sandbox.repo_root)]
    lake_state = sandbox.repo_root / _LAKE_STATE_DIRNAME
    vector += ["--overlay-src", str(lake_state)]
    for layer in sandbox.uppers:
        vector += ["--overlay-src", str(layer)]
    vector += ["--overlay", str(upper), str(work), str(lake_state)]
    vector += ["--chdir", str(sandbox.repo_root), "--", *argv]
    return vector

@dataclass(frozen=True)
class _Outcome:
    """Captured result of one Lean process invocation."""

    name: str
    argv: tuple[str, ...]
    exit_code: int
    timed_out: bool
    stdout: bytes
    stderr: bytes

    @property
    def ok(self) -> bool:
        return self.exit_code == 0 and not self.timed_out

    @property
    def text(self) -> str:
        return (self.stdout + self.stderr).decode("utf-8", "replace")


@dataclass
class _Run:
    """State collected while evaluating one candidate, archived as one bundle."""

    repo_root: Path
    candidate_dir: Path
    candidate_id: str
    timestamp: str
    toolchain: str | None
    paths: dict[str, str] = field(default_factory=dict)
    hashes: dict[str, str] = field(default_factory=dict)
    outputs: dict[str, str] = field(default_factory=dict)
    commands: list[dict[str, object]] = field(default_factory=list)
    logs: dict[str, bytes] = field(default_factory=dict)


def evaluate_candidate(
    candidate_dir: Path | str,
    evidence_paths: Sequence[Path | str],
    repo_root: Path | str,
    output_dir: Path | str,
    timestamp: str,
) -> list[EvaluationResult]:
    """Evaluate one candidate and archive the canonical result bundle.

    The first result is always the formal Lean verdict, with no evidence id. One
    result per requested evidence record follows, in the given order, and only when
    the formal verdict passes. Raises `ArtifactError` when `candidate_dir` is not a
    directory beneath `repo_root`, when its name is not a valid artifact id, or when
    an archived bundle with the same identity holds different bytes.
    """
    root = Path(repo_root).resolve()
    directory = _candidate_directory(candidate_dir, root)
    run = _Run(
        repo_root=root,
        candidate_dir=directory,
        candidate_id=directory.name,
        timestamp=timestamp,
        toolchain=_toolchain(root),
    )
    manifest, formal = _formal_stage(run)
    results = [formal]
    if manifest is not None and _status(formal) is EvaluationStatus.PASS:
        results.extend(_evidence_stage(run, manifest, evidence_paths))
    _archive(run, results, Path(output_dir))
    return results


# --- formal stage -----------------------------------------------------------


def _formal_stage(run: _Run) -> tuple[CandidateManifest | None, EvaluationResult]:
    manifest_path = run.candidate_dir / CANDIDATE_MANIFEST_NAME
    manifest_rel = _repo_relative(manifest_path, run.repo_root)
    run.paths["candidate_manifest"] = manifest_rel
    if not manifest_path.is_file():
        return None, _result(
            run, EvaluationStatus.ERROR, f"there is no candidate manifest at {manifest_rel}"
        )
    try:
        run.hashes["candidate_manifest_file"] = _sha256_file(manifest_path)
    except OSError as exc:
        return None, _result(
            run,
            EvaluationStatus.ERROR,
            f"the candidate manifest {manifest_rel} cannot be read: {exc}",
        )
    try:
        manifest = load_candidate(run.candidate_dir)
    except ArtifactError as exc:
        return None, _result(
            run, EvaluationStatus.FAIL, f"the candidate manifest {manifest_rel} is invalid: {exc}"
        )
    run.hashes["candidate_manifest"] = sha256_json(manifest.to_dict())

    problems = verify_candidate(manifest, run.candidate_dir, run.repo_root)
    if problems:
        return manifest, _result(
            run,
            EvaluationStatus.FAIL,
            f"the candidate {manifest.id} does not verify: " + "; ".join(problems),
            metrics={"manifest_problems": len(problems)},
        )

    lean = manifest.lean
    entrypoint = resolve_repo_path(run.repo_root, lean.entrypoint, must_exist=True)
    run.paths["lean_entrypoint"] = lean.entrypoint
    run.hashes["lean_entrypoint"] = _sha256_file(entrypoint)
    metrics: dict[str, object] = dict(candidate_complexity(manifest, run.repo_root))
    metrics["claim_symbols"] = len(lean.claims)
    metrics["witness_symbols"] = len(lean.witnesses)

    checker_bytes = _checker_source(manifest).encode("utf-8")
    digest = _sha256_bytes(checker_bytes)
    run.hashes["lean_checker"] = digest
    checker = _checker_path(run.repo_root, digest)
    run.paths["lean_checker"] = _repo_relative(checker, run.repo_root)

    lake_bin = _lake_bin_dir()
    if lake_bin is None:
        return manifest, _result(
            run,
            EvaluationStatus.ERROR,
            "the `lake` executable is neither on PATH nor in ~/.elan/bin, so the "
            "candidate cannot be verified",
            metrics=metrics,
        )
    bwrap = shutil.which(_BWRAP)
    if bwrap is None:
        return manifest, _result(
            run,
            EvaluationStatus.ERROR,
            "bubblewrap is required to contain candidate Lean elaboration and is "
            "not installed, so the candidate cannot be verified",
            metrics=metrics,
        )
    try:
        outcomes = _run_lean(run, lake_bin, bwrap, lean, entrypoint, checker, checker_bytes)
    except OSError as exc:
        return manifest, _result(
            run,
            EvaluationStatus.ERROR,
            f"a Lean process could not be started: {exc}",
            metrics=metrics,
        )
    return manifest, _verdict(run, lean, outcomes, metrics)


def _run_lean(
    run: _Run,
    lake_bin: Path,
    bwrap: str,
    lean: LeanSpec,
    entrypoint: Path,
    checker: Path,
    checker_bytes: bytes,
) -> dict[str, _Outcome]:
    """Build the module, compile the entrypoint, then run the generated checker.

    Candidate Lean source is untrusted code, so every step runs inside the
    bubblewrap sandbox over stacked Lake-state overlays: the module olean built
    in the first step stays visible to the generated checker, and none of the
    writes reach the repository.
    """
    scratch = Path(tempfile.mkdtemp(prefix="principia-lean-"))
    home = Path.home() / ".elan"
    elan_home = home if lake_bin == home / "bin" else None
    sandbox = _Sandbox(
        bwrap=bwrap,
        repo_root=run.repo_root,
        lake_bin=lake_bin,
        scratch=scratch,
        elan_home=elan_home,
    )
    try:
        return _run_lean_steps(run, sandbox, lean, entrypoint, checker, checker_bytes)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


def _run_lean_steps(
    run: _Run,
    sandbox: _Sandbox,
    lean: LeanSpec,
    entrypoint: Path,
    checker: Path,
    checker_bytes: bytes,
) -> dict[str, _Outcome]:
    # Lake reports incremental build progress that depends on cache state rather
    # than on the candidate, so its output is logged but never hashed.
    outcomes = {
        _BUILD_COMMAND: _invoke(
            run,
            _BUILD_COMMAND,
            (_LAKE, "build", lean.module),
            sandbox,
            _BUILD_TIMEOUT_SECONDS,
            hash_output=False,
        )
    }
    outcomes[_COMPILE_COMMAND] = _invoke(
        run,
        _COMPILE_COMMAND,
        (_LAKE, "env", "lean", _repo_relative(entrypoint, run.repo_root)),
        sandbox,
        _COMPILE_TIMEOUT_SECONDS,
    )
    if not outcomes[_BUILD_COMMAND].ok or not outcomes[_COMPILE_COMMAND].ok:
        return outcomes
    checker.parent.mkdir(parents=True, exist_ok=True)
    try:
        _write_bytes(checker, checker_bytes)
        outcomes[_CHECK_COMMAND] = _invoke(
            run,
            _CHECK_COMMAND,
            (_LAKE, "env", "lean", run.paths["lean_checker"]),
            sandbox,
            _CHECK_TIMEOUT_SECONDS,
        )
    finally:
        shutil.rmtree(checker.parent, ignore_errors=True)
    return outcomes


def _verdict(
    run: _Run,
    lean: LeanSpec,
    outcomes: Mapping[str, _Outcome],
    metrics: dict[str, object],
) -> EvaluationResult:
    artifacts = {**run.hashes, **run.outputs}
    build = outcomes[_BUILD_COMMAND]
    compiled = outcomes[_COMPILE_COMMAND]
    timed_out = sorted(name for name, outcome in outcomes.items() if outcome.timed_out)
    if timed_out:
        return _result(
            run,
            EvaluationStatus.ERROR,
            f"the Lean toolchain timed out during {', '.join(timed_out)}",
            metrics=metrics,
            artifacts=artifacts,
        )
    broken = sorted(
        name
        for name, outcome in outcomes.items()
        if not outcome.ok and outcome.stderr.startswith(_SANDBOX_STDERR_PREFIX)
    )
    if broken:
        first = outcomes[broken[0]]
        return _result(
            run,
            EvaluationStatus.ERROR,
            f"the evaluation sandbox failed during {', '.join(broken)}: "
            f"{_diagnostics(first)}",
            metrics=metrics,
            artifacts=artifacts,
        )
    if not compiled.ok:
        return _result(
            run,
            EvaluationStatus.FAIL,
            f"the Lean entrypoint {lean.entrypoint} does not compile: {_diagnostics(compiled)}",
            metrics=metrics,
            artifacts=artifacts,
        )
    if not build.ok:
        return _result(
            run,
            EvaluationStatus.ERROR,
            f"`lake build {lean.module}` failed, so the generated checker cannot import "
            f"the module: {_diagnostics(build)}",
            metrics=metrics,
            artifacts=artifacts,
        )

    checked = outcomes[_CHECK_COMMAND]
    audit = _parse_audit(checked.text)
    if audit is not None:
        metrics["declarations_audited"] = audit.checked
        metrics["axiom_violations"] = audit.violations
    violations = _VIOLATION_RE.findall(checked.text)
    if violations:
        detail = ", ".join(f"{name} depends on {axiom}" for name, axiom in violations)
        return _result(
            run,
            EvaluationStatus.FAIL,
            f"{len(violations)} declaration(s) under {lean.namespace} use a forbidden "
            f"axiom: {detail}",
            metrics=metrics,
            artifacts=artifacts,
        )
    not_theorems = _NOT_THEOREM_RE.findall(checked.text)
    if not_theorems:
        return _result(
            run,
            EvaluationStatus.FAIL,
            f"{len(not_theorems)} declared claim symbol(s) are not theorems: "
            f"{', '.join(not_theorems)}",
            metrics=metrics,
            artifacts=artifacts,
        )
    if not checked.ok:
        return _result(
            run,
            EvaluationStatus.FAIL,
            f"the generated Lean checker rejected the candidate: {_diagnostics(checked)}",
            metrics=metrics,
            artifacts=artifacts,
        )
    if audit is None:
        return _result(
            run,
            EvaluationStatus.ERROR,
            "the generated Lean checker reported no audit summary",
            metrics=metrics,
            artifacts=artifacts,
        )
    return _result(
        run,
        EvaluationStatus.PASS,
        f"the candidate compiles, its {audit.claims} claim and {audit.witnesses} witness "
        f"symbol(s) elaborate, and all {audit.checked} declaration(s) under "
        f"{lean.namespace} depend only on {', '.join(ALLOWED_AXIOMS)}",
        metrics=metrics,
        artifacts=artifacts,
    )


# --- generated checker ------------------------------------------------------


def _checker_source(manifest: CandidateManifest) -> str:
    """Return the Lean checker that elaborates declared symbols and audits axioms."""
    lean = manifest.lean
    claims = list(lean.claims)
    witnesses = list(lean.witnesses)
    lines = [
        "import Lean",
        f"import {lean.module}",
        "",
        "/-!",
        f"# Generated checker for candidate `{manifest.id}` version {manifest.version}",
        "",
        "`principia.evaluator` writes this file for one evaluation and deletes it",
        "afterwards. It elaborates every declared claim and witness symbol, requires",
        f"every claim to be a theorem, and audits the axioms of `{lean.namespace}`.",
        "-/",
        "",
        "open Lean",
        "",
        f"section {_CHECKER_SECTION}",
        f"open {lean.namespace}",
        "",
        *(f"#check @{symbol}" for symbol in (*claims, *witnesses)),
        "",
        "open Elab Command in",
        "run_cmd do",
        f"  let allowed : List Name := [{_name_literals(ALLOWED_AXIOMS)}]",
        f"  let root : Name := `{lean.namespace}",
        f"  let claims : List Name := [{_name_literals(claims)}]",
        f"  let witnesses : List Name := [{_name_literals(witnesses)}]",
        "  let env ← getEnv",
        "  let mut audited : Array Name := #[]",
        "  for (name, _) in env.constants.toList do",
        "    if root.isPrefixOf name then audited := audited.push name",
        "  for name in claims ++ witnesses do",
        "    unless audited.contains name do audited := audited.push name",
        "  let mut violations : Array (Name × Name) := #[]",
        "  for name in audited do",
        "    let axioms ← Lean.collectAxioms name",
        "    for ax in axioms do",
        "      unless allowed.contains ax do violations := violations.push (name, ax)",
        "  let mut nonTheorems : Array Name := #[]",
        "  for name in claims do",
        "    let isTheorem := match env.find? name with",
        "      | some (.thmInfo _) => true",
        "      | _ => false",
        "    unless isTheorem do nonTheorems := nonTheorems.push name",
        "  for (name, ax) in violations do",
        '    logError m!"PRINCIPIA_AXIOM_VIOLATION {name} {ax}"',
        "  for name in nonTheorems do",
        '    logError m!"PRINCIPIA_CLAIM_NOT_THEOREM {name}"',
        '  logInfo m!"PRINCIPIA_AUDIT checked={audited.size} claims={claims.length}'
        ' witnesses={witnesses.length} violations={violations.size}"',
        "  if audited.isEmpty then",
        f'    throwError "PRINCIPIA_AUDIT_EMPTY: no declaration under {lean.namespace}"',
        "  unless violations.isEmpty do",
        '    throwError "PRINCIPIA_AUDIT_FAILED: {violations.size} forbidden axiom'
        ' dependency(ies)"',
        "  unless nonTheorems.isEmpty do",
        '    throwError "PRINCIPIA_CLAIMS_NOT_THEOREMS: {nonTheorems.size} claim(s) are'
        ' not theorems"',
        f"end {_CHECKER_SECTION}",
        "",
    ]
    return "\n".join(lines)


def _name_literals(names: Sequence[str]) -> str:
    """Render Lean resolved-name literals, which fail to elaborate when unknown."""
    return ", ".join(f"``{name}" for name in names)


def _checker_path(repo_root: Path, digest: str) -> Path:
    """Content addressed location, so Lean diagnostics stay byte reproducible."""
    directory = f"checker-{digest[:_ID_DIGEST_LENGTH]}"
    return repo_root / _CHECKER_ROOT / directory / _CHECKER_FILENAME


def _parse_audit(text: str) -> _Audit | None:
    match = _AUDIT_RE.search(text)
    if match is None:
        return None
    checked, claims, witnesses, violations = (int(value) for value in match.groups())
    return _Audit(checked=checked, claims=claims, witnesses=witnesses, violations=violations)


def _diagnostics(outcome: _Outcome, limit: int = _DIAGNOSTIC_LIMIT) -> str:
    lines = [line.strip() for line in outcome.text.splitlines() if line.strip()]
    # Lean 4 writes both `: error: msg` and `: error(lean.someTag): msg`.
    errors = [line for line in lines if ": error" in line] or lines
    if not errors:
        return f"no diagnostics, exit code {outcome.exit_code}"
    extra = f" (+{len(errors) - limit} more)" if len(errors) > limit else ""
    return " | ".join(errors[:limit]) + extra


# --- evidence stage ---------------------------------------------------------


def _evidence_stage(
    run: _Run, manifest: CandidateManifest, evidence_paths: Sequence[Path | str]
) -> list[EvaluationResult]:
    results: list[EvaluationResult] = []
    for index, item in enumerate(evidence_paths):
        path = Path(item).resolve()
        label = f"evidence.{index}"
        run.paths[label] = _repo_relative(path, run.repo_root)
        try:
            file_digest = _sha256_file(path)
            record = load_evidence(path)
        except (ArtifactError, OSError) as exc:
            results.append(
                _result(
                    run,
                    EvaluationStatus.ERROR,
                    f"the evidence record {run.paths[label]} cannot be used: {exc}",
                )
            )
            continue
        run.hashes[f"{label}.file"] = file_digest
        run.hashes[f"{label}.record"] = sha256_json(record.to_dict())
        results.append(evaluate_evidence(record, manifest, run.repo_root, run.timestamp))
    return results


# --- archive ----------------------------------------------------------------


def _archive(run: _Run, results: Sequence[EvaluationResult], output_dir: Path) -> None:
    """Write the canonical bundle atomically and never overwrite differing bytes."""
    root = output_dir.resolve()
    bundle_id = _bundle_id(run)
    bundle = {
        "schema_version": BUNDLE_SCHEMA_VERSION,
        "bundle_id": bundle_id,
        "candidate": {
            "dir": _repo_relative(run.candidate_dir, run.repo_root),
            "id": run.candidate_id,
        },
        "commands": list(run.commands),
        "hashes": dict(run.hashes),
        "paths": dict(run.paths),
        "results": [result.to_dict() for result in results],
        "timestamp": run.timestamp,
        "toolchain": run.toolchain,
    }
    root.mkdir(parents=True, exist_ok=True)
    staging = root / f".staging-{bundle_id}-{os.getpid()}"
    shutil.rmtree(staging, ignore_errors=True)
    try:
        (staging / LOG_DIRNAME).mkdir(parents=True)
        for name, data in run.logs.items():
            _write_bytes(staging / LOG_DIRNAME / name, data)
        staged = staging / BUNDLE_FILENAME
        digest = write_json_atomic(staged, bundle)
        _write_bytes(staging / BUNDLE_DIGEST_FILENAME, f"{digest}\n".encode())
        _publish(staging, root / bundle_id, staged.read_bytes())
    finally:
        shutil.rmtree(staging, ignore_errors=True)


def _publish(staging: Path, final: Path, staged_bundle: bytes) -> None:
    try:
        os.replace(staging, final)
    except OSError:
        archived = final / BUNDLE_FILENAME
        if not archived.is_file():
            raise ArtifactError(
                f"the archive path {final} exists but holds no {BUNDLE_FILENAME}"
            ) from None
        if archived.read_bytes() != staged_bundle:
            raise ArtifactError(
                f"the archived bundle {archived} differs from this evaluation, and "
                "archived bundles are immutable"
            ) from None
        return
    _fsync_dir(final.parent)


def _bundle_id(run: _Run) -> str:
    """Identity over the evaluation inputs, never over process output."""
    identity = {
        "candidate": {
            "dir": _repo_relative(run.candidate_dir, run.repo_root),
            "id": run.candidate_id,
        },
        "hashes": dict(run.hashes),
        "paths": dict(run.paths),
        "schema_version": BUNDLE_SCHEMA_VERSION,
        "timestamp": run.timestamp,
        "toolchain": run.toolchain,
    }
    digest = sha256_json(identity)[:_ID_DIGEST_LENGTH]
    return f"{run.candidate_id[:_ID_PREFIX_LENGTH]}-{digest}"


# --- processes --------------------------------------------------------------


def _invoke(
    run: _Run,
    name: str,
    argv: tuple[str, ...],
    sandbox: _Sandbox,
    timeout: float,
    *,
    hash_output: bool = True,
) -> _Outcome:
    outcome = _run_process(name, argv, sandbox, timeout)
    run.logs[f"{name}.stdout"] = outcome.stdout
    run.logs[f"{name}.stderr"] = outcome.stderr
    record: dict[str, object] = {
        "argv": list(outcome.argv),
        "exit_code": outcome.exit_code,
        "name": name,
        "sandboxed": True,
        "timed_out": outcome.timed_out,
    }
    if hash_output:
        for stream, data in (("stdout", outcome.stdout), ("stderr", outcome.stderr)):
            digest = _sha256_bytes(data)
            run.outputs[f"{name}.{stream}"] = digest
            record[f"{stream}_sha256"] = digest
    run.commands.append(record)
    return outcome


def _run_process(
    name: str, argv: tuple[str, ...], sandbox: _Sandbox, timeout: float
) -> _Outcome:
    """Spawn one Lean step inside the sandbox and capture what it did.

    The recorded argv stays the inner command, which is machine-independent;
    the sandbox prefix is containment, not identity. The parent environment is
    never forwarded: bubblewrap starts from `--clearenv` plus the pinned
    toolchain variables.
    """
    upper, work = sandbox.allocate_layer()
    spawn = _sandbox_argv(sandbox, argv, upper, work)
    process = subprocess.Popen(
        spawn,
        cwd=str(sandbox.repo_root),
        env={"PATH": os.defpath},
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        _terminate(process)
        stdout, stderr = process.communicate()
        timed_out = True
    sandbox.uppers.append(upper)
    return _Outcome(
        name=name,
        argv=argv,
        exit_code=process.returncode,
        timed_out=timed_out,
        stdout=stdout or b"",
        stderr=stderr or b"",
    )


def _terminate(process: subprocess.Popen[bytes]) -> None:
    """Kill the whole process group, because lake spawns lean as a child."""
    try:
        group = os.getpgid(process.pid)
    except OSError:
        process.kill()
        return
    os.killpg(group, signal.SIGTERM)
    try:
        process.wait(timeout=_TERMINATE_GRACE_SECONDS)
    except subprocess.TimeoutExpired:
        os.killpg(group, signal.SIGKILL)


def _lake_bin_dir() -> Path | None:
    """Directory holding `lake`; elan installs it outside the default PATH."""
    found = shutil.which(_LAKE)
    if found is not None:
        return Path(found).parent
    elan = Path.home() / ".elan" / "bin"
    return elan if os.access(elan / _LAKE, os.X_OK) else None


# --- helpers ----------------------------------------------------------------


def _candidate_directory(candidate_dir: Path | str, repo_root: Path) -> Path:
    path = Path(candidate_dir).resolve()
    if not path.is_dir():
        raise ArtifactError(f"the candidate directory {path} does not exist")
    if path == repo_root or not path.is_relative_to(repo_root):
        raise ArtifactError(f"the candidate directory {path} is not inside {repo_root}")
    return path


def _result(
    run: _Run,
    status: EvaluationStatus,
    summary: str,
    *,
    metrics: Mapping[str, object] | None = None,
    artifacts: Mapping[str, str] | None = None,
) -> EvaluationResult:
    return EvaluationResult(
        schema_version=SCHEMA_VERSION,
        candidate_id=run.candidate_id,
        evidence_id=None,
        status=status,
        summary=summary,
        metrics=dict(metrics or {}),
        artifacts=dict(artifacts or {}),
        timestamp=run.timestamp,
    )


def _status(result: EvaluationResult) -> EvaluationStatus:
    return EvaluationStatus(result.status)


def _toolchain(repo_root: Path) -> str | None:
    path = repo_root / _TOOLCHAIN_FILENAME
    return path.read_text(encoding="utf-8").strip() if path.is_file() else None


def _repo_relative(path: Path, repo_root: Path) -> str:
    inside = path.is_relative_to(repo_root)
    return (path.relative_to(repo_root) if inside else path).as_posix()


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def _write_bytes(path: Path, data: bytes) -> None:
    """Write bytes atomically and flush them to disk."""
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    with temporary.open("wb") as handle:
        handle.write(data)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)
    _fsync_dir(path.parent)


def _fsync_dir(path: Path) -> None:
    handle = os.open(path, os.O_RDONLY)
    try:
        os.fsync(handle)
    finally:
        os.close(handle)
