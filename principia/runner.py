"""Isolated agent execution.

Agents are untrusted code. Every agent runs under bubblewrap in private
namespaces: the repository is bound read-only, exactly one directory is writable
(the agent's workspace, which is also its working directory), the home directory
and `/tmp` are private tmpfs mounts, the environment holds only what the spec
allows, and there is no network unless the spec asks for one. The command is an
argv list; no shell ever sees it.

There is no unsandboxed fallback. If bubblewrap is missing, or the kernel
refuses the namespaces, the run is refused with `SandboxUnavailableError`.

A failing agent is data, not an exception: a nonzero exit status, a fatal signal
and a timeout all come back in the `CommandResult`. The result also carries
SHA-256 hashes of the request and of the captured output, computed over the
canonical bytes of the stored text, so an archived record verifies against
itself.
"""

from __future__ import annotations

import contextlib
import hashlib
import os
import re
import shutil
import signal
import subprocess
import sys
import time
from collections.abc import Iterable, Sequence
from pathlib import Path, PurePosixPath
from typing import NamedTuple

from .artifacts import canonical_json
from .models import AgentSpec, ArtifactError, CommandResult

__all__ = [
    "BWRAP",
    "SANDBOX_HOME",
    "SANDBOX_LOCALE",
    "SANDBOX_PATH",
    "SANDBOX_TMP",
    "SandboxUnavailableError",
    "run_agent",
]

BWRAP = "bwrap"
SANDBOX_HOME = "/sandbox/home"
SANDBOX_TMP = "/tmp"
SANDBOX_PATH = "/usr/local/bin:/usr/local/sbin:/usr/bin:/usr/sbin:/bin:/sbin"
SANDBOX_LOCALE = "C.UTF-8"

# Read-only system directories the sandbox needs to run any program at all.
# Symlinked directories (merged-`/usr` layouts) resolve to their target, so a
# single list covers both layouts.
_SYSTEM_READ_ONLY: tuple[str, ...] = (
    "/usr",
    "/etc",
    "/bin",
    "/sbin",
    "/lib",
    "/lib32",
    "/lib64",
    "/libx32",
)

# Mounts the sandbox owns. A bind, repository or workspace that covered one of
# them would silently cancel an isolation guarantee, so they are refused.
_MANAGED_MOUNTS: tuple[str, ...] = ("/proc", "/dev", SANDBOX_TMP, SANDBOX_HOME)

# Sandbox layout, so the spec cannot point them at the host.
_SANDBOX_ENV: dict[str, str] = {"HOME": SANDBOX_HOME, "TMPDIR": SANDBOX_TMP}
_RESERVED_ENV = frozenset({*_SANDBOX_ENV, "PWD"})
_DEFAULT_ENV: dict[str, str] = {
    "PATH": SANDBOX_PATH,
    "LANG": SANDBOX_LOCALE,
    "LC_ALL": SANDBOX_LOCALE,
}

_ENV_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_TERMINATION_GRACE_SECONDS = 2.0
_DIAGNOSTIC_LIMIT = 500


class SandboxUnavailableError(RuntimeError):
    """The sandbox cannot be built, so no agent may run.

    Infrastructure, not validation: the caller cannot fix it by editing a spec.
    """


class _Completed(NamedTuple):
    """What the sandbox process did."""

    stdout: bytes
    stderr: bytes
    status: int
    timed_out: bool
    duration_seconds: float


def run_agent(
    spec: AgentSpec,
    workspace: Path | str,
    request: object,
    repo_root: Path | str,
    timestamp: str,
) -> CommandResult:
    """Run `spec.command` inside the sandbox and report what it did.

    `request` reaches the agent as canonical JSON on stdin, which is then
    closed. The agent starts in `workspace`, the only writable path it has.

    Raises `SandboxUnavailableError` when the sandbox cannot be built and
    `ArtifactError` when the spec or the paths are unusable. A nonzero exit
    status, a fatal signal and a timeout are reported, never raised.
    """
    bwrap = _require_sandbox()
    repo = _sandbox_directory(repo_root, "repo_root")
    work = _sandbox_directory(workspace, "workspace")
    if work == repo:
        raise ArtifactError(
            f"workspace {work} is the repository root, which stays read-only"
        )
    if work in repo.parents:
        raise ArtifactError(
            f"workspace {work} contains the repository root {repo}, "
            "which stays read-only"
        )
    binds = _read_only_binds(spec.read_only_binds)
    environment = _sandbox_environment(spec.env_allowlist)
    mounts = (*_system_read_only(), *binds, repo, work)
    executable = _resolve_executable(spec.command, environment["PATH"], mounts)
    command = (executable, *spec.command[1:])
    payload = canonical_json(request)
    argv = _sandbox_argv(bwrap, spec.network, command, binds, repo, work, environment)
    completed = _execute(argv, payload, work, float(spec.timeout_seconds))
    stdout = completed.stdout.decode("utf-8", "replace")
    stderr = completed.stderr.decode("utf-8", "replace")
    killed_by = -completed.status if completed.status < 0 else None
    return CommandResult(
        command=command,
        exit_code=completed.status if killed_by is None else None,
        signal=killed_by,
        timed_out=completed.timed_out,
        stdout=stdout,
        stderr=stderr,
        stdout_sha256=_sha256(stdout.encode("utf-8")),
        stderr_sha256=_sha256(stderr.encode("utf-8")),
        request_sha256=_sha256(payload),
        duration_seconds=round(completed.duration_seconds, 6),
        timestamp=timestamp,
    )


def _require_sandbox() -> str:
    """Return the bubblewrap program, or refuse to run anything."""
    if sys.platform != "linux":
        raise SandboxUnavailableError(
            f"agent sandboxing needs Linux; this host is {sys.platform!r}"
        )
    bwrap = shutil.which(BWRAP)
    if bwrap is None:
        raise SandboxUnavailableError(
            f"{BWRAP} (bubblewrap) is not installed; refusing to run an agent unsandboxed"
        )
    return bwrap


def _sandbox_directory(value: Path | str, label: str) -> Path:
    path = Path(value)
    if not path.is_absolute():
        raise ArtifactError(f"{label} must be an absolute path: {str(value)!r}")
    resolved = path.resolve()
    if not resolved.is_dir():
        raise ArtifactError(f"{label} is not an existing directory: {str(value)!r}")
    _reject_managed(resolved, label)
    return resolved


def _read_only_binds(entries: Iterable[str]) -> tuple[Path, ...]:
    """Resolve the extra read-only capabilities the spec asks for.

    Binds are absolute host paths. The repository is already read-only, so a
    bind exists to reach something outside it, such as a toolchain.
    """
    binds: list[Path] = []
    for entry in entries:
        if ".." in PurePosixPath(entry).parts:
            raise ArtifactError(f"read-only bind must not contain '..': {entry!r}")
        path = Path(entry)
        if not path.is_absolute():
            raise ArtifactError(f"read-only bind must be an absolute path: {entry!r}")
        resolved = path.resolve()
        if not resolved.exists():
            raise ArtifactError(f"read-only bind does not exist: {entry!r}")
        _reject_managed(resolved, "read-only bind")
        if resolved not in binds:
            binds.append(resolved)
    return tuple(binds)


def _reject_managed(path: Path, label: str) -> None:
    for mount in _MANAGED_MOUNTS:
        if _contains(path, Path(mount)):
            raise ArtifactError(
                f"{label} {path} would cover the sandbox mount at {mount}"
            )


def _sandbox_environment(allowlist: Iterable[str]) -> dict[str, str]:
    """Build the agent environment: sandbox defaults plus allowed host values."""
    environment = dict(_DEFAULT_ENV)
    for name in allowlist:
        if not _ENV_NAME.fullmatch(name):
            raise ArtifactError(f"not an environment variable name: {name!r}")
        if name in _RESERVED_ENV:
            raise ArtifactError(
                f"the sandbox sets {name}; it cannot be inherited from the host"
            )
        value = os.environ.get(name)
        if value is not None:
            environment[name] = value
    environment.update(_SANDBOX_ENV)
    return environment


def _resolve_executable(
    command: Sequence[str], search_path: str, mounts: Sequence[Path]
) -> str:
    """Find the program on the host before the sandbox exists.

    A bare name resolves against the sandbox `PATH`, not the host one, because
    that is the `PATH` the agent will see. Resolving here turns an unreachable
    program into a clear spec error instead of an opaque exit status, and
    catches a program the sandbox would not be able to see.
    """
    if not command:
        raise ArtifactError("the agent command is empty; there is nothing to run")
    name = command[0]
    if ".." in PurePosixPath(name).parts:
        raise ArtifactError(f"the agent command must not contain '..': {name!r}")
    if "/" in name:
        located = Path(name)
        if not located.is_absolute():
            raise ArtifactError(
                "the agent command must be an absolute path or a bare program name: "
                f"{name!r}"
            )
    else:
        found = shutil.which(name, path=search_path)
        if found is None:
            raise ArtifactError(
                f"the agent command {name!r} is not on the sandbox PATH {search_path}"
            )
        located = Path(found)
    if not (located.is_file() and os.access(located, os.X_OK)):
        raise ArtifactError(f"the agent command is not an executable file: {name!r}")
    # The link and its target both have to be inside a mount, because the
    # sandbox resolves the link itself. argv[0] stays the path the spec named:
    # some programs dispatch on it.
    for path in (located, located.resolve()):
        if not any(_contains(mount, path) for mount in mounts):
            raise ArtifactError(
                f"the agent command {path} is not visible inside the sandbox; "
                "declare a read-only bind that covers it"
            )
    return str(located)


def _sandbox_argv(
    bwrap: str,
    network: bool,
    command: Sequence[str],
    binds: Sequence[Path],
    repo: Path,
    work: Path,
    environment: dict[str, str],
) -> list[str]:
    """Assemble the bubblewrap command line.

    Mount order is load-bearing: bubblewrap applies operations in order and a
    later mount covers an earlier one. The sandbox mounts come before the
    declared binds, the repository and the workspace, so a repository or
    workspace living under `/tmp` stays reachable, and the workspace stays
    writable inside the read-only repository.
    """
    argv = [bwrap, "--unshare-all"]
    if network:
        argv.append("--share-net")
    argv += ["--die-with-parent", "--new-session", "--clearenv"]
    for name in sorted(environment):
        argv += ["--setenv", name, environment[name]]
    for path in _system_read_only():
        argv += ["--ro-bind", str(path), str(path)]
    argv += ["--proc", "/proc", "--dev", "/dev"]
    argv += ["--tmpfs", SANDBOX_TMP, "--tmpfs", SANDBOX_HOME]
    for path in binds:
        argv += ["--ro-bind", str(path), str(path)]
    argv += ["--ro-bind", str(repo), str(repo)]
    argv += ["--bind", str(work), str(work)]
    argv += ["--chdir", str(work), "--", *command]
    return argv


def _system_read_only() -> tuple[Path, ...]:
    return tuple(Path(path) for path in _SYSTEM_READ_ONLY if os.path.isdir(path))


def _execute(argv: Sequence[str], payload: bytes, cwd: Path, timeout: float) -> _Completed:
    """Run the sandbox, feed it the request, and collect everything it produced.

    Bubblewrap reports the sandboxed process on its info descriptor as soon as
    the namespaces exist. Silence there means the sandbox never came up, which
    is an unavailable sandbox rather than a failing agent.
    """
    started = time.monotonic()
    info_read, info_write = os.pipe()
    try:
        try:
            process = subprocess.Popen(
                [argv[0], "--info-fd", str(info_write), *argv[1:]],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                cwd=str(cwd),
                env={},
                pass_fds=(info_write,),
                start_new_session=True,
            )
        finally:
            os.close(info_write)
        timed_out = False
        with process:
            try:
                stdout, stderr = process.communicate(payload, timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                _terminate(process)
                stdout, stderr = process.communicate()
            status = process.wait()
        duration = time.monotonic() - started
        started_sandbox = os.read(info_read, 4096)
    finally:
        os.close(info_read)
    if not started_sandbox and not timed_out:
        raise SandboxUnavailableError(
            "bubblewrap could not create the sandbox, so the agent did not run "
            "(unprivileged user namespaces may be disabled): "
            + _diagnostic(stderr)
        )
    return _Completed(stdout, stderr, status, timed_out, duration)


def _terminate(process: subprocess.Popen[bytes]) -> None:
    """Kill the sandbox and everything inside it.

    The sandbox leads its own process group and its own PID namespace. SIGTERM
    asks bubblewrap to stop; the SIGKILL that always follows reaches the
    namespace's init process, and the kernel then kills every process still
    inside the namespace, however deeply the agent nested them.
    """
    group = process.pid  # start_new_session made the child its group leader
    _signal_group(group, signal.SIGTERM)
    with contextlib.suppress(subprocess.TimeoutExpired):
        process.wait(timeout=_TERMINATION_GRACE_SECONDS)
    _signal_group(group, signal.SIGKILL)


def _signal_group(group: int, number: int) -> None:
    with contextlib.suppress(ProcessLookupError, PermissionError):
        os.killpg(group, number)


def _contains(parent: Path, child: Path) -> bool:
    return child == parent or parent in child.parents


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _diagnostic(stderr: bytes) -> str:
    text = " ".join(stderr.decode("utf-8", "replace").split())
    return text[:_DIAGNOSTIC_LIMIT] if text else "no diagnostic output"
