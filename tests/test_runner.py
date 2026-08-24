"""Behaviour tests for the bubblewrap-backed agent runner.

The tests drive the real sandbox through `run_agent`. They skip only when
bubblewrap is genuinely absent, because a sandbox test that skips itself proves
nothing about isolation.

Each test builds a throwaway repository under `/tmp` on purpose: the sandbox
mounts a private tmpfs on `/tmp`, so a repository living there also proves that
the repository and workspace binds survive that tmpfs.
"""

from __future__ import annotations

import errno
import hashlib
import json
import os
import shutil
import signal
import sys
import tempfile
import textwrap
import time
import unittest
from pathlib import Path

from principia.artifacts import canonical_json
from principia.models import AgentSpec, ArtifactError, CommandResult
from principia.runner import (
    SANDBOX_HOME,
    SANDBOX_PATH,
    SANDBOX_TMP,
    SandboxUnavailableError,
    run_agent,
)

_LINUX = sys.platform == "linux"
_HAS_BWRAP = _LINUX and shutil.which("bwrap") is not None
_TRUE = shutil.which("true", path=SANDBOX_PATH)
_TIMESTAMP = "2026-08-23T12:00:00.000000Z"
_INTERPRETER = str(Path(sys.executable))

# The descendant in the timeout test writes its second marker three seconds
# after it starts. Waiting longer than that proves the marker never arrives.
_DESCENDANT_WINDOW = 4.0

requires_linux = unittest.skipUnless(_LINUX, "the sandbox is Linux only")
requires_sandbox = unittest.skipUnless(_HAS_BWRAP, "bubblewrap (bwrap) is not installed")

# One agent for most tests: it reports what it sees and performs the file
# operations the request asks for, so the variation lives in data.
_PROBE = textwrap.dedent(
    """
    import json, os, sys
    from pathlib import Path

    request = json.load(sys.stdin)
    report = {
        "request": request,
        "cwd": os.getcwd(),
        "environ": dict(os.environ),
        "interfaces": sorted(
            line.split(":", 1)[0].strip()
            for line in Path("/proc/net/dev").read_text().splitlines()
            if ":" in line
        ),
    }
    if "echo_to" in request:
        Path(request["echo_to"]).write_text(json.dumps(request, sort_keys=True))
    writes = {}
    for label, target in request.get("write", {}).items():
        try:
            Path(target).write_text("written")
            writes[label] = "ok"
        except OSError as error:
            writes[label] = error.errno
    report["writes"] = writes
    reads = {}
    for label, target in request.get("read", {}).items():
        try:
            reads[label] = Path(target).read_text()
        except OSError as error:
            reads[label] = error.errno
    report["reads"] = reads
    report["exists"] = {
        label: os.path.exists(target)
        for label, target in request.get("exists", {}).items()
    }
    if request.get("stderr"):
        print(request["stderr"], file=sys.stderr)
    print(json.dumps(report, sort_keys=True))
    sys.exit(request.get("exit_code", 0))
    """
)

# An agent that leaves a descendant behind and then hangs.
_SPAWNER = textwrap.dedent(
    """
    import subprocess, sys, time
    from pathlib import Path

    descendant = (
        "import time; from pathlib import Path; "
        "Path('spawned.txt').write_text('here'); "
        "time.sleep(3); "
        "Path('late.txt').write_text('survived')"
    )
    subprocess.Popen([sys.executable, "-I", "-c", descendant])
    time.sleep(60)
    """
)


def _interpreter_binds() -> tuple[str, ...]:
    """Grant the sandbox this interpreter when it lives outside the system tree."""
    prefixes = {Path(sys.prefix).resolve(), Path(sys.base_prefix).resolve()}
    return tuple(
        str(prefix)
        for prefix in sorted(prefixes)
        if prefix != Path("/") and not str(prefix).startswith("/usr")
    )


def _spec(
    command: list[str],
    *,
    network: bool = False,
    timeout: float = 30.0,
    env: list[str] | tuple[str, ...] = (),
    binds: list[str] | tuple[str, ...] = (),
) -> AgentSpec:
    """Build an agent spec from its JSON shape, the way a caller does."""
    return AgentSpec.from_dict(
        {
            "command": list(command),
            "network": network,
            "timeout_seconds": timeout,
            "env_allowlist": list(env),
            "read_only_binds": list(binds),
        }
    )


def _probe(
    *,
    network: bool = False,
    timeout: float = 30.0,
    env: list[str] | tuple[str, ...] = (),
    binds: list[str] | tuple[str, ...] = (),
) -> AgentSpec:
    return _spec(
        [_INTERPRETER, "-I", "-c", _PROBE],
        network=network,
        timeout=timeout,
        env=env,
        binds=(*_interpreter_binds(), *binds),
    )


def _host_interfaces() -> set[str]:
    return {
        line.split(":", 1)[0].strip()
        for line in Path("/proc/net/dev").read_text(encoding="utf-8").splitlines()
        if ":" in line
    }


def _restore_env(name: str, previous: str | None) -> None:
    if previous is None:
        os.environ.pop(name, None)
    else:
        os.environ[name] = previous


class RunAgentTests(unittest.TestCase):
    def setUp(self) -> None:
        root = Path(
            self.enterContext(
                tempfile.TemporaryDirectory(prefix="principia-runner-", dir=SANDBOX_TMP)
            )
        ).resolve()
        self.root = root
        self.repo = root / "repo"
        self.workspace = self.repo / ".principia/workspace"
        self.workspace.mkdir(parents=True)
        (self.repo / "README.md").write_text("repo content", encoding="utf-8")

    # --- helpers ------------------------------------------------------------

    def run_probe(self, request: object, **spec_options) -> CommandResult:
        spec = _probe(**spec_options)
        return run_agent(spec, self.workspace, request, self.repo, _TIMESTAMP)

    def report(self, result: CommandResult) -> dict:
        self.assertEqual(result.exit_code, 0, msg=result.stderr)
        self.assertFalse(result.timed_out)
        return json.loads(result.stdout)

    def host_env(self, name: str, value: str) -> None:
        self.addCleanup(_restore_env, name, os.environ.get(name))
        os.environ[name] = value

    # --- what the agent can do ----------------------------------------------

    @requires_sandbox
    def test_the_agent_reads_its_request_and_writes_its_workspace(self) -> None:
        request = {"echo_to": "answer.json", "note": "ünïcode", "count": 2}
        result = self.run_probe(request)

        report = self.report(result)
        self.assertIsNone(result.signal)
        self.assertEqual(result.timestamp, _TIMESTAMP)
        self.assertEqual(tuple(result.command), (_INTERPRETER, "-I", "-c", _PROBE))
        self.assertGreaterEqual(result.duration_seconds, 0.0)
        self.assertEqual(report["request"], request)
        self.assertEqual(report["cwd"], str(self.workspace))
        written = (self.workspace / "answer.json").read_text(encoding="utf-8")
        self.assertEqual(json.loads(written), request)
        self.assertEqual(
            result.request_sha256, hashlib.sha256(canonical_json(request)).hexdigest()
        )

    @requires_sandbox
    @unittest.skipUnless(_TRUE, "no 'true' program on the sandbox PATH")
    def test_a_bare_program_name_resolves_before_the_sandbox_starts(self) -> None:
        result = run_agent(_spec(["true"]), self.workspace, {}, self.repo, _TIMESTAMP)

        self.assertEqual(tuple(result.command), (_TRUE,))
        self.assertEqual(result.exit_code, 0)
        self.assertEqual(result.stdout, "")
        self.assertEqual(result.stdout_sha256, hashlib.sha256(b"").hexdigest())

    @requires_sandbox
    def test_a_failing_agent_is_reported_and_not_raised(self) -> None:
        result = self.run_probe({"exit_code": 3, "stderr": "boom"})

        self.assertEqual(result.exit_code, 3)
        self.assertIsNone(result.signal)
        self.assertFalse(result.timed_out)
        self.assertEqual(result.stderr.strip(), "boom")

    # --- what the agent cannot do -------------------------------------------

    @requires_sandbox
    def test_the_repository_is_read_only_outside_the_workspace(self) -> None:
        blocked = self.repo / "blocked.txt"
        report = self.report(
            self.run_probe(
                {
                    "write": {"repo": str(blocked), "workspace": "allowed.txt"},
                    "read": {"repo": str(self.repo / "README.md")},
                }
            )
        )

        self.assertEqual(report["writes"]["repo"], errno.EROFS)
        self.assertEqual(report["writes"]["workspace"], "ok")
        self.assertEqual(report["reads"]["repo"], "repo content")
        self.assertFalse(blocked.exists())
        self.assertEqual(
            (self.workspace / "allowed.txt").read_text(encoding="utf-8"), "written"
        )

    @requires_sandbox
    def test_the_home_directory_and_tmp_are_private(self) -> None:
        marker = f"principia-{os.getpid()}"
        host = Path(SANDBOX_TMP) / f"host-{marker}"
        host.write_text("host", encoding="utf-8")
        self.addCleanup(lambda: host.unlink(missing_ok=True))
        escaped_tmp = Path(SANDBOX_TMP) / f"escaped-{marker}"
        escaped_home = Path(SANDBOX_HOME) / f"escaped-{marker}"

        report = self.report(
            self.run_probe(
                {
                    "write": {"tmp": str(escaped_tmp), "home": str(escaped_home)},
                    "exists": {"host_tmp": str(host)},
                }
            )
        )

        self.assertEqual(report["writes"]["tmp"], "ok")
        self.assertEqual(report["writes"]["home"], "ok")
        self.assertEqual(report["environ"]["HOME"], SANDBOX_HOME)
        self.assertEqual(report["environ"]["TMPDIR"], SANDBOX_TMP)
        self.assertFalse(report["exists"]["host_tmp"], "the host /tmp was visible")
        self.assertFalse(escaped_tmp.exists(), "the agent wrote to the host /tmp")
        self.assertFalse(escaped_home.exists(), "the agent wrote to a host home")
        self.assertEqual(host.read_text(encoding="utf-8"), "host")

    @requires_sandbox
    def test_the_environment_holds_only_what_the_spec_allows(self) -> None:
        self.host_env("PRINCIPIA_TEST_VISIBLE", "visible-value")
        self.host_env("PRINCIPIA_TEST_HIDDEN", "hidden-value")

        result = self.run_probe({}, env=["PRINCIPIA_TEST_VISIBLE"])
        environ = self.report(result)["environ"]

        self.assertEqual(environ["PRINCIPIA_TEST_VISIBLE"], "visible-value")
        self.assertNotIn("PRINCIPIA_TEST_HIDDEN", environ)
        self.assertNotIn("hidden-value", result.stdout)
        self.assertNotEqual(environ["HOME"], os.environ.get("HOME"))
        # Nothing else from the host reaches the agent. PWD comes from the
        # sandbox chdir and LC_CTYPE from the interpreter's own locale handling.
        expected = {
            "PRINCIPIA_TEST_VISIBLE",
            "HOME",
            "TMPDIR",
            "PATH",
            "LANG",
            "LC_ALL",
            "LC_CTYPE",
            "PWD",
        }
        self.assertEqual(sorted(set(environ) - expected), [])

    @requires_sandbox
    def test_the_network_is_unshared_by_default(self) -> None:
        report = self.report(self.run_probe({}))

        self.assertEqual(report["interfaces"], ["lo"])

    @requires_sandbox
    def test_the_network_is_shared_only_when_the_spec_declares_it(self) -> None:
        report = self.report(self.run_probe({}, network=True))

        self.assertEqual(set(report["interfaces"]), _host_interfaces())

    @requires_sandbox
    def test_a_timeout_kills_the_whole_process_tree(self) -> None:
        spec = _spec(
            [_INTERPRETER, "-I", "-c", _SPAWNER],
            timeout=1.5,
            binds=_interpreter_binds(),
        )

        result = run_agent(spec, self.workspace, {}, self.repo, _TIMESTAMP)

        self.assertTrue(result.timed_out)
        self.assertIsNone(result.exit_code)
        self.assertIn(result.signal, {int(signal.SIGTERM), int(signal.SIGKILL)})
        self.assertTrue(
            (self.workspace / "spawned.txt").exists(),
            "the agent never spawned its descendant, so nothing was proven",
        )
        time.sleep(_DESCENDANT_WINDOW)
        self.assertFalse(
            (self.workspace / "late.txt").exists(), "a descendant outlived the sandbox"
        )

    # --- refusals -----------------------------------------------------------

    @requires_sandbox
    def test_an_unusable_read_only_bind_is_refused(self) -> None:
        cases = {
            "relative": "etc",
            "traversal": f"{self.root}/../etc",
            "missing": str(self.root / "nowhere"),
            "covers /tmp": SANDBOX_TMP,
            "covers /proc": "/proc",
            "covers the filesystem root": "/",
        }
        for label, entry in cases.items():
            with self.subTest(bind=label), self.assertRaises(ArtifactError):
                self.run_probe({}, binds=[entry])

    @requires_sandbox
    def test_a_sandbox_controlled_environment_name_is_refused(self) -> None:
        for name in ("HOME", "TMPDIR", "PWD", "not-a-name", ""):
            with self.subTest(name=name), self.assertRaises(ArtifactError):
                self.run_probe({}, env=[name])

    @requires_sandbox
    def test_an_unreachable_command_is_refused(self) -> None:
        outside = self.root / "outside"
        outside.mkdir()
        tool = outside / "tool"
        tool.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        tool.chmod(0o755)
        cases = {
            "not on the sandbox PATH": "principia-no-such-program",
            "relative": "./tool",
            "traversal": "../tool",
            "outside every mount": str(tool),
            "not executable": str(self.repo / "README.md"),
            "empty": "",
        }
        for label, program in cases.items():
            with self.subTest(command=label), self.assertRaises(ArtifactError):
                run_agent(_spec([program]), self.workspace, {}, self.repo, _TIMESTAMP)
        with self.subTest(command="no command at all"), self.assertRaises(ArtifactError):
            run_agent(_spec([]), self.workspace, {}, self.repo, _TIMESTAMP)

    @requires_sandbox
    def test_an_unusable_workspace_is_refused(self) -> None:
        cases = {
            "missing": self.root / "nowhere",
            "a file": self.repo / "README.md",
            "relative": Path("workspace"),
            "the repository root": self.repo,
            "above the repository root": self.root,
            "covers /tmp": Path(SANDBOX_TMP),
        }
        for label, workspace in cases.items():
            with self.subTest(workspace=label), self.assertRaises(ArtifactError):
                run_agent(_probe(), workspace, {}, self.repo, _TIMESTAMP)

    @requires_sandbox
    def test_an_unusable_repository_root_is_refused(self) -> None:
        cases = {
            "missing": self.root / "nowhere",
            "a file": self.repo / "README.md",
            "relative": Path("repo"),
            "covers /tmp": Path(SANDBOX_TMP),
            "the filesystem root": Path("/"),
        }
        for label, repo in cases.items():
            with self.subTest(repo_root=label), self.assertRaises(ArtifactError):
                run_agent(_probe(), self.workspace, {}, repo, _TIMESTAMP)

    @requires_linux
    def test_a_missing_bwrap_refuses_to_run(self) -> None:
        empty = self.root / "empty-path"
        empty.mkdir()
        self.host_env("PATH", str(empty))

        with self.assertRaises(SandboxUnavailableError):
            run_agent(_probe(), self.workspace, {}, self.repo, _TIMESTAMP)

    @requires_linux
    def test_a_sandbox_that_never_starts_refuses_to_run(self) -> None:
        fake = self.root / "fake-bin"
        fake.mkdir()
        bwrap = fake / "bwrap"
        bwrap.write_text(
            "#!/bin/sh\necho 'bwrap: No permissions to create new namespace' >&2\nexit 1\n",
            encoding="utf-8",
        )
        bwrap.chmod(0o755)
        self.host_env("PATH", str(fake))

        with self.assertRaises(SandboxUnavailableError) as raised:
            run_agent(_probe(), self.workspace, {}, self.repo, _TIMESTAMP)

        self.assertIn("No permissions", str(raised.exception))

    # --- reproducibility ----------------------------------------------------

    @requires_sandbox
    def test_output_hashes_are_stable_and_cover_the_captured_text(self) -> None:
        request = {"echo_to": "answer.json", "stderr": "diagnostic line"}

        first = self.run_probe(request)
        second = self.run_probe(request)

        self.report(first)
        self.report(second)
        self.assertEqual(first.stdout, second.stdout)
        self.assertEqual(first.stdout_sha256, second.stdout_sha256)
        self.assertEqual(first.stderr_sha256, second.stderr_sha256)
        self.assertEqual(first.request_sha256, second.request_sha256)
        self.assertEqual(
            first.stdout_sha256, hashlib.sha256(first.stdout.encode("utf-8")).hexdigest()
        )
        self.assertEqual(
            first.stderr_sha256, hashlib.sha256(first.stderr.encode("utf-8")).hexdigest()
        )


if __name__ == "__main__":
    unittest.main()
