"""Canonical JSON, content digests, atomic writes and repo path containment.

One byte sequence per value: UTF-8, sorted keys, no insignificant whitespace. Digests
are taken over those bytes, so a hash is reproducible from the value alone and cannot
drift with dict ordering. A file holds exactly the canonical bytes and nothing else,
so the digest of the file is the digest of the value.

Every write is atomic. A reader either sees the previous bytes or the new bytes, never
a truncated file, and the rename is durable before the call returns.
"""

from __future__ import annotations

import hashlib
import hmac
import json
import os
import tempfile
from collections.abc import Mapping
from pathlib import Path, PurePath

from .models import ArtifactError, validate_sha256_hex

__all__ = [
    "canonical_json",
    "sha256_json",
    "load_json",
    "write_json_atomic",
    "verify_file_sha256",
    "resolve_repo_path",
]

StrPath = str | os.PathLike[str]

_DEFAULT_MODE = 0o644


def _unsupported(value: object) -> object:
    if isinstance(value, Mapping):
        return dict(value)
    raise TypeError(f"{type(value).__name__} is not JSON data")


def canonical_json(value: object) -> bytes:
    """Return the one canonical UTF-8 encoding of *value*, without a trailing newline."""
    try:
        text = json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
            default=_unsupported,
        )
    except (TypeError, ValueError) as error:
        raise ArtifactError(f"value cannot be encoded as canonical JSON: {error}") from error
    return text.encode("utf-8")


def sha256_json(value: object) -> str:
    """Return the SHA-256 of the canonical encoding of *value*."""
    return hashlib.sha256(canonical_json(value)).hexdigest()


def load_json(path: StrPath) -> object:
    """Read one JSON document.

    Duplicate object keys, non-finite numbers and malformed syntax are corruption, not
    data, and raise ``ArtifactError``. A missing or unreadable file raises ``OSError``,
    which callers map to an infrastructure failure.
    """
    raw = Path(path).read_bytes()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ArtifactError(f"{path}: expected UTF-8 encoded JSON: {error}") from error
    try:
        return json.loads(text, object_pairs_hook=_object, parse_constant=_reject_constant)
    except ArtifactError as error:
        raise ArtifactError(f"{path}: {error}") from error
    except json.JSONDecodeError as error:
        raise ArtifactError(f"{path}: invalid JSON: {error}") from error


def _object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    document: dict[str, object] = {}
    for key, value in pairs:
        if key in document:
            raise ArtifactError(f"duplicate object key {key!r}")
        document[key] = value
    return document


def _reject_constant(name: str) -> object:
    raise ArtifactError(f"{name} is not JSON data")


def write_json_atomic(path: StrPath, value: object) -> str:
    """Write *value* as exactly its canonical bytes. Return their SHA-256.

    The file holds no trailing newline, so the returned digest is both
    :func:`sha256_json` of the value and the digest of the bytes on disk:
    ``verify_file_sha256(path, write_json_atomic(path, value))`` always holds.
    """
    target = Path(path)
    payload = canonical_json(value)
    target.parent.mkdir(parents=True, exist_ok=True)
    handle, temporary = tempfile.mkstemp(dir=target.parent, prefix=f".{target.name}.", suffix=".tmp")
    try:
        with os.fdopen(handle, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.chmod(temporary, _mode(target))
        os.replace(temporary, target)
    except BaseException:
        Path(temporary).unlink(missing_ok=True)
        raise
    _fsync_directory(target.parent)
    return hashlib.sha256(payload).hexdigest()


def _mode(target: Path) -> int:
    try:
        return target.stat().st_mode & 0o777
    except FileNotFoundError:
        return _DEFAULT_MODE


def _fsync_directory(directory: Path) -> None:
    handle = os.open(directory, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(handle)
    finally:
        os.close(handle)


def verify_file_sha256(path: StrPath, expected: str) -> None:
    """Raise ``ArtifactError`` unless the bytes at *path* hash to *expected*."""
    wanted = validate_sha256_hex(expected, "expected")
    with open(path, "rb") as stream:
        actual = hashlib.file_digest(stream, "sha256").hexdigest()
    if not hmac.compare_digest(actual, wanted):
        raise ArtifactError(f"{path}: expected sha256 {wanted}, found {actual}")


def resolve_repo_path(root: StrPath, relative: StrPath, must_exist: bool = False) -> Path:
    """Resolve a repo-relative path and prove it stays under *root*.

    *root* is any existing directory used as the containment boundary. Absolute paths,
    ``..`` segments and symlinks pointing outside *root* raise ``ArtifactError``. A
    symlink resolving inside *root* is fine, and the resolved real path is returned so
    callers can judge where it actually landed.
    """
    base = Path(os.path.realpath(root))
    if not base.is_dir():
        raise ArtifactError(f"containment root is not an existing directory: {root}")
    resolved = Path(os.path.realpath(base / _relative_text(relative)))
    if not resolved.is_relative_to(base):
        raise ArtifactError(f"{_show(relative)} escapes {base}: it resolves to {resolved}")
    if must_exist and not resolved.exists():
        raise ArtifactError(f"{_show(relative)} does not exist under {base}: {resolved}")
    return resolved


def _relative_text(relative: StrPath) -> str:
    if isinstance(relative, PurePath):
        text = relative.as_posix()
    elif isinstance(relative, str):
        text = relative
    else:
        raise ArtifactError(f"expected a repo-relative path string, got {type(relative).__name__}")
    if not text or "\x00" in text:
        raise ArtifactError(f"expected a non-empty repo-relative path, got {text!r}")
    if text.startswith("/"):
        raise ArtifactError(f"expected a repo-relative path, got absolute path {text!r}")
    if ".." in text.split("/"):
        raise ArtifactError(f"repo-relative path must not contain '..': {text!r}")
    return text


def _show(relative: StrPath) -> str:
    return repr(relative.as_posix() if isinstance(relative, PurePath) else relative)
