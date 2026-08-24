"""Behaviour tests for `principia.artifacts`.

These four functions are the durability and provenance floor of the pipeline, so the
tests use a real filesystem rather than mocks: real symlinks for containment, real
bytes for digests, real interruptions for atomicity. The properties asserted are the
ones the rest of the system relies on. One value has one encoding whatever the dict
order. A digest identifies content, not layout. A write either lands whole or leaves
the previous bytes untouched. A corrupted file is detected, not consumed.
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from principia.artifacts import (
    canonical_json,
    load_json,
    resolve_repo_path,
    sha256_json,
    verify_file_sha256,
    write_json_atomic,
)
from principia.models import ArtifactError, EvidenceGate

_DOCUMENT = {"b": 1, "a": [2, {"d": 4, "c": 3}], "\u00e9": "caf\u00e9"}
_SHUFFLED = {"\u00e9": "caf\u00e9", "a": [2, {"c": 3, "d": 4}], "b": 1}
_CANONICAL = b'{"a":[2,{"c":3,"d":4}],"b":1,"\xc3\xa9":"caf\xc3\xa9"}'


class ArtifactCase(unittest.TestCase):
    """A throwaway repository with a directory outside it to escape to."""

    def setUp(self) -> None:
        base = Path(tempfile.mkdtemp(prefix="principia-artifacts-")).resolve()
        self.addCleanup(shutil.rmtree, base, ignore_errors=True)
        self.repo = base / "repo"
        self.outside = base / "outside"
        (self.repo / "evidence/data").mkdir(parents=True)
        self.outside.mkdir()

    def write(self, relative: str, content: bytes) -> Path:
        path = self.repo / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        return path

    def names(self, directory: Path) -> list[str]:
        return sorted(entry.name for entry in directory.iterdir())


class CanonicalJsonTest(ArtifactCase):
    def test_key_order_does_not_change_the_bytes(self) -> None:
        self.assertEqual(_CANONICAL, canonical_json(_DOCUMENT))
        self.assertEqual(canonical_json(_DOCUMENT), canonical_json(_SHUFFLED))
        self.assertEqual(sha256_json(_DOCUMENT), sha256_json(_SHUFFLED))

    def test_the_encoding_is_compact_utf8_without_a_trailing_newline(self) -> None:
        encoded = canonical_json(_DOCUMENT)

        self.assertNotIn(b" ", encoded)
        self.assertFalse(encoded.endswith(b"\n"))
        self.assertEqual("caf\u00e9", json.loads(encoded.decode("utf-8"))["\u00e9"])

    def test_the_digest_is_taken_over_the_canonical_bytes(self) -> None:
        self.assertEqual(hashlib.sha256(_CANONICAL).hexdigest(), sha256_json(_DOCUMENT))

    def test_frozen_model_payloads_encode_directly(self) -> None:
        gate = EvidenceGate.from_dict(
            {
                "evaluator": "principia.evaluators.bell_ch",
                "required_claims": ["chsh.violation"],
                "inputs": {"b": 1, "a": {"d": [1, 2]}},
                "decision": {},
            }
        )

        self.assertEqual(b'{"a":{"d":[1,2]},"b":1}', canonical_json(gate.inputs))
        self.assertEqual(b"{}", canonical_json(gate.decision))

    def test_data_that_is_not_json_is_refused(self) -> None:
        for value in (float("nan"), float("inf"), {"a": float("-inf")}, {1, 2}, object()):
            with self.subTest(value=value):
                with self.assertRaises(ArtifactError) as caught:
                    canonical_json(value)
                self.assertIn("canonical JSON", str(caught.exception))


class LoadJsonTest(ArtifactCase):
    def test_a_written_document_reads_back_equal(self) -> None:
        path = self.repo / "out/record.json"
        write_json_atomic(path, _DOCUMENT)

        loaded = load_json(path)

        self.assertEqual(_DOCUMENT, loaded)
        self.assertIsInstance(loaded, dict)

    def test_arrays_and_scalars_are_valid_documents(self) -> None:
        self.assertEqual([1, 2], load_json(self.write("a.json", b"[1, 2]\n")))
        self.assertEqual(7, load_json(self.write("b.json", b"7")))

    def test_duplicate_keys_are_corruption(self) -> None:
        path = self.write("dup.json", b'{"id": "a", "id": "b"}')

        with self.assertRaises(ArtifactError) as caught:
            load_json(path)

        self.assertIn("duplicate object key 'id'", str(caught.exception))
        self.assertIn(str(path), str(caught.exception))

    def test_non_finite_numbers_are_not_json(self) -> None:
        for literal in (b'{"x": NaN}', b'{"x": Infinity}', b'{"x": -Infinity}'):
            with self.subTest(literal=literal):
                with self.assertRaises(ArtifactError) as caught:
                    load_json(self.write("nan.json", literal))
                self.assertIn("not JSON data", str(caught.exception))

    def test_malformed_syntax_names_the_file(self) -> None:
        path = self.write("broken.json", b'{"id": ')

        with self.assertRaises(ArtifactError) as caught:
            load_json(path)

        self.assertIn(str(path), str(caught.exception))
        self.assertIn("invalid JSON", str(caught.exception))

    def test_non_utf8_bytes_are_rejected(self) -> None:
        path = self.write("latin.json", b'{"id": "\xe9"}')

        with self.assertRaises(ArtifactError) as caught:
            load_json(path)

        self.assertIn("UTF-8", str(caught.exception))

    def test_a_missing_file_is_an_infrastructure_error(self) -> None:
        with self.assertRaises(FileNotFoundError):
            load_json(self.repo / "absent.json")


class WriteJsonAtomicTest(ArtifactCase):
    def test_the_file_holds_exactly_the_canonical_bytes(self) -> None:
        path = self.repo / "out/record.json"

        digest = write_json_atomic(path, _DOCUMENT)

        self.assertEqual(sha256_json(_DOCUMENT), digest)
        self.assertEqual(hashlib.sha256(_CANONICAL).hexdigest(), digest)
        self.assertEqual(_CANONICAL, path.read_bytes())
        self.assertEqual(sha256_json(load_json(path)), digest)

    def test_the_returned_digest_verifies_the_file_it_wrote(self) -> None:
        path = self.repo / "out/record.json"

        verify_file_sha256(path, write_json_atomic(path, _DOCUMENT))

    def test_key_order_does_not_change_the_file(self) -> None:
        first = self.repo / "a.json"
        second = self.repo / "b.json"

        self.assertEqual(write_json_atomic(first, _DOCUMENT), write_json_atomic(second, _SHUFFLED))
        self.assertEqual(first.read_bytes(), second.read_bytes())

    def test_missing_parent_directories_are_created(self) -> None:
        path = self.repo / "bundles/2026/08/result.json"

        write_json_atomic(path, {"ok": True})

        self.assertEqual(b'{"ok":true}', path.read_bytes())

    def test_no_temporary_file_survives_a_write(self) -> None:
        path = self.repo / "out/record.json"

        write_json_atomic(path, _DOCUMENT)
        write_json_atomic(path, {"second": True})

        self.assertEqual(["record.json"], self.names(path.parent))
        self.assertEqual(b'{"second":true}', path.read_bytes())

    def test_the_destination_is_never_written_through(self) -> None:
        path = self.write("out/record.json", b"OLD\n")
        seen: list[bytes] = []
        real_replace = os.replace

        def watched(source: object, destination: object) -> None:
            seen.append(Path(str(destination)).read_bytes())
            real_replace(source, destination)

        with mock.patch("os.replace", watched):
            write_json_atomic(path, _DOCUMENT)

        self.assertEqual([b"OLD\n"], seen)
        self.assertEqual(_CANONICAL, path.read_bytes())

    def test_a_failed_rename_leaves_the_previous_bytes(self) -> None:
        path = self.write("out/record.json", b"OLD\n")

        with mock.patch("os.replace", side_effect=OSError("no space left on device")):
            with self.assertRaises(OSError):
                write_json_atomic(path, _DOCUMENT)

        self.assertEqual(b"OLD\n", path.read_bytes())
        self.assertEqual(["record.json"], self.names(path.parent))

    def test_a_failed_flush_leaves_the_previous_bytes(self) -> None:
        path = self.write("out/record.json", b"OLD\n")

        with mock.patch("os.fsync", side_effect=OSError("io error")):
            with self.assertRaises(OSError):
                write_json_atomic(path, _DOCUMENT)

        self.assertEqual(b"OLD\n", path.read_bytes())
        self.assertEqual(["record.json"], self.names(path.parent))

    def test_an_unencodable_value_touches_nothing(self) -> None:
        path = self.repo / "fresh/record.json"

        with self.assertRaises(ArtifactError):
            write_json_atomic(path, {"x": float("nan")})

        self.assertFalse(path.parent.exists())

    def test_an_existing_file_keeps_its_permissions(self) -> None:
        path = self.write("out/record.json", b"OLD\n")
        path.chmod(0o600)

        write_json_atomic(path, _DOCUMENT)

        self.assertEqual(0o600, path.stat().st_mode & 0o777)

    def test_a_new_file_is_readable(self) -> None:
        path = self.repo / "out/record.json"

        write_json_atomic(path, _DOCUMENT)

        self.assertEqual(0o644, path.stat().st_mode & 0o777)


class VerifyFileSha256Test(ArtifactCase):
    def test_matching_content_passes(self) -> None:
        content = b'{"minus":[10,20]}\n'
        path = self.write("evidence/data/chsh.json", content)

        self.assertIsNone(verify_file_sha256(path, hashlib.sha256(content).hexdigest()))

    def test_an_empty_file_is_verifiable(self) -> None:
        path = self.write("evidence/data/empty.json", b"")

        verify_file_sha256(path, hashlib.sha256(b"").hexdigest())

    def test_one_flipped_byte_is_detected(self) -> None:
        original = b'{"minus":[10,20]}\n'
        path = self.write("evidence/data/chsh.json", original.replace(b"10", b"11"))
        expected = hashlib.sha256(original).hexdigest()

        with self.assertRaises(ArtifactError) as caught:
            verify_file_sha256(path, expected)

        message = str(caught.exception)
        self.assertIn(str(path), message)
        self.assertIn(expected, message)
        self.assertIn(hashlib.sha256(path.read_bytes()).hexdigest(), message)

    def test_a_truncated_file_is_detected(self) -> None:
        original = b'{"minus":[10,20]}\n'
        path = self.write("evidence/data/chsh.json", original[:-1])

        with self.assertRaises(ArtifactError):
            verify_file_sha256(path, hashlib.sha256(original).hexdigest())

    def test_a_malformed_expectation_is_rejected_before_reading(self) -> None:
        path = self.write("evidence/data/chsh.json", b"{}")

        for expected in ("", "abc", hashlib.sha256(b"{}").hexdigest().upper()):
            with self.subTest(expected=expected):
                with self.assertRaises(ArtifactError) as caught:
                    verify_file_sha256(path, expected)
                self.assertIn("64 lowercase hexadecimal", str(caught.exception))

    def test_a_missing_file_is_an_infrastructure_error(self) -> None:
        with self.assertRaises(FileNotFoundError):
            verify_file_sha256(self.repo / "absent.json", hashlib.sha256(b"").hexdigest())


class ResolveRepoPathTest(ArtifactCase):
    def test_a_contained_path_resolves_to_its_real_location(self) -> None:
        data = self.write("evidence/data/chsh.json", b"{}")

        self.assertEqual(data, resolve_repo_path(self.repo, "evidence/data/chsh.json", must_exist=True))
        self.assertEqual(data, resolve_repo_path(self.repo, Path("evidence/data/chsh.json")))
        self.assertEqual(data, resolve_repo_path(self.repo, "./evidence/data/chsh.json"))

    def test_any_directory_can_be_the_containment_root(self) -> None:
        source = self.write("CandidateLab/Demo/Theory.lean", b"-- lean\n")

        self.assertEqual(source, resolve_repo_path(self.repo / "CandidateLab", "Demo/Theory.lean", must_exist=True))

    def test_existence_is_only_required_when_asked(self) -> None:
        absent = resolve_repo_path(self.repo, "evidence/data/absent.json")

        self.assertEqual(self.repo / "evidence/data/absent.json", absent)
        with self.assertRaises(ArtifactError) as caught:
            resolve_repo_path(self.repo, "evidence/data/absent.json", must_exist=True)
        self.assertIn("does not exist", str(caught.exception))

    def test_parent_traversal_is_refused_even_when_it_stays_inside(self) -> None:
        self.write("evidence/data/chsh.json", b"{}")

        with self.assertRaises(ArtifactError) as caught:
            resolve_repo_path(self.repo, "evidence/../evidence/data/chsh.json", must_exist=True)

        self.assertIn("'..'", str(caught.exception))

    def test_absolute_paths_are_refused(self) -> None:
        with self.assertRaises(ArtifactError) as caught:
            resolve_repo_path(self.repo, "/etc/hostname")

        self.assertIn("absolute", str(caught.exception))

    def test_a_symlink_resolving_inside_is_accepted_and_followed(self) -> None:
        target = self.write("Atlas/Specs/Frozen.lean", b"-- frozen\n")
        link = self.repo / "CandidateLab/Demo/Theory.lean"
        link.parent.mkdir(parents=True)
        link.symlink_to(target)

        resolved = resolve_repo_path(self.repo, "CandidateLab/Demo/Theory.lean", must_exist=True)

        self.assertEqual(target, resolved)

    def test_a_symlink_escaping_the_root_is_refused(self) -> None:
        target = self.outside / "chsh.json"
        target.write_bytes(b"{}")
        link = self.repo / "evidence/data/chsh.json"
        link.symlink_to(target)

        with self.assertRaises(ArtifactError) as caught:
            resolve_repo_path(self.repo, "evidence/data/chsh.json", must_exist=True)

        self.assertIn("escapes", str(caught.exception))
        self.assertIn("evidence/data/chsh.json", str(caught.exception))

    def test_a_symlinked_parent_directory_cannot_smuggle_a_path_out(self) -> None:
        (self.outside / "data").mkdir()
        (self.outside / "data/chsh.json").write_bytes(b"{}")
        (self.repo / "evidence/link").symlink_to(self.outside / "data")

        with self.assertRaises(ArtifactError) as caught:
            resolve_repo_path(self.repo, "evidence/link/chsh.json", must_exist=True)

        self.assertIn("escapes", str(caught.exception))

    def test_an_unusable_relative_path_is_refused(self) -> None:
        for relative in ("", "a\x00b", 7, None):
            with self.subTest(relative=relative):
                with self.assertRaises(ArtifactError):
                    resolve_repo_path(self.repo, relative)

    def test_a_root_that_is_not_a_directory_is_refused(self) -> None:
        file_root = self.write("evidence/data/chsh.json", b"{}")

        for root in (file_root, self.repo / "absent"):
            with self.subTest(root=root):
                with self.assertRaises(ArtifactError) as caught:
                    resolve_repo_path(root, "x.json")
                self.assertIn("containment root", str(caught.exception))


if __name__ == "__main__":
    unittest.main()
