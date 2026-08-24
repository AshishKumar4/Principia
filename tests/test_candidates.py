"""Behaviour tests for `principia.candidates`.

Every test builds a throwaway repository on disk, because the rules under test are
about real paths: an entrypoint that escapes through `..` or a symlink, a candidate
directory whose name disagrees with the manifest id, a Lean file whose size feeds the
complexity vector. Only the public functions are called.
"""

from __future__ import annotations

import dataclasses
import json
import shutil
import tempfile
import unittest
from pathlib import Path

from principia.candidates import (
    candidate_complexity,
    candidate_lineage,
    load_candidate,
    verify_candidate,
)
from principia.models import SCHEMA_VERSION, ArtifactError, CandidateManifest

_CANDIDATE_ID = "demo-theory"
_MODULE = "CandidateLab.Demo.Theory"
_NAMESPACE = "CandidateLab.Demo.Theory"
_ENTRYPOINT = "CandidateLab/Demo/Theory.lean"
_WITNESS = f"{_NAMESPACE}.demoWitness"
_CLAIM_SYMBOL = f"{_NAMESPACE}.demo_bound"
_SOURCE = b"import Atlas.Specs.Bell\n\nnamespace CandidateLab.Demo.Theory\n\nend\n"


def _source_document() -> dict:
    return {
        "title": "Experimental Test of Bell's Inequalities Using Time-Varying Analyzers",
        "authors": ["Alain Aspect", "Jean Dalibard", "Gerard Roger"],
        "url": "https://doi.org/10.1103/PhysRevLett.49.1804",
        "doi": "10.1103/PhysRevLett.49.1804",
        "published": "1982-12-20",
    }


def _candidate_document(candidate_id: str = _CANDIDATE_ID) -> dict:
    return {
        "schema_version": SCHEMA_VERSION,
        "id": candidate_id,
        "version": 1,
        "parent": None,
        "title": "Demo candidate theory",
        "lean": {
            "module": _MODULE,
            "entrypoint": _ENTRYPOINT,
            "namespace": _NAMESPACE,
            "witnesses": [_WITNESS],
            "claims": [_CLAIM_SYMBOL],
        },
        "assumptions": [
            {
                "id": "locality",
                "lean_symbol": f"{_NAMESPACE}.Locality",
                "source": _source_document(),
            }
        ],
        "claims": [{"id": "demo-bound", "lean_symbol": _CLAIM_SYMBOL}],
        "parameters": [{"id": "alpha", "value": 0.05, "unit": None}],
        "exceptions": [{"id": "detector.efficiency", "description": "no fair sampling"}],
        "evidence": [{"id": "bell.chsh.test", "prediction": {"chsh": 2.7}}],
    }


class CandidateCase(unittest.TestCase):
    """A temporary repository holding one candidate and its Lean source."""

    def setUp(self) -> None:
        base = Path(tempfile.mkdtemp(prefix="principia-candidates-")).resolve()
        self.addCleanup(shutil.rmtree, base, ignore_errors=True)
        self.repo = base / "repo"
        self.outside = base / "outside"
        self.candidates = self.repo / "candidates"
        self.candidates.mkdir(parents=True)
        self.outside.mkdir()

    # --- fixtures ----------------------------------------------------------

    def write_source(self, relative: str = _ENTRYPOINT, content: bytes = _SOURCE) -> Path:
        path = self.repo / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        return path

    def write_candidate(
        self, document: dict | None = None, directory_name: str | None = None
    ) -> Path:
        document = _candidate_document() if document is None else document
        directory = self.candidates / (directory_name or str(document["id"]))
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "candidate.json").write_text(
            json.dumps(document) + "\n", encoding="utf-8"
        )
        return directory

    def document(self, *, lean: dict | None = None, **overrides: object) -> dict:
        document = _candidate_document()
        if lean is not None:
            document["lean"] = {**document["lean"], **lean}
        document.update(overrides)
        return document

    def verify(self, document: dict, directory_name: str | None = None) -> list[str]:
        directory = self.write_candidate(document, directory_name)
        manifest = CandidateManifest.from_dict(document)
        return verify_candidate(manifest, directory, self.repo)

    # --- assertions --------------------------------------------------------

    def assertReports(self, problems: list[str], *fragments: str) -> None:
        for fragment in fragments:
            if not any(fragment in problem for problem in problems):
                self.fail(f"no problem contains {fragment!r}: {problems}")


class LoadCandidateTests(CandidateCase):
    def test_loads_manifest_from_directory(self) -> None:
        directory = self.write_candidate()

        manifest = load_candidate(directory)

        self.assertEqual(_CANDIDATE_ID, manifest.id)
        self.assertEqual(_MODULE, manifest.lean.module)
        self.assertEqual(_ENTRYPOINT, manifest.lean.entrypoint)
        self.assertIsNone(manifest.parent)

    def test_trailing_separator_still_yields_the_directory_name(self) -> None:
        directory = self.write_candidate()

        manifest = load_candidate(f"{directory}/")

        self.assertEqual(_CANDIDATE_ID, manifest.id)

    def test_missing_manifest_is_rejected(self) -> None:
        empty = self.candidates / _CANDIDATE_ID
        empty.mkdir()

        with self.assertRaises(ArtifactError) as caught:
            load_candidate(empty)

        self.assertIn("candidate manifest not found", str(caught.exception))

    def test_manifest_that_is_not_an_object_is_rejected(self) -> None:
        directory = self.candidates / _CANDIDATE_ID
        directory.mkdir()
        (directory / "candidate.json").write_text("[]\n", encoding="utf-8")

        with self.assertRaises(ArtifactError) as caught:
            load_candidate(directory)

        self.assertIn("must be a JSON object", str(caught.exception))

    def test_id_must_equal_the_directory_name(self) -> None:
        directory = self.write_candidate(directory_name="other-name")

        with self.assertRaises(ArtifactError) as caught:
            load_candidate(directory)

        message = str(caught.exception)
        self.assertIn(_CANDIDATE_ID, message)
        self.assertIn("other-name", message)


class VerifyCandidateTests(CandidateCase):
    def test_valid_candidate_has_no_problems(self) -> None:
        self.write_source()
        directory = self.write_candidate()

        manifest = load_candidate(directory)

        self.assertEqual([], verify_candidate(manifest, directory, self.repo))

    def test_id_directory_mismatch_is_reported(self) -> None:
        self.write_source()

        problems = self.verify(_candidate_document(), directory_name="other-name")

        self.assertReports(problems, "does not match candidate directory name")

    def test_candidate_outside_the_repo_is_reported(self) -> None:
        self.write_source()
        directory = self.outside / _CANDIDATE_ID
        directory.mkdir()
        manifest = CandidateManifest.from_dict(_candidate_document())

        problems = verify_candidate(manifest, directory, self.repo)

        self.assertReports(problems, "is not inside repo root")

    def test_candidate_that_is_its_own_parent_is_reported(self) -> None:
        self.write_source()

        problems = self.verify(self.document(parent=_CANDIDATE_ID))

        self.assertReports(problems, "is the candidate itself")

    # --- entrypoint containment -------------------------------------------

    def test_dot_dot_in_the_entrypoint_is_rejected_even_inside_the_repo(self) -> None:
        self.write_source()

        problems = self.verify(
            self.document(
                lean={"entrypoint": "CandidateLab/../CandidateLab/Demo/Theory.lean"}
            )
        )

        self.assertReports(problems, "lean.entrypoint")
        self.assertEqual(1, len(problems), problems)

    def test_entrypoint_traversal_out_of_the_repo_is_reported(self) -> None:
        (self.outside / "Theory.lean").write_bytes(_SOURCE)

        problems = self.verify(
            self.document(lean={"entrypoint": "CandidateLab/../../outside/Theory.lean"})
        )

        self.assertReports(problems, "lean.entrypoint")

    def test_absolute_entrypoint_is_reported(self) -> None:
        escaped = self.outside / "Theory.lean"
        escaped.write_bytes(_SOURCE)

        problems = self.verify(self.document(lean={"entrypoint": str(escaped)}))

        self.assertReports(problems, "lean.entrypoint")

    def test_symlinked_entrypoint_escaping_the_repo_is_reported(self) -> None:
        escaped = self.outside / "Theory.lean"
        escaped.write_bytes(_SOURCE)
        link = self.repo / _ENTRYPOINT
        link.parent.mkdir(parents=True)
        link.symlink_to(escaped)

        problems = self.verify(_candidate_document())

        self.assertReports(problems, "lean.entrypoint")

    def test_symlinked_entrypoint_reaching_the_frozen_atlas_is_reported(self) -> None:
        frozen = self.repo / "Atlas/Specs/Frozen.lean"
        frozen.parent.mkdir(parents=True)
        frozen.write_bytes(_SOURCE)
        link = self.repo / _ENTRYPOINT
        link.parent.mkdir(parents=True)
        link.symlink_to(frozen)

        problems = self.verify(_candidate_document())

        self.assertReports(problems, "outside the candidate Lean tree")

    def test_entrypoint_outside_the_candidate_lean_tree_is_reported(self) -> None:
        self.write_source("Atlas/Specs/Frozen.lean")

        problems = self.verify(
            self.document(
                lean={
                    "module": "Atlas.Specs.Frozen",
                    "entrypoint": "Atlas/Specs/Frozen.lean",
                }
            )
        )

        self.assertReports(problems, "outside the candidate Lean tree")

    def test_missing_entrypoint_is_reported(self) -> None:
        problems = self.verify(_candidate_document())

        self.assertReports(problems, "lean.entrypoint")

    def test_entrypoint_that_is_a_directory_is_reported(self) -> None:
        (self.repo / _ENTRYPOINT).mkdir(parents=True)

        problems = self.verify(_candidate_document())

        self.assertReports(problems, "is not a regular file")

    def test_entrypoint_must_be_a_lean_file(self) -> None:
        self.write_source("CandidateLab/Demo/Theory.txt")

        problems = self.verify(
            self.document(lean={"entrypoint": "CandidateLab/Demo/Theory.txt"})
        )

        self.assertReports(problems, "is not a .lean file")

    def test_entrypoint_must_provide_the_declared_module(self) -> None:
        self.write_source("CandidateLab/Demo/Other.lean")

        problems = self.verify(
            self.document(lean={"entrypoint": "CandidateLab/Demo/Other.lean"})
        )

        self.assertReports(problems, "cannot provide module")

    # --- Lean name sanity --------------------------------------------------

    def test_malformed_module_and_namespace_are_reported(self) -> None:
        self.write_source()

        problems = self.verify(
            self.document(lean={"module": "CandidateLab..Demo", "namespace": "1Bad"})
        )

        self.assertReports(
            problems,
            "lean.module: 'CandidateLab..Demo' is not a dotted ASCII Lean name",
            "lean.namespace: '1Bad' is not a dotted ASCII Lean name",
        )

    def test_reserved_lean_token_in_a_symbol_is_reported(self) -> None:
        self.write_source()
        symbol = f"{_NAMESPACE}.theorem"

        problems = self.verify(
            self.document(
                lean={"claims": [symbol]},
                claims=[{"id": "demo-bound", "lean_symbol": symbol}],
            )
        )

        self.assertReports(problems, "uses reserved Lean token(s) theorem")

    def test_lean_source_injection_in_a_symbol_is_reported(self) -> None:
        self.write_source()
        symbol = f'{_NAMESPACE}.demo_bound; #eval IO.println "pwned"'

        problems = self.verify(
            self.document(
                lean={"claims": [symbol]},
                claims=[{"id": "demo-bound", "lean_symbol": symbol}],
            )
        )

        self.assertReports(problems, "is not a dotted ASCII Lean name")

    def test_symbol_outside_the_namespace_is_reported(self) -> None:
        self.write_source()
        foreign = "Atlas.Specs.Bell.chsh_le_two"

        problems = self.verify(
            self.document(
                lean={"claims": [foreign]},
                claims=[{"id": "demo-bound", "lean_symbol": foreign}],
            )
        )

        self.assertReports(problems, "is not a declaration inside namespace")

    def test_assumption_symbol_outside_the_namespace_is_reported(self) -> None:
        self.write_source()
        assumptions = [
            {
                "id": "locality",
                "lean_symbol": "Atlas.Specs.Bell.Locality",
                "source": _source_document(),
            }
        ]

        problems = self.verify(self.document(assumptions=assumptions))

        self.assertReports(
            problems, "assumptions.lean_symbol[0]", "is not a declaration inside namespace"
        )

    def test_repeated_symbol_is_reported(self) -> None:
        self.write_source()

        problems = self.verify(self.document(lean={"witnesses": [_WITNESS, _WITNESS]}))

        self.assertReports(problems, "is listed more than once")

    def test_symbol_declared_as_both_witness_and_claim_is_reported(self) -> None:
        self.write_source()

        problems = self.verify(self.document(lean={"witnesses": [_CLAIM_SYMBOL]}))

        self.assertReports(problems, "is declared as both a witness and a claim")

    def test_candidate_without_witness_or_claim_symbols_is_reported(self) -> None:
        self.write_source()
        directory = self.write_candidate()
        manifest = load_candidate(directory)
        stripped = dataclasses.replace(
            manifest, lean=dataclasses.replace(manifest.lean, witnesses=(), claims=())
        )

        problems = verify_candidate(stripped, directory, self.repo)

        self.assertReports(
            problems,
            "lean.witnesses: empty",
            "lean.claims: empty",
        )

    # --- reference arrays --------------------------------------------------

    def test_claim_symbol_missing_from_lean_claims_is_reported(self) -> None:
        self.write_source()

        problems = self.verify(
            self.document(
                claims=[{"id": "demo-bound", "lean_symbol": f"{_NAMESPACE}.other_bound"}]
            )
        )

        self.assertReports(
            problems,
            "is missing from lean.claims",
            "is not named by any claim entry",
        )

    def test_duplicate_reference_ids_are_reported(self) -> None:
        self.write_source()
        document = self.document(
            claims=[
                {"id": "demo-bound", "lean_symbol": _CLAIM_SYMBOL},
                {"id": "demo-bound", "lean_symbol": _CLAIM_SYMBOL},
            ],
            parameters=[
                {"id": "alpha", "value": 0.05, "unit": None},
                {"id": "alpha", "value": 0.01, "unit": None},
            ],
            exceptions=[
                {"id": "detector.efficiency", "description": "no fair sampling"},
                {"id": "detector.efficiency", "description": "duplicated"},
            ],
            evidence=[
                {"id": "bell.chsh.test", "prediction": {"chsh": 2.7}},
                {"id": "bell.chsh.test", "prediction": {"chsh": 2.8}},
            ],
        )

        problems = self.verify(document)

        self.assertReports(
            problems,
            "claims: id 'demo-bound' is used 2 times",
            "parameters: id 'alpha' is used 2 times",
            "exceptions: id 'detector.efficiency' is used 2 times",
            "evidence: id 'bell.chsh.test' is used 2 times",
        )

    def test_evidence_prediction_key_must_be_clean(self) -> None:
        self.write_source()

        problems = self.verify(
            self.document(evidence=[{"id": "bell.chsh.test", "prediction": {" chsh": 2.7}}])
        )

        self.assertReports(problems, "prediction key ' chsh'")

    def test_empty_evidence_prediction_is_reported(self) -> None:
        self.write_source()
        directory = self.write_candidate()
        manifest = load_candidate(directory)
        blanked = dataclasses.replace(
            manifest,
            evidence=tuple(
                dataclasses.replace(reference, prediction={})
                for reference in manifest.evidence
            ),
        )

        problems = verify_candidate(blanked, directory, self.repo)

        self.assertReports(problems, "prediction is empty")


class CandidateComplexityTests(CandidateCase):
    def test_source_bytes_is_the_entrypoint_size_on_disk(self) -> None:
        content = b"-- one line\n"
        self.write_source(content=content)
        manifest = load_candidate(self.write_candidate())

        complexity = candidate_complexity(manifest, self.repo)

        self.assertEqual(len(content), complexity["source_bytes"])

    def test_source_bytes_follows_the_file_not_the_manifest(self) -> None:
        self.write_source(content=b"-- short\n")
        manifest = load_candidate(self.write_candidate())
        before = candidate_complexity(manifest, self.repo)["source_bytes"]

        grown = b"-- short\n" + b"-- padding\n" * 40
        self.write_source(content=grown)
        after = candidate_complexity(manifest, self.repo)["source_bytes"]

        self.assertEqual(len(grown), after)
        self.assertGreater(after, before)

    def test_counts_come_from_the_manifest_arrays(self) -> None:
        self.write_source()
        document = self.document(
            assumptions=[
                {
                    "id": f"assumption-{index}",
                    "lean_symbol": f"{_NAMESPACE}.Assumption{index}",
                    "source": _source_document(),
                }
                for index in range(3)
            ],
            parameters=[
                {"id": "alpha", "value": 0.05, "unit": None},
                {"id": "beta", "value": 1, "unit": "s"},
            ],
            exceptions=[],
        )
        manifest = CandidateManifest.from_dict(document)

        complexity = candidate_complexity(manifest, self.repo)

        self.assertEqual(
            {
                "source_bytes": len(_SOURCE),
                "assumption_count": 3,
                "parameter_count": 2,
                "exception_count": 0,
            },
            complexity,
        )

    def test_declared_parameters_cannot_fake_the_complexity(self) -> None:
        self.write_source()
        document = self.document(
            parameters=[
                {"id": "source-bytes", "value": 1, "unit": None},
                {"id": "assumption-count", "value": 0, "unit": None},
            ]
        )
        manifest = CandidateManifest.from_dict(document)

        complexity = candidate_complexity(manifest, self.repo)

        self.assertEqual(len(_SOURCE), complexity["source_bytes"])
        self.assertEqual(1, complexity["assumption_count"])
        self.assertEqual(2, complexity["parameter_count"])

    def test_missing_entrypoint_raises(self) -> None:
        manifest = CandidateManifest.from_dict(_candidate_document())

        with self.assertRaises(ArtifactError):
            candidate_complexity(manifest, self.repo)

    def test_entrypoint_escaping_the_repo_raises(self) -> None:
        (self.outside / "Theory.lean").write_bytes(_SOURCE)
        manifest = CandidateManifest.from_dict(
            self.document(lean={"entrypoint": "CandidateLab/../../outside/Theory.lean"})
        )

        with self.assertRaises(ArtifactError):
            candidate_complexity(manifest, self.repo)

    def test_directory_entrypoint_raises(self) -> None:
        (self.repo / _ENTRYPOINT).mkdir(parents=True)
        manifest = CandidateManifest.from_dict(_candidate_document())

        with self.assertRaises(ArtifactError):
            candidate_complexity(manifest, self.repo)


class CandidateLineageTests(CandidateCase):
    def chain(self, *links: tuple[str, str | None]) -> None:
        for candidate_id, parent in links:
            document = _candidate_document(candidate_id)
            document["parent"] = parent
            self.write_candidate(document)

    def test_lineage_of_a_root_candidate_is_itself(self) -> None:
        self.chain(("root", None))

        self.assertEqual(["root"], candidate_lineage(self.candidates, "root"))

    def test_lineage_runs_from_the_earliest_ancestor(self) -> None:
        self.chain(("root", None), ("middle", "root"), ("leaf", "middle"))

        self.assertEqual(
            ["root", "middle", "leaf"], candidate_lineage(self.candidates, "leaf")
        )

    def test_unknown_candidate_is_rejected(self) -> None:
        with self.assertRaises(ArtifactError) as caught:
            candidate_lineage(self.candidates, "ghost")

        self.assertIn("candidate 'ghost' not found", str(caught.exception))

    def test_missing_parent_is_rejected(self) -> None:
        self.chain(("leaf", "ghost"))

        with self.assertRaises(ArtifactError) as caught:
            candidate_lineage(self.candidates, "leaf")

        self.assertIn("parent 'ghost' of candidate 'leaf' not found", str(caught.exception))

    def test_cycle_is_rejected(self) -> None:
        self.chain(("first", "second"), ("second", "first"))

        with self.assertRaises(ArtifactError) as caught:
            candidate_lineage(self.candidates, "first")

        self.assertIn("cycle", str(caught.exception))
        self.assertIn("first -> second -> first", str(caught.exception))

    def test_self_parent_is_rejected_as_a_cycle(self) -> None:
        self.chain(("loop", "loop"))

        with self.assertRaises(ArtifactError) as caught:
            candidate_lineage(self.candidates, "loop")

        self.assertIn("cycle", str(caught.exception))

    def test_traversal_in_the_requested_id_is_rejected(self) -> None:
        self.chain(("root", None))

        with self.assertRaises(ArtifactError) as caught:
            candidate_lineage(self.candidates, "../outside")

        self.assertIn("not a plain directory name", str(caught.exception))

    def test_traversal_in_a_parent_id_is_rejected(self) -> None:
        self.chain(("root", None))
        document = _candidate_document("leaf")
        document["parent"] = "../root"
        self.write_candidate(document)

        with self.assertRaises(ArtifactError):
            candidate_lineage(self.candidates, "leaf")

    def test_lineage_rejects_a_candidate_whose_id_is_not_its_directory(self) -> None:
        self.write_candidate(_candidate_document("root"), directory_name="renamed")

        with self.assertRaises(ArtifactError) as caught:
            candidate_lineage(self.candidates, "renamed")

        self.assertIn("does not match candidate directory name", str(caught.exception))


if __name__ == "__main__":
    unittest.main()
