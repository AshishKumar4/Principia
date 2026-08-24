"""Tests for the CH-Eberhard Bell gate.

Three things are checked: the numerics against an independent exact oracle, the
recomputation against every p-value published by Shalm et al., Phys. Rev. Lett. 115,
250402 (2015), and the committed evidence end to end, including mutations that must
not survive. A mutation test earns its place only if the mutation is one a careless
edit could really make: a swapped detection column, a sign, a threshold, a
predictability, a pinned number.
"""

from __future__ import annotations

import copy
import json
import math
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

from principia.candidates import load_candidate
from principia.evaluators.bell_ch import (
    TEST_NAME,
    binomial_tail_ge,
    evaluate_bell_ch,
    martingale_success_probability,
)
from principia.evidence import evaluate_evidence, load_evidence, verify_evidence
from principia.models import ArtifactError, CandidateManifest, EvaluationStatus, EvidenceRecord

REPO_ROOT = Path(__file__).resolve().parents[1]
CANDIDATE_DIR = REPO_ROOT / "candidates/local-realism"
VIOLATION_RECORD = REPO_ROOT / "evidence/records/shalm-2015-ch-eberhard.json"
CONTROL_RECORD = REPO_ROOT / "evidence/records/shalm-2015-null-control.json"
VIOLATION_DATA = REPO_ROOT / "evidence/data/shalm-2015-xor3-pulses-4-8.json"
TIMESTAMP = "2026-08-23T00:00:00Z"

# Shalm et al. (2015) Table I: aggregate pulses, N_stop, N(++|ab), p-value, adjusted
# p-value at eps_p = 3e-3. The paper prints two significant figures, so a faithful
# recomputation can sit a couple of percent away from the printed number.
TABLE_ONE = (
    (1, 2376, 1257, 2.5e-03, 5.9e-03),
    (3, 7211, 3800, 2.4e-06, 2.4e-05),
    (5, 12127, 6378, 5.9e-09, 2.3e-07),
    (7, 16979, 8820, 2.0e-07, 9.2e-06),
)
# Supplemental Table S-I, run '02-54 (first run)', pulse 6: p-values at eps = 0,
# 1e-4, 1e-3, 1e-2. This run shows no violation, so it is the null control.
TABLE_S_ONE_CONTROL = ((0.0, 0.5238), (1e-04, 0.5278), (1e-03, 0.5637), (1e-02, 0.8566))


def read_json(path: Path) -> dict:
    return json.loads(path.read_text("utf-8"))


def exact_tail(trials: int, successes: int, probability: Fraction) -> Fraction:
    """P(Binomial >= successes) by exact rational arithmetic, an independent oracle."""
    complement = 1 - probability
    return sum(
        (
            Fraction(math.comb(trials, k)) * probability**k * complement ** (trials - k)
            for k in range(successes, trials + 1)
        ),
        Fraction(0),
    )


class BinomialTailTest(unittest.TestCase):
    def test_agrees_with_exact_rational_arithmetic(self) -> None:
        cases = (
            (40, 25, Fraction(1, 2)),
            (61, 40, Fraction(503, 1000)),
            (200, 90, Fraction(1, 2)),
            (17, 3, Fraction(1, 2)),
            (128, 128, Fraction(1, 2)),
            (77, 39, Fraction(509999, 1000000)),
        )
        for trials, successes, probability in cases:
            with self.subTest(trials=trials, successes=successes):
                expected = float(exact_tail(trials, successes, probability))
                found = binomial_tail_ge(trials, successes, float(probability))
                self.assertAlmostEqual(found, expected, delta=abs(expected) * 1e-09)

    def test_boundaries(self) -> None:
        self.assertEqual(binomial_tail_ge(10, 0, 0.5), 1.0)
        self.assertEqual(binomial_tail_ge(10, -3, 0.5), 1.0)
        self.assertEqual(binomial_tail_ge(10, 11, 0.5), 0.0)
        self.assertAlmostEqual(binomial_tail_ge(10, 10, 0.5), 2.0**-10)
        self.assertAlmostEqual(binomial_tail_ge(10, 1, 0.5), 1.0 - 2.0**-10)

    def test_rejects_degenerate_arguments(self) -> None:
        for probability in (0.0, 1.0, -0.5, 1.5):
            with self.subTest(probability=probability), self.assertRaises(ArtifactError):
                binomial_tail_ge(10, 5, probability)
        with self.assertRaises(ArtifactError):
            binomial_tail_ge(-1, 0, 0.5)


class SuccessProbabilityTest(unittest.TestCase):
    def test_equiprobable_settings_give_one_half(self) -> None:
        self.assertEqual(martingale_success_probability(0.0), 0.5)

    def test_matches_the_ratio_it_is_derived_from(self) -> None:
        """Eq. (S4) must equal Eq. (S3) evaluated at the saturating settings."""
        for epsilon in (1e-06, 1e-04, 3e-03, 1e-02, 0.25):
            with self.subTest(epsilon=epsilon):
                high = (1.0 + epsilon) / 2.0
                low = (1.0 - epsilon) / 2.0
                ratio = high * high / (high * high + low * low)
                self.assertAlmostEqual(martingale_success_probability(epsilon), ratio, places=14)

    def test_grows_with_predictability(self) -> None:
        values = [martingale_success_probability(eps) for eps in (0.0, 1e-04, 1e-03, 1e-02)]
        self.assertEqual(values, sorted(values))
        self.assertEqual(len(set(values)), len(values))

    def test_rejects_predictability_outside_range(self) -> None:
        for epsilon in (-1e-09, 1.0, 2.0, float("inf")):
            with self.subTest(epsilon=epsilon), self.assertRaises(ArtifactError):
                martingale_success_probability(epsilon)


class PublishedResultTest(unittest.TestCase):
    """The recomputation must land on the published numbers, which it never reads."""

    def test_reproduces_table_one(self) -> None:
        adjusted = martingale_success_probability(3e-03)
        for pulses, trials, successes, published, published_adjusted in TABLE_ONE:
            with self.subTest(pulses=pulses):
                plain = binomial_tail_ge(trials, successes, 0.5)
                self.assertLess(abs(plain - published) / published, 0.03)
                found = binomial_tail_ge(trials, successes, adjusted)
                self.assertLess(abs(found - published_adjusted) / published_adjusted, 0.03)

    def test_reproduces_the_control_columns_of_table_s_one(self) -> None:
        for epsilon, published in TABLE_S_ONE_CONTROL:
            with self.subTest(epsilon=epsilon):
                found = binomial_tail_ge(2528, 1263, martingale_success_probability(epsilon))
                self.assertLess(abs(found - published) / published, 0.01)

    def test_predictability_only_weakens_the_evidence(self) -> None:
        plain = binomial_tail_ge(12127, 6378, 0.5)
        adjusted = binomial_tail_ge(12127, 6378, martingale_success_probability(3e-03))
        self.assertLess(plain, adjusted)


class CommittedStatisticsTest(unittest.TestCase):
    """The committed counts must agree with the paper's own arithmetic."""

    def setUp(self) -> None:
        self.data = read_json(VIOLATION_DATA)
        self.table = self.data["outcome_table"]

    def test_ch_terms_sum_to_the_published_stopping_point(self) -> None:
        terms = (
            self.table["ab"]["++"],
            self.table["ab_prime"]["+0"],
            self.table["a_prime_b"]["0+"],
            self.table["a_prime_b_prime"]["++"],
        )
        self.assertEqual(sum(terms), self.data["trials_in_T"])
        self.assertEqual(terms[0], self.data["successes"])

    def test_table_sums_to_the_published_trial_count(self) -> None:
        self.assertEqual(
            sum(sum(row.values()) for row in self.table.values()), self.data["total_trials"]
        )

    def test_alice_setting_fraction_matches_the_supplement(self) -> None:
        rows = {pair: sum(row.values()) for pair, row in self.table.items()}
        fraction = (rows["ab"] + rows["ab_prime"]) / self.data["total_trials"]
        # Supplement Sec. III D quotes the excess to two significant figures over the
        # whole run: the fraction of "0"-setting trials "exceeds 0.5 by 8.0e-5" at
        # Alice. Table S-II's subset gives 7.75e-5, consistent at quoted precision.
        self.assertAlmostEqual(fraction - 0.5, 8.0e-05, delta=1.0e-05)

    def test_every_pinned_upstream_digest_is_a_sha256(self) -> None:
        for role, pinned in self.data["pinned_sources"].items():
            with self.subTest(role=role):
                self.assertTrue(pinned["url"].startswith("https://"))
                if pinned["sha256"] is not None:
                    self.assertRegex(pinned["sha256"], r"\A[0-9a-f]{64}\Z")
                    self.assertGreater(pinned["bytes"], 0)


class CommittedEvidenceTest(unittest.TestCase):
    """The two committed records, evaluated through the platform."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.candidate = load_candidate(CANDIDATE_DIR)
        cls.violation = load_evidence(VIOLATION_RECORD)
        cls.control = load_evidence(CONTROL_RECORD)

    def test_records_verify(self) -> None:
        self.assertEqual(verify_evidence(self.violation, REPO_ROOT), [])
        self.assertEqual(verify_evidence(self.control, REPO_ROOT), [])

    def test_violation_refutes_local_realism(self) -> None:
        result = evaluate_evidence(self.violation, self.candidate, REPO_ROOT, TIMESTAMP)
        self.assertEqual(result.status, EvaluationStatus.FAIL)
        self.assertEqual(result.evidence_id, "shalm-2015-ch-eberhard")
        self.assertEqual(result.metrics["trials_in_T"], 12127)
        self.assertEqual(result.metrics["successes"], 6378)
        self.assertLess(result.metrics["p_value"], 1e-06)
        self.assertGreater(result.metrics["ch_eberhard_functional"], 0.0)
        self.assertIn("dataset", result.artifacts)

    def test_control_does_not_reject_local_realism(self) -> None:
        result = evaluate_evidence(self.control, self.candidate, REPO_ROOT, TIMESTAMP)
        self.assertEqual(result.status, EvaluationStatus.INCONCLUSIVE)
        self.assertGreater(result.metrics["p_value"], 0.5)

    def test_a_candidate_predicting_violation_passes(self) -> None:
        manifest = read_json(CANDIDATE_DIR / "candidate.json")
        manifest["id"] = "nonlocal-correlations"
        for entry in manifest["evidence"]:
            entry["prediction"]["ch_eberhard_functional"] = "positive"
        result = evaluate_bell_ch(
            self.violation, CandidateManifest.from_dict(manifest), REPO_ROOT, TIMESTAMP
        )
        self.assertEqual(result.status, EvaluationStatus.PASS)

    def test_a_candidate_without_the_required_claim_is_not_applicable(self) -> None:
        manifest = read_json(CANDIDATE_DIR / "candidate.json")
        manifest["claims"] = [
            claim for claim in manifest["claims"] if claim["id"] != "ch-eberhard-expectation-bound"
        ]
        manifest["lean"]["claims"] = [claim["lean_symbol"] for claim in manifest["claims"]]
        result = evaluate_evidence(
            self.violation, CandidateManifest.from_dict(manifest), REPO_ROOT, TIMESTAMP
        )
        self.assertEqual(result.status, EvaluationStatus.NOT_APPLICABLE)


class MutationTest(unittest.TestCase):
    """Every mutation here changes the physics, and none may survive."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.candidate = load_candidate(CANDIDATE_DIR)
        cls.record = read_json(VIOLATION_RECORD)
        cls.data = read_json(VIOLATION_DATA)

    def evaluate(self, *, data=None, gate=None):
        """Evaluate a mutated copy from a scratch root, so file digests stay out of the way."""
        counts = copy.deepcopy(self.data)
        if data is not None:
            data(counts)
        record = copy.deepcopy(self.record)
        if gate is not None:
            gate(record["gate"])
        with tempfile.TemporaryDirectory() as root:
            (Path(root) / "counts.json").write_text(json.dumps(counts), "utf-8")
            record["dataset"]["local_path"] = "counts.json"
            return evaluate_bell_ch(
                EvidenceRecord.from_dict(record), self.candidate, Path(root), TIMESTAMP
            )

    def test_unmutated_copy_still_fails_local_realism(self) -> None:
        self.assertEqual(self.evaluate().status, EvaluationStatus.FAIL)

    def test_swapping_the_single_detection_columns_is_caught(self) -> None:
        def swap(counts: dict) -> None:
            for pair in ("ab_prime", "a_prime_b"):
                row = counts["outcome_table"][pair]
                row["+0"], row["0+"] = row["0+"], row["+0"]

        with self.assertRaises(ArtifactError):
            self.evaluate(data=swap)

    def test_moving_one_count_is_caught(self) -> None:
        def bump(counts: dict) -> None:
            counts["outcome_table"]["ab"]["++"] += 1

        with self.assertRaises(ArtifactError):
            self.evaluate(data=bump)

    def test_restating_the_statistic_is_caught(self) -> None:
        def bump(counts: dict) -> None:
            counts["successes"] += 1

        with self.assertRaises(ArtifactError):
            self.evaluate(data=bump)

    def test_a_threshold_below_the_p_value_withholds_the_verdict(self) -> None:
        def lower(gate: dict) -> None:
            gate["decision"]["significance_level"] = 1e-09

        self.assertEqual(self.evaluate(gate=lower).status, EvaluationStatus.INCONCLUSIVE)

    def test_predictability_below_the_observed_setting_bias_is_refused(self) -> None:
        for epsilon in (0.0, 1e-05):
            with self.subTest(epsilon=epsilon), self.assertRaises(ArtifactError):
                self.evaluate(
                    gate=lambda gate: gate["inputs"].__setitem__("excess_predictability", epsilon)
                )

    def test_predictability_far_above_the_paper_stops_reproducing_it(self) -> None:
        def loosen(gate: dict) -> None:
            gate["inputs"]["excess_predictability"] = 0.1

        with self.assertRaises(ArtifactError):
            self.evaluate(gate=loosen)

    def test_asking_for_another_test_is_refused(self) -> None:
        def rename(gate: dict) -> None:
            gate["inputs"]["test"]["name"] = "prediction-based-ratio"

        with self.assertRaises(ArtifactError):
            self.evaluate(gate=rename)

    def test_pinning_the_unadjusted_p_value_as_the_adjusted_one_is_caught(self) -> None:
        def repin(gate: dict) -> None:
            gate["decision"]["published"]["p_value"] = 5.85e-09

        with self.assertRaises(ArtifactError):
            self.evaluate(gate=repin)

    def test_pinning_a_count_off_by_one_is_caught(self) -> None:
        def repin(gate: dict) -> None:
            gate["decision"]["published"]["successes"] = 6377

        with self.assertRaises(ArtifactError):
            self.evaluate(gate=repin)

    def test_pinning_a_quantity_the_gate_does_not_compute_is_caught(self) -> None:
        def repin(gate: dict) -> None:
            gate["decision"]["published"]["chsh_s"] = 2.42

        with self.assertRaises(ArtifactError):
            self.evaluate(gate=repin)

    def test_dropping_the_assumptions_is_refused(self) -> None:
        def strip(gate: dict) -> None:
            gate["inputs"]["assumptions"] = []

        with self.assertRaises(ArtifactError):
            self.evaluate(gate=strip)

    def test_an_unknown_dataset_key_is_refused(self) -> None:
        def smuggle(counts: dict) -> None:
            counts["p_value"] = 5.85e-09

        with self.assertRaises(ArtifactError):
            self.evaluate(data=smuggle)

    def test_a_pinned_size_without_a_digest_is_refused(self) -> None:
        def unpin(counts: dict) -> None:
            counts["pinned_sources"]["raw_data_alice"]["sha256"] = None

        with self.assertRaises(ArtifactError):
            self.evaluate(data=unpin)

    def test_the_functional_is_negative_for_a_local_strategy(self) -> None:
        """The sign convention: a table a local model could produce must come out negative."""

        def local_strategy(counts: dict) -> None:
            counts["outcome_table"] = {
                "ab": {"++": 100, "+0": 50, "0+": 50, "00": 9800},
                "ab_prime": {"++": 100, "+0": 120, "0+": 50, "00": 9730},
                "a_prime_b": {"++": 100, "+0": 50, "0+": 130, "00": 9720},
                "a_prime_b_prime": {"++": 90, "+0": 50, "0+": 50, "00": 9810},
            }
            counts["trials_in_T"] = 440
            counts["successes"] = 100
            counts["total_trials"] = sum(
                sum(row.values()) for row in counts["outcome_table"].values()
            )

        def pins(gate: dict) -> None:
            gate["decision"]["published"] = {
                "trials_in_T": 440,
                "successes": 100,
                "citation": "constructed for this test, not a published result",
            }

        result = self.evaluate(data=local_strategy, gate=pins)
        self.assertEqual(result.status, EvaluationStatus.INCONCLUSIVE)
        self.assertLess(result.metrics["ch_eberhard_functional"], 0.0)


class GateWiringTest(unittest.TestCase):
    def test_the_records_name_this_evaluator_and_its_test(self) -> None:
        for path in (VIOLATION_RECORD, CONTROL_RECORD):
            record = read_json(path)
            with self.subTest(record=record["id"]):
                self.assertEqual(record["gate"]["evaluator"], "principia.evaluators.bell_ch")
                self.assertEqual(record["gate"]["inputs"]["test"]["name"], TEST_NAME)
                self.assertEqual(
                    record["gate"]["required_claims"], ["ch-eberhard-expectation-bound"]
                )

    def test_the_candidate_predicts_both_records(self) -> None:
        candidate = load_candidate(CANDIDATE_DIR)
        predicted = {entry.id for entry in candidate.evidence}
        self.assertEqual(predicted, {"shalm-2015-ch-eberhard", "shalm-2015-null-control"})
        self.assertEqual(
            {entry.prediction["ch_eberhard_functional"] for entry in candidate.evidence},
            {"non-positive"},
        )

    def test_the_lean_claims_and_the_manifest_claims_are_the_same_set(self) -> None:
        candidate = load_candidate(CANDIDATE_DIR)
        self.assertEqual(
            set(candidate.lean.claims), {claim.lean_symbol for claim in candidate.claims}
        )
        for symbol in candidate.lean.claims + candidate.lean.witnesses:
            with self.subTest(symbol=symbol):
                self.assertTrue(symbol.startswith(candidate.lean.namespace + "."))


if __name__ == "__main__":
    unittest.main()
