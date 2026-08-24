"""Bell gate: recompute a loophole-free Clauser-Horne-Eberhard test from counts.

The gate answers one question about a candidate theory: does a published
loophole-free Bell experiment refute what the candidate predicts for the
Clauser-Horne-Eberhard functional? Nothing here echoes a published p-value.
The test statistic and its p-value bound are recomputed from committed counts,
and the record pins the published numbers so a disagreement is an error rather
than a silent verdict.

Every formula below is traceable to the primary source, cited as `[Sn]` for the
Supplemental Material of Shalm et al., *A strong loophole-free test of local
realism*, Phys. Rev. Lett. 115, 250402 (2015), arXiv:1511.03189:

* Inequality [S1]: under local realism
  `P(++|ab) - P(+0|ab') - P(0+|a'b) - P(++|a'b') <= 0`.
* Test statistic [Sec. I A]: `T` is the sequence of trials whose settings and
  outcomes lie in `{++ab, +0ab', 0+a'b, ++a'b'}`; the statistic `N_S` counts the
  `++ab` trials among the first `N` elements of `T`, where `N` is fixed before
  the analysis.
* p-value [S2], from Bierhorst, J. Phys. A 48, 195302 (2015): the indicator
  sequence is a supermartingale under local realism, so
  `p <= P(Binomial(N, p0) >= N_S)`. This holds for hidden variables with memory,
  which is why no independence assumption enters.
* Setting predictability [S3, S4], from Bierhorst, arXiv:1312.2999: settings need
  not be exactly equiprobable. Bounding both parties by `P <= (1 + eps)/2` raises
  the binomial success probability to `p0 = 1/2 + eps/(1 + eps^2)`.

A Bell test can refute local realism but never confirm it, so this gate returns
`pass`/`fail` only against what the candidate predicts, and `inconclusive`
whenever the data does not reject at the record's significance level.
"""

from __future__ import annotations

import hashlib
import math
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING

from principia.artifacts import load_json, resolve_repo_path
from principia.models import (
    SCHEMA_VERSION,
    ArtifactError,
    EvaluationResult,
    EvaluationStatus,
)

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path

    from principia.models import CandidateManifest, EvidenceRecord

__all__ = [
    "TEST_NAME",
    "binomial_tail_ge",
    "evaluate_bell_ch",
    "martingale_success_probability",
]

TEST_NAME = "martingale-binomial-ch-eberhard"
PREDICTION_KEY = "ch_eberhard_functional"

_PREDICTIONS = ("positive", "non-positive")
_SETTING_PAIRS = ("ab", "ab_prime", "a_prime_b", "a_prime_b_prime")
_OUTCOMES = ("++", "+0", "0+", "00")
# The four terms of inequality [S1], in the order they are written there.
_CH_TERMS = (
    ("ab", "++", 1),
    ("ab_prime", "+0", -1),
    ("a_prime_b", "0+", -1),
    ("a_prime_b_prime", "++", -1),
)
# Setting pairs in which Alice chose `a`, respectively Bob chose `b`.
_ALICE_FIRST = ("ab", "ab_prime")
_BOB_FIRST = ("ab", "a_prime_b")

_TEST_KEYS = ("name", "inequality", "statistic", "p_value", "success_probability")
_INPUT_KEYS = ("assumptions", "excess_predictability", "test")
_DECISION_KEYS = ("published", "reproduction_tolerance", "significance_level")
_ASSUMPTION_KEYS = ("id", "source", "statement")
_DATA_REQUIRED = (
    "id",
    "pinned_sources",
    "provenance",
    "pulse_aggregate",
    "run",
    "schema_version",
    "successes",
    "title",
    "total_trials",
    "trials_in_T",
)
_DATA_OPTIONAL = ("outcome_table",)
_HEX = "0123456789abcdef"


def martingale_success_probability(excess_predictability: float) -> float:
    """Largest `P(J = +1)` a local realistic strategy reaches at this predictability.

    Supplemental Eq. (S3): the local deterministic strategy that always fires both
    detectors makes a relevant trial with probability `p_a p_b + p_a' p_b'`, of which
    the fraction `p_a p_b / (p_a p_b + p_a' p_b')` is `++ab`. That ratio grows with
    both setting probabilities, so the predictability bound `P <= (1 + eps)/2` is
    saturated at `p_a = p_b = (1 + eps)/2`, which is Eq. (S4) below. All 16 local
    deterministic strategies obey it, so it is the binomial success probability used
    in the p-value bound.
    """
    eps = _number(excess_predictability, "excess predictability")
    if not 0.0 <= eps < 1.0:
        raise ArtifactError(f"excess predictability {eps!r} is outside [0, 1)")
    return 0.5 + eps / (1.0 + eps * eps)


def binomial_tail_ge(trials: int, successes: int, success_probability: float) -> float:
    """Return `P(Binomial(trials, success_probability) >= successes)`.

    The mass at `successes` is computed once in log space, and the neighbouring
    masses follow from the exact term ratio, so no factorial ever overflows. The
    walk starts at `successes` and stops as soon as the remaining geometric tail
    cannot change the sum, which keeps the cost independent of the trial count.
    Below the mean the complement is used, reflected onto the same upward walk by
    `P(X <= m) = P(n - X >= n - m)` with `n - X` binomial in the complement.
    """
    if trials < 0:
        raise ArtifactError(f"trial count {trials!r} is negative")
    if not 0.0 < success_probability < 1.0:
        raise ArtifactError(f"success probability {success_probability!r} is outside (0, 1)")
    if successes <= 0:
        return 1.0
    if successes > trials:
        return 0.0
    if successes > trials * success_probability:
        return min(1.0, _upper_tail(trials, successes, success_probability))
    reflected = _upper_tail(trials, trials - successes + 1, 1.0 - success_probability)
    return max(0.0, 1.0 - reflected)


def evaluate_bell_ch(
    record: "EvidenceRecord",
    candidate: "CandidateManifest",
    repo_root: "Path",
    timestamp: str,
) -> EvaluationResult:
    """Evaluate one Bell record against one candidate theory."""
    epsilon, test = _inputs(record.gate.inputs)
    alpha, tolerance, published = _decision(record.gate.decision)
    if test["name"] != TEST_NAME:
        raise ArtifactError(f"gate asks for test {test['name']!r}, this evaluator is {TEST_NAME!r}")
    if record.dataset.local_path is None:
        raise ArtifactError("the gate needs the counts committed to the repository")
    path = resolve_repo_path(repo_root, record.dataset.local_path, must_exist=True)
    series = _series(load_json(path))
    metrics = _recompute(series, epsilon, alpha)
    _reproduces(metrics, published, tolerance)
    prediction = _prediction(candidate, record.id)
    status, verdict = _verdict(metrics, prediction, alpha)
    return EvaluationResult(
        schema_version=SCHEMA_VERSION,
        candidate_id=candidate.id,
        evidence_id=record.id,
        status=status,
        summary=(
            f"{verdict}: the CH-Eberhard martingale test on {series.trials} relevant trials "
            f"({series.successes} of them ++ab) gives p = {metrics['p_value']:.3e} at excess "
            f"predictability {epsilon:.1e}, against a significance level of {alpha:.1e}; the "
            f"candidate predicts a {prediction} CH-Eberhard functional"
        ),
        metrics=metrics,
        artifacts={"dataset": hashlib.sha256(path.read_bytes()).hexdigest()},
        timestamp=timestamp,
    )


@dataclass(frozen=True, slots=True)
class _Series:
    """One analysed trial series: the statistic, and the counts it came from."""

    trials: int
    successes: int
    total_trials: int
    table: "Mapping[str, Mapping[str, int]] | None"


def _upper_tail(trials: int, start: int, probability: float) -> float:
    """Sum binomial masses from `start` upwards until they stop mattering.

    `start` is above the mean, so the term ratio is below one and shrinking: once
    the geometric bound on everything still ahead is below the rounding error of
    what is already summed, the rest cannot move the answer.
    """
    complement = 1.0 - probability
    odds = probability / complement
    log_start = (
        math.lgamma(trials + 1)
        - math.lgamma(start + 1)
        - math.lgamma(trials - start + 1)
        + start * math.log(probability)
        + (trials - start) * math.log(complement)
    )
    total = 1.0
    term = 1.0
    for index in range(start, trials):
        step = ((trials - index) / (index + 1)) * odds
        term *= step
        total += term
        if step < 1.0 and term * step <= 1e-18 * total * (1.0 - step):
            break
    return math.exp(log_start) * total


def _inputs(inputs: "Mapping[str, object]") -> tuple[float, "Mapping[str, str]"]:
    """Read the evaluator inputs: the predictability bound and the cited method."""
    _keys(inputs, _INPUT_KEYS, (), "gate inputs")
    epsilon = _number(inputs["excess_predictability"], "gate input 'excess_predictability'")
    test = _mapping(inputs["test"], "gate input 'test'")
    _keys(test, _TEST_KEYS, (), "gate input 'test'")
    documented = {key: _text(test[key], f"gate input 'test.{key}'") for key in _TEST_KEYS}
    _assumptions(inputs["assumptions"])
    return epsilon, documented


def _assumptions(value: object) -> None:
    """Require the record to carry its physical assumptions, each with a source.

    The assumptions are not machine-interpreted: predictability, spacelike
    separation and the fixed stopping rule cannot be checked from counts. They are
    what the verdict is conditional on, so a record without them is unusable.
    """
    if not _sequence(value) or not value:
        raise ArtifactError("gate input 'assumptions' must be a non-empty list")
    seen: set[str] = set()
    for index, entry in enumerate(value):
        stated = _mapping(entry, f"assumption {index}")
        _keys(stated, _ASSUMPTION_KEYS, (), f"assumption {index}")
        for key in _ASSUMPTION_KEYS:
            _text(stated[key], f"assumption {index} field {key!r}")
        name = str(stated["id"])
        if name in seen:
            raise ArtifactError(f"assumption {name!r} is listed twice")
        seen.add(name)


def _decision(decision: "Mapping[str, object]") -> tuple[float, float, "Mapping[str, object]"]:
    """Read the decision rule: the level, the reproduction tolerance, the pinned result."""
    _keys(decision, _DECISION_KEYS, (), "gate decision")
    alpha = _number(decision["significance_level"], "gate decision 'significance_level'")
    if not 0.0 < alpha < 1.0:
        raise ArtifactError(f"significance level {alpha!r} is outside (0, 1)")
    tolerance = _number(decision["reproduction_tolerance"], "gate decision 'reproduction_tolerance'")
    if not 0.0 < tolerance < 1.0:
        raise ArtifactError(f"reproduction tolerance {tolerance!r} is outside (0, 1)")
    published = _mapping(decision["published"], "gate decision 'published'")
    if "citation" not in published:
        raise ArtifactError("gate decision 'published' must cite where its numbers are published")
    _text(published["citation"], "gate decision 'published.citation'")
    return alpha, tolerance, published


def _series(data: object) -> _Series:
    """Read committed counts, and hold them to their own internal arithmetic."""
    counts = _mapping(data, "dataset")
    _keys(counts, _DATA_REQUIRED, _DATA_OPTIONAL, "dataset")
    if _integer(counts["schema_version"], "dataset 'schema_version'") != SCHEMA_VERSION:
        raise ArtifactError(f"dataset schema version {counts['schema_version']!r} is not supported")
    trials = _integer(counts["trials_in_T"], "dataset 'trials_in_T'")
    successes = _integer(counts["successes"], "dataset 'successes'")
    total = _integer(counts["total_trials"], "dataset 'total_trials'")
    if trials <= 0:
        raise ArtifactError(f"dataset declares {trials} relevant trials")
    if not 0 <= successes <= trials:
        raise ArtifactError(f"dataset declares {successes} of {trials} relevant trials as ++ab")
    if total < trials:
        raise ArtifactError(f"dataset declares {total} trials in total but {trials} relevant ones")
    _aggregate(counts["pulse_aggregate"])
    _provenance(counts["provenance"])
    _pinned_sources(counts["pinned_sources"])
    table = _table(counts["outcome_table"]) if "outcome_table" in counts else None
    if table is not None:
        _consistent(table, trials, successes, total)
    return _Series(trials=trials, successes=successes, total_trials=total, table=table)


def _table(value: object) -> "Mapping[str, Mapping[str, int]]":
    """Read the settings-by-outcome table, exactly four settings pairs by four outcomes."""
    rows = _mapping(value, "dataset 'outcome_table'")
    _keys(rows, _SETTING_PAIRS, (), "dataset 'outcome_table'")
    table: dict[str, dict[str, int]] = {}
    for pair in _SETTING_PAIRS:
        row = _mapping(rows[pair], f"outcome row {pair!r}")
        _keys(row, _OUTCOMES, (), f"outcome row {pair!r}")
        table[pair] = {}
        for outcome in _OUTCOMES:
            count = _integer(row[outcome], f"count {pair!r} {outcome!r}")
            if count < 0:
                raise ArtifactError(f"count {pair!r} {outcome!r} is negative")
            table[pair][outcome] = count
    return table


def _consistent(
    table: "Mapping[str, Mapping[str, int]]",
    trials: int,
    successes: int,
    total: int,
) -> None:
    """Hold the table against the separately published statistic and trial count.

    The counts come from two different tables of the same paper. Their agreement is
    the check that the committed numbers were transcribed and interpreted correctly,
    so a mismatch stops the gate instead of producing a verdict.
    """
    relevant = sum(table[pair][outcome] for pair, outcome, _ in _CH_TERMS)
    if relevant != trials:
        raise ArtifactError(
            f"the four CH-Eberhard terms of the outcome table sum to {relevant} relevant "
            f"trials, the dataset declares {trials}"
        )
    if table["ab"]["++"] != successes:
        raise ArtifactError(
            f"the outcome table has {table['ab']['++']} ++ab trials, "
            f"the dataset declares {successes}"
        )
    tabled = sum(sum(row.values()) for row in table.values())
    if tabled != total:
        raise ArtifactError(
            f"the outcome table holds {tabled} trials, the dataset declares {total}"
        )


def _recompute(series: _Series, epsilon: float, alpha: float) -> dict[str, float | int]:
    """Recompute the statistic, its p-value bound, and the table-level diagnostics."""
    probability = martingale_success_probability(epsilon)
    metrics: dict[str, float | int] = {
        "trials_in_T": series.trials,
        "successes": series.successes,
        "total_trials": series.total_trials,
        "excess_predictability": epsilon,
        "binomial_success_probability": probability,
        "significance_level": alpha,
        "p_value": binomial_tail_ge(series.trials, series.successes, probability),
        "p_value_without_predictability": binomial_tail_ge(series.trials, series.successes, 0.5),
    }
    if series.table is None:
        return metrics
    rows = {pair: sum(row.values()) for pair, row in series.table.items()}
    empty = sorted(pair for pair, count in rows.items() if count == 0)
    if empty:
        raise ArtifactError(f"settings pairs {', '.join(empty)} were never chosen")
    metrics["ch_eberhard_functional"] = math.fsum(
        sign * series.table[pair][outcome] / rows[pair] for pair, outcome, sign in _CH_TERMS
    )
    alice = sum(rows[pair] for pair in _ALICE_FIRST) / series.total_trials
    bob = sum(rows[pair] for pair in _BOB_FIRST) / series.total_trials
    observed = max(abs(2.0 * alice - 1.0), abs(2.0 * bob - 1.0))
    if epsilon < observed:
        raise ArtifactError(
            f"the gate assumes excess predictability {epsilon!r} but the settings themselves "
            f"deviate from equiprobability by {observed!r}; the p-value bound needs a "
            f"predictability bound at least as large as the observed setting bias"
        )
    metrics["alice_setting_fraction"] = alice
    metrics["bob_setting_fraction"] = bob
    metrics["observed_excess_predictability"] = observed
    return metrics


def _reproduces(
    metrics: "Mapping[str, float | int]",
    published: "Mapping[str, object]",
    tolerance: float,
) -> None:
    """Require the recomputation to land on the published result.

    Counts must agree exactly. Published p-values and frequencies are rounded to a
    few figures, so they are compared relatively. Anything else means the record,
    the committed counts and the paper disagree, which is an error and not a verdict
    about the candidate.
    """
    for key, expected in published.items():
        if key == "citation":
            continue
        if key not in metrics:
            raise ArtifactError(f"the gate pins {key!r}, which this evaluator does not compute")
        found = metrics[key]
        if isinstance(expected, bool) or not isinstance(expected, (int, float)):
            raise ArtifactError(f"published {key!r} must be a number, got {expected!r}")
        if isinstance(expected, int) and isinstance(found, int):
            if found != expected:
                raise ArtifactError(f"recomputed {key} = {found}, published {expected}")
            continue
        if expected == 0.0:
            raise ArtifactError(f"published {key!r} cannot be pinned at zero")
        deviation = abs(found - expected) / abs(expected)
        if deviation > tolerance:
            raise ArtifactError(
                f"recomputed {key} = {found!r} deviates from the published {expected!r} "
                f"by {deviation:.3g}, more than the tolerance {tolerance!r}"
            )


def _prediction(candidate: "CandidateManifest", evidence_id: str) -> str:
    """Read what the candidate predicts for the CH-Eberhard functional of this record."""
    matches = [entry for entry in candidate.evidence if entry.id == evidence_id]
    if len(matches) != 1:
        raise ArtifactError(
            f"candidate {candidate.id!r} makes {len(matches)} predictions for evidence "
            f"{evidence_id!r}, exactly one is needed"
        )
    prediction = _mapping(matches[0].prediction, f"prediction for {evidence_id!r}")
    _keys(prediction, (PREDICTION_KEY,), (), f"prediction for {evidence_id!r}")
    sign = _text(prediction[PREDICTION_KEY], f"prediction {PREDICTION_KEY!r}")
    if sign not in _PREDICTIONS:
        raise ArtifactError(f"prediction {sign!r} is not one of {', '.join(_PREDICTIONS)}")
    return sign


def _verdict(
    metrics: "Mapping[str, float | int]",
    prediction: str,
    alpha: float,
) -> tuple[EvaluationStatus, str]:
    """Turn the recomputed p-value and the candidate's prediction into a verdict.

    The test is one-sided: it can reject a non-positive CH-Eberhard functional and
    nothing else. Above the significance level the experiment discriminates between
    no theories at all, so neither prediction is rewarded or punished.
    """
    if metrics["p_value"] > alpha:
        return EvaluationStatus.INCONCLUSIVE, "local realism is not rejected by this run"
    if prediction == "non-positive":
        return EvaluationStatus.FAIL, "the candidate's non-positive functional is refuted"
    return EvaluationStatus.PASS, "the candidate's positive functional is what the data shows"


def _aggregate(value: object) -> None:
    """Check the pulse aggregate that identifies the analysed slots."""
    if not _sequence(value) or len(value) != 2:
        raise ArtifactError("dataset 'pulse_aggregate' must be a pair of pulse numbers")
    first, last = (_integer(bound, "dataset 'pulse_aggregate' bound") for bound in value)
    if first < 1 or last < first:
        raise ArtifactError(f"pulse aggregate [{first}, {last}] is not an ascending pulse range")


def _provenance(value: object) -> None:
    """Check that every committed number says where in the source it comes from."""
    stated = _mapping(value, "dataset 'provenance'")
    if not stated:
        raise ArtifactError("dataset 'provenance' must say where the counts come from")
    for key, text in stated.items():
        _text(text, f"dataset provenance {key!r}")


def _pinned_sources(value: object) -> None:
    """Check the upstream chain: where each artefact lives, and its checksum if pinned.

    A committed count is only as good as the trail back to the experiment. Every
    role names a URL and says something about it; a checksum is optional because
    the raw archives run to gigabytes, but when it is there it must be a SHA-256
    over a stated number of bytes, and when it is not the note has to say why.
    """
    sources = _mapping(value, "dataset 'pinned_sources'")
    if not sources:
        raise ArtifactError("dataset 'pinned_sources' must pin at least the primary source")
    for role, entry in sources.items():
        pinned = _mapping(entry, f"pinned source {role!r}")
        _keys(pinned, ("bytes", "note", "sha256", "url"), (), f"pinned source {role!r}")
        _text(pinned["url"], f"pinned source {role!r} url")
        _text(pinned["note"], f"pinned source {role!r} note")
        digest, size = pinned["sha256"], pinned["bytes"]
        if digest is None:
            if size is not None:
                raise ArtifactError(f"pinned source {role!r} states a size but no checksum")
            continue
        text = _text(digest, f"pinned source {role!r} sha256")
        if len(text) != 64 or text.strip(_HEX):
            raise ArtifactError(f"pinned source {role!r} sha256 {text!r} is not a SHA-256 digest")
        if _integer(size, f"pinned source {role!r} bytes") <= 0:
            raise ArtifactError(f"pinned source {role!r} declares {size} bytes")


def _keys(
    mapping: "Mapping[str, object]",
    required: "Iterable[str]",
    optional: "Iterable[str]",
    what: str,
) -> None:
    """Reject a mapping that misses a required key or carries an unknown one."""
    required = tuple(required)
    missing = [key for key in required if key not in mapping]
    unknown = sorted(set(mapping) - set(required) - set(optional))
    if missing:
        raise ArtifactError(f"{what} is missing {', '.join(missing)}")
    if unknown:
        raise ArtifactError(f"{what} has unknown keys {', '.join(unknown)}")


def _sequence(value: object) -> bool:
    """Accept a JSON array, whether it arrived as a list or frozen into a tuple."""
    return isinstance(value, Sequence) and not isinstance(value, (str, bytes))


def _mapping(value: object, what: str) -> "Mapping[str, object]":
    if not isinstance(value, Mapping):
        raise ArtifactError(f"{what} must be a JSON object, got {type(value).__name__}")
    return value


def _integer(value: object, what: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ArtifactError(f"{what} must be an integer, got {value!r}")
    return value


def _number(value: object, what: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ArtifactError(f"{what} must be a number, got {value!r}")
    number = float(value)
    if not math.isfinite(number):
        raise ArtifactError(f"{what} must be finite, got {value!r}")
    return number


def _text(value: object, what: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ArtifactError(f"{what} must be a non-empty string")
    return value
