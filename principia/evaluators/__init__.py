"""Built-in evidence evaluators.

The mapping below is the whole registration surface: `principia.evidence` imports it
and registers every entry when that module is first imported. Evaluator modules never
import `principia.evidence` and never register themselves, so the set of built-in
evaluators is fixed at import time and an evidence record can only select from it.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from .bell_ch import evaluate_bell_ch

if TYPE_CHECKING:
    from collections.abc import Mapping

    from ..evidence import Evaluator

BUILTIN_EVALUATORS: "Mapping[str, Evaluator]" = {
    "principia.evaluators.bell_ch": evaluate_bell_ch,
}

__all__ = ["BUILTIN_EVALUATORS"]
