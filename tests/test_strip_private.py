"""Unit tests for ``scripts.isolation.strip_private`` (plan §3.3, comparator#58).

The strip removes the ``private`` visibility modifier from isolated specs so
declaration names do not mangle with the Lean *module* name
(``_private.<Module>.0.<name>``), which under Comparator's Challenge/Solution
split falsely rejects faithful submissions. These are the pure-text cases; the
authoritative guarantees (the stripped specs still compile, statements
unchanged) are the container isolation suites.
"""

from __future__ import annotations

import pytest

from scripts.isolation import strip_private

# One case per modifier shape present in the committed data (see the census in
# scripts/comparator_drift.py): def, noncomputable def, instance, abbrev.
_SHAPES = [
    ("private def helper : Nat := 1\n", "def helper : Nat := 1\n"),
    (
        "private noncomputable def a_val : ℕ → ℕ := sorry\n",
        "noncomputable def a_val : ℕ → ℕ := sorry\n",
    ),
    (
        "private instance (n : ℕ) : Decidable (P n) := inferInstance\n",
        "instance (n : ℕ) : Decidable (P n) := inferInstance\n",
    ),
    ("private abbrev PQS := PowerSeries ℚ\n", "abbrev PQS := PowerSeries ℚ\n"),
]


@pytest.mark.parametrize(("src", "expected"), _SHAPES)
def test_strips_each_modifier_shape(src: str, expected: str) -> None:
    assert strip_private(src) == expected


def test_idempotent_and_noop_without_private() -> None:
    src = "def helper : Nat := 1\n\ntheorem t : helper = 1 := rfl\n"
    assert strip_private(src) == src
    stripped = strip_private(_SHAPES[0][0])
    assert strip_private(stripped) == stripped


def test_prose_mentions_are_untouched() -> None:
    # `private` in comments, doc comments, and strings is not a modifier.
    src = (
        "/-- A `private` def would mangle. -/\n"
        "def helper : Nat := 1\n"
        "-- private def commented_out : Nat := 2\n"
        'def s : String := "private def in a string"\n'
    )
    assert strip_private(src) == src


def test_unhandled_private_shape_raises() -> None:
    # `open private` (or any shape the modifier regex does not account for)
    # must fail loudly rather than silently surviving into a committed spec.
    with pytest.raises(ValueError, match="unhandled 'private'"):
        strip_private("open private foo from Bar in\ndef x := foo\n")
