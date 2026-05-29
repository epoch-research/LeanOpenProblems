"""The proof-sketch data model.

A *proof sketch* (the paper's term) is a Lean source file consisting of a target
theorem with ``sorry`` in place of a proof, plus supporting definitions and
imports. The user annotates the file with markers delimiting the regions the
agent is allowed to modify:

* ``-- EVOLVE-BLOCK-START`` / ``-- EVOLVE-BLOCK-END`` enclose code the agent may
  rewrite freely (helper lemmas, definitions, proof steps).
* ``-- EVOLVE-VALUE-START`` / ``-- EVOLVE-VALUE-END`` enclose an expression
  (e.g. a parameter) whose *value* the agent may change.

Everything outside these regions -- crucially, the target theorem statement --
is frozen; the agent edits the file with Inspect's ``text_editor`` tool, and
edits that touch anything outside the editable regions are rejected by
SafeVerify (see :mod:`apn.safeverify`).

This module is pure text manipulation with no Lean dependency; authoritative
``sorry`` detection comes from the Lean compiler (see :mod:`apn.verifier`). The
:meth:`ProofSketch.contains_sorry` heuristic here is a cheap, comment-aware
pre-check.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from enum import Enum

EVOLVE_BLOCK_START = "-- EVOLVE-BLOCK-START"
EVOLVE_BLOCK_END = "-- EVOLVE-BLOCK-END"
EVOLVE_VALUE_START = "-- EVOLVE-VALUE-START"
EVOLVE_VALUE_END = "-- EVOLVE-VALUE-END"

# A marker is a comment line (optionally indented) consisting solely of the
# marker token.
_MARKER_RE = re.compile(
    r"^[ \t]*-- EVOLVE-(?P<kind>BLOCK|VALUE)-(?P<side>START|END)[ \t]*$",
    re.MULTILINE,
)

# `sorry` as a standalone token (Lean identifiers may contain letters, digits,
# underscores and primes). This deliberately does not match `sorryAx`.
_SORRY_RE = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")

# Sentinel substituted for editable-region content when computing a sketch's
# frozen "skeleton" for integrity comparison. Uses control characters that
# cannot occur in Lean source.
_EVOLVE_SENTINEL = "\x00EVOLVE\x00"


class EvolveKind(Enum):
    BLOCK = "BLOCK"
    VALUE = "VALUE"


class SketchParseError(ValueError):
    """Raised when EVOLVE markers are malformed (unbalanced or interleaved)."""


@dataclass(frozen=True)
class EvolveRegion:
    """An editable region, identified by the character span of its content.

    ``content_start`` is the offset of the first character after the START
    marker line's newline; ``content_end`` is the offset at which the END marker
    line begins. The marker lines themselves are *not* part of the content and
    are not editable.
    """

    kind: EvolveKind
    content_start: int
    content_end: int


@dataclass(frozen=True)
class ProofSketch:
    """A Lean proof sketch: the full source text plus EVOLVE-region structure."""

    text: str

    @property
    def regions(self) -> list[EvolveRegion]:
        """Editable regions, in document order.

        Raises:
            SketchParseError: if markers are unbalanced or improperly nested.
        """
        return _parse_regions(self.text)

    def contains_sorry(self) -> bool:
        """Heuristic check for a remaining ``sorry`` token, ignoring comments.

        Authoritative detection is done by the Lean compiler; this is a fast
        pre-check that avoids false positives from the word "sorry" appearing in
        natural-language comments.
        """
        return _SORRY_RE.search(strip_comments(self.text)) is not None

    def skeleton(self) -> str:
        """The frozen part of the file, with editable content blanked out.

        Two sketches with identical skeletons differ only inside their editable
        regions; this is the basis of the statement-integrity check.
        """
        regions = self.regions
        if not regions:
            return self.text
        out: list[str] = []
        cursor = 0
        for region in regions:
            out.append(self.text[cursor : region.content_start])
            out.append(_EVOLVE_SENTINEL)
            cursor = region.content_end
        out.append(self.text[cursor:])
        return "".join(out)


def _parse_regions(text: str) -> list[EvolveRegion]:
    """Pair up EVOLVE markers into regions.

    BLOCK and VALUE regions may not overlap or nest. Markers must be balanced.
    """
    regions: list[EvolveRegion] = []
    open_kind: EvolveKind | None = None
    content_start = 0

    for match in _MARKER_RE.finditer(text):
        kind = EvolveKind(match.group("kind"))
        side = match.group("side")
        if side == "START":
            if open_kind is not None:
                raise SketchParseError(
                    f"Found EVOLVE-{kind.value}-START while an "
                    f"EVOLVE-{open_kind.value} region was still open."
                )
            open_kind = kind
            # Content begins after this marker line (and its newline, if any).
            line_end = text.find("\n", match.end())
            content_start = len(text) if line_end == -1 else line_end + 1
        else:  # END
            if open_kind is None:
                raise SketchParseError(
                    f"Found EVOLVE-{kind.value}-END with no matching START."
                )
            if open_kind != kind:
                raise SketchParseError(
                    f"EVOLVE-{kind.value}-END does not match the open "
                    f"EVOLVE-{open_kind.value} region."
                )
            regions.append(EvolveRegion(kind, content_start, match.start()))
            open_kind = None

    if open_kind is not None:
        raise SketchParseError(
            f"EVOLVE-{open_kind.value}-START is missing its END marker."
        )
    return regions


def strip_comments(code: str) -> str:
    """Replace Lean comments with spaces (preserving offsets is not required).

    Handles ``--`` line comments, nested ``/- -/`` block comments, and string
    literals (so ``--`` inside a string is not treated as a comment). Comment
    bodies are dropped; this is used only for the ``sorry`` heuristic.
    """
    out: list[str] = []
    i = 0
    n = len(code)
    block_depth = 0
    while i < n:
        ch = code[i]
        two = code[i : i + 2]
        if block_depth > 0:
            if two == "/-":
                block_depth += 1
                i += 2
            elif two == "-/":
                block_depth -= 1
                i += 2
            else:
                i += 1
            continue
        if two == "/-":
            block_depth += 1
            i += 2
        elif two == "--":
            nl = code.find("\n", i)
            i = n if nl == -1 else nl
        elif ch == '"':
            out.append(ch)
            i += 1
            while i < n:
                out.append(code[i])
                if code[i] == "\\" and i + 1 < n:
                    out.append(code[i + 1])
                    i += 2
                    continue
                if code[i] == '"':
                    i += 1
                    break
                i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)
