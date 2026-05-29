"""Validate a candidate proof against its specification.

With the EVOLVE-marker machinery removed, the anti-cheat lives entirely here (and
in the scorer that calls it). A candidate proof is valid only if:

1. **Compiles** -- the Lean file has no error diagnostics.
2. **Statement preserved** -- the target theorem's signature (everything up to
   the proof's ``:=``) still appears verbatim, so the agent cannot weaken or
   replace the goal (e.g. turn it into ``: True``).
3. **No axiom injection** -- the target declarations depend only on permitted
   axioms. ``sorryAx`` is tolerated only while a ``sorry`` legitimately remains.

A candidate *passes validation* if all three hold (allowing a remaining
``sorry``); it is a *complete proof* if additionally ``sorry``-free.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Sequence

from apn.verifier.base import LeanVerifier

DEFAULT_ALLOWED_AXIOMS: frozenset[str] = frozenset(
    {"propext", "Classical.choice", "Quot.sound"}
)

SORRY_AX = "sorryAx"


@dataclass(frozen=True)
class IntegrityResult:
    ok: bool
    reason: str | None = None


def extract_statement(text: str, decl: str) -> str | None:
    """Return the source of ``decl``'s signature: from ``theorem``/``lemma`` up
    to and including the ``:=`` that begins its proof, or ``None`` if not found.
    """
    match = re.search(rf"\b(?:theorem|lemma)\s+{re.escape(decl)}\b", text)
    if match is None:
        return None
    end = text.find(":=", match.start())
    if end == -1:
        return None
    return text[match.start() : end + 2]


def check_statement_preserved(
    original: str, candidate: str, declarations: Sequence[str]
) -> IntegrityResult:
    """Verify each target declaration's signature is unchanged in ``candidate``."""
    for decl in declarations:
        statement = extract_statement(original, decl)
        if statement is None:
            # Could not locate the original signature; nothing to compare.
            continue
        if statement not in candidate:
            return IntegrityResult(
                ok=False,
                reason=(
                    f"The statement of `{decl}` was changed. The theorem signature "
                    "must remain exactly as provided; only the proof may change."
                ),
            )
    return IntegrityResult(ok=True)


def check_axioms(
    axioms_used: Sequence[str],
    *,
    allow_sorry_ax: bool,
    allowed: frozenset[str] = DEFAULT_ALLOWED_AXIOMS,
) -> IntegrityResult:
    """Flag any axiom outside the permitted set.

    ``sorryAx`` is permitted only when ``allow_sorry_ax`` is set.
    """
    permitted = set(allowed)
    if allow_sorry_ax:
        permitted.add(SORRY_AX)
    disallowed = sorted({a for a in axioms_used if a not in permitted})
    if disallowed:
        return IntegrityResult(
            ok=False, reason="Disallowed axioms detected: " + ", ".join(disallowed)
        )
    return IntegrityResult(ok=True)


@dataclass(frozen=True)
class ValidationVerdict:
    compiles: bool
    statement_preserved: bool
    has_sorry: bool
    uses_sorry_ax: bool
    disallowed_axioms: tuple[str, ...]
    feedback: str

    @property
    def passes_validation(self) -> bool:
        return (
            self.compiles
            and self.statement_preserved
            and not self.disallowed_axioms
        )

    @property
    def is_complete_proof(self) -> bool:
        return (
            self.passes_validation
            and not self.has_sorry
            and not self.uses_sorry_ax
        )


async def safe_verify(
    verifier: LeanVerifier,
    original: str,
    candidate: str,
    target_declarations: Sequence[str],
    *,
    allowed_axioms: frozenset[str] = DEFAULT_ALLOWED_AXIOMS,
) -> ValidationVerdict:
    """Run the full validation pipeline on ``candidate`` proof source."""
    integrity = check_statement_preserved(original, candidate, target_declarations)
    compiled = await verifier.compile(candidate)
    feedback_parts: list[str] = []

    if compiled.system_error is not None:
        return ValidationVerdict(
            compiles=False,
            statement_preserved=integrity.ok,
            has_sorry=False,
            uses_sorry_ax=False,
            disallowed_axioms=(),
            feedback=compiled.feedback(),
        )

    if not integrity.ok:
        assert integrity.reason is not None
        feedback_parts.append(integrity.reason)
    if not compiled.ok:
        feedback_parts.append(compiled.feedback())

    has_sorry = compiled.has_sorry
    uses_sorry_ax = False
    disallowed: tuple[str, ...] = ()

    if compiled.ok and integrity.ok and target_declarations:
        axiom_result = await verifier.print_axioms(candidate, target_declarations)
        if axiom_result.error is not None:
            feedback_parts.append(f"Axiom check failed: {axiom_result.error}")
        else:
            used = axiom_result.all_axioms()
            uses_sorry_ax = SORRY_AX in used
            axiom_check = check_axioms(
                sorted(used),
                allow_sorry_ax=has_sorry or uses_sorry_ax,
                allowed=allowed_axioms,
            )
            if not axiom_check.ok:
                assert axiom_check.reason is not None
                feedback_parts.append(axiom_check.reason)
                disallowed = tuple(
                    a
                    for a in sorted(used)
                    if a not in allowed_axioms and a != SORRY_AX
                )

    if not feedback_parts:
        feedback_parts.append(compiled.feedback())

    return ValidationVerdict(
        compiles=compiled.ok,
        statement_preserved=integrity.ok,
        has_sorry=has_sorry,
        uses_sorry_ax=uses_sorry_ax,
        disallowed_axioms=disallowed,
        feedback="\n\n".join(feedback_parts),
    )
