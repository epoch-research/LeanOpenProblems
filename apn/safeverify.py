"""SafeVerify: validate a candidate sketch against its specification.

The paper validates every episode's output with "SafeVerify", which "checks the
proof against the theorem specification and guards against environment exploits
(e.g., axiom injection)". Concretely, validation here has three parts:

1. **Compiles** -- the Lean file has no error diagnostics.
2. **Statement preserved** -- nothing outside the EVOLVE regions changed, so the
   agent cannot weaken or replace the target theorem. (EVOLVE-VALUE regions may
   legitimately change a value, including a truth value, so changes there are
   allowed by design.)
3. **No axiom injection** -- the target declarations depend only on permitted
   axioms. Lean's standard axioms are allowed; ``sorryAx`` is tolerated *only*
   while the proof still contains ``sorry`` (an incomplete sketch), and any other
   axiom (e.g. a user-declared ``axiom cheat : False``) fails validation.

A sketch *passes validation* if all three hold allowing for remaining ``sorry``;
it is a *complete proof* if, additionally, it is ``sorry``-free and does not use
``sorryAx``.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from apn.sketch import ProofSketch, SketchParseError
from apn.verifier.base import LeanVerifier

# Lean's standard axioms, always permitted.
DEFAULT_ALLOWED_AXIOMS: frozenset[str] = frozenset(
    {"propext", "Classical.choice", "Quot.sound"}
)

SORRY_AX = "sorryAx"


@dataclass(frozen=True)
class IntegrityResult:
    ok: bool
    reason: str | None = None


def check_statement_integrity(
    original: ProofSketch, candidate: ProofSketch
) -> IntegrityResult:
    """Verify the candidate changed only inside EVOLVE regions.

    Both sketches must expose the same frozen skeleton (identical text outside
    editable regions, and identical marker placement).
    """
    try:
        original_skeleton = original.skeleton()
        candidate_skeleton = candidate.skeleton()
    except SketchParseError as exc:
        return IntegrityResult(
            ok=False, reason=f"EVOLVE markers are malformed: {exc}"
        )
    if original_skeleton != candidate_skeleton:
        return IntegrityResult(
            ok=False,
            reason=(
                "The code outside the EVOLVE regions changed (or an EVOLVE "
                "marker moved). The target theorem statement and surrounding "
                "context must remain exactly as provided."
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

    ``sorryAx`` is permitted only when ``allow_sorry_ax`` is set (i.e. the sketch
    legitimately still contains ``sorry``).
    """
    permitted = set(allowed)
    if allow_sorry_ax:
        permitted.add(SORRY_AX)
    disallowed = sorted({a for a in axioms_used if a not in permitted})
    if disallowed:
        return IntegrityResult(
            ok=False,
            reason="Disallowed axioms detected: " + ", ".join(disallowed),
        )
    return IntegrityResult(ok=True)


@dataclass(frozen=True)
class ValidationVerdict:
    """The full SafeVerify outcome for a candidate sketch."""

    compiles: bool
    statement_preserved: bool
    has_sorry: bool
    uses_sorry_ax: bool
    disallowed_axioms: tuple[str, ...]
    feedback: str

    @property
    def passes_validation(self) -> bool:
        """Safe to keep/admit: compiles, statement intact, no injected axioms.

        May still contain ``sorry`` (an incomplete-but-honest sketch).
        """
        return (
            self.compiles
            and self.statement_preserved
            and not self.disallowed_axioms
        )

    @property
    def is_complete_proof(self) -> bool:
        """A genuine, complete, ``sorry``-free proof of the target."""
        return (
            self.passes_validation
            and not self.has_sorry
            and not self.uses_sorry_ax
        )


async def safe_verify(
    verifier: LeanVerifier,
    original: ProofSketch,
    candidate: ProofSketch,
    target_declarations: Sequence[str],
    *,
    allowed_axioms: frozenset[str] = DEFAULT_ALLOWED_AXIOMS,
) -> ValidationVerdict:
    """Run the full validation pipeline on ``candidate``.

    ``target_declarations`` are the theorem names whose axioms are inspected
    (typically the single target theorem).
    """
    integrity = check_statement_integrity(original, candidate)

    compiled = await verifier.compile(candidate.text)
    feedback_parts: list[str] = []

    if compiled.system_error is not None:
        return ValidationVerdict(
            compiles=False,
            statement_preserved=integrity.ok,
            has_sorry=candidate.contains_sorry(),
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

    # Only inspect axioms when the file compiles and the statement is intact;
    # otherwise the axiom query is meaningless or impossible.
    if compiled.ok and integrity.ok and target_declarations:
        axiom_result = await verifier.print_axioms(
            candidate.text, target_declarations
        )
        if axiom_result.error is not None:
            feedback_parts.append(f"Axiom check failed: {axiom_result.error}")
        else:
            used = axiom_result.all_axioms()
            uses_sorry_ax = SORRY_AX in used
            # A complete proof must not use sorryAx; an incomplete one may.
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
