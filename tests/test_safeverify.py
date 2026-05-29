"""Tests for SafeVerify integrity, axiom guarding, and the full pipeline."""

from __future__ import annotations

from typing import Sequence

from apn.safeverify import (
    DEFAULT_ALLOWED_AXIOMS,
    check_axioms,
    check_statement_integrity,
    safe_verify,
)
from apn.sketch import ProofSketch
from apn.verifier.base import AxiomResult, CompileResult, Diagnostic
from apn.verifier.fake import FakeVerifier

ORIGINAL = """\
import Mathlib
theorem tgt : 1 + 1 = 2 := by
-- EVOLVE-BLOCK-START
  sorry
-- EVOLVE-BLOCK-END
"""


def _with_body(body: str) -> ProofSketch:
    return ProofSketch(
        "import Mathlib\n"
        "theorem tgt : 1 + 1 = 2 := by\n"
        "-- EVOLVE-BLOCK-START\n"
        f"{body}\n"
        "-- EVOLVE-BLOCK-END\n"
    )


def test_integrity_ok_when_only_block_changes() -> None:
    result = check_statement_integrity(ProofSketch(ORIGINAL), _with_body("  rfl"))
    assert result.ok


def test_integrity_fails_when_statement_changes() -> None:
    tampered = ProofSketch(
        "import Mathlib\n"
        "theorem tgt : 1 + 1 = 3 := by\n"  # statement weakened
        "-- EVOLVE-BLOCK-START\n"
        "  rfl\n"
        "-- EVOLVE-BLOCK-END\n"
    )
    result = check_statement_integrity(ProofSketch(ORIGINAL), tampered)
    assert not result.ok
    assert result.reason is not None


def test_check_axioms_allows_standard() -> None:
    assert check_axioms(sorted(DEFAULT_ALLOWED_AXIOMS), allow_sorry_ax=False).ok


def test_check_axioms_rejects_injected() -> None:
    result = check_axioms(["propext", "cheat"], allow_sorry_ax=False)
    assert not result.ok
    assert "cheat" in (result.reason or "")


def test_check_axioms_sorry_ax_conditional() -> None:
    assert not check_axioms(["sorryAx"], allow_sorry_ax=False).ok
    assert check_axioms(["sorryAx"], allow_sorry_ax=True).ok


async def test_safe_verify_complete_proof() -> None:
    verdict = await safe_verify(
        FakeVerifier(), ProofSketch(ORIGINAL), _with_body("  rfl"), ["tgt"]
    )
    assert verdict.passes_validation
    assert verdict.is_complete_proof


async def test_safe_verify_incomplete_passes_but_not_complete() -> None:
    verdict = await safe_verify(
        FakeVerifier(), ProofSketch(ORIGINAL), _with_body("  sorry"), ["tgt"]
    )
    assert verdict.passes_validation
    assert not verdict.is_complete_proof
    assert verdict.has_sorry


async def test_safe_verify_rejects_tampered_statement() -> None:
    tampered = ProofSketch(
        "import Mathlib\ntheorem tgt : True := by\n"
        "-- EVOLVE-BLOCK-START\n  trivial\n-- EVOLVE-BLOCK-END\n"
    )
    verdict = await safe_verify(
        FakeVerifier(), ProofSketch(ORIGINAL), tampered, ["tgt"]
    )
    assert not verdict.statement_preserved
    assert not verdict.passes_validation


async def test_safe_verify_rejects_axiom_injection() -> None:
    # The cheat stays inside the EVOLVE block, so statement integrity holds and
    # only the axiom guard should reject it.
    cheat = _with_body("  exact test_axiom")

    def axioms_fn(code: str, decls: Sequence[str]) -> AxiomResult:
        return AxiomResult(axioms={d: ("propext", "test_axiom") for d in decls})

    verdict = await safe_verify(
        FakeVerifier(axioms_fn=axioms_fn), ProofSketch(ORIGINAL), cheat, ["tgt"]
    )
    # Statement is preserved, but an injected axiom must fail validation.
    assert verdict.statement_preserved
    assert not verdict.passes_validation
    assert "test_axiom" in verdict.disallowed_axioms


async def test_safe_verify_compile_error_blocks_validation() -> None:
    def compile_fn(code: str) -> CompileResult:
        return CompileResult(
            diagnostics=(Diagnostic("error", "unknown identifier 'foo'", 4),),
            has_sorry=False,
        )

    verdict = await safe_verify(
        FakeVerifier(compile_fn=compile_fn),
        ProofSketch(ORIGINAL),
        _with_body("  foo"),
        ["tgt"],
    )
    assert not verdict.compiles
    assert not verdict.passes_validation
    assert "unknown identifier" in verdict.feedback
