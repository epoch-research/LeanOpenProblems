"""Tests for SafeVerify: statement preservation, axiom guarding, pipeline."""

from __future__ import annotations

from typing import Sequence

from apn.safeverify import (
    DEFAULT_ALLOWED_AXIOMS,
    check_axioms,
    check_statement_preserved,
    extract_statement,
    safe_verify,
)
from apn.verifier.base import AxiomResult, CompileResult, Diagnostic
from apn.verifier.fake import FakeVerifier

ORIGINAL = "import Mathlib\ntheorem tgt : 1 + 1 = 2 := by\n  sorry\n"


def _proof(body: str) -> str:
    return f"import Mathlib\ntheorem tgt : 1 + 1 = 2 := by\n  {body}\n"


def test_extract_statement() -> None:
    assert extract_statement(ORIGINAL, "tgt") == "theorem tgt : 1 + 1 = 2 :="
    assert extract_statement(ORIGINAL, "missing") is None


def test_statement_preserved_ok() -> None:
    assert check_statement_preserved(ORIGINAL, _proof("norm_num"), ["tgt"]).ok


def test_statement_preserved_detects_change() -> None:
    tampered = "import Mathlib\ntheorem tgt : True := by\n  trivial\n"
    result = check_statement_preserved(ORIGINAL, tampered, ["tgt"])
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
    verdict = await safe_verify(FakeVerifier(), ORIGINAL, _proof("norm_num"), ["tgt"])
    assert verdict.passes_validation
    assert verdict.is_complete_proof


async def test_safe_verify_incomplete_passes_but_not_complete() -> None:
    verdict = await safe_verify(FakeVerifier(), ORIGINAL, _proof("sorry"), ["tgt"])
    assert verdict.passes_validation
    assert not verdict.is_complete_proof
    assert verdict.has_sorry


async def test_safe_verify_rejects_tampered_statement() -> None:
    tampered = "import Mathlib\ntheorem tgt : True := by\n  trivial\n"
    verdict = await safe_verify(FakeVerifier(), ORIGINAL, tampered, ["tgt"])
    assert not verdict.statement_preserved
    assert not verdict.passes_validation


async def test_safe_verify_rejects_axiom_injection() -> None:
    def axioms_fn(code: str, decls: Sequence[str]) -> AxiomResult:
        return AxiomResult(axioms={d: ("propext", "evil_axiom") for d in decls})

    verdict = await safe_verify(
        FakeVerifier(axioms_fn=axioms_fn), ORIGINAL, _proof("norm_num"), ["tgt"]
    )
    assert verdict.statement_preserved
    assert not verdict.passes_validation
    assert "evil_axiom" in verdict.disallowed_axioms


async def test_safe_verify_compile_error() -> None:
    def compile_fn(code: str) -> CompileResult:
        return CompileResult(
            diagnostics=(Diagnostic("error", "unknown identifier 'foo'", 3),),
            has_sorry=False,
        )

    verdict = await safe_verify(
        FakeVerifier(compile_fn=compile_fn), ORIGINAL, _proof("foo"), ["tgt"]
    )
    assert not verdict.compiles
    assert not verdict.passes_validation
    assert "unknown identifier" in verdict.feedback
