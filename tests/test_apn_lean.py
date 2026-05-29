"""Tests for the sandbox-side daemon's pure parsing helpers.

``apn/lean/apn_lean.py`` is a standalone in-container script (not an importable
package module), so it is loaded by path. Only its pure, stdlib-only helpers are
exercised here; the PyPantograph integration is validated against the real
sandbox.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
from types import ModuleType

_SCRIPT = Path(__file__).resolve().parent.parent / "apn" / "lean" / "apn_lean.py"


def _load() -> ModuleType:
    spec = importlib.util.spec_from_file_location("apn_lean", _SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


apn_lean = _load()


def test_normalize_severity() -> None:
    assert apn_lean.normalize_severity("error") == "error"
    assert apn_lean.normalize_severity("warning") == "warning"
    assert apn_lean.normalize_severity("information") == "info"
    assert apn_lean.normalize_severity("weird") == "info"


def test_summarize_compile_clean() -> None:
    result = apn_lean.summarize_compile([])
    assert result["ok"] is True
    assert result["has_sorry"] is False
    assert result["system_error"] is None


def test_summarize_compile_error_and_sorry() -> None:
    messages = [
        ("error", "unknown identifier 'foo'", 4, 2),
        ("warning", "declaration uses 'sorry'", 3, 0),
    ]
    result = apn_lean.summarize_compile(messages)
    assert result["ok"] is False
    assert result["has_sorry"] is True
    assert result["diagnostics"][0]["severity"] == "error"
    assert result["diagnostics"][0]["line"] == 4


def test_sorry_detection_handles_backticks_and_quotes() -> None:
    # Lean v4.29.1 uses backticks; older toolchains use single quotes.
    assert apn_lean.message_indicates_sorry("declaration uses `sorry`")
    assert apn_lean.message_indicates_sorry("declaration uses 'sorry'")
    assert not apn_lean.message_indicates_sorry("this proof is not sorry-based")


def test_parse_axioms_depends() -> None:
    messages = [
        ("information", "'tgt' depends on axioms: [propext, Classical.choice, Quot.sound]"),
    ]
    result = apn_lean.parse_axiom_messages(messages, ["tgt"])
    assert result["axioms"]["tgt"] == ["propext", "Classical.choice", "Quot.sound"]
    assert result["error"] is None


def test_parse_axioms_with_sorry() -> None:
    messages = [("information", "'tgt' depends on axioms: [sorryAx]")]
    result = apn_lean.parse_axiom_messages(messages, ["tgt"])
    assert result["axioms"]["tgt"] == ["sorryAx"]


def test_parse_axioms_none() -> None:
    messages = [("information", "'rfl_thm' does not depend on any axioms")]
    result = apn_lean.parse_axiom_messages(messages, ["rfl_thm"])
    assert result["axioms"]["rfl_thm"] == []


def test_parse_axioms_unknown_declaration_reports_error() -> None:
    messages = [("error", "unknown identifier 'ghost'")]
    result = apn_lean.parse_axiom_messages(messages, ["ghost"])
    assert result["axioms"] == {}
    assert result["error"] is not None
    assert "ghost" in result["error"]
