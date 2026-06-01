"""Tests for the sandbox-side SafeVerify runner's pure classification helper.

``apn/lean/apn_safeverify.py`` is a standalone in-container script, loaded by
path. Only the pure ``classify_safeverify`` is exercised here; the real
``safe_verify`` exe is validated against the toolchain.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
from types import ModuleType

_SCRIPT = Path(__file__).resolve().parent.parent / "apn" / "lean" / "apn_safeverify.py"


def _load() -> ModuleType:
    spec = importlib.util.spec_from_file_location("apn_safeverify", _SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


apn_safeverify = _load()


def test_classify_pass() -> None:
    result = apn_safeverify.classify_safeverify(0, "SafeVerify check passed.")
    assert result == {"ok": True, "stage": "safeverify", "detail": "SafeVerify check passed."}


def test_classify_clean_check_failure() -> None:
    result = apn_safeverify.classify_safeverify(1, "SafeVerify check failed.")
    assert result["ok"] is False
    assert result["stage"] == "safeverify"


def test_classify_replay_rejection_is_incorrect_not_infra() -> None:
    # A replay-time throw (unsafe/partial/kernel-fail) exits nonzero before the
    # "check failed" marker -- it is a real rejection, not an infra failure.
    detail = "Replaying submission\nuncaught exception: unsafe constant fakeProof detected"
    result = apn_safeverify.classify_safeverify(1, detail)
    assert result["ok"] is False
    assert "system_error" not in result


def test_classify_signal_kill_is_system_error() -> None:
    # Negative return code = killed by a signal (e.g. OOM SIGKILL) -> infra.
    result = apn_safeverify.classify_safeverify(-9, "Replaying submission")
    assert "system_error" in result
    assert "signal 9" in result["system_error"]
