#!/usr/bin/env python3
"""Sandbox-side SafeVerify runner.

Runs *inside* the Lean sandbox. Reads a JSON request from stdin describing the
target spec and the submitted proof, compiles both to ``.olean`` files, and runs
the vendored ``safe_verify`` executable to check the submission against the
target (kernel-level statement integrity + axiom guard). Prints a JSON result.

    request  : {"target": "<lean source>", "submission": "<lean source>"}
    response : {"ok": bool, "stage": str, "detail": str}

``stage`` is where a failure occurred: ``compile_target``,
``compile_submission``, or ``safeverify`` (and ``ok`` reflects the verdict).
"""

from __future__ import annotations

import json
import os
import subprocess
import sys

PROJECT = os.environ.get("APN_LEAN_PROJECT", "/workspace/leanproject")
SAFE_VERIFY_BIN = os.environ.get(
    "APN_SAFEVERIFY_BIN", "/opt/apn/safeverify/.lake/build/bin/safe_verify"
)
# The Lean files must live inside the lake project root for `lake env lean -o`.
SCORE_DIR = os.path.join(PROJECT, "_apn_score")
_MAX_DETAIL = 6000


def _run(cmd: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=PROJECT, capture_output=True, text=True)


def _compile(stem: str, source: str) -> tuple[str, subprocess.CompletedProcess[str]]:
    os.makedirs(SCORE_DIR, exist_ok=True)
    lean_path = os.path.join(SCORE_DIR, f"{stem}.lean")
    olean_path = os.path.join(SCORE_DIR, f"{stem}.olean")
    with open(lean_path, "w") as handle:
        handle.write(source)
    result = _run(["lake", "env", "lean", "-o", olean_path, lean_path])
    return olean_path, result


def _emit(ok: bool, stage: str, detail: str) -> None:
    print(json.dumps({"ok": ok, "stage": stage, "detail": detail[-_MAX_DETAIL:]}))


def main() -> int:
    request = json.load(sys.stdin)
    target = request["target"]
    submission = request["submission"]

    target_olean, target_result = _compile("target", target)
    if target_result.returncode != 0:
        _emit(False, "compile_target", target_result.stderr)
        return 0

    submission_olean, submission_result = _compile("submission", submission)
    if submission_result.returncode != 0:
        _emit(False, "compile_submission", submission_result.stderr)
        return 0

    verify = _run(["lake", "env", SAFE_VERIFY_BIN, target_olean, submission_olean])
    detail = (verify.stdout + "\n" + verify.stderr).strip()
    _emit(verify.returncode == 0, "safeverify", detail)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
