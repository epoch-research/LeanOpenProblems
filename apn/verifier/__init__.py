"""Lean verification: the compiler interface used for in-loop agent feedback.

A :class:`~apn.verifier.base.LeanVerifier` compiles Lean source and reports
diagnostics plus whether it uses ``sorry``. The real implementation
(:class:`~apn.verifier.pantograph.PantographVerifier`) runs Lean 4 + Mathlib +
Pantograph inside an Inspect sandbox. Final, authoritative validation is done
separately by SafeVerify (see :mod:`apn.checker`).
"""

from apn.verifier.base import CompileResult, Diagnostic, LeanVerifier, Severity

__all__ = [
    "CompileResult",
    "Diagnostic",
    "LeanVerifier",
    "Severity",
]
