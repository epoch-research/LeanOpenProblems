"""Lean verification: the interface plus its implementations.

The agent's only source of ground truth about a proof is the Lean compiler. A
:class:`~apn.verifier.base.LeanVerifier` compiles sketch source, reports
diagnostics, and prints the axioms a declaration depends on (for the SafeVerify
axiom guard). The real implementation runs Lean 4 + Mathlib + Pantograph inside
an Inspect sandbox; a lightweight in-process fake is provided for testing agent
logic without the toolchain.
"""

from apn.verifier.base import (
    AxiomResult,
    CompileResult,
    Diagnostic,
    LeanVerifier,
    Severity,
)

__all__ = [
    "AxiomResult",
    "CompileResult",
    "Diagnostic",
    "LeanVerifier",
    "Severity",
]
