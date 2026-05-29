"""An in-process fake :class:`LeanVerifier` for tests and offline development.

This does not run Lean. It is driven by caller-supplied functions so tests can
script exact compiler/axiom behaviour, and it ships with a simple heuristic
default that is good enough to exercise the agent loop without the toolchain.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Callable, Sequence

from apn.verifier.base import AxiomResult, CompileResult, Diagnostic

CompileFn = Callable[[str], CompileResult]
AxiomsFn = Callable[[str, Sequence[str]], AxiomResult]

# `sorry` as a standalone token (matches the daemon's detection closely enough
# for an in-process fake).
_SORRY_RE = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")


def _default_compile(code: str) -> CompileResult:
    """A crude stand-in for the compiler.

    Treats a line containing ``-- FAKE-ERROR`` as an error diagnostic, and
    detects ``sorry`` via the sketch heuristic. Everything else "compiles".
    """
    diagnostics: list[Diagnostic] = []
    for lineno, line in enumerate(code.splitlines(), start=1):
        if "-- FAKE-ERROR" in line:
            diagnostics.append(
                Diagnostic("error", line.split("-- FAKE-ERROR", 1)[1].strip(), lineno)
            )
    has_sorry = bool(_SORRY_RE.search(code))
    if has_sorry:
        diagnostics.append(Diagnostic("warning", "declaration uses 'sorry'"))
    return CompileResult(diagnostics=tuple(diagnostics), has_sorry=has_sorry)


def _default_axioms(code: str, declarations: Sequence[str]) -> AxiomResult:
    """Report standard axioms, adding ``sorryAx`` when ``sorry`` is present and
    surfacing any ``axiom <name>`` the code declares (a crude injection model)."""
    base = ["Classical.choice", "propext", "Quot.sound"]
    if _SORRY_RE.search(code):
        base.append("sorryAx")
    injected = re.findall(r"^\s*axiom\s+(\w+)", code, re.MULTILINE)
    used = tuple(sorted(set(base + injected)))
    return AxiomResult(axioms={decl: used for decl in declarations})


@dataclass
class FakeVerifier:
    """A scriptable in-process verifier implementing the ``LeanVerifier`` protocol."""

    compile_fn: CompileFn = _default_compile
    axioms_fn: AxiomsFn = _default_axioms
    compile_calls: list[str] = field(default_factory=list)

    async def compile(self, code: str) -> CompileResult:
        self.compile_calls.append(code)
        return self.compile_fn(code)

    async def print_axioms(
        self, code: str, declarations: Sequence[str]
    ) -> AxiomResult:
        return self.axioms_fn(code, declarations)
