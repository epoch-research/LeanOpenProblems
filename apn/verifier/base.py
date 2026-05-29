"""The Lean verifier interface and its result types."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Protocol, runtime_checkable

Severity = Literal["error", "warning", "info"]


@dataclass(frozen=True)
class Diagnostic:
    """A single compiler message."""

    severity: Severity
    message: str
    start_line: int | None = None
    start_col: int | None = None

    def render(self) -> str:
        loc = ""
        if self.start_line is not None:
            loc = f"line {self.start_line}"
            if self.start_col is not None:
                loc += f", column {self.start_col}"
            loc = f" ({loc})"
        return f"{self.severity}{loc}: {self.message}"


@dataclass(frozen=True)
class CompileResult:
    """The outcome of compiling a Lean source file."""

    diagnostics: tuple[Diagnostic, ...] = ()
    has_sorry: bool = False
    # Set when the toolchain itself failed (timeout, sandbox error) rather than
    # the code being rejected. Such results should not be treated as a clean
    # compile or a clean failure.
    system_error: str | None = None

    @property
    def ok(self) -> bool:
        """True when the file compiled with no error-severity diagnostics."""
        return self.system_error is None and not any(
            d.severity == "error" for d in self.diagnostics
        )

    @property
    def errors(self) -> tuple[Diagnostic, ...]:
        return tuple(d for d in self.diagnostics if d.severity == "error")

    def feedback(self, max_chars: int = 8000) -> str:
        """Compiler feedback to return to the model, errors first.

        Truncated to ``max_chars`` so a wall of diagnostics cannot blow the
        context budget.
        """
        if self.system_error is not None:
            return f"System error during compilation: {self.system_error}"
        if not self.diagnostics:
            base = "The file compiled successfully with no messages."
            if self.has_sorry:
                base += " It still contains `sorry`."
            return base
        order = {"error": 0, "warning": 1, "info": 2}
        ordered = sorted(self.diagnostics, key=lambda d: order.get(d.severity, 3))
        rendered = "\n".join(d.render() for d in ordered)
        if len(rendered) > max_chars:
            rendered = rendered[:max_chars] + "\n... (feedback truncated)"
        return rendered


@runtime_checkable
class LeanVerifier(Protocol):
    """Compiles Lean source, reporting diagnostics and ``sorry`` usage.

    This is the in-loop compiler the proving agent talks to for feedback. The
    final, authoritative validation (statement integrity + axiom guard) is done
    separately by SafeVerify (see :mod:`apn.checker`), so the verifier does not
    need to inspect axioms itself.
    """

    async def compile(self, code: str) -> CompileResult:
        """Compile ``code`` and report diagnostics and whether it uses sorry."""
        ...
