"""The Lean verifier interface and its result types."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Literal, Protocol, Sequence, runtime_checkable

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


@dataclass(frozen=True)
class AxiomResult:
    """The axioms each requested declaration depends on.

    ``axioms`` maps a declaration name to the sorted tuple of axiom names it
    transitively uses. ``error`` is set if the axiom query could not run (e.g.
    the file did not compile, or a declaration was not found).
    """

    axioms: dict[str, tuple[str, ...]] = field(default_factory=dict)
    error: str | None = None

    def all_axioms(self) -> set[str]:
        result: set[str] = set()
        for used in self.axioms.values():
            result.update(used)
        return result


@runtime_checkable
class LeanVerifier(Protocol):
    """Compiles Lean source and inspects the axioms it relies on."""

    async def compile(self, code: str) -> CompileResult:
        """Compile ``code`` and report diagnostics and whether it uses sorry."""
        ...

    async def print_axioms(
        self, code: str, declarations: Sequence[str]
    ) -> AxiomResult:
        """Return the axioms each named declaration in ``code`` depends on."""
        ...
