"""Shared filesystem layout for the multi-module submission.

The agent now authors its proof as a small Lean *project subtree* rather than a
single file: a registered source root ``Submission/`` under the Lake project,
with the conjecture's defs + target theorem in the entry module
``Submission/Spec.lean`` (module name ``Submission.Spec``). Helpers live in
sibling modules (``Submission/Helpers/Foo.lean`` -> ``Submission.Helpers.Foo``)
that the entry file ``import``s natively.

These constants are the single source of truth for *where* that subtree lives,
so the solver (writes the entry file, reads the tree back), the scorer (ingests
the tree, stages it for verification), and the checker (compiles target +
submission, runs ``safe_verify``) all agree without importing one another -- the
scorer previously reached into the agent module for ``PROOF_PATH``; these
constants break that coupling. ``Submission/`` is registered as a lean_lib in the
project's lakefile (see ``apn/lean/Dockerfile``) so ``import Submission.…``
resolves and ``lake build Submission.Spec`` builds the helper graph.
"""

from __future__ import annotations

# Root of the Lake project, shared by both sandbox images (agent + scorer).
PROJECT = "/workspace/leanproject"

# The agent's source root: only this subtree is ingested by the scorer (never
# the lakefile, Mathlib, or FormalConjectures). Registered as the ``Submission``
# lean_lib (globs = ["Submission.+"]) in the project lakefile.
SUBMISSION_DIR = f"{PROJECT}/Submission"

# The entry module holding the conjecture's defs + target theorem. Path relative
# to the project root, absolute path, and the Lean module name Lean derives from
# that path. The module name is load-bearing: the checker compiles the trusted
# target spec *at this same path* so it gets the same module name as the
# submission, preserving private/mangled name matching (see apn.checker).
ENTRY_REL = "Submission/Spec.lean"
ENTRY_PATH = f"{PROJECT}/{ENTRY_REL}"
ENTRY_MODULE = "Submission.Spec"
