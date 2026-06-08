"""Shared filesystem layout for the agent's submission.

The agent authors its proof as a single Lean file -- the entry module
``Submission/Spec.lean`` (module name ``Submission.Spec``) under the Lake
project's ``Submission/`` directory -- holding the conjecture's defs + target
theorem and a complete proof. The proof must stay in this one file: the checker
compiles it standalone, so an ``import Submission.…`` of a helper module does
not resolve (see ``apn.checker``).

These constants are the single source of truth for *where* that file lives, so
the solver (writes the entry file), the scorer (reads it back as a tar, stages
it for verification), and the checker (compiles target + submission, runs
``safe_verify``) all agree without importing one another -- the scorer
previously reached into the agent module for ``PROOF_PATH``; these constants
break that coupling.
"""

from __future__ import annotations

# Root of the Lake project, shared by both sandbox images (agent + scorer).
PROJECT = "/workspace/leanproject"

# The agent's source directory: only this is ingested by the scorer (never the
# lakefile, Mathlib, or FormalConjectures).
SUBMISSION_DIR = f"{PROJECT}/Submission"

# The entry module holding the conjecture's defs + target theorem: its path
# relative to the project root and the corresponding absolute path. The path is
# load-bearing: the checker compiles BOTH the trusted target spec and the
# submission at this same path so they get the same module name (Submission.Spec),
# preserving private/mangled name matching (see apn.checker).
ENTRY_REL = "Submission/Spec.lean"
ENTRY_PATH = f"{PROJECT}/{ENTRY_REL}"
