from __future__ import annotations

# Root of the Lake project, shared by both sandbox images (agent + scorer).
PROJECT = "/workspace/leanproject"

# The agent's submission directory. Its Lean module tree is what the scorer
# ingests (apn.filetree) and the checker stages for verification (apn.checker).
SUBMISSION_DIR = f"{PROJECT}/Submission"
# The directory is registered as a Lake library of this name in both images
# (apn/lean/Dockerfile), so `Submission/Foo/Bar.lean` is the module
# `Submission.Foo.Bar` -- in the agent's sandbox and in the checker's alike.
SUBMISSION_LIB = "Submission"

# The entry module holding the conjecture's defs + target theorem
ENTRY_REL = "Submission/Spec.lean"
ENTRY_PATH = f"{PROJECT}/{ENTRY_REL}"
ENTRY_MODULE = f"{SUBMISSION_LIB}.Spec"
