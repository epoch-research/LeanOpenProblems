from __future__ import annotations

# Root of the Lake project, shared by both sandbox images (agent + scorer).
PROJECT = "/workspace/leanproject"

# The agent's source directory: only this is ingested by the scorer
SUBMISSION_DIR = f"{PROJECT}/Submission"

# The entry module holding the conjecture's defs + target theorem
ENTRY_REL = "Submission/Spec.lean"
ENTRY_PATH = f"{PROJECT}/{ENTRY_REL}"

# Where a task's optional attachment (``apn/data/attachments/<name>/``, see
# ``apn.dataset.with_attachments``) is copied in the agent's sandbox. Outside
# the Lake project, so lake never sees it and it cannot be imported.
ATTACHMENTS_DIR = "/workspace/attachments"
