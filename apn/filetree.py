"""Collecting and displaying the agent's ``Submission/`` directory.

The agent's submission is the Lean module tree under ``Submission/``: the entry
module ``Submission/Spec.lean`` plus any helper modules it imports (see
:mod:`apn.checker` for exactly what of the directory counts).
:func:`read_submission_tar` tars ``Submission/`` from the sandbox and returns the
bytes.

The tar bytes are used two ways, which must not be conflated:

* For **verification**, the scorer hands the raw bytes to the checker, which
  sanitizes them host-side into an archive of the submission's Lean modules and
  unpacks that in its own sandbox (see :mod:`apn.checker`).
* For **display**, :func:`build_tree_from_tar` turns the bytes into a nested
  :data:`FileTreeForLogViewer` that the scorer sets on
  ``state.metadata["submission_contents"]`` so the Inspect log viewer renders an
  expandable tree.
"""

from __future__ import annotations

import tarfile
from io import BytesIO
from pathlib import Path
from typing import Union

from inspect_ai.util import SandboxEnvironment

from apn.layout import SUBMISSION_DIR

FileTreeForLogViewer = dict[str, Union[str, "FileTreeForLogViewer"]]

_TAR_TMP = "/tmp/apn_submission.tar"


async def read_submission_tar(sb: SandboxEnvironment) -> bytes:
    """Tar the *contents* of ``Submission/`` in ``sb`` and return the bytes.

    Tars with ``-C SUBMISSION_DIR .`` so members are relative to the submission
    root (``./Spec.lean``, ``./Helpers/Parity.lean``). A read failure propagates;
    the caller decides whether that is infrastructure (the scorer errors the
    sample) or best-effort (the solver records an empty tree).
    """
    await sb.exec(["tar", "-cf", _TAR_TMP, "-C", SUBMISSION_DIR, "."])
    try:
        return await sb.read_file(_TAR_TMP, text=False)
    finally:
        await sb.exec(["rm", "-f", _TAR_TMP])


def build_tree_from_tar(tar_bytes: bytes) -> FileTreeForLogViewer:
    """Build a nested dict of text-file contents from the tar, **for display only**."""
    tree: FileTreeForLogViewer = {}
    # "r:" -- uncompressed only, as the checker parses it: the bytes are
    # agent-controlled, and transparent decompression would let a small
    # archive expand into gigabytes of headers here.
    with tarfile.open(fileobj=BytesIO(tar_bytes), mode="r:") as tf:
        for member in tf.getmembers():
            if not member.isfile():
                continue
            extracted = tf.extractfile(member)
            if extracted is None:
                continue
            try:
                text = extracted.read().decode("utf-8")
            except UnicodeDecodeError:
                continue

            parts = Path(member.name).parts
            current = tree
            for part in parts[:-1]:
                node = current.setdefault(part, {})
                # A file and a directory can't share a name; if a prior member
                # claimed this name as a file, treat the tree as malformed.
                if not isinstance(node, dict):
                    node = current[part] = {}
                current = node
            current[parts[-1]] = text
    return tree
