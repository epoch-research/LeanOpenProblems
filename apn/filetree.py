"""Collecting and displaying the agent's ``Submission/`` subtree.

The agent's proof is a subtree of ``.lean`` files (entry module + helpers), not
a single file. :func:`read_submission_tar` tars ``Submission/`` from the sandbox
and returns the bytes; that tar is the one source of truth.

The tar bytes are used two ways, which must not be conflated:

* For **verification**, the scorer hands the raw bytes to the checker, which
  unpacks them straight into its own sandbox and builds (see :mod:`apn.checker`).
  Nothing decodes the tar in Python on that path.
* For **display**, :func:`build_tree_from_tar` turns the bytes into a nested
  :data:`FileTreeForLogViewer` that the scorer sets on
  ``state.metadata["submission_contents"]`` so the Inspect log viewer renders an
  expandable tree (same shape as PortBench's ``workspace_src_contents``). This is
  cosmetic; nothing functional depends on it.
"""

from __future__ import annotations

import tarfile
from io import BytesIO
from pathlib import Path
from typing import Union

from inspect_ai.util import SandboxEnvironment

from apn.layout import SUBMISSION_DIR

# A recursive directory tree for the Inspect log viewer: directories map to
# nested dicts, text files map to their contents as string leaves. The name is
# the contract: this representation exists *only* to be displayed.
FileTreeForLogViewer = dict[str, Union[str, "FileTreeForLogViewer"]]

# Where read_submission_tar stages the tar inside the sandbox before reading it
# back; removed afterwards so nothing lingers between attempts.
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
    """Build a nested dict of text-file contents from the tar, **for display**.

    Counterpart of PortBench's ``_build_directory_tree_from_tar``: the solver
    hands this to the Inspect log viewer via ``submission_contents``. It is not
    used for verification -- the checker unpacks the tar in its own sandbox. Only
    regular files that decode as UTF-8 are kept (the submission is ``.lean``
    source); binary blobs and non-file members are skipped.
    """
    tree: FileTreeForLogViewer = {}
    with tarfile.open(fileobj=BytesIO(tar_bytes)) as tf:
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
