"""Tools for the proving agent.

Editing is done with Inspect's built-in ``text_editor`` tool. ``lean_check``
compiles the proof file in the sandbox and returns the Lean compiler feedback.
``arxiv_search`` / ``arxiv_source`` let the agent consult the literature (the
network call runs host-side, in the controller -- the sandbox stays airgapped).
Statement integrity and the axiom guard are enforced by SafeVerify at scoring
time, not inside the tools.
"""

from __future__ import annotations

import asyncio
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET

from inspect_ai.tool import Tool, ToolError, tool
from inspect_ai.util import sandbox

from apn.verifier.base import CompileResult, LeanVerifier


def format_check_feedback(result: CompileResult) -> str:
    """Render compiler output for the ``lean_check`` tool, with a status note."""
    feedback = result.feedback()
    if result.system_error is not None:
        return feedback
    if result.ok and not result.has_sorry:
        feedback += (
            "\n\nThe file compiles with no errors and no remaining `sorry`. "
            "The proof is complete."
        )
    elif result.ok and result.has_sorry:
        feedback += "\n\nThe file compiles, but it still contains `sorry`."
    return feedback


@tool
def lean_check(
    verifier: LeanVerifier, path: str, sandbox_name: str | None = None
) -> Tool:
    """Build a tool that compiles the proof file and returns Lean feedback."""

    async def execute() -> str:
        """Compile the current Lean proof file and return the compiler feedback.

        Call this after editing the file with the text editor to see compilation
        errors and whether any `sorry` remains. The execution environment already
        imports Mathlib, so `import` lines are ignored.

        Returns:
            The Lean compiler messages, plus a note on whether the proof is
            complete.
        """
        code = await sandbox(sandbox_name).read_file(path)
        result = await verifier.compile(code)
        return format_check_feedback(result)

    return execute


@tool(name="bash")
def bash(
    timeout: int | None = None,
    user: str | None = None,
    sandbox_name: str | None = None,
) -> Tool:
    """Bash tool that surfaces the exit status to the agent on failure.

    Equivalent to ``inspect_ai.tool.bash`` on success (stdout, with stderr
    prepended if any). On a non-zero exit -- which the built-in tool would
    silently swallow -- the agent gets stdout, stderr, and the raw returncode
    each in pseudo-XML tags so the model sees the streams separately and knows
    the command failed. Interpreting specific codes (137 = SIGKILL/OOM,
    127 = command not found, ...) is left to the model.
    """

    async def execute(command: str) -> str:
        """
        Use this function to execute bash commands.

        Args:
          command: The bash command to execute.

        Returns:
          The output of the command.
        """
        result = await sandbox(sandbox_name).exec(
            cmd=["bash", "--login", "-c", command], timeout=timeout, user=user
        )
        if result.returncode == 0:
            # Mimic inspect_ai.tool.bash, which just concatenates
            # stderr and stdout.
            output = ""
            if result.stderr:
                output = f"{result.stderr}\n"
            return f"{output}{result.stdout}"
        return (
            f"<stdout>{result.stdout}</stdout>\n"
            f"<stderr>{result.stderr}</stderr>\n"
            f"<returncode>{result.returncode}</returncode>"
        )

    return execute


# --------------------------------------------------------------------------- #
# arXiv access                                                                 #
# --------------------------------------------------------------------------- #
# The benchmark conjectures are OPEN as of arXiv:2605.22763 (May 2026), so any
# paper from that month onward could contain a solution and would leak the
# answer. Every fetch is gated to material that *predates* the benchmark paper:
# search uses a ``submittedDate`` upper bound, and source resolves the newest
# pre-cutoff *version* of a paper (a pre-cutoff v1 can have a post-cutoff
# revision that adds the solution; ``e-print/<id>`` serves the latest version,
# so we pin to a safe one).
_ARXIV_API = "http://export.arxiv.org/api/query"
_ARXIV_EPRINT = "https://arxiv.org/e-print/"
_ATOM = "{http://www.w3.org/2005/Atom}"

# Strictly before the benchmark paper's month (2026-05). ISO dates compare
# lexically, so a YYYY-MM-DD < this string means "submitted before May 2026".
_CUTOFF_DATE = "2026-05-01"
# Same boundary for the API's submittedDate filter (YYYYMMDDTTTT, end of Apr).
_CUTOFF_API = "202604302359"


def _http_get(url: str) -> bytes:
    # arXiv asks for a descriptive UA and ~1 request / 3s; under heavy
    # parallelism you'd add a throttle/retry here.
    req = urllib.request.Request(url, headers={"User-Agent": "apn-bench/0.1"})
    with urllib.request.urlopen(req, timeout=30) as response:
        return response.read()


def _arxiv_meta(aid: str) -> dict[str, str]:
    """Fetch one paper's metadata by id (a versioned id returns that version)."""
    qs = urllib.parse.urlencode({"id_list": aid, "max_results": 1})
    feed = ET.fromstring(_http_get(f"{_ARXIV_API}?{qs}"))
    entry = feed.find(f"{_ATOM}entry")
    if entry is None or entry.findtext(f"{_ATOM}id") is None:
        return {}
    return {
        # Full id including the resolved version, e.g. ``2301.00001v3``.
        "id": entry.findtext(f"{_ATOM}id", "").rsplit("/abs/", 1)[-1],
        "published": entry.findtext(f"{_ATOM}published", "")[:10],  # v1 date
        "updated": entry.findtext(f"{_ATOM}updated", "")[:10],  # this version's date
    }


def _resolve_safe_version(aid: str) -> tuple[str | None, str]:
    """Pick the newest version of ``aid`` submitted before the cutoff.

    Returns ``(id_to_fetch, note)``; ``id_to_fetch`` is ``None`` (with an
    explanatory note) when nothing predating the benchmark paper exists.
    """
    meta = _arxiv_meta(aid)
    if not meta:
        return None, f"arXiv '{aid}' was not found via the API."
    if meta["published"] >= _CUTOFF_DATE:
        return None, (
            f"Refused: arXiv {meta['id']} first appeared {meta['published']}, not "
            f"before the benchmark paper (these conjectures are open as of 2026-05)."
        )
    if meta["updated"] < _CUTOFF_DATE:
        return meta["id"], f"{meta['id']} (submitted {meta['updated']})."
    # v1 predates the cutoff but the latest version doesn't: walk versions down
    # from the latest to the newest one still submitted before the cutoff.
    base, _, latest = meta["id"].rpartition("v")
    if not base or not latest.isdigit():
        return None, f"arXiv {meta['id']}: cannot resolve a pre-cutoff version."
    for version in range(int(latest), 0, -1):
        vmeta = _arxiv_meta(f"{base}v{version}")
        if vmeta and vmeta["updated"] < _CUTOFF_DATE:
            return f"{base}v{version}", (
                f"latest version postdates the benchmark paper; pinned to "
                f"{base}v{version} (submitted {vmeta['updated']})."
            )
    return None, f"arXiv {meta['id']}: no version submitted before {_CUTOFF_DATE}."


@tool
def arxiv_search(max_results: int = 5) -> Tool:
    """Build a tool that searches arXiv (papers before the benchmark paper)."""

    async def execute(query: str) -> str:
        """Search arXiv for papers. Returns id, title, authors, and abstract.

        Only papers submitted before the benchmark paper are returned (later
        work could state a solution to these still-open conjectures). Use the
        returned id with `arxiv_source` to read a paper's full LaTeX source.

        Args:
            query: An arXiv query, e.g. `au:erdos AND ti:sequence`, `ti:"sum of
                divisors"`, or free text.

        Returns:
            One block per hit (id, title, authors, abstract), or a no-results note.
        """
        qs = urllib.parse.urlencode(
            {
                "search_query": f"({query}) AND submittedDate:[190001010000 TO {_CUTOFF_API}]",
                "start": 0,
                "max_results": max_results,
            }
        )
        try:
            raw = await asyncio.to_thread(_http_get, f"{_ARXIV_API}?{qs}")
            feed = ET.fromstring(raw)
        except Exception as exc:  # network / parse failure -> tell the model
            raise ToolError(f"arXiv search failed: {exc}") from exc
        blocks = []
        for entry in feed.findall(f"{_ATOM}entry"):
            aid = entry.findtext(f"{_ATOM}id", "").rsplit("/abs/", 1)[-1]
            title = " ".join(entry.findtext(f"{_ATOM}title", "").split())
            authors = ", ".join(
                a.findtext(f"{_ATOM}name", "") for a in entry.findall(f"{_ATOM}author")
            )
            summary = " ".join(entry.findtext(f"{_ATOM}summary", "").split())
            blocks.append(f"## {aid}\n{title}\n{authors}\n\n{summary}")
        return "\n\n".join(blocks) or "No results."

    return execute


@tool
def arxiv_source(dest_dir: str = "/tmp/arxiv", sandbox_name: str | None = None) -> Tool:
    """Build a tool that unpacks an arXiv paper's source into the workspace."""

    async def execute(arxiv_id: str) -> str:
        """Download an arXiv paper's source and unpack it into the workspace.

        The whole source archive is placed under a per-paper directory; read the
        files with the text editor or `bash`. Papers not predating the benchmark
        paper are refused (they could contain a solution to these open
        conjectures); if the latest version is too recent, the newest pre-cutoff
        version is fetched instead.

        Args:
            arxiv_id: e.g. `2301.00001`, `2301.00001v2`, or `math/0211159`.

        Returns:
            The directory the source was unpacked to and a file listing.
        """
        safe_id, note = await asyncio.to_thread(_resolve_safe_version, arxiv_id.strip())
        if safe_id is None:
            return note
        try:
            raw = await asyncio.to_thread(_http_get, _ARXIV_EPRINT + safe_id)
        except Exception as exc:
            raise ToolError(f"arXiv source download failed: {exc}") from exc

        dest = f"{dest_dir}/{safe_id.replace('/', '_')}"
        sb = sandbox(sandbox_name)
        await sb.write_file(f"{dest}/_source", raw)
        # arXiv e-prints are usually a gzipped tar, sometimes a single gzipped
        # .tex, occasionally a bare PDF. Unpack in the sandbox (preserves
        # structure and binaries); -C confines extraction to `dest`.
        unpack = (
            f"cd {dest} && "
            f"( tar xf _source -C {dest} 2>/dev/null && rm -f _source "
            f"  || ( gunzip -c _source > main.tex 2>/dev/null && rm -f _source ) "
            f"  || true ) && find . -type f | sort"
        )
        result = await sb.exec(["bash", "-c", unpack])
        listing = result.stdout.strip() or "(no files extracted)"
        return f"Fetched {note}\nUnpacked to {dest}:\n{listing}"

    return execute
