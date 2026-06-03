"""Tools for the proving agent.

Editing is done with Inspect's built-in ``text_editor`` tool. ``bash`` gives the
agent a shell in the workspace where PyPantograph is installed and the Mathlib +
FormalConjectures oleans are baked into the image, so it can drive
``pantograph.Server`` from Python directly. ``arxiv_search`` / ``arxiv_source``
let the agent consult the literature (the network call runs host-side, in the
controller -- the sandbox stays airgapped). Statement integrity and the axiom
guard are enforced by SafeVerify at scoring time, not inside the tools.
"""

from __future__ import annotations

import asyncio
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET

from inspect_ai.tool import Tool, ToolError, tool
from inspect_ai.util import sandbox


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
            f"arXiv {meta['id']} was first submitted {meta['published']}; only "
            f"papers submitted before {_CUTOFF_DATE} are available."
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
                f"pinned to {base}v{version} (submitted {vmeta['updated']}); only "
                f"versions submitted before {_CUTOFF_DATE} are available."
            )
    return None, f"arXiv {meta['id']}: no version submitted before {_CUTOFF_DATE}."


@tool
def arxiv_search() -> Tool:
    """Build a tool that searches arXiv (papers before the benchmark paper)."""

    async def execute(
        query: str = "",
        id_list: str = "",
        start: int = 0,
        max_results: int = 10,
        sort_by: str = "relevance",
        sort_order: str = "descending",
    ) -> str:
        """Search arXiv via its export API (http://export.arxiv.org/api/query).

        `query` uses the standard arXiv API query language: field prefixes
        `ti:` (title), `au:` (author), `abs:` (abstract), `co:` (comment),
        `jr:` (journal reference), `cat:` (subject category), `rn:` (report
        number), `all:`; operators `AND`, `OR`, `ANDNOT`; parentheses for
        grouping; double quotes for phrases.

        This API searches metadata (title, abstract, ...) only, not full text,
        and strips punctuation when tokenizing, so math notation is not
        searchable. Search a concept's words, not its formula (`Mersenne`,
        not `2^k-1`).

        Only papers submitted before 2026-05-01 are returned. Use the returned
        id with `arxiv_source` to read a paper's full LaTeX source.

        Args:
            query: An arXiv API `search_query`, e.g.
                `abs:"primitive root" AND cat:math.NT`.
            id_list: Comma-delimited arXiv ids to restrict to (or, with an
                empty query, to look up directly).
            start: 0-based result offset, for paging.
            max_results: Number of results to return (API slices are capped
                at 2000 per call).
            sort_by: `relevance`, `lastUpdatedDate`, or `submittedDate`.
            sort_order: `ascending` or `descending`.

        Returns:
            The total match count, then one block per hit (id, title, authors,
            date, primary category, abstract).
        """
        params: dict[str, str | int] = {
            # The cutoff filter must constrain every result, including pure
            # id_list lookups, so it always contributes a search_query term.
            "search_query": (
                f"({query}) AND " if query else ""
            )
            + f"submittedDate:[190001010000 TO {_CUTOFF_API}]",
            "start": start,
            "max_results": max_results,
            "sortBy": sort_by,
            "sortOrder": sort_order,
        }
        if id_list:
            params["id_list"] = id_list
        qs = urllib.parse.urlencode(params)
        try:
            raw = await asyncio.to_thread(_http_get, f"{_ARXIV_API}?{qs}")
            feed = ET.fromstring(raw)
        except Exception as exc:  # network / parse failure -> tell the model
            raise ToolError(f"arXiv search failed: {exc}") from exc
        total = feed.findtext("{http://a9.com/-/spec/opensearch/1.1/}totalResults", "?")
        blocks = []
        for entry in feed.findall(f"{_ATOM}entry"):
            aid = entry.findtext(f"{_ATOM}id", "").rsplit("/abs/", 1)[-1]
            title = " ".join(entry.findtext(f"{_ATOM}title", "").split())
            authors = ", ".join(
                a.findtext(f"{_ATOM}name", "") for a in entry.findall(f"{_ATOM}author")
            )
            published = entry.findtext(f"{_ATOM}published", "")[:10]
            category = entry.find("{http://arxiv.org/schemas/atom}primary_category")
            cat_term = category.get("term", "") if category is not None else ""
            summary = " ".join(entry.findtext(f"{_ATOM}summary", "").split())
            blocks.append(
                f"## {aid}\n{title}\n{authors}\n{published} [{cat_term}]\n\n{summary}"
            )
        header = f"{total} total matches."
        return header + "\n\n" + "\n\n".join(blocks) if blocks else "No results."

    return execute


@tool
def arxiv_source(dest_dir: str = "/tmp/arxiv", sandbox_name: str | None = None) -> Tool:
    """Build a tool that unpacks an arXiv paper's source into the workspace."""

    async def execute(arxiv_id: str) -> str:
        """Download an arXiv paper's source and unpack it into the workspace.

        The whole source archive is placed under a per-paper directory; read the
        files with the text editor or `bash`. Only papers submitted before
        2026-05-01 are available; for a paper whose latest version is more
        recent, the newest version from before that date is fetched instead.

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
