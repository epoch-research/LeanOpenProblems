"""Tests for the arXiv-id parsing in the corpus builder.

``apn/lean/build_corpus.py`` is a build-time script (run inside the Docker
``corpus_build`` stage), not part of the ``apn`` package, so we load it by path.
The parsing of proof-pile ``meta.file`` paths into canonical arXiv ids drives
both the src/ layout and the metadata join, so it's worth pinning down --
especially the pre-2007 id scheme and path-traversal rejection. (Importing the
module is cheap: pyarrow is imported lazily, only inside build_metadata.)
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "build_corpus", Path(__file__).resolve().parent.parent / "apn" / "lean" / "build_corpus.py"
)
assert _SPEC and _SPEC.loader
bc = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(bc)


def test_parse_modern_id() -> None:
    cid, ver, rest = bc.parse_arxiv_path("1812.02537/v5 arxiv/sections/5_interp.tex")
    assert (cid, ver, rest) == ("1812.02537", 5, "sections/5_interp.tex")


def test_parse_old_scheme_reinserts_slash() -> None:
    cid, ver, rest = bc.parse_arxiv_path("math0211159/v2 arxiv/main.tex")
    assert cid == "math/0211159" and ver == 2 and rest == "main.tex"


def test_parse_old_scheme_with_subclass() -> None:
    cid, _, _ = bc.parse_arxiv_path("math.AG0501001/v1 arxiv/p.tex")
    assert cid == "math.AG/0501001"


def test_parse_defaults_version_to_one() -> None:
    cid, ver, _ = bc.parse_arxiv_path("0704.0074/arxiv/p.tex")
    assert cid == "0704.0074" and ver == 1


def test_parse_bare_single_file_modern() -> None:
    # Single-file submissions have no directory or version segment at all --
    # 45% of proof-pile's arxiv rows look like this.
    assert bc.parse_arxiv_path("0911.5478.tex") == ("0911.5478", 1, "0911.5478.tex")


def test_parse_bare_single_file_old_scheme() -> None:
    assert bc.parse_arxiv_path("math0406055.tex") == ("math/0406055", 1, "math0406055.tex")
    cid, _, _ = bc.parse_arxiv_path("math.AG0501001.tex")
    assert cid == "math.AG/0501001"


def test_parse_rejects_unrecognized_id() -> None:
    assert bc.parse_arxiv_path("not-an-id/v1 arxiv/p.tex") is None
    assert bc.parse_arxiv_path("nopath") is None
    assert bc.parse_arxiv_path("0911.5478.pdf") is None
    assert bc.parse_arxiv_path("notes.tex") is None


def test_safe_id_replaces_slash() -> None:
    assert bc.safe_id("math/0211159") == "math_0211159"
    assert bc.safe_id("1812.02537") == "1812.02537"


def test_safe_rest_strips_and_rejects_traversal() -> None:
    assert bc.safe_rest("sections/./a.tex") == "sections/a.tex"
    assert bc.safe_rest("/abs/a.tex") == "abs/a.tex"
    assert bc.safe_rest("../escape.tex") is None
    assert bc.safe_rest("") is None


def _write_shard(path: Path, rows: list[dict[str, object]]) -> None:
    import gzip
    import json

    with gzip.open(path, "wt", encoding="utf-8") as fh:
        for row in rows:
            fh.write(json.dumps(row) + "\n")


def test_build_source_writes_both_shapes(tmp_path: Path) -> None:
    _write_shard(
        tmp_path / "shard.jsonl.gz",
        [
            {"text": "single", "meta": {"config": "arxiv", "file": "0911.5478.tex"}},
            {"text": "multi", "meta": {"config": "arxiv", "file": "1812.02537/v5 arxiv/main.tex"}},
            {"text": "other", "meta": {"config": "wiki", "file": "ignored"}},
        ],
    )
    out = tmp_path / "out"
    written = bc.build_source([tmp_path / "shard.jsonl.gz"], out, max_papers=None)
    assert written == {"0911.5478": "src/0911.5478", "1812.02537": "src/1812.02537"}
    assert (out / "src/0911.5478/0911.5478.tex").read_text() == "single"
    assert (out / "src/1812.02537/main.tex").read_text() == "multi"


def test_build_source_fails_on_unrecognized_rows(tmp_path: Path) -> None:
    # The invariant that caught (and now prevents) the silent loss of all
    # single-file submissions: a meta.file shape we can't parse fails the
    # build instead of being skipped.
    import pytest

    _write_shard(
        tmp_path / "shard.jsonl.gz",
        [
            {"text": "ok", "meta": {"config": "arxiv", "file": "0911.5478.tex"}},
            {"text": "??", "meta": {"config": "arxiv", "file": "something-new.xyz"}},
        ],
    )
    with pytest.raises(RuntimeError, match="something-new.xyz"):
        bc.build_source([tmp_path / "shard.jsonl.gz"], tmp_path / "out", max_papers=None)
