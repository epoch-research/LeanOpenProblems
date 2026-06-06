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


def test_parse_rejects_unrecognized_id() -> None:
    assert bc.parse_arxiv_path("not-an-id/v1 arxiv/p.tex") is None
    assert bc.parse_arxiv_path("nopath") is None


def test_safe_id_replaces_slash() -> None:
    assert bc.safe_id("math/0211159") == "math_0211159"
    assert bc.safe_id("1812.02537") == "1812.02537"


def test_safe_rest_strips_and_rejects_traversal() -> None:
    assert bc.safe_rest("sections/./a.tex") == "sections/a.tex"
    assert bc.safe_rest("/abs/a.tex") == "abs/a.tex"
    assert bc.safe_rest("../escape.tex") is None
    assert bc.safe_rest("") is None
