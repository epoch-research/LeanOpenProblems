"""Tests for the arXiv tools' date/version gating.

The conjectures are open as of the benchmark paper (arXiv:2605.22763, May 2026),
so ``arxiv_source`` must only ever fetch material that predates it. These tests
stub the arXiv metadata API and exercise the pure ``_resolve_safe_version``
resolver -- the network and tarball unpacking are validated end-to-end.
"""

from __future__ import annotations

import pytest

import apn.tools as apn_tools


def _stub_meta(monkeypatch: pytest.MonkeyPatch, meta_by_id: dict[str, dict[str, str]]) -> None:
    monkeypatch.setattr(apn_tools, "_arxiv_meta", lambda aid: meta_by_id.get(aid, {}))


def test_pre_cutoff_paper_is_fetched_as_is(monkeypatch: pytest.MonkeyPatch) -> None:
    _stub_meta(
        monkeypatch,
        {"2401.00001": {"id": "2401.00001v1", "published": "2024-01-02", "updated": "2024-01-02"}},
    )
    safe_id, _ = apn_tools._resolve_safe_version("2401.00001")
    assert safe_id == "2401.00001v1"


def test_post_cutoff_paper_is_refused(monkeypatch: pytest.MonkeyPatch) -> None:
    _stub_meta(
        monkeypatch,
        {"2605.00001": {"id": "2605.00001v1", "published": "2026-05-10", "updated": "2026-05-10"}},
    )
    safe_id, note = apn_tools._resolve_safe_version("2605.00001")
    assert safe_id is None
    assert "first submitted 2026-05-10" in note
    assert "papers submitted before 2026-05-01 are available" in note


def test_post_cutoff_revision_pins_to_newest_pre_cutoff_version(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # v1 predates the cutoff but the latest (v3) is a 2026-06 revision that could
    # add the solution -> must pin to v2, the newest version still before May 2026.
    _stub_meta(
        monkeypatch,
        {
            "2402.00001": {"id": "2402.00001v3", "published": "2024-02-01", "updated": "2026-06-01"},
            "2402.00001v3": {"id": "2402.00001v3", "published": "2024-02-01", "updated": "2026-06-01"},
            "2402.00001v2": {"id": "2402.00001v2", "published": "2024-02-01", "updated": "2024-03-01"},
            "2402.00001v1": {"id": "2402.00001v1", "published": "2024-02-01", "updated": "2024-02-01"},
        },
    )
    safe_id, _ = apn_tools._resolve_safe_version("2402.00001")
    assert safe_id == "2402.00001v2"


def test_unknown_paper_is_refused(monkeypatch: pytest.MonkeyPatch) -> None:
    _stub_meta(monkeypatch, {})
    safe_id, note = apn_tools._resolve_safe_version("9999.99999")
    assert safe_id is None
    assert "not found" in note


def test_search_query_carries_the_cutoff_bound() -> None:
    # The submittedDate upper bound must be the benchmark paper's predecessor
    # month so the API never returns later work.
    assert apn_tools._CUTOFF_API == "202604302359"
    assert apn_tools._CUTOFF_DATE == "2026-05-01"
