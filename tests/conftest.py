"""Shared pytest fixtures."""

from __future__ import annotations

import pytest
from inspect_ai.util import store

from apn.checker import CACHE_STORE_KEY


@pytest.fixture(autouse=True)
def clear_check_cache() -> None:
    """Drop the checker's one-entry result cache before each test.

    ``SandboxComparator.check`` caches its last outcome in the Inspect sample
    store. Under pytest there is no sample, so ``store()`` hands back a
    process-global default shared by every test in the session -- two tests
    that check a byte-identical submission against the same spec, decl and
    claim would otherwise have the second one silently served from the first
    one's verdict, running no sandbox at all.
    """
    try:
        store().delete(CACHE_STORE_KEY)
    except KeyError:
        pass
