import pytest

from apn.dataset import FC_PINS, OEIS_DIR, fc_commit, fc_profile


@pytest.fixture(scope="module", params=FC_PINS, ids=lambda p: p[:12])
def every_pin(request: pytest.FixtureRequest) -> str:
    return str(request.param)


@pytest.fixture(scope="module")
def pin() -> str:
    return fc_commit(OEIS_DIR)


@pytest.fixture(scope="module")
def imp(pin: str) -> str:
    return f"import {fc_profile(pin).util_module}\n"
