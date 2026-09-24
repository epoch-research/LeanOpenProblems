import pytest

from apn.dataset import FC_PINS


@pytest.fixture(scope="module", params=FC_PINS, ids=lambda p: p[:12])
def every_pin(request: pytest.FixtureRequest) -> str:
    return str(request.param)
