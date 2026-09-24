import pytest

from apn.dataset import FC_PINS, fc_profile


def pytest_addoption(parser: pytest.Parser) -> None:
    parser.addoption(
        "--fc-pin",
        action="store",
        default=None,
        help="run the pin-parametrized tests at this registered FC pin only",
    )


def pytest_generate_tests(metafunc: pytest.Metafunc) -> None:
    if "pin" not in metafunc.fixturenames:
        return
    chosen: str | None = metafunc.config.getoption("--fc-pin")
    if chosen is None:
        pins = list(FC_PINS)
    elif chosen in FC_PINS:
        pins = [chosen]
    else:
        raise pytest.UsageError(
            f"--fc-pin {chosen!r} is not a registered FC pin; known: {sorted(FC_PINS)}"
        )
    metafunc.parametrize("pin", pins, ids=lambda p: p[:12], scope="module")


@pytest.fixture(scope="module")
def imp(pin: str) -> str:
    return f"import {fc_profile(pin).util_module}\n"
