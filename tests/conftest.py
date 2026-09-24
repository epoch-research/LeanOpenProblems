import pytest

from apn.dataset import FC_PINS


def pytest_addoption(parser: pytest.Parser) -> None:
    parser.addoption(
        "--fc-pin",
        action="store",
        default=None,
        help="run the every_pin-parametrized tests at this registered FC pin only",
    )


def pytest_generate_tests(metafunc: pytest.Metafunc) -> None:
    if "every_pin" not in metafunc.fixturenames:
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
    metafunc.parametrize("every_pin", pins, ids=lambda p: p[:12], scope="module")
