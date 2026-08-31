"""Inspect registry entry point for package-based runners such as Hawk."""

from apn.redteam import apn_redteam_collatz
from apn.task import (
    apn_arxiv,
    apn_erdos,
    apn_erdos_autoformalized,
    apn_fc100open,
    apn_oeis,
    apn_oeis_open,
    apn_wikipedia,
)

__all__ = [
    "apn_arxiv",
    "apn_erdos",
    "apn_erdos_autoformalized",
    "apn_fc100open",
    "apn_oeis",
    "apn_oeis_open",
    "apn_redteam_collatz",
    "apn_wikipedia",
]
