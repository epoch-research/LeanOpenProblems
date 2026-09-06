"""Inspect registry entry point for package-based runners such as Hawk."""

from apn.redteam import apn_redteam_collatz
from apn.software_test import apn_math_software_test
from apn.task import apn_erdos, apn_erdos_autoformalized, apn_fc100open, apn_oeis

__all__ = [
    "apn_erdos",
    "apn_erdos_autoformalized",
    "apn_fc100open",
    "apn_math_software_test",
    "apn_oeis",
    "apn_redteam_collatz",
]
