from typing import Any

from inspect_ai._eval import registry as eval_registry
from inspect_ai._util import registry as util_registry


def test_hawk_task_registry_name() -> None:
    ensure_entry_points: Any = getattr(util_registry, "ensure_entry_points")
    registry_info: Any = getattr(eval_registry, "registry_info")
    registry_lookup: Any = getattr(eval_registry, "registry_lookup")

    ensure_entry_points("apn")

    task = registry_lookup("task", "apn/apn_oeis")

    assert task is not None
    assert registry_info(task).name == "apn/apn_oeis"
