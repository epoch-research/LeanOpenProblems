from typing import Any

import pytest
from inspect_ai._eval import registry as eval_registry
from inspect_ai._util import registry as util_registry


@pytest.mark.parametrize("task_name", ["apn/apn_oeis", "apn/apn_fc100open", "apn/apn_erdos"])
def test_hawk_task_registry_name(task_name: str) -> None:
    ensure_entry_points: Any = getattr(util_registry, "ensure_entry_points")
    registry_info: Any = getattr(eval_registry, "registry_info")
    registry_lookup: Any = getattr(eval_registry, "registry_lookup")

    ensure_entry_points("apn")

    task = registry_lookup("task", task_name)

    assert task is not None
    assert registry_info(task).name == task_name
