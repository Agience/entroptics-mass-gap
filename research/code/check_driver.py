"""The shared driver for the exact-check scripts.

A check script is a list of sections, each a function that prints its rows and asserts its
statement, plus a run-time budget its module docstring states. `run_sections` runs them in order,
prints the elapsed time measured from the script's own start `t0`, and asserts the budget.
"""
from __future__ import annotations

import time
from typing import Callable, Iterable


def run_sections(sections: Iterable[Callable[[], None]], t0: float, budget_s: float) -> None:
    """Run each section in order, print the time since `t0`, and assert it is under `budget_s`."""
    for section in sections:
        section()
    dt = time.time() - t0
    print(f"time {dt:.2f} s")
    assert dt < budget_s
