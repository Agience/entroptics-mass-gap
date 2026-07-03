"""
table.py -- generic CSV writer for the section scripts.

Keeps the data scripts thin: hand it rows (list of dicts) and the column order.
"""
from __future__ import annotations

import csv
import os


def write(path, rows, cols):
    """Write ``rows`` (list of dicts) as a CSV at ``path`` with columns ``cols``."""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow({k: r[k] for k in cols})
    return path
