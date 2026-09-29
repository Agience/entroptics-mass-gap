"""The thin helper modules: table (CSV) and plot (figure)."""
import csv

import matplotlib
matplotlib.use("Agg")                       # headless, before plot imports pyplot

import table
import plot


# ── table.write (CSV) ─────────────────────────────────────────────────────────

def test_table_write_roundtrips(tmp_path):
    rows = [{"beta": 1.0, "K": 0.21}, {"beta": 2.0, "K": 0.30}]
    path = tmp_path / "t.csv"
    table.write(str(path), rows, ["beta", "K"])
    with open(path) as f:
        got = list(csv.DictReader(f))
    assert [r["beta"] for r in got] == ["1.0", "2.0"]
    assert [r["K"] for r in got] == ["0.21", "0.3"]


# ── plot.line (figure) ────────────────────────────────────────────────────────

def test_plot_line_writes_png(tmp_path):
    path = tmp_path / "fig.png"
    plot.line(str(path), [0.0, 1.0, 2.0],
              [{"y": [0.0, 1.0, 4.0], "label": "y = x^2"}],
              xlabel="x", ylabel="y", title="smoke")
    assert path.exists() and path.stat().st_size > 0
