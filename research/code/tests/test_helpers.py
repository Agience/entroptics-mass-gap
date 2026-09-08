"""The thin helper modules: table (CSV), configio (NERSC gauge IO), plot (figure).

``configio`` (the NERSC SU(3) gauge-IO helper) was removed from research/code in the big refactor
(git d74a6b6) and never restored -- ``lattice_generator.gauge_field`` still mentions "export via
configio", but the module is not in the repo. Rather than fabricate it, the four configio tests below
``pytest.importorskip("configio")`` so they SKIP with a clear reason; the table/plot tests (whose
modules DO exist) still run. Restore configio.py to un-skip them.
"""
import csv

import matplotlib
matplotlib.use("Agg")                       # headless, before plot imports pyplot

import numpy as np
import pytest

import table
import lattice_generator as generator
import plot

_NO_CONFIGIO = "configio (NERSC gauge IO) is not in the repo (removed in refactor d74a6b6, never restored)"


# ── table.write (CSV) ─────────────────────────────────────────────────────────

def test_table_write_roundtrips(tmp_path):
    rows = [{"beta": 1.0, "K": 0.21}, {"beta": 2.0, "K": 0.30}]
    path = tmp_path / "t.csv"
    table.write(str(path), rows, ["beta", "K"])
    with open(path) as f:
        got = list(csv.DictReader(f))
    assert [r["beta"] for r in got] == ["1.0", "2.0"]
    assert [r["K"] for r in got] == ["0.21", "0.3"]


# ── configio (NERSC SU(3) gauge IO) ───────────────────────────────────────────

def test_nersc_roundtrip_3x3(tmp_path):
    configio = pytest.importorskip("configio", reason=_NO_CONFIGIO)
    U = generator.gauge_field((2, 2, 2, 2), beta=5.7, group="su3", seed=0, therm=2)
    path = tmp_path / "cfg.nersc"
    configio.save_nersc(str(path), U, beta=5.7)
    V = configio.load_nersc(str(path), verify=True)
    assert V.shape == U.shape
    assert np.allclose(V, U, atol=1e-10)


def test_nersc_two_row_reconstructs_third(tmp_path):
    configio = pytest.importorskip("configio", reason=_NO_CONFIGIO)
    U = generator.gauge_field((2, 2, 2, 2), beta=5.7, group="su3", seed=1, therm=2)
    path = tmp_path / "cfg2.nersc"
    configio.save_nersc(str(path), U, beta=5.7, two_row=True)
    V = configio.load_nersc(str(path), verify=True)
    assert V.shape == U.shape
    assert np.allclose(V, U, atol=1e-6)          # third row reconstructed from the first two


def test_nersc_header_has_dimensions(tmp_path):
    configio = pytest.importorskip("configio", reason=_NO_CONFIGIO)
    U = generator.gauge_field((2, 2, 2, 2), beta=5.7, group="su3", seed=2, therm=2)
    path = tmp_path / "cfg3.nersc"
    configio.save_nersc(str(path), U, beta=5.7)
    hdr = configio.read_nersc_header(str(path))
    assert hdr["DIMENSION_1"] == "2" and hdr["DIMENSION_4"] == "2"
    assert "PLAQUETTE" in hdr and "CHECKSUM" in hdr


def test_nersc_rejects_non_su3_shape(tmp_path):
    configio = pytest.importorskip("configio", reason=_NO_CONFIGIO)
    with pytest.raises(ValueError):
        configio.save_nersc(str(tmp_path / "bad.nersc"), np.zeros((2, 2, 2, 2, 4)), beta=1.0)


# ── plot.line (figure) ────────────────────────────────────────────────────────

def test_plot_line_writes_png(tmp_path):
    path = tmp_path / "fig.png"
    plot.line(str(path), [0.0, 1.0, 2.0],
              [{"y": [0.0, 1.0, 4.0], "label": "y = x^2"}],
              xlabel="x", ylabel="y", title="smoke")
    assert path.exists() and path.stat().st_size > 0
