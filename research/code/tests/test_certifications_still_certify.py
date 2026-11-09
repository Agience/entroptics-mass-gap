"""The certifications the paper calls exact checks still certify.

`research/code/README.md` lists `certify/small_volume_enclosure.py` as an exact check: a rigorous
small-volume enclosure for the SU(2) Kogut–Susskind Hamiltonian. A certification is a program, so its
verdict can change when the code around it changes -- a constant edited, a bound tightened, an import
moved -- and the documents would go on claiming the old result. This test runs it and checks the verdict.

Only the arithmetic certification runs here: it needs no ensemble, no store and no GPU, so it costs
seconds.
"""
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
CERT = REPO / "research" / "code" / "certify"


def _run(script: str) -> str:
    p = CERT / script
    if not p.exists():
        pytest.skip(f"{script} not present")
    e = dict(os.environ)
    e.update({"PYTHONIOENCODING": "utf-8", "OMP_NUM_THREADS": "4"})
    r = subprocess.run([sys.executable, "-u", str(p)], cwd=CERT, capture_output=True,
                       text=True, timeout=600, env=e)
    assert r.returncode == 0, f"{script} exited {r.returncode}:\n{r.stdout[-3000:]}\n{r.stderr[-2000:]}"
    return r.stdout


def test_small_volume_enclosure_certifies():
    """The single-plaquette gap is certified above the floor, at every crossover point."""
    out = _run("small_volume_enclosure.py")
    assert "CERTIFIED" in out, f"small_volume_enclosure did not certify:\n{out[-1500:]}"
    assert "NO" not in out.split("Crossover coverage")[-1], \
        f"a crossover point fails the aperture ceiling:\n{out[-1500:]}"
