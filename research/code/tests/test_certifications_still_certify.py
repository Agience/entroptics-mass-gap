"""The certifications the paper calls "certified" still certify, and still certify the same numbers.

PAPER.md states several results as certified and names the script that certifies them. A
certification is a program, so its verdict can change when the code around it changes -- a constant
edited, a bound tightened, an import moved -- and the paper would go on claiming the old result.
These tests run the certifications and check both the verdict and the specific values the paper
quotes from them.

Only the arithmetic certifications run here: they need no ensemble, no store and no GPU, so they cost
seconds. The ones that read configurations (`gap_of_margin`, `apriori_A1`,
`gap_refinement_invariant`, `string_tension_eq_centre`) are driven by `research/regen_all.py`, which
carries their resource class.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
CERT = REPO / "research" / "code" / "certify"
PAPER = REPO / "research" / "PAPER.md"


def _run(script: str) -> str:
    p = CERT / script
    if not p.exists():
        pytest.skip(f"{script} not present")
    env = {"PYTHONIOENCODING": "utf-8", "OMP_NUM_THREADS": "4"}
    import os
    e = dict(os.environ)
    e.update(env)
    r = subprocess.run([sys.executable, "-u", str(p)], cwd=CERT, capture_output=True,
                       text=True, timeout=600, env=e)
    assert r.returncode == 0, f"{script} exited {r.returncode}:\n{r.stdout[-3000:]}\n{r.stderr[-2000:]}"
    return r.stdout


def test_beta_star_enclosure_certifies_the_quoted_interval():
    """The strong-coupling threshold is certified, and it is the interval the paper quotes."""
    out = _run("beta_star_enclosure.py")
    assert "CERTIFIED" in out, f"beta_star_enclosure did not certify:\n{out[-1500:]}"
    assert "beta_star in (0.749, 0.750)" in out, \
        f"the certified interval is not (0.749, 0.750):\n{out[-1500:]}"
    text = PAPER.read_text(encoding="utf-8")
    assert "(0.749,0.750)" in text.replace(" ", ""), \
        "the paper does not quote the interval this certification establishes"


def test_small_volume_enclosure_certifies_the_quoted_gap():
    """The single-plaquette gap is certified above the floor at the value the paper quotes."""
    out = _run("small_volume_enclosure.py")
    assert "CERTIFIED" in out, f"small_volume_enclosure did not certify:\n{out[-1500:]}"
    assert "NO" not in out.split("Crossover coverage")[-1], \
        f"a crossover point fails the aperture ceiling:\n{out[-1500:]}"
    # the paper quotes the mid-crossover gap to three decimals
    text = PAPER.read_text(encoding="utf-8")
    quoted = "1.633"
    assert quoted in text, "the paper no longer quotes the mid-crossover gap"
    assert quoted in out, \
        f"the certification no longer produces {quoted} at mid-crossover:\n{out[-1500:]}"


def test_interval_enclosure_still_separates_the_regions():
    """The rigorous strong and weak regions, and the residual crossover interior, are reported.

    The residual is the open item the paper is explicit about, so this pins that the certification
    still reports one rather than silently claiming full coverage.
    """
    out = _run("interval_enclosure.py")
    assert "RIGOROUS strong sub-floor region" in out, f"strong region not reported:\n{out[-1500:]}"
    assert "RIGOROUS weak region" in out, f"weak region not reported:\n{out[-1500:]}"
    assert "RESIDUAL" in out, \
        f"the certification no longer reports a residual interior; the paper says there is one:\n{out[-1500:]}"
