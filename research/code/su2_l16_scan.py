"""The SU(2) L=16 coupling-scan population, named once.

WHY THIS FILE EXISTS. Two scripts read the same quantity across the same coupling scan --
`9_1_run_d2_bound.py` measures the central value of the whitened second moment and
`9_1_run_d2_certify.py` certifies an upper bound ON that central value -- and each carried its own
hardcoded collection list and its own copy of the loader. While the two lists happened to agree,
nothing said they had to, and when `configs_gpu_su2_L16` was added to one of them the two artifacts
began describing different data. `test_the_two_d2_artifacts_describe_the_same_measurement` caught it
at `beta = 2.40`: 0.15808 against 0.15915, one number read over two populations.

A second copy of the same fact had the same shape: `9_1_run_d2_bound.py` truncated each coupling's
sample at 256 configurations and its sibling did not. That was invisible for as long as no coupling
exceeded 256, which is how a truncation waits.

So the population is a decision, it is made here, and there is one loader.

WHAT IS AND IS NOT IN IT. `configs_gpu_su2_L16` joined on 2026-09-17, once its three ensembles
(beta = 2.30, 2.40, 2.50) had a thermalisation verdict: `at_equilibrium` at 0.1, 0.1 and 0.4 sigma.
Holding an ensemble out until it is validated is a reason; holding it out afterwards would need one.

NOT A GENERAL LOADER. Three other scripts read `su2_L16` for DIFFERENT quantities and carry their
own narrower lists. They are not wrong -- no two artifacts disagree about one number -- but they are
three more places where this decision lives. Pointing them here is the obvious next step and it
moves numbers in the paper, so it wants doing with time to re-verify them.

DERIVED: `16` is the aperture the shipped SU(2) scan was generated at; every collection below holds
`su2_L16_*` shards and no other size enters. Nothing here is a magnitude.
"""
from __future__ import annotations

import glob
import os

import numpy as np

import store_path

#: The lattice extent this scan is at.
#: DERIVED: `16` is not chosen here -- it is the extent the shipped SU(2) coupling scan was
#: generated at, and every collection in `POPULATION` holds `su2_L16_*` shards and no other size.
#: Changing it would not select a different aperture; it would select nothing.
L = 16

#: Every collection holding `su2_L16` configurations of the coupling scan, in one place.
POPULATION = ("configs_densebeta", "configs_phase1", "configs_betasweep", "configs_ladder",
              "configs_gpu_su2_L16")


def collections() -> tuple[str, ...]:
    """The population, resolved against the configured store. Empty when nothing is configured, so
    a caller's own refusal fires rather than this raising during import."""
    base = store_path.store_root(required=False)
    if not base:
        return ()
    return tuple(d for d in POPULATION if os.path.isdir(os.path.join(base, d)))


def load_beta(beta: float):
    """Every configuration at this coupling, from every collection in the population.

    NO CAP. A truncation here would silently make this a different sample from the one the
    certificate is computed on -- see the module docstring.
    """
    base = store_path.store_root(required=False)
    if not base:
        return None
    fs = []
    for d in collections():
        fs += sorted(glob.glob(os.path.join(base, d, f"su2_L{L}_b{beta:.2f}.s*.npy")))
    return np.concatenate([np.load(f) for f in fs], 0) if fs else None
