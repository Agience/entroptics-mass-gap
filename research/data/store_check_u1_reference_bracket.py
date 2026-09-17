"""Does the U(1) equilibrium reference actually bracket the value it is compared against?

WHY THIS EXISTS. `store_run_thermalisation.py` classifies a shipped ensemble by comparing its mean
action density against a reference chain, and `test_ensembles_are_thermalised` describes that
reference as "bracketed from both a hot and a cold start". It is not: `equilibrium()` runs ONE chain,
from `lattice_generator._u1_init`, which is a uniform (hot) start. Nothing in the development ever
approached the value from below.

WHAT MADE THAT WORTH CHECKING. Across the artifact's level-tested rows the offsets `stored - reference`
are balanced for the heat-bath groups -- SU(2) 27 of 58 negative, SU(3) 7 of 16 -- and one-sided for
U(1) at large beta: 8 of 8 negative for `beta >= 1.4`, a sign test at `p = 0.0039`. One row carries
enough configurations to resolve it on its own (`configs_phase1`, `u1 L=8 T=16 beta=2.5`, n=512):
8.5 sigma BELOW its reference. A shipped ensemble sitting below equilibrium has no mechanism -- a
chain relaxes toward equilibrium from above -- so the suspect is the reference, not the data.

THE MECHANISM THIS TESTS. `_ops("u1")` returns a Metropolis proposal width of `1.0` radians for
every beta. The width that keeps acceptance near its optimum scales like the local action's
curvature, `1/sqrt(beta * staples)`, so a fixed width means acceptance falls as beta rises, the chain
decorrelates more slowly, and a hot start is still descending when the flat-tail test declares it
converged -- reading HIGH, by more at larger beta. The heat-bath groups have no proposal width and
show no bias, which is the discrimination.

WHAT IS MEASURED, and it is decisive either way. The same chain is run from a hot start (uniform,
approaches from above) and a cold start (all angles zero, approaches from below) at the same sweeps.

* If the two MEET, the reference is converged and the stored means really do sit below equilibrium,
  which would be a defect in the shipped ensembles.
* If they do NOT meet, the reference is not converged at that beta, the truth lies between them, and
  the question is whether the stored mean lies in that interval -- if it does, the shipped data is
  right and the classification was reading an artifact of the reference.

The acceptance rate is recorded alongside, because it is the quantity the mechanism is stated in: a
bracket that fails to close where acceptance is low, and closes where it is high, names the cause
rather than just the symptom.

DERIVED: the betas are the two the finding is about -- the largest in the store, where the effect is
resolved (`2.5`), and the smallest beta of the one-sided run (`1.6`), which fixes whether the bracket
closes where the bias is not yet visible. The lattice, sweeps, chain count and measurement cadence
are `store_run_thermalisation`'s own, not new ones, so a difference between the two files cannot be
an artifact of settings.
"""
from __future__ import annotations

import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "code"))

import lattice_generator as G  # noqa: E402
import table  # noqa: E402

sys.path.insert(0, HERE)
from store_run_thermalisation import (  # noqa: E402
    EQ_EVERY, EQ_N, EQ_SWEEPS_U1, DEVICE, _per_config_mean, tolerance_sigma,
)

OUT = os.path.join(os.path.dirname(HERE), "data", "store_dat_u1_reference_bracket.csv")

COLS = ["group", "L", "T", "beta", "start", "sweeps", "n_chains", "tail_blocks", "tail_mean",
        "tail_sem", "acceptance", "stored_mean", "verdict"]

#: DERIVED: the two betas the finding is about (see the module docstring).
BETAS = (1.6, 2.5)

#: DERIVED: the lattice the affected rows are on -- every U(1) ensemble in the store is L=8, T=16.
L, T = 8, 16


def _cold(b, dims, batch):
    """A cold start: every link angle zero, which is the ordered configuration.

    DERIVED: `0` is the identity of `U(1)`, not a small number -- the cold start is the ordered
    configuration by definition, and its action density is the minimum, so a chain leaving it
    approaches equilibrium strictly from below.
    """
    return b.zeros((*batch, *dims, G.D))


def _trace(beta: float, start: str):
    """`(block means, block sems, acceptance)` for one chain, measured exactly as the reference is."""
    init, sweep, action, dstep = G._ops("u1", "metropolis")
    dims = (L, L, L, T)
    b = G._Backend(DEVICE).seed(0)
    batch = G._batch_tuple(EQ_N)
    link = init(b, dims, batch) if start == "hot" else _cold(b, dims, batch)
    before = None
    moved = []
    means, sems = [], []
    for s in range(1, EQ_SWEEPS_U1 + 1):
        # DERIVED: `10` samples the acceptance at ten points across the chain rather than every
        # sweep, which would dominate the run; `0` is the remainder that says "this is a sample
        # point". Neither is a magnitude -- the acceptance is a rate and any regular sampling of it
        # measures the same rate.
        before = np.asarray(_as_np(link)).copy() if (s % (EQ_SWEEPS_U1 // 10) == 0) else None
        sweep(b, link, dims, beta, dstep)
        if before is not None:
            after = np.asarray(_as_np(link))
            # DERIVED: `0` is the definition of "this link moved" -- a Metropolis proposal is either
            # accepted or not, so the acceptance rate is the fraction of links that changed at all.
            # It is an equality against zero, not a tolerance.
            moved.append(float(np.mean(np.abs(after - before) > 0)))
        if s % EQ_EVERY:
            continue
        phi = action(b, link)
        a = _as_np(phi)
        per = _per_config_mean(a.reshape(EQ_N, -1))
        means.append(float(per.mean()))
        sems.append(float(per.std(ddof=1) / np.sqrt(EQ_N)))
    return means, sems, (float(np.mean(moved)) if moved else float("nan"))


def _as_np(x):
    return x.detach().cpu().numpy() if hasattr(x, "detach") else np.asarray(x)


def _tail(means, sems):
    """The flat tail, found exactly as `store_run_thermalisation.equilibrium` finds it."""
    use = 2
    while use < len(means):
        mu = float(np.mean(means[-use:]))
        if abs(means[-(use + 1)] - mu) > 2 * max(float(np.mean(sems[-use:])), 1e-9):
            break
        use += 1
    return float(np.mean(means[-use:])), float(np.mean(sems[-use:]) / np.sqrt(use)), use


def _stored_means():
    """The shipped means for these betas, read from the thermalisation artifact."""
    import csv
    path = os.path.join(os.path.dirname(HERE), "data", "store_dat_thermalisation.csv")
    if not os.path.exists(path):
        return {}
    out = {}
    with open(path, newline="", encoding="utf-8") as fh:
        for r in csv.DictReader(fh):
            if r["group"] == "u1" and r.get("test") == "level_vs_reference":
                out[float(r["beta"])] = float(r["stored_mean"])
    return out


def main() -> int:
    stored = _stored_means()
    rows = []
    print(f"device: {DEVICE}  sweeps: {EQ_SWEEPS_U1}  chains: {EQ_N}  cadence: {EQ_EVERY}",
          flush=True)
    for beta in BETAS:
        got = {}
        for start in ("hot", "cold"):
            means, sems, acc = _trace(beta, start)
            mu, sem, use = _tail(means, sems)
            got[start] = (mu, sem, use, acc)
            print(f"  beta={beta} {start:<4} tail={mu:.6f} +- {sem:.6f} over {use} blocks, "
                  f"acceptance={acc:.3f}", flush=True)
        (hm, hs, hu, ha), (cm, cs, cu, ca) = got["hot"], got["cold"]
        gap = hm - cm
        z = abs(gap) / np.sqrt(hs ** 2 + cs ** 2)
        # DERIVED: the same multiple-comparison tolerance the classification uses, at the number of
        # brackets measured here -- so "the two starts have met" is decided by the same rule that
        # decides "this ensemble is at equilibrium", not by a second one written for this file.
        tol = tolerance_sigma(len(BETAS))
        closed = z < tol
        sm = stored.get(beta)
        inside = (sm is not None) and (min(cm, hm) <= sm <= max(cm, hm))
        if closed:
            verdict = "bracket_closed"
        elif inside:
            verdict = "bracket_open_stored_inside"
        else:
            verdict = "bracket_open_stored_outside"
        print(f"  beta={beta} gap hot-cold = {gap:+.6f} ({z:.1f} sigma, tol {tol:.2f}) -> {verdict}"
              + (f"; stored {sm:.6f}" if sm is not None else ""), flush=True)
        for start, (mu, sem, use, acc) in got.items():
            rows.append(dict(group="u1", L=L, T=T, beta=beta, start=start, sweeps=EQ_SWEEPS_U1,
                             n_chains=EQ_N, tail_blocks=use, tail_mean=round(mu, 6),
                             tail_sem=round(sem, 6), acceptance=round(acc, 4),
                             stored_mean=(round(sm, 6) if sm is not None else ""),
                             verdict=verdict))
    table.write(OUT, rows, COLS)
    print(f"\nwrote {OUT}: {len(rows)} rows")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
