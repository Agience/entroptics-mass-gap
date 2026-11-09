"""The cell-energy field of the observer on compact U(1): the gapless control for the Wasserstein row read.

The row read of cellview_w1.py on SU(2) gives a cell-energy W1 row that falls with the cell side and crosses one
near 2 r0. This script makes the same cell field on the abelian foil, so the same read can be run where the
answer is known: compact U(1) in its Coulomb phase (beta above 1.01) has a massless photon, so no cell size
gives exponential clustering, and a row read that carried the gap would have to stay at or above one there.

Per configuration: n applications of the U(1) form of the observer step (observer_step.step's rule with the
group product of U(1): every link at once, V = U + c * (sum of its six staples), U <- V / |V|), then the
six-plane energy density sum_{mu < nu} (1 - Re U_p), then the sum over each cube of side b. The chains are
evolved together (a leading batch axis) by lattice_generator's checkerboard Metropolis from a cold start
(lattice_generator.cold_init: a hot start at Coulomb couplings carries frozen monopole loops for tens of
thousands of sweeps). Writes one npz per shard: for each b, b{b} of shape (chain, m, m, m, m), m = L / b, in the
(x, y, z, t) order; plus plaq, the mean plaquette per chain. With SAVE_LINKS=1 the shard also holds theta (the raw
link phases, (chain, x, y, z, t, direction) float32) and theta_s (the phases after the n observer steps).

    python u1_cell_read.py OUT_DIR L beta nchain therm nshard gap c nsteps b1,b2,... seed
"""
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from lattice_generator import _Backend, _ops, _sax, cold_init  # noqa: E402

# DERIVED: the spacetime dimension of the four-dimensional lattice
D = 4


def staple_sum(b, U, mu):
    """The six staples of the mu-links (complex phases), forward and backward in each nu != mu."""
    S = b.zeros_like(U[..., 0])
    Umu = U[..., mu]
    for nu in range(D):  # NOT A READ: the staple orientations
        if nu == mu:
            continue
        Unu = U[..., nu]
        Unu_pmu = b.roll(Unu, -1, _sax(mu, 0))
        # forward: U_nu(x) U_mu(x + nu) U_nu(x + mu)^-1
        S = S + Unu * b.roll(Umu, -1, _sax(nu, 0)) * b.conj(Unu_pmu)
        # backward: U_nu(x - nu)^-1 U_mu(x - nu) U_nu(x - nu + mu)
        S = S + (b.conj(b.roll(Unu, 1, _sax(nu, 0))) * b.roll(Umu, 1, _sax(nu, 0))
                 * b.roll(Unu_pmu, 1, _sax(nu, 0)))
    return S


def obs_step(b, U, c):
    out = U.copy()
    for mu in range(D):  # NOT A READ: every link at once, from the configuration before the step
        V = U[..., mu] + c * staple_sum(b, U, mu)
        out[..., mu] = V / np.abs(V)
    return out


def energy_density(b, U):
    tot = 0.0
    for mu in range(D):  # NOT A READ: the six plaquette planes
        for nu in range(mu + 1, D):
            P = U[..., mu] * b.roll(U[..., nu], -1, _sax(mu, 0)) * b.conj(b.roll(U[..., mu], -1, _sax(nu, 0))) \
                * b.conj(U[..., nu])
            tot = tot + (1.0 - P.real)
    return tot


def cubes(e, bs):
    """Cube sums over the last four axes of e (leading chain axis kept)."""
    nc, L = e.shape[0], e.shape[1]
    m = L // bs
    assert m * bs == L, "b must divide L"
    return e.reshape(nc, m, bs, m, bs, m, bs, m, bs).sum(axis=(2, 4, 6, 8))


if __name__ == "__main__":
    out, L, beta, nch, therm, nsh, gap = (sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]),
                                          int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7]))
    cw, nst, bs, seed = float(sys.argv[8]), int(sys.argv[9]), [int(v) for v in sys.argv[10].split(",")], \
        int(sys.argv[11])
    os.makedirs(out, exist_ok=True)
    b = _Backend(None).seed(seed)
    _init, sweep, action, dstep = _ops("u1")
    sdims = (L, L, L, L)
    theta = cold_init(b, "u1", sdims, (nch,))
    t0 = time.time()
    for i in range(therm):
        sweep(b, theta, sdims, beta, dstep)
        # CHOSEN: a progress line every 100 thermalisation sweeps; logging cadence only
        if i % 100 == 0:
            print(f"therm {i} plaq {1 - action(b, theta).mean() / 6:.5f} t {time.time() - t0:.0f}s", flush=True)
    for s in range(nsh):
        for _ in range(gap):
            sweep(b, theta, sdims, beta, dstep)
        U = np.exp(1j * theta)
        plaq = 1 - action(b, theta).reshape(nch, -1).mean(1) / 6
        for _ in range(nst):
            U = obs_step(b, U, cw)
        e = energy_density(b, U)
        res = {f"b{bb}": cubes(e, bb).astype(np.float64) for bb in bs}
        res["plaq"] = plaq
        if os.environ.get("SAVE_LINKS") == "1":  # raw and smoothed link phases, for the coarse-link reads
            res["theta"] = theta.astype(np.float32)
            res["theta_s"] = np.angle(U).astype(np.float32)
        np.savez(os.path.join(out, f"u1_L{L}_b{beta}_s{s:03d}_c{cw}_n{nst}.npz"), **res)
        print(f"shard {s} plaq {plaq.mean():.5f} e {float(e.mean()):.5f} t {time.time() - t0:.0f}s", flush=True)
