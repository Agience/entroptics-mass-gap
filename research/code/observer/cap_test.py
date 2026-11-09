"""Does the observer's step cap the energy density at a fixed physical aperture on Haar-random links?

The step is observer_step.step (BlockSU2.blockLink on the same lattice, ApeLattice.apeConf). A fixed physical
aperture on a fixed physical box: L = L0 * 2^j sites (a = 1/L), n = n0 * 4^j steps (n a^2 fixed). The
substrate is Haar-random links (beta = 0), the roughest there is. Per lattice size and seed this prints
a^-4 (1 - (1/2) tr P) in box units, (L/L0)^4 * (1 - (1/2) tr P), as its mean and its maximum over all
plaquettes of the six planes, and the unscaled mean. The cap holds at this worst case when the scaled values
stay bounded in j.

    python cap_test.py c L0 n0 jmax seeds
"""
import json
import sys

import numpy as np

import observer_step as O
from lattice_generator import _Backend

bg = _Backend(None)


def oneminus(q):
    """(6, x, y, z, t): 1 - (1/2) tr P per plane, for one configuration (x, y, z, t, mu, 4)."""
    return np.stack(list(O.planes(bg, q)))


if __name__ == "__main__":
    c, L0, n0, jmax, seeds = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    for j in range(jmax + 1):
        L, n = L0 * 2 ** j, n0 * 4 ** j
        for s in range(seeds):
            rng = np.random.default_rng(1000 * j + s)
            q = rng.standard_normal((L, L, L, L, O.D, 4))
            q /= np.linalg.norm(q, axis=-1, keepdims=True)
            for _ in range(n):
                q = O.step(bg, q, c)
            e = oneminus(q) * (L / L0) ** 4
            row = {"L": L, "n": n, "seed": s, "scaled_mean": float(e.mean()), "scaled_max": float(e.max()),
                   "raw_mean": float(e.mean() / (L / L0) ** 4)}
            print(json.dumps(row), flush=True)
