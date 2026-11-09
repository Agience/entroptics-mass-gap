"""QuotientStep on stored SU(2) data: normalised correlations at matched physical time, beta 2.50 (coarse) vs 2.70 (fine).

ViewQuotient.QuotientStep asks, for every view vector v, R_fine(v, t) <= R_coarse(v, t) + delta at one physical
time, R(v, t) = C_v(t)/C_v(0) the normalised connected reflected correlation. Two reads, no fit:

(a) the observer's energy density at its own scale (paper section 10): zero-momentum slice sums of the spatial-plaquette
    density on the smeared links, n = 31 at beta 2.50 (32^4, 40 shards x 8 chains) and n = 113 at beta 2.70
    (64^4, chains of the _mc and _mc2 runs joined: 4 chains). R(t) = C(t)/C(0).
(b) the 0++ GEVP over five smearing levels at one physical set of radii (levels 5..60 at 2.50, 18..216 at 2.70):
    lambda_0(t) = sup over the measured basis of v'C(t)v / v'C(0)v, the sup of R over the basis.
The fine read is taken at the coarse one's physical times t/r0 = D/(r0/a)_coarse by log-linear interpolation
between its two neighbouring lattice times. Errors: delete-one-chain jackknife at each beta, combined in
quadrature (independent ensembles). r0/a: 6.1 (6.03-6.21) at 2.50, 11.87 (11.4-11.9) at 2.70; both ends shown.

    python quotient_read.py PULLDIR
"""
import glob
import math
import os
import sys

import numpy as np
import scipy.linalg as sla

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code: the adapter
import entroptics_adapter as E  # noqa: E402

P = sys.argv[1]


def load_obs(dirs):
    blocks = {}
    for d in dirs:
        for f in sorted(glob.glob(os.path.join(P, d, "*.npy"))):
            x = np.load(f)
            for ch in range(x.shape[0]):
                blocks.setdefault(ch, []).append(x[ch])
    return [np.stack(blocks[k]) for k in sorted(blocks)]  # each (shard, T)


def load_glue(dirs):
    blocks = {}
    for d in dirs:
        for f in sorted(glob.glob(os.path.join(P, d, "*_glue.npz"))):
            z = np.load(f)
            for ch in range(z["S"].shape[0]):
                blocks.setdefault(ch, []).append(z["S"][ch])
    return [np.stack(blocks[k]) for k in sorted(blocks)]  # each (config, level, T)


def r_obs(X):
    """R(D) = C(D)/C(0), D = 0..T/2: entroptics.reads.decay on the time ring (periodic), each configuration a channel,
    the ensemble mean as the disconnected level."""
    T = X.shape[-1]
    c = np.asarray(E.decay(X.T, periodic=True, disconnected=float(X.mean())), dtype=float)[:T // 2 + 1]
    return c / c[0]


# CHOSEN: tmax=6, the default time range of the GEVP read; both callers below pass their own (3 coarse, 6 fine),
# enough for the compared physical times (fine x = 2 * 11.87 / 6.03 < 4 at Dmax = 2)
def r_glue(X, tmax=6):
    d = X - X.mean(axis=(0, 2), keepdims=True)              # each level's ensemble mean removed
    nl = d.shape[1]
    lags = range(tmax + 1)
    # C_ij(t) from entroptics.reads.cross_covariance on the time ring, configurations as channels; the levels'
    # means differ, so they are removed above and the read is told the records are connected
    M = np.zeros((tmax + 1, nl, nl))
    for i in range(nl):  # NOT A READ: the pairs of smearing levels, each lag profile is the library's
        for j in range(nl):
            M[:, i, j] = E.cross_covariance(d[:, i, :].T, d[:, j, :].T, lags, periodic=True,
                                            disconnected=None) / d.shape[0]
    C = [0.5 * (M[t] + M[t].T) for t in lags]
    out = []
    for t in range(tmax + 1):
        try:
            out.append(sla.eigh(C[t], C[0], eigvals_only=True).max())
        except (np.linalg.LinAlgError, ValueError):
            out.append(np.nan)
    return np.array(out)


def jk(blocks, f):
    full = f(np.concatenate(blocks))
    reps = np.stack([f(np.concatenate([b for j, b in enumerate(blocks) if j != i])) for i in range(len(blocks))])
    n = len(blocks)
    return full, reps, np.sqrt((n - 1) / n * np.nansum((reps - reps.mean(0)) ** 2, axis=0))


def interp(R, x):
    """log-linear interpolation of R at fractional lattice time x (no fit)."""
    i = int(math.floor(x)); w = x - i
    # DERIVED: log-linear interpolation needs both values positive; otherwise it falls back to linear
    if R[i] <= 0 or R[i + 1] <= 0:
        return (1 - w) * R[i] + w * R[i + 1]
    return math.exp((1 - w) * math.log(R[i]) + w * math.log(R[i + 1]))


def compare(name, Rc, ec, repc, Rf, repf, rc, rf_list, Dmax):
    print(f"\n{name}")
    print(f"{'t/r0':>6} {'R coarse':>16} " + " ".join(f"{'R fine r0/a=' + str(rf):>22} {'delta':>16}" for rf in rf_list))
    for D in range(0, Dmax + 1):
        t = D / rc
        row = f"{t:>6.3f} {Rc[D]:>8.4f} +- {ec[D]:<6.4f}"
        for rf in rf_list:
            x = t * rf
            vf = interp(Rf, x)
            ef = np.sqrt((len(repf) - 1) / len(repf) * sum((interp(r, x) - np.mean([interp(q, x) for q in repf])) ** 2 for r in repf))
            de = vf - Rc[D]
            row += f" {vf:>12.4f} +- {ef:<6.4f} {de:>+8.4f} +- {math.hypot(ef, ec[D]):<6.4f}"
        print(row)


oc = load_obs(["obs4/su2_L32_b2.50"]); of = load_obs(["obs4/su2_L64_b2.70_mc", "obs4/su2_L64_b2.70_mc2"])
Rc, repc, ec = jk(oc, r_obs); Rf, repf, ef = jk(of, r_obs)
for rc in (6.03, 6.1, 6.21):
    compare(f"(a) energy density R(t) = C(t)/C(0); coarse r0/a = {rc}", Rc, ec, repc, Rf, repf, rc, (11.4, 11.87), 4)
gc = load_glue(["glue/su2_L32_b2.50"]); gf = load_glue(["glue/su2_L64_b2.70_mc", "glue/su2_L64_b2.70_mc2"])
print(f"\nglue configs: coarse {sum(len(b) for b in gc)} in {len(gc)} chains, fine {sum(len(b) for b in gf)} in {len(gf)} chains")
Gc, repgc, egc = jk(gc, lambda X: r_glue(X, 3)); Gf, repgf, egf = jk(gf, lambda X: r_glue(X, 6))
for rc in (6.03, 6.1, 6.21):
    compare(f"(b) GEVP lambda_0(t), sup of R over the 0++ basis; coarse r0/a = {rc}", Gc, egc, repgc, Gf, repgf, rc, (11.4, 11.87), 2)
