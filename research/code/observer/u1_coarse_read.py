"""The coarse-link part of the joint view's near row, on compact U(1): the TV influence row of the cell-scale coarse
links. numpy only.

The coarse link of a cell of side b at its corner X in direction mu is the holonomy of the observer-smoothed field
along the cell's edge, Theta_mu(X) = sum_{j < b} theta_s(bX + j mu, mu) (u1_cell_read.py's theta_s). The coarse
plaquettes are the b x b Wilson loops of the smoothed field. For a coarse link l, S_l is the sum of its six
staples, so that sum_{p containing l} cos(P_p) = |S_l| cos(Theta_l + arg S_l); the read takes the conditional law of
phi_l = Theta_l + arg S_l given r_l = |S_l| (a Wilson-like coarse action), the analogue of influence_read.py's staple
modulus for SU(2).

Influence. Changing one other coarse link of a plaquette through l changes one staple term of S_l, a unit vector,
so S_l moves by at most 2: r' within r +- 2 and arg S rotating by at most arcsin(2/r) (pi if r <= 2). The influence
of that link is the TV distance sup over such moves between the laws of phi at (r, 0) and (r', delta): read from the
densities h_i of phi in bins of r (each reconstructed from its first KH harmonics <cos k phi>, <sin k phi>, the U(1)
character series with Fejer weights, which keeps the density non-negative and the sampling noise of a histogram out
of the TV; the TV of the smoothed laws is a lower reading of the TV of the laws) as max over bin pairs |r_i - r_j| <= 2 and shifts |delta| <= delta_max of
(1/2) sum |h_i(phi) - h_j(phi - delta)|. Each coarse link is in 6 plaquettes with 3 other links each, so the row is
18 C. Cross-fit: the worst (i, j, delta) is chosen on one half of the chains and its TV read on the other half;
null: the same read on two random halves of one bin (the histogram noise floor).

Control (KEY=theta EXACT_BETA=beta, b = 1): the raw links of a Wilson ensemble at coupling beta, whose single-link
conditional law given its staples is exactly exp(beta r cos phi). The read is repeated with each bin's harmonics
replaced by their exact values, the mean over the bin's links of I_k(beta r)/I_0(beta r), so the exact row on the
same bins, harmonics and shifts is printed beside the read one.

    [KEY=theta_s] [KH=6] [EXACT_BETA=..] python u1_coarse_read.py OUT.json b file1.npz file2.npz ...
"""
import os
import json
import sys

import numpy as np

# CHOSEN: grid on [-pi, pi) for the reconstructed densities and the shifts; it also sets the shift resolution
# of the sup (2 pi / 256), so the sup over delta is read on this grid
NPHI = 256
KH = int(__import__("os").environ.get("KH", 6))  # CHOSEN: harmonics kept (character series of the U(1) law)
# CHOSEN: r bins (quantiles of r); a resolution-vs-noise budget
NR = 12
# CHOSEN: least samples in an r bin for it to enter the sup (half of it per cross-fit half); bins below it are
# skipped, so it decides which pairs the sup ranges over
MINCOUNT = 400


def coarse_links(ts, b):
    """ts: (chain, x, y, z, t, mu) smoothed phases; returns (chain, m, m, m, m, mu) coarse holonomies."""
    out = np.zeros(ts.shape, dtype=np.float64)
    for mu in range(4):  # NOT A READ: the edge sums
        acc = np.zeros(ts.shape[:-1])
        for j in range(b):
            acc += np.roll(ts[..., mu], -j, axis=1 + mu)
        out[..., mu] = acc
    return out[:, ::b, ::b, ::b, ::b, :]


def phi_r(Th):
    """phi = Theta + arg S and r = |S| for every coarse link (chain, m^4, mu)."""
    sh = lambda a, mu, s: np.roll(a, -s, axis=1 + mu)
    phis, rs = [], []
    for mu in range(4):
        S = 0
        for nu in range(4):
            if nu == mu:
                continue
            a_up = sh(Th[..., nu], mu, 1) - sh(Th[..., mu], nu, 1) - Th[..., nu]
            a_dn = (sh(Th[..., nu], nu, -1) - sh(sh(Th[..., nu], nu, -1), mu, 1)
                    - sh(Th[..., mu], nu, -1))
            S = S + np.exp(1j * a_up) + np.exp(1j * a_dn)
        phis.append(np.angle(np.exp(1j * (Th[..., mu] + np.angle(S)))))
        rs.append(np.abs(S))
    return np.stack(phis, -1), np.stack(rs, -1)


GRID = np.linspace(-np.pi, np.pi, NPHI, endpoint=False)


def hists(phi, r, edges, exact_beta=None):
    """Per r bin: the count in column 0 and the density of phi on GRID from its first KH harmonics
    (p = (1/2pi)[1 + 2 sum_k (<cos k phi> cos k x + <sin k phi> sin k x)]), as probabilities on GRID."""
    ib = np.clip(np.searchsorted(edges, r, side="right") - 1, 0, len(edges) - 2)
    nb = len(edges) - 1
    cnt = np.bincount(ib, minlength=nb).astype(float)
    dens = np.ones((nb, NPHI))
    for k in range(1, KH + 1):  # NOT A READ: the character series
        if exact_beta is None:
            ck = np.bincount(ib, np.cos(k * phi), minlength=nb) / np.maximum(cnt, 1)
            sk = np.bincount(ib, np.sin(k * phi), minlength=nb) / np.maximum(cnt, 1)
        else:
            from scipy.special import ive
            ck = np.bincount(ib, ive(k, exact_beta * r) / ive(0, exact_beta * r), minlength=nb) / np.maximum(cnt, 1)
            sk = np.zeros(nb)
        fej = 1 - k / (KH + 1)  # Fejer weights: a non-negative density, the law smoothed on a scale 2 pi/KH
        dens += 2 * fej * (ck[:, None] * np.cos(k * GRID)[None] + sk[:, None] * np.sin(k * GRID)[None])
    return np.concatenate([cnt[:, None], dens / NPHI], 1)


def worst(Ha, centres, ok):
    """Worst (i, j, shift) on histograms Ha and its TV."""
    P = Ha[:, 1:]
    best = (-1.0, None)
    dphi = 2 * np.pi / NPHI
    for i in range(len(centres)):  # NOT A READ: admissible pairs
        if not ok[i]:
            continue
        for j in range(len(centres)):
            # DERIVED: one other coarse link changes one unit staple term, so S moves by at most 2: r' in r +- 2
            if not ok[j] or abs(centres[i] - centres[j]) > 2:
                continue
            # DERIVED: a move of S by at most 2 turns arg S by at most arcsin(2/r), any angle (pi) when r <= 2
            dmax =np.pi if centres[i] <= 2 else np.arcsin(min(1.0, 2 / centres[i]))
            for s in range(-int(dmax / dphi), int(dmax / dphi) + 1):
                tv = 0.5 * np.abs(P[i] - np.roll(P[j], s)).sum()
                if tv > best[0]:
                    best = (tv, (i, j, s))
    return best


def tv_at(H, key):
    i, j, s = key
    P = H[:, 1:]
    return 0.5 * np.abs(P[i] - np.roll(P[j], s)).sum()


if __name__ == "__main__":
    out, b, files = sys.argv[1], int(sys.argv[2]), sys.argv[3:]
    phis, rs = [], []
    for f in files:
        ts = np.load(f)[os.environ.get("KEY", "theta_s")].astype(np.float64)
        ph, r = phi_r(coarse_links(ts, b))
        phis.append(ph)
        rs.append(r)
    phi = np.concatenate(phis, 0)   # (chain*shard, m, m, m, m, mu)
    r = np.concatenate(rs, 0)
    # groups: one per chain of one run (directory), so independent runs never share a group
    dirs = sorted({os.path.dirname(os.path.abspath(f)) for f in files})
    chain = np.concatenate([np.arange(len(p_)) + dirs.index(os.path.dirname(os.path.abspath(f))) * 1000
                            for f, p_ in zip(files, phis)])
    groups = np.unique(chain)
    nch = len(groups)
    edges = np.quantile(r, np.linspace(0, 1, NR + 1))
    edges[-1] += 1e-9
    centres = 0.5 * (edges[1:] + edges[:-1])
    rng = np.random.default_rng(20261005)
    H = hists(phi.ravel(), r.ravel(), edges)
    ok = H[:, 0] >= MINCOUNT
    full = worst(H, centres, ok)
    xf, nulls = [], []
    for sp in range(8):  # NOT A READ: cross-fit half-splits of the chains
        A = rng.permutation(groups)[: nch // 2]
        selA = np.isin(chain, A)
        HA = hists(phi[selA].ravel(), r[selA].ravel(), edges)
        HB = hists(phi[~selA].ravel(), r[~selA].ravel(), edges)
        okAB = (HA[:, 0] >= MINCOUNT // 2) & (HB[:, 0] >= MINCOUNT // 2)
        kA = worst(HA, centres, okAB)[1]
        kB = worst(HB, centres, okAB)[1]
        xf.append(0.5 * (tv_at(HB, kA) + tv_at(HA, kB)))
        # null: one bin read against itself across the halves
        i = full[1][0]
        nulls.append(0.5 * np.abs(HA[i, 1:] - HB[i, 1:]).sum())
    xf, nulls = np.array(xf), np.array(nulls)
    cosphi = float(np.cos(phi).mean())
    eb = os.environ.get("EXACT_BETA")
    exact = None
    if eb:
        HE = hists(phi.ravel(), r.ravel(), edges, exact_beta=float(eb))
        exact = {"C_exact_sup": worst(HE, centres, ok)[0], "C_exact_at_read": tv_at(HE, full[1])}
        exact["row_exact_sup"] = 18 * exact["C_exact_sup"]
    rep = {"files": files, "b": b, "m": int(phi.shape[1]), "KH": KH, "links": int(phi.size),
           "r_quantiles": edges.tolist(), "mean_cos_phi": cosphi, "mean_r": float(r.mean()),
           "C_sup": full[0], "C_xfit": float(xf.mean()), "C_xfit_sd": float(xf.std()),
           "C_null": float(nulls.mean()), "row_sup": 18 * full[0], "row_xfit": 18 * float(xf.mean()),
           "row_null": 18 * float(nulls.mean()), "worst": [int(v) for v in full[1]], "exact": exact}
    print(json.dumps({k: v for k, v in rep.items() if k not in ("files", "r_quantiles")}), flush=True)
    with open(out, "w") as f:
        json.dump(rep, f, indent=1)
