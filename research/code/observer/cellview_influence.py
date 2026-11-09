"""The TV influence row of the truncated cell-energy field (the Dobrushin law clause for the truncated
cell view), read on the cell energies of cell_read.py (or cube_read_gpu.py). numpy, with the pair correlations
read through entroptics_adapter.correlation.

The field. One real x_c per cell: the cell energy minus its ensemble mean (the subtraction of obsEnergyOn is a
constant). The truncation at level L is the clamp to [-L, L]; L runs over the
quantiles QS of |x| and the largest |x| read.

The conditional law. The law of T_L(x_c) given the other cells is read through the mean S of its 8 nearest
neighbours (T_L applied to each), the cell analogue of the staple sum in influence_local.py: T_L(x_c) is
histogrammed in NY quantile bins per S quantile bin (NS bins). The tests below check that S carries the
dependence.

The influence. Changing one nearest neighbour c' moves S by at most w/8, w the realised range of T_L(x). For a
pair of S bins whose mean S differ by at most w/8 the TV is 1/2 sum |p(.|S_i) - p(.|S_j)|; C is its sup over
such pairs and the row is 8 C (the eight nearest neighbours; the range tests read what lies beyond them).
  * sup: the plain sup on all data; cross-fit: the worst pair chosen on one half of the groups, its TV read
    on the other half (both directions, NSPLIT random splits);
  * errors: delete-one-block jackknife over the groups (shard blocks or chains);
  * null: T_L(x_c) permuted among the centres of each configuration (S kept), the same read.

Range tests (TruncLaw lets influence move one unit of the time separation per step):
  * S2: within each S bin, the TV between the conditional laws in the lowest and highest tercile of the mean
    of the cells at axis distance 2, weighted over S bins, against the same with S2 permuted;
  * SD: the same for the mean of the 24 planar-diagonal cells (c +- e_mu +- e_nu).
Pair reads: the correlation of x_c with x_{c+d} and the TV between the laws of T_L(x_c) given x_{c+d} in its
lowest and highest decile, for d = e_t, 2 e_t, e_x, e_t + e_x.

Controls (CONTROL env, same grid and group structure as the data):
  * "iid": every cell redrawn from the pooled data marginal (independent cells; exact row 0);
  * "gmrf:kappa": a Gaussian Markov field x_c | rest ~ N(kappa sum_nn x, 1), Gibbs (checkerboard) from 0 for
    GIBBS sweeps per configuration; exact row: 8 x the TV, at the selected pair's mean S, of the clamped
    conditional laws, binned with the read's bins (binned) and unbinned (continuous).
Moments: <x^2>, <x^6> (centred) and <e^2>, <e^6> (raw cell energy), jackknifed.

    [CONTROL=iid|gmrf:k] python cellview_influence.py OUT.json grouping KEY file1 file2 ...
grouping: "shardN" (blocks of N consecutive files) or "chain" (chain index within a family; families are the
directory names with a trailing _mc2 folded into _mc). KEY: npz array name (e.g. b8) or "npy" (cube_read_gpu
output, shape (chain, m^4), cell grid not periodic: only interior centres are read).
"""
import json
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code: the adapter
import entroptics_adapter as E  # noqa: E402

# CHOSEN: the truncation quantile levels of UV-A-FINDINGS section 5 (a grid of levels, one per decade)
QS = [0.9, 0.99, 0.999, 0.9999]
NS, NY = 12, 16                   # CHOSEN: S bins and T_L(x) bins
# CHOSEN: random half-splits for the cross-fit (a compute budget against split noise)
NSPLIT = 8
# CHOSEN: jackknife blocks (at most); a budget trading error-of-the-error against block size
NBLK = 10
# CHOSEN: Gibbs sweeps per control configuration (a burn-in budget for the GMRF control)
GIBBS = 400
rng = np.random.default_rng(12345)


def load(files, key, grouping):
    """Cell fields (nconf, m, m, m, m), group id per configuration, periodic flag."""
    fields, gid, labels = [], [], {}
    for i, f in enumerate(files):
        if key == "npy":
            a = np.load(f)
            m = int(round(a.shape[1] ** 0.25))
            a = a.reshape(a.shape[0], m, m, m, m)
        else:
            a = np.load(f)[key]
        fam = os.path.basename(os.path.dirname(f)).replace("_mc2", "_mc")
        for ch in range(a.shape[0]):  # NOT A READ: group labels
            if grouping == "chain":
                lab = (fam, ch)
            else:
                lab = (fam, i // int(grouping[5:]))
            gid.append(labels.setdefault(lab, len(labels)))
        fields.append(a.astype(np.float64))
    return np.concatenate(fields), np.array(gid), key != "npy"


def shifts(X, d):
    return np.roll(X, tuple(-x for x in d), axis=(1, 2, 3, 4))


# DERIVED: s=1 is the unit step, so unit(mu) is the lattice unit vector e_mu
def unit(mu, s=1):
    d = [0, 0, 0, 0]
    d[mu] = s
    return tuple(d)


def interior(m, periodic, r):
    if periodic:
        return np.ones((m,) * 4, bool)
    ok = np.zeros(m, bool)
    ok[r:m - r] = True
    return ok[:, None, None, None] & ok[None, :, None, None] & ok[None, None, :, None] & ok[None, None, None, :]


def statistics(X, periodic):
    """Per centre: x_c, the 8 nearest neighbours, S2 cells, diagonal cells, pair partners; plus config index."""
    n, m = X.shape[0], X.shape[1]
    nn = [unit(mu, s) for mu in range(4) for s in (1, -1)]
    a2 = sorted({tuple(x % m for x in unit(mu, s * 2)) for mu in range(4) for s in (1, -1)})
    dg = [tuple(np.add(unit(mu, s), unit(nu, t))) for mu in range(4) for nu in range(mu + 1, 4)
          for s in (1, -1) for t in (1, -1)]
    pairs = {"t": unit(3), "2t": unit(3, 2), "x": unit(0), "t+x": (1, 0, 0, 1)}
    mask = interior(m, periodic, 1)
    sel = lambda A: A[:, mask]
    out = {"x": sel(X), "nn": np.stack([sel(shifts(X, d)) for d in nn]),
           "dg": np.stack([sel(shifts(X, d)) for d in dg])}
    if periodic:  # cells at axis distance 2 of a non-tiling grid sit across its gap: not read there
        out["a2"] = np.stack([sel(shifts(X, d)) for d in a2])
    pr = {}
    for k, d in pairs.items():  # NOT A READ: pair partners, without wrapping on a non-tiling grid
        if periodic:
            pr[k] = (X.reshape(n, -1), shifts(X, d).reshape(n, -1))
        else:
            src = X[:, :m - d[0], :m - d[1], :m - d[2], :m - d[3]]
            dst = X[:, d[0]:, d[1]:, d[2]:, d[3]:]
            pr[k] = (src.reshape(n, -1), dst.reshape(n, -1))
    out["pairs"] = pr
    return out


def tv(p, q):
    return 0.5 * np.abs(p - q).sum(-1)


def cond_table(y, S, gid, yedges, sedges, G):
    yb = np.clip(np.searchsorted(yedges, y, side="right") - 1, 0, len(yedges) - 2)
    sb = np.clip(np.searchsorted(sedges, S, side="right") - 1, 0, len(sedges) - 2)
    T = np.zeros((G, len(sedges) - 1, len(yedges) - 1))
    np.add.at(T, (gid, sb, yb), 1.0)
    Ssum = np.zeros((G, len(sedges) - 1))
    np.add.at(Ssum, (gid, sb), S)
    return T, Ssum


def row_from(T, Ssum, w, pick=None):
    cnt = T.sum(-1)
    # DERIVED: an S bin with no centres has no conditional law to compare (a count, exact)
    ok = cnt > 0
    P = np.where(ok[:, None], T / np.maximum(cnt, 1)[:, None], 0.0)
    Sbar = Ssum / np.maximum(cnt, 1)
    D = tv(P[:, None, :], P[None, :, :])
    adm = (np.abs(Sbar[:, None] - Sbar[None, :]) <= w / 8.0) & ok[:, None] & ok[None, :]
    if pick is not None:
        i, j = pick
        return 8.0 * D[i, j], pick
    D = np.where(adm, D, -1.0)
    k = np.unravel_index(np.argmax(D), D.shape)
    return 8.0 * D[k], k


def read_level(st, gid, G, L, blocks):
    x = st["x"]
    y = np.clip(x, -L, L)
    S = np.clip(st["nn"], -L, L).mean(0)
    cfg = np.repeat(gid[:, None], x.shape[1], 1)
    y, S, g = y.ravel(), S.ravel(), cfg.ravel()
    yedges = np.unique(np.quantile(y, np.linspace(0, 1, NY + 1)))
    yedges[0], yedges[-1] = -np.inf, np.inf
    sedges = np.quantile(S, np.linspace(0, 1, NS + 1))
    sedges[0], sedges[-1] = -np.inf, np.inf
    w = float(np.clip(x, -L, L).max() - np.clip(x, -L, L).min())
    T, Ss = cond_table(y, S, g, yedges, sedges, G)
    # null: y permuted among centres of each configuration (rows of the (conf, centre) array)
    yp = np.clip(x, -L, L)
    yp = np.take_along_axis(yp, rng.permuted(np.tile(np.arange(yp.shape[1]), (yp.shape[0], 1)), axis=1), 1).ravel()
    Tn, Ssn = cond_table(yp, S, g, yedges, sedges, G)

    def full(Tx, Sx, sub):
        return row_from(Tx[sub].sum(0), Sx[sub].sum(0), w)[0]

    def xfit(Tx, Sx, sub):
        sub = np.asarray(sub)
        vals = []
        for _ in range(NSPLIT):  # NOT A READ: random half-splits
            perm = rng.permutation(sub)
            A, B = perm[: len(sub) // 2], perm[len(sub) // 2:]
            for P1, P2 in ((A, B), (B, A)):
                _, k = row_from(Tx[P1].sum(0), Sx[P1].sum(0), w)
                vals.append(row_from(Tx[P2].sum(0), Sx[P2].sum(0), w, pick=k)[0])
        return float(np.mean(vals))

    allg = np.arange(G)
    res = {"L": L, "w": w, "n_centres": int(y.size)}
    for name, (Tx, Sx) in {"data": (T, Ss), "null": (Tn, Ssn)}.items():
        sup_all, k = row_from(Tx.sum(0), Sx.sum(0), w)
        xf_all = xfit(Tx, Sx, allg)
        jk_s, jk_x = [], []
        for b in blocks:  # NOT A READ: delete-one-block jackknife
            sub = np.setdiff1d(allg, b)
            jk_s.append(full(Tx, Sx, sub))
            jk_x.append(xfit(Tx, Sx, sub))
        nb = len(blocks)
        err = lambda v: float(math.sqrt((nb - 1) / nb * np.sum((np.array(v) - np.mean(v)) ** 2)))
        res[name] = {"sup": float(sup_all), "sup_err": err(jk_s), "xfit": xf_all, "xfit_err": err(jk_x),
                     "pair": [int(k[0]), int(k[1])]}
        if name == "data":
            cnt = Tx.sum(0).sum(-1)
            res["Sbar"] = (Sx.sum(0) / np.maximum(cnt, 1)).tolist()
            res["yedges"] = yedges.tolist()
    # Kantorovich (W1) form of the same read: W1 between the conditional laws of two S bins per unit change of
    # one neighbour, W1_ij / (8 |S_i - S_j|), times the 8 neighbours; pairs at least NS // 4 bins apart
    sb = np.clip(np.searchsorted(sedges, S, side="right") - 1, 0, NS - 1)
    U = np.linspace(0.005, 0.995, 199)

    def w1row(yy, sub):
        ok = np.isin(g, sub)
        Q = np.array([np.quantile(yy[ok & (sb == s)], U) for s in range(NS)])
        Sm = np.array([S[ok & (sb == s)].mean() for s in range(NS)])
        best, ext = 0.0, 0.0
        for a in range(NS):  # NOT A READ: bin pairs
            for b in range(a + NS // 4, NS):
                r = np.mean(np.abs(Q[a] - Q[b])) / abs(Sm[a] - Sm[b])
                best = max(best, r)
        ext = np.mean(np.abs(Q[0] - Q[-1])) / abs(Sm[0] - Sm[-1])
        return best, ext

    for lab, yy in (("data", y), ("null", yp)):
        b0, e0 = w1row(yy, allg)
        jb, je = [], []
        for bl in blocks:  # NOT A READ: delete-one-block jackknife
            bb, ee = w1row(yy, np.setdiff1d(allg, bl))
            jb.append(bb)
            je.append(ee)
        nb = len(blocks)
        err = lambda v: float(math.sqrt((nb - 1) / nb * np.sum((np.array(v) - np.mean(v)) ** 2)))
        res["w1_" + lab] = {"sup": float(b0), "sup_err": err(jb), "extreme": float(e0), "extreme_err": err(je)}
    # range tests: S2 and diagonal terciles inside S bins
    for key in [k for k in ("a2", "dg") if k in st]:
        Z = np.clip(st[key], -L, L).mean(0).ravel()
        vals = {}
        for lab, Zx in (("data", Z), ("null", rng.permutation(Z))):
            sb = np.clip(np.searchsorted(sedges, S, side="right") - 1, 0, NS - 1)
            yb = np.clip(np.searchsorted(yedges, y, side="right") - 1, 0, len(yedges) - 2)
            tot, wt = 0.0, 0.0
            for s in range(NS):  # NOT A READ: S bins
                ii = sb == s
                # CHOSEN: least centres in an S bin for its terciles to be read (about 10 per tercile); bins
                # below it are skipped, so this decides which bins enter the weighted range test
                if ii.sum() < 30:
                    continue
                lo, hi = np.quantile(Zx[ii], [1 / 3, 2 / 3])
                a = np.bincount(yb[ii & (Zx <= lo)], minlength=len(yedges) - 1).astype(float)
                c = np.bincount(yb[ii & (Zx > hi)], minlength=len(yedges) - 1).astype(float)
                tot += ii.sum() * tv(a / a.sum(), c / c.sum())
                wt += ii.sum()
            vals[lab] = tot / wt
        res["range_" + key] = vals
    return res


def pair_reads(st, L):
    out = {}
    for k, (a, b) in st["pairs"].items():
        a, b = a.ravel(), b.ravel()
        r = E.correlation(a, b)
        ya = np.clip(a, -L, L)
        edges = np.unique(np.quantile(ya, np.linspace(0, 1, NY + 1)))
        edges[0], edges[-1] = -np.inf, np.inf
        lo, hi = np.quantile(b, [0.1, 0.9])
        h = lambda s: np.histogram(ya[s], edges)[0].astype(float)
        p, q = h(b <= lo), h(b > hi)
        bp = rng.permutation(b)
        pn, qn = h(bp <= lo), h(bp > hi)
        out[k] = {"corr": r, "tv_decile": float(tv(p / p.sum(), q / q.sum())),
                  "tv_null": float(tv(pn / pn.sum(), qn / qn.sum()))}
    return out


def moments(X, gid, blocks, mean):
    res = {}
    for lab, A in (("centred", X - mean), ("raw", X)):
        for p in (2, 6):
            v = A.reshape(A.shape[0], -1) ** p
            full = float(v.mean())
            jk = [float(v[~np.isin(gid, b)].mean()) for b in blocks]
            nb = len(blocks)
            e = math.sqrt((nb - 1) / nb * np.sum((np.array(jk) - np.mean(jk)) ** 2))
            res[f"{lab}_m{p}"] = [full, e]
    return res


def gmrf(shape, kappa):
    X = np.zeros(shape)
    m = shape[1]
    par = np.indices((m,) * 4).sum(0) % 2
    for _ in range(GIBBS):  # NOT A READ: checkerboard Gibbs sweeps
        for c in (0, 1):
            s = sum(np.roll(X, s_, axis=ax) for ax in (1, 2, 3, 4) for s_ in (1, -1))
            new = kappa * s + rng.standard_normal(shape)
            X = np.where(par[None] == c, new, X)
    return X


def exact_row(res, kappa, L):
    """8 x TV of the clamped conditionals N(8 kappa S, 1) at the mean S of the S bins: at the pair the read
    selected, and the sup over every admissible pair (|S_i - S_j| <= w/8), binned with the read's bins and
    unbinned (continuous)."""
    from math import erf
    Phi = lambda z: 0.5 * (1 + erf(z / math.sqrt(2)))
    e = np.clip(np.array(res["yedges"]), -L, L)
    e[0], e[-1] = -np.inf, np.inf  # the clamp puts the tails in the end bins
    # DERIVED: the infinite end edges have Phi(-inf) = 0 and Phi(+inf) = 1; the sign test picks which
    pb = lambda mu: np.diff([Phi(v - mu) if np.isfinite(v) else (0.0 if v < 0 else 1.0) for v in e])
    g = np.linspace(-L, L, 4001)
    dens = lambda mu: np.exp(-0.5 * (g - mu) ** 2) / math.sqrt(2 * math.pi)
    cont = lambda m1, m2: 0.5 * (abs(Phi(-L - m1) - Phi(-L - m2)) + abs(Phi(m1 - L) - Phi(m2 - L))
                                 + np.trapezoid(np.abs(dens(m1) - dens(m2)), g))
    Sb = np.array(res["Sbar"])
    i, j = res["data"]["pair"]
    out = {"binned_at_pick": 8 * float(tv(pb(8 * kappa * Sb[i]), pb(8 * kappa * Sb[j]))),
           "continuous_at_pick": 8 * float(cont(8 * kappa * Sb[i], 8 * kappa * Sb[j]))}
    bs, cs = 0.0, 0.0
    for a in range(len(Sb)):  # NOT A READ: admissible pairs
        for b in range(len(Sb)):
            if abs(Sb[a] - Sb[b]) <= res["w"] / 8.0:
                bs = max(bs, float(tv(pb(8 * kappa * Sb[a]), pb(8 * kappa * Sb[b]))))
                cs = max(cs, float(cont(8 * kappa * Sb[a], 8 * kappa * Sb[b])))
    out["binned_sup"], out["continuous_sup"] = 8 * bs, 8 * cs
    return out


if __name__ == "__main__":
    out, grouping, key, files = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
    X, gid, periodic = load(files, key, grouping)
    mean = float(X.mean())
    control = os.environ.get("CONTROL", "")
    kappa = None
    if control == "iid":
        pool = (X - mean).ravel()
        X = rng.choice(pool, size=X.shape) + mean
    elif control.startswith("gmrf:"):
        kappa = float(control[5:])
        X = gmrf(X.shape, kappa) + mean
    G = int(gid.max()) + 1
    groups = np.arange(G)
    blocks = [b for b in np.array_split(groups, min(NBLK, G)) if len(b)]
    st = statistics(X - mean, periodic)
    ax = np.abs(X - mean).ravel()
    levels = [(f"q{q}", float(np.quantile(ax, q))) for q in QS] + [("max", float(ax.max()))]
    rep = {"files": files, "key": key, "grouping": grouping, "control": control, "periodic": periodic,
           "nconf": int(X.shape[0]), "m": int(X.shape[1]), "groups": G, "blocks": len(blocks), "mean": mean,
           "sd": float(np.std(X)), "moments": moments(X, gid, blocks, mean), "levels": {}}
    for name, L in levels:
        r = read_level(st, gid, G, L, blocks)
        r["pairs"] = pair_reads(st, L)
        if kappa is not None:
            r["exact"] = exact_row(r, kappa, L)
        rep["levels"][name] = r
        d, n = r["data"], r["null"]
        print(name, f"L={L:.3f} w={r['w']:.2f} n={r['n_centres']} sup={d['sup']:.3f}+-{d['sup_err']:.3f} "
              f"xfit={d['xfit']:.3f}+-{d['xfit_err']:.3f} null={n['sup']:.3f}/{n['xfit']:.3f} "
              + (f"S2={r['range_a2']['data']:.3f}/{r['range_a2']['null']:.3f} " if "range_a2" in r else "") +
              f"SD={r['range_dg']['data']:.3f}/{r['range_dg']['null']:.3f} "
              f"corr_t={r['pairs']['t']['corr']:.3f} corr_2t={r['pairs']['2t']['corr']:.3f} "
              f"W1={r['w1_data']['sup']:.3f}+-{r['w1_data']['sup_err']:.3f} ext={r['w1_data']['extreme']:.3f} "
              f"W1null={r['w1_null']['sup']:.3f}"
              + (f" exact={r['exact']}" if kappa is not None else ""), flush=True)
    json.dump(rep, open(out, "w"), indent=1)
