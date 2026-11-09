"""The Kantorovich (W1) influence row of the cell-energy field, read by local-linear distribution regression.
numpy only.

The quantity. For a cell x and a cell y, C(x, y) is the Lipschitz constant in W1 of x's conditional energy
law in y's energy: for two 1-D laws W1 = int |F_1 - F_2| dt = int_0^1 |Q_1 - Q_2| du, so

    C(x, y)(omega) = int |d F_x(t | omega) / d omega_y| dt = int_0^1 |d Q_x(u | omega) / d omega_y| du,

and the row is sum_y C(x, y). Dobrushin's coefficient takes the sup over omega; the read reports the row as
a function of where omega sits (through S, the mean of the 8 nearest-neighbour cells), its largest value
over the read S range, and its centre-weighted mean.

The estimator. At a point s0 of S, every centre gets the weight K((S - s0) / (h sd(S))), K Gaussian, and the
indicator 1{x_c <= t_j} is regressed, weighted least squares, on 1 and the regressor cells (the 8 nearest
neighbours; or those, the 24 planar diagonals and the axis-distance-2 cells). The slope beta_y(t_j; s0) is
d F(t_j | omega) / d omega_y, local-linear in omega inside the window (h = inf: one global linear fit).
The thresholds t_j are NT quantiles of x in [UQ0, 1 - UQ0]; the t-integral is the trapezoid on them.
Every sum is additive over centres, so the read keeps, per group (chain or chain-shard), the sums
A_g = sum w X X' and C_g(t) = sum_{x <= t} w X, and every split and jackknife replicate is a sum of these.

Regressor sets (SETS env): "nn" the 8 nearest neighbours; "all" those, the 24 planar diagonals and the
axis-distance-2 cells (periodic grid, m >= 4); "box" those and the 48 + 16 cells of the 3^4 box with three or
four non-zero offsets; "range" (range_regressors) every cell of a periodic grid, classed by time
separation. A truncated set reads the partial influence of the cells it holds; cells outside it
act through their correlation with the held cells.

Readings of the row at each (s0, h), bracketing the noise of |beta|:
  * upper   sum_y int |beta_y| dt on all data (|.| of a noisy slope reads high: E|b + e| >= |b|);
  * xfit    sum_y int sign(beta_y^A) beta_y^B dt, averaged over the two directions of NSPLIT random
            half-splits of the groups (E sign(b + e_A) (b + e_B) = |b| (1 - 2 P(sign wrong)) <= |b|);
  * mean    sum_y |int beta_y dt| = sum_y |d E[x | omega] / d omega_y|, the conditional-mean slope
            (equals the row when every beta_y(t) has one sign in t; below it otherwise).
  * signed  sum_y d E[x | omega] / d omega_y (the sign of the coupling), and xmean, the cross-fit of mean.
upper - xfit sizes the noise; xfit - mean sizes the part of the influence that is not a shift of the mean.
Errors: delete-one-block jackknife over the groups. The largest row over s0 and its error are read per
replicate.

Controls (CONTROL env; same grid, centres and groups as the data):
  * "iid": cells redrawn from the pooled data marginal (row 0);
  * "gmrf:k": x_c | rest ~ N(k sum_nn x, 1) (row 8k at every omega);
  * "gmrf2:k1:k2": x_c | rest ~ N(k1 sum_nn x + k2 sum_dg x, 1); row 8|k1| + 24|k2|, above 1 for mixed signs with a positive-definite precision
    (k1 = 0.1, k2 = -0.02: row 1.28, precision eigenvalues in [0.60, 2.28]);
  * "gmrf3:kt:ks:kd": time and space nearest-neighbour couplings apart, and the planar diagonals; row
    2|kt| + 6|ks| + 24|kd|;
  * "phi4:lam:r": density of x_c given the rest prop. to exp(-x^2/2 - lam x^4 + k h x), h = sum_nn x,
    with k = r / (8 Var(X | h = 0)); exact row 8 k Var(X | h) (the exponential family:
    d F(t | h) / d h = k Cov(1{X <= t}, X) <= 0 for every t, and int Cov(1{X > t}, X) dt = Var X);
    the reference at (s0, h) is its kernel-weighted mean over the centres.
  Every control is drawn by GIBBS sweeps over colour classes that hold no coupled pair (colours()), on the
  read's own periodic grid.

    [CONTROL=...] python cellview_w1.py OUT.json grouping KEY file1 file2 ...
grouping: "chain", "shardN" (cellview_influence.load) or "chainshard" (one group per chain per file).
KEY: npz array name (b8, ...) or "npy" (cube_read_gpu output, non-tiling grid: interior centres only).
"""
import json
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cellview_influence import interior, load, shifts, unit

# CHOSEN: thresholds t_j for the t-integral; a quadrature grid (trapezoid), finer costs only time
NT = 200
UQ0 = float(os.environ.get("UQ0", 0.001))  # CHOSEN: threshold quantile range [UQ0, 1 - UQ0]
SETS = os.environ.get("SETS", "nn,all").split(",")  # CHOSEN: regressor sets read
# CHOSEN: kernel bandwidths in units of sd(S), a grid from local to global (None = one global linear fit)
HS = [0.15, 0.25, 0.4, 0.6, 1.0, None]
# CHOSEN: s0 at these S quantiles; a grid over the bulk of S, denser at the tails where the sup tends to sit
SQ = [0.02, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 0.95, 0.98]
# CHOSEN: random half-splits for the cross-fit (a compute budget against split noise)
NSPLIT = 8
# CHOSEN: jackknife blocks (at most); a budget trading error-of-the-error against block size
NBLK = 20
# CHOSEN: Gibbs sweeps per control configuration (a burn-in budget for the controls)
GIBBS = 400
rng = np.random.default_rng(int(os.environ.get("SEED", 20261003)))  # SEED: control replicas


def load_groups(files, key, grouping):
    if grouping != "chainshard":
        return load(files, key, grouping)
    X, _, periodic = load(files, key, "shard1")
    gid, k = [], 0
    for f in files:  # NOT A READ: one label per (file, chain)
        n = np.load(f)[key].shape[0] if key != "npy" else np.load(f).shape[0]
        gid += list(range(k, k + n))
        k += n
    return X, np.array(gid), periodic


def regressors(X, periodic):
    """x at the read centres, the regressor cells (columns), their class labels, S = mean of the 8 nn."""
    m = X.shape[1]
    nn = [unit(mu, s) for mu in range(4) for s in (1, -1)]
    dg = [tuple(np.add(unit(mu, s), unit(nu, t))) for mu in range(4) for nu in range(mu + 1, 4)
          for s in (1, -1) for t in (1, -1)]
    a2 = sorted({tuple(v % m for v in unit(mu, 2 * s)) for mu in range(4) for s in (1, -1)})
    offs, lab = list(nn), ["t" if d[3] else "s" for d in nn]
    # DERIVED: a planar diagonal +-e_mu +-e_nu is a distinct cell from the centre and its nn only when m >= 3
    if m >= 3:
        offs += dg
        lab += ["dg"] * len(dg)
    # DERIVED: +-2 e_mu are distinct cells (not each other, not the centre) on a periodic grid only when m >= 4
    if periodic and m >= 4:
        offs += a2
        lab += ["a2"] * len(a2)
    # DERIVED: the 3^4 box around a centre is distinct cells only when m >= 3
    if "box" in SETS and m >= 3:  # the rest of the 3^4 box: offsets with three or four non-zero components
        # DERIVED: in ndindex(3, ...) the index 1 is the zero offset, so v != 1 counts non-zero components
        rest = [d for d in np.ndindex(3, 3, 3, 3) if sum(v != 1 for v in d) >= 3]
        offs += [tuple(v - 1 for v in d) for d in rest]
        # DERIVED: three non-zero components is class b3, four is b4 (index 1 = zero offset, as above)
        lab += ["b3" if sum(v != 1 for v in d) == 3 else "b4" for d in rest]
    mask = interior(m, periodic, 1)
    x = X[:, mask]
    R = np.stack([shifts(X, d)[:, mask] for d in offs], -1)
    return x, R, np.array(lab)


def range_regressors(X, periodic):
    """The "range" set (periodic grid): every cell of the torus, classed by the reach the Lean W1 law allows
    (cellDist = time separation |dt| in cells). Cells within Chebyshev distance 1 and the axis-distance-2 cells
    are single regressors (classes t, s, dg, b3, b4, a2s, a2t); every other cell enters through one regressor per
    |dt|, the mean of its cells (classes agg0, agg1, agg2, ...), whose coefficient is the class's summed
    coefficient: its signed total, a lower reading of its sum of |C|."""
    assert periodic
    m = X.shape[1]
    canon = lambda v: ((v + m // 2) % m) - m // 2 if m % 2 else ((v + m // 2 - 1) % m) - (m // 2 - 1)
    single, slab, agg = [], [], {}
    for d in np.ndindex(m, m, m, m):
        d = tuple(int(canon(v)) for v in d)
        if d == (0, 0, 0, 0):
            continue
        # DERIVED: the number of non-zero offset components names the class (t/s, dg, b3, b4)
        nz = sum(v != 0 for v in d)
        cheb = max(abs(v) for v in d)
        # DERIVED: Chebyshev distance 1 is the near row, read as single regressors (docstring)
        if cheb == 1:
            c = {1: "t" if d[3] else "s", 2: "dg", 3: "b3", 4: "b4"}[nz]
        # DERIVED: one non-zero component at distance 2 is an axis-distance-2 cell (classes a2s, a2t)
        elif nz == 1 and cheb == 2:
            c = "a2t" if d[3] else "a2s"
        else:
            agg.setdefault(abs(d[3]), []).append(d)
            continue
        single.append(d)
        slab.append(c)
    mask = interior(m, periodic, 1)
    cols = [shifts(X, d)[:, mask] for d in single]
    mult = [1.0] * len(single)
    for j in sorted(agg):
        cols.append(sum(shifts(X, d) for d in agg[j])[:, mask] / len(agg[j]))
        mult.append(1.0)  # the mean's coefficient is the class's summed coefficient
        slab.append(f"agg{j}")
    return np.stack(cols, -1), np.array(slab), np.array(mult)


def boxsum(E, b):
    """Sum of E over the b^4 cube with lower corner at every site, periodic (cumulative sums, no transform)."""
    S = E.astype(np.float64)
    for ax in range(4):
        L = S.shape[ax]
        P = np.concatenate([S, np.take(S, range(b), axis=ax)], axis=ax)
        c = np.cumsum(P, axis=ax)
        c = np.concatenate([np.zeros_like(np.take(c, [0], axis=ax)), c], axis=ax)
        S = np.take(c, range(b, b + L), axis=ax) - np.take(c, range(L), axis=ax)
    return S


def load_slide(files, key, grouping):
    """Cells of side b on a sliding grid ("slide:b:stride", from cell_read.py's E): a centre at every site of the
    stride grid, its 8 nearest-neighbour cells at +-b along each axis and its 24 planar-diagonal cells at
    +-b e_mu +- b e_nu. The cells of one neighbourhood are disjoint while 3 b <= L. Groups: one per chain per
    file ("chainshard") or per chain of a family ("chain")."""
    _, b, stride = key.split(":")
    b, stride = int(b), int(stride)
    nn = [unit(mu, s) for mu in range(4) for s in (1, -1)]
    dg = [tuple(np.add(unit(mu, s), unit(nu, t))) for mu in range(4) for nu in range(mu + 1, 4)
          for s in (1, -1) for t in (1, -1)]
    xs, Rs, gid, labels = [], [], [], {}
    for i, f in enumerate(files):
        E = np.load(f)["E"]
        L = E.shape[1]
        assert 3 * b <= L
        o = np.arange(0, L, stride)
        I = np.stack(np.meshgrid(o, o, o, o, indexing="ij"), -1).reshape(-1, 4)
        fam = os.path.basename(os.path.dirname(f)).replace("_mc2", "_mc")
        for ch in range(E.shape[0]):  # NOT A READ: one chain at a time bounds the memory
            S = boxsum(E[ch], b)
            at = lambda d: S[tuple(((I + b * np.array(d)) % L).T)]
            xs.append(at((0, 0, 0, 0)))
            Rs.append(np.stack([at(d) for d in nn + dg], -1))
            lab = (fam, ch) if grouping == "chain" else (f, ch)
            gid.append(labels.setdefault(lab, len(labels)))
    x = np.stack(xs)
    m0 = float(x.mean())
    x, R = x - m0, np.stack(Rs) - m0
    lab = np.array(["t" if d[3] else "s" for d in nn] + ["dg"] * len(dg))
    return x, R, lab, np.array(gid)


class Read:
    """Per-group sufficient statistics of the weighted indicator regression at one (s0, h)."""

    def __init__(self, y, R, g, G, tj, w):
        Xd = np.concatenate([np.ones((len(y), 1)), R], 1)
        Xw = Xd * w[:, None]
        p1 = Xd.shape[1]
        self.A = np.zeros((G, p1, p1))
        for gg in range(G):  # NOT A READ: per-group Gram matrices
            s = g == gg
            self.A[gg] = Xd[s].T @ Xw[s]
        tb = np.searchsorted(tj, y, side="left")  # 1{y <= t_j} for j >= tb
        idx = g * (len(tj) + 1) + tb
        H = np.stack([np.bincount(idx, Xw[:, c], G * (len(tj) + 1)) for c in range(p1)], -1)
        self.C = np.cumsum(H.reshape(G, len(tj) + 1, p1), 1)[:, :len(tj)]  # (G, T, p1)

    def beta(self, sub):
        A = self.A[sub].sum(0)
        C = self.C[sub].sum(0)
        return np.linalg.solve(A, C.T)[1:]  # (p, T)


def readings(rd, sub, dt, cls, splits, mult=None):
    B = rd.beta(sub)
    if mult is not None:  # an aggregated regressor carries the summed coefficient of its cells
        B = B * mult[:, None]
    up = np.abs(B) @ dt
    mean = np.abs(B @ dt)
    sig = -(B @ dt)  # d E[x | omega] / d omega_y
    xf = np.zeros(B.shape[0])
    xm = np.zeros(B.shape[0])
    for a, b in splits:  # NOT A READ: cross-fit halves
        Ba, Bb = rd.beta(a), rd.beta(b)
        if mult is not None:
            Ba, Bb = Ba * mult[:, None], Bb * mult[:, None]
        xf += 0.5 * ((np.sign(Ba) * Bb) @ dt + (np.sign(Bb) * Ba) @ dt)
        ma, mb = Ba @ dt, Bb @ dt
        xm += 0.5 * (np.sign(ma) * mb + np.sign(mb) * ma)
    xf /= len(splits)
    xm /= len(splits)
    out = {}
    for name, sel in cls.items():  # upper, xfit, mean, signed mean slope, cross-fit mean
        out[name] = [float(up[sel].sum()), float(xf[sel].sum()), float(mean[sel].sum()), float(sig[sel].sum()),
                     float(xm[sel].sum())]
    return out


def make_splits(sub):
    sp = []
    for _ in range(NSPLIT):  # NOT A READ: random half-splits
        p = rng.permutation(sub)
        sp.append((p[: len(p) // 2], p[len(p) // 2:]))
    return sp


def colours(shape):
    """Update classes holding no coupled pair (nn or planar diagonal): the 16 sublattices (i_mu mod 2) on an
    even grid; single sites on an odd one (there i_mu mod 2 pairs the cells across the wrap)."""
    m = shape[1]
    # DERIVED: the 16 parity sublattices hold no coupled pair only on an even grid (docstring)
    if m % 2 == 0:
        sub =(np.indices(shape[1:]) % 2 * np.array([1, 2, 4, 8])[:, None, None, None, None]).sum(0)
    else:
        sub = np.arange(m ** 4).reshape(shape[1:])
    return [sub == c for c in np.unique(sub)]


NN = [unit(mu, s) for mu in range(4) for s in (1, -1)]
DG = [tuple(np.add(unit(mu, s), unit(nu, t))) for mu in range(4) for nu in range(mu + 1, 4)
      for s in (1, -1) for t in (1, -1)]


def gibbs(shape, draw, dg=False):
    """GIBBS sweeps over the colour classes; draw(h_nn, h_dg) samples a cell given its neighbour sums."""
    X = np.zeros(shape)
    for _ in range(GIBBS):  # NOT A READ: Gibbs sweeps
        for c in colours(shape):
            hn = sum(shifts(X, d) for d in NN)
            hd = sum(shifts(X, d) for d in DG) if dg else None
            # DERIVED: a draw taking 3 arguments also wants the field X (gmrf3); the others take (hn, hd)
            X = np.where(c[None], draw(hn, hd, X) if draw.__code__.co_argcount == 3 else draw(hn, hd), X)
    return X


def gmrf2(shape, k1, k2):
    """x_c | rest ~ N(k1 sum_nn x + k2 sum_dg x, 1)."""
    return gibbs(shape, lambda hn, hd: k1 * hn + k2 * hd + rng.standard_normal(shape), dg=True)


def gmrf3(shape, kt, ks, kd):
    """x_c | rest ~ N(kt sum_time-nn x + ks sum_space-nn x + kd sum_dg x, 1): row 2|kt| + 6|ks| + 24|kd|."""
    tn = [unit(3, 1), unit(3, -1)]
    return gibbs(shape, lambda hn, hd, X: (kt - ks) * sum(shifts(X, d) for d in tn) + ks * hn + kd * hd
                 + rng.standard_normal(shape), dg=True)


def gmrf(shape, kappa):
    return gibbs(shape, lambda hn, hd: kappa * hn + rng.standard_normal(shape))


class Phi4:
    def __init__(self, lam, r):
        self.xg = np.linspace(-6, 6, 4001)
        V = 0.5 * self.xg ** 2 + lam * self.xg ** 4
        p0 = np.exp(-(V - V.min()))
        self.k = r / (8 * self.var_of(p0))
        self.hg = np.linspace(-60, 60, 2401)
        self.ug = np.linspace(0, 1, 2001)
        self.Q = np.empty((len(self.hg), len(self.ug)))
        self.var = np.empty(len(self.hg))
        for i, h in enumerate(self.hg):  # NOT A READ: tabulate the exact conditionals
            e = -V + self.k * h * self.xg
            p = np.exp(e - e.max())
            self.var[i] = self.var_of(p)
            F = np.cumsum(p)
            F = (F - F[0]) / (F[-1] - F[0])
            self.Q[i] = np.interp(self.ug, F, self.xg)

    def var_of(self, p):
        p = p / p.sum()
        mu = (p * self.xg).sum()
        return float((p * (self.xg - mu) ** 2).sum())

    def hidx(self, h):
        return np.clip(np.rint((h - self.hg[0]) / (self.hg[1] - self.hg[0])).astype(int), 0, len(self.hg) - 1)

    def draw(self, h):
        i = self.hidx(h)
        u = rng.random(h.shape) * (len(self.ug) - 1)
        j = np.minimum(u.astype(int), len(self.ug) - 2)
        f = u - j
        return (1 - f) * self.Q[i, j] + f * self.Q[i, j + 1]

    def sample(self, shape):
        return gibbs(shape, lambda hn, hd: self.draw(hn))

    def row(self, h):
        return 8 * self.k * self.var[self.hidx(h)]


if __name__ == "__main__":
    out, grouping, key, files = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
    slide = key.startswith("slide:")
    if slide:
        x, R, lab, gid = load_slide(files, key, grouping)
        X, periodic = np.zeros((x.shape[0], int(key.split(":")[1]))), False
    else:
        X, gid, periodic = load_groups(files, key, grouping)
    control = os.environ.get("CONTROL", "")
    exact = None
    if control == "iid":
        pool = (X - X.mean()).ravel()
        X = rng.choice(pool, size=X.shape)
    elif control.startswith("gmrf:"):
        X = gmrf(X.shape, float(control[5:]))
    elif control.startswith("gmrf2:"):
        k1, k2 = (float(v) for v in control[6:].split(":"))
        X = gmrf2(X.shape, k1, k2)
    elif control.startswith("gmrf3:"):
        kt, ks, kd = (float(v) for v in control[6:].split(":"))
        X = gmrf3(X.shape, kt, ks, kd)
    elif control.startswith("phi4:"):
        lam, r = (float(v) for v in control[5:].split(":"))
        ph = Phi4(lam, r)
        X = ph.sample(X.shape)
    if not slide:
        X = X - X.mean()
        x, R, lab = regressors(X, periodic)
    n, nc = x.shape
    S = R[..., :8].mean(-1)
    if control.startswith("phi4:"):
        exact = ph.row(8 * S).ravel()
    elif control.startswith("gmrf:"):
        exact = np.full(x.size, 8 * float(control[5:]))
    elif control.startswith("gmrf2:"):
        exact = np.full(x.size, 8 * abs(k1) + 24 * abs(k2))
    elif control.startswith("gmrf3:"):
        exact = np.full(x.size, 2 * abs(kt) + 6 * abs(ks) + 24 * abs(kd))
    elif control == "iid":
        exact = np.zeros(x.size)
    g = np.repeat(gid[:, None], nc, 1).ravel()
    y, S, R = x.ravel(), S.ravel(), R.reshape(-1, R.shape[-1])
    G = int(gid.max()) + 1
    allg = np.arange(G)
    blocks = [b for b in np.array_split(rng.permutation(allg), min(NBLK, G)) if len(b)]
    tj = np.quantile(y, np.linspace(UQ0, 1 - UQ0, NT))
    dt = np.gradient(tj)  # trapezoid weights on the threshold grid (half-intervals at the ends)
    dt[0], dt[-1] = 0.5 * (tj[1] - tj[0]), 0.5 * (tj[-1] - tj[-2])
    nall = int(np.isin(lab, ["t", "s", "dg", "a2"]).sum())
    sets = {k: v for k, v in {"nn": slice(0, 8), "all": slice(0, nall), "box": slice(0, R.shape[1])}.items()
            if k in SETS}
    sdS = float(S.std())
    s0s = np.quantile(S, SQ)
    rep = {"files": files, "key": key, "grouping": grouping, "control": control, "periodic": periodic,
           "nconf": int(n), "m": int(X.shape[1]), "centres": int(y.size), "groups": G, "blocks": len(blocks),
           "sd_x": float(y.std()), "sd_S": sdS, "s0": s0s.tolist(), "SQ": SQ, "HS": [h if h else "inf" for h in HS],
           "regressors": {k: int(lab[v].size) for k, v in sets.items()}, "reads": {}}
    if control.startswith("phi4:"):
        rep["phi4_k"] = ph.k
    if "range" in SETS:
        Rr, lr, mr = range_regressors(X, periodic)
        sets["range"] = None
    for sname, sl in sets.items():
        Rs, ls, mult = (R[:, sl], lab[sl], None) if sl is not None else (Rr.reshape(-1, Rr.shape[-1]), lr, mr)
        cls = {"row": np.ones(len(ls), bool)}
        for c in ["t", "s", "dg", "a2", "b3", "b4", "a2s", "a2t"] + sorted({v for v in ls if v.startswith("agg")}):
            if (ls == c).any():
                cls[c] = ls == c
        res = {}
        for h in HS:
            hk = str(h) if h else "inf"
            res[hk] = []
            locs = [None] if h is None else list(s0s)
            for s0 in locs:
                w = np.ones_like(y) if s0 is None else np.exp(-0.5 * ((S - s0) / (h * sdS)) ** 2)
                rd = Read(y, Rs, g, G, tj, w)
                full = readings(rd, allg, dt, cls, make_splits(allg), mult)
                jk = []
                for b in blocks:  # NOT A READ: delete-one-block jackknife
                    sub = np.setdiff1d(allg, b)
                    jk.append(readings(rd, sub, dt, cls, make_splits(sub), mult))
                nb = len(blocks)
                ent = {"s0": None if s0 is None else float(s0), "neff": float(w.sum() ** 2 / (w ** 2).sum()),
                       "read": full, "jk": jk}
                if exact is not None:
                    ent["exact"] = float((w * exact).sum() / w.sum())
                res[hk].append(ent)
            # summary per h: largest row over s0 and centre-weighted mean (weights: S density at s0 ~ equal
            # spacing in quantile, so the mean over the SQ points between 0.1 and 0.9 is the typical value)
            summ = {}
            for k in range(5):  # upper, xfit, mean, signed, xmean
                vals = np.array([e["read"]["row"][k] for e in res[hk]])
                jv = np.array([[e["jk"][b]["row"][k] for e in res[hk]] for b in range(nb)])
                er = lambda v: float(math.sqrt((nb - 1) / nb * np.sum((v - v.mean()) ** 2)))
                # CHOSEN: the "typical" row averages the s0 points at S quantiles 0.1..0.9, dropping the four
                # tail points of SQ; a choice of which part of the S range counts as typical
                mid =[i for i, q in enumerate(SQ) if 0.1 <= q <= 0.9] if h else [0]
                summ[["upper", "xfit", "mean", "signed", "xmean"][k]] = {
                    "max": float(vals.max()), "max_err": er(jv.max(1)), "argmax_s0q": SQ[int(vals.argmax())] if h else None,
                    "typ": float(vals[mid].mean()), "typ_err": er(jv[:, mid].mean(1)),
                    "per_s0": vals.tolist(), "per_s0_err": [er(jv[:, i]) for i in range(len(vals))]}
            if exact is not None:
                ex = np.array([e["exact"] for e in res[hk]])
                summ["exact"] = {"max": float(ex.max()), "typ": float(ex[mid].mean()), "per_s0": ex.tolist()}
            for e in res[hk]:  # the per-replicate dicts are summarised above
                e["jk_err"] = {c: [er(np.array([j[c][k] for j in e["jk"]])) for k in range(5)] for c in e["read"]}
                del e["jk"]
            mp = res[hk][len(res[hk]) // 2]
            classes = {c: f"{mp['read'][c][1]:.3f}+-{mp['jk_err'][c][1]:.3f}/{mp['read'][c][3]:+.3f}" for c in mp["read"]}
            res[hk] = {"summary": summ, "points": res[hk]}
            su = summ
            print(sname, f"h={hk}", "upper max/typ", f"{su['upper']['max']:.3f}+-{su['upper']['max_err']:.3f}",
                  f"{su['upper']['typ']:.3f}+-{su['upper']['typ_err']:.3f}", "xfit max/typ",
                  f"{su['xfit']['max']:.3f}+-{su['xfit']['max_err']:.3f}", f"{su['xfit']['typ']:.3f}+-{su['xfit']['typ_err']:.3f}",
                  "xmean typ", f"{su['xmean']['typ']:.3f}+-{su['xmean']['typ_err']:.3f}",
                  ("exact max/typ " + f"{su['exact']['max']:.3f}/{su['exact']['typ']:.3f}") if exact is not None else "",
                  "classes(xfit/signed, mid s0)", classes, flush=True)
        rep["reads"][sname] = res
    json.dump(rep, open(out, "w"), indent=1)
