"""The Dobrushin influence of the observer's coarse configuration, from influence_read.py's histograms.

For each block level k the conditional law of a coarse link U given its staple sum A (|A| = r, direction a in
R^4, t = <u, a>) is read as its density relative to Haar,

    g_r(t) = 1 + sum_{n=1}^{N*} c_n(r) U_n(t),   c_n(r) = mean of U_n(t) over the links in the r bin,

the SU(2) character expansion: every c_n is a bin mean, nothing is fitted. The links are histogrammed in
theta = arccos t; each theta bin carries the Haar-weighted bin mean of U_n. N* is the largest n whose chi^2 over the populated bins
(c_n against its jackknife error) exceeds ZCUT times the largest chi^2 of any character on the shuffled null; the fine r
bins are merged into bins of at least min(TGT, links/12) links, and c_n(r) is linear between the merged bins'
mean values of r.

The influence of one plaquette partner l' of l. Changing U_{l'} replaces one unit staple s in A = rho + s by
another s' (any unit quaternion: one link of a staple rotates the staple freely). With a = rho + s and
a' = rho + s', the total variation distance between the two conditionals is

    TV = (1/2) E_{(x, w) uniform on the unit disk} | g_{|a|}(x) - g_{|a'|}(x cos phi + w sin phi) |,

cos phi = <a, a'>/(|a||a'|), since the projection of the uniform law on S^3 to a 2-plane is uniform on the
disk. C = sup over rho, s, s' with |a| and |a'| inside the populated range (a sup over neighbourhoods the
ensemble realises): a sampled search over (|rho|, s, s') refined by Nelder-Mead. The Dobrushin row sum of the
plaquette partners is 18 C (6 staples x 3 links).

The box influence (a Dobrushin row sum to be held <= alpha) does not use the TV: its entries
q(e^{2 beta n2}) + q(e^{2 mix}) bound tanh(osc/4), osc the oscillation over u of the log-ratio of the two
conditionals. So every box representation of a conditional has
entries at least tanh(osc/4) of that conditional. That entry is read too (Cosc, row18osc), on the same
geometries.

Errors: delete-one-block jackknife over shard blocks (the search is rerun at the full-sample optimum and
its neighbourhood for every block).

Controls computed here:
  * exact Wilson at the campaign's beta for k = 0: the same TV with g_r(t) = e^{beta r t}/Z(beta r), both
    restricted to the data's populated r range and over every rho (|rho| <= 5);
  * the null: the same search on the shuffled-neighbourhood histograms at the data's N*.
Staple sufficiency: the bin means of <u, v_rect> and <u, v_adj> (influence_read.py), in units of the
linear-response couplings eps_rect = E<u, v>/(|v_perp| (1 - E t^2)/3) and the same for adj.

Also: the jackknife bias-corrected sup (row18_bc = 18 (n C - (n-1) mean C_jk)); with AGG_SIZES=1 the sup on
disjoint shard groups of S/8, S/4, S/2, S shards (how the sup moves with sample size), with the cross-fit
value (worst geometry found on one half of a group, its TV read on the other half: free of the selection
bias a sup over noisy estimates carries); and, when the read
carries them, the row read inside each tercile of the rectangle alignment q_rect and the adjoint invariant
q_adj at the full read's truncation (the effect of conditioning on more than |A|).

    [AGG_SIZES=1] python influence_agg.py READ.npz[+READ2.npz...] [beta_for_exact or -] [levels] > out.json
Joined reads are pooled shard by shard (the tercile edges of each read are its own).
"""
import json
import os
import sys

import numpy as np
from scipy.optimize import minimize

# CHOSEN: a character is kept when its chi^2 exceeds twice the null maximum. This factor decides the
# truncation N*, and N* feeds every row read below; it is a margin over the null, not derived from it
ZCUT = 2.0
# CHOSEN: links per merged r bin (at most a twelfth of the level's links); a resolution-vs-noise budget
TGT = 5e5
# CHOSEN: highest character examined (the ceiling on N*); a budget, N* has to land below it to be read
NMAX = 48
# CHOSEN: jackknife blocks over shards (at most); a budget trading error-of-the-error against block size
NBLK = 16
RNG = np.random.default_rng(7)

# the disk quadrature: equal-area polar grid
_nr, _na = 120, 240
_rad = np.sqrt((np.arange(_nr) + 0.5) / _nr)
_ang = (np.arange(_na) + 0.5) / _na * 2 * np.pi
DX = (_rad[:, None] * np.cos(_ang)[None, :]).ravel()
DW = (_rad[:, None] * np.sin(_ang)[None, :]).ravel()


def cheb(t, n):
    """U_1..U_n at t, shape (n, len(t))."""
    out = np.empty((n, len(t)))
    um, u = np.ones_like(t), 2 * t
    for i in range(n):  # NOT A READ: the Chebyshev recursion
        out[i] = u
        um, u = u, 2 * t * u - um
    return out


# CHOSEN: sub=64 midpoint sub-samples per theta bin for the Haar-weighted bin average; a quadrature resolution
def bin_chars(nt, sub=64):
    """U_n averaged over each theta bin under the Haar weight sin^2 theta (a bin-centre value is biased: its
    Haar mean is not 0 and the bias exceeds the statistical error at 10^7 links)."""
    th = (np.arange(nt * sub) + 0.5) / (nt * sub) * np.pi
    w = np.sin(th) ** 2
    U = cheb(np.cos(th), NMAX) * w
    return U.reshape(NMAX, nt, sub).sum(-1) / w.reshape(nt, sub).sum(-1)


class Law:
    """g_r(t) = 1 + sum_n c_n(r) U_n(t), c_n linear in r between the populated bins' mean r."""

    def __init__(self, rgrid, C):
        self.r, self.C = rgrid, C            # C: (nbins, N)

    def coef(self, r):
        return np.array([np.interp(r, self.r, self.C[:, j]) for j in range(self.C.shape[1])])

    def g(self, r, t):
        # DERIVED: no characters kept (N* = 0) leaves the Haar density, g = 1
        if self.C.shape[1] == 0:
            return np.ones_like(t)
        return 1.0 + self.coef(r) @ cheb(t, self.C.shape[1])


class Exact:
    """Wilson: g_r(t) = exp(beta r t)/Z, Z = E_Haar exp(beta r t) = 2 I_1(beta r)/(beta r)."""

    def __init__(self, beta):
        self.beta = beta
        th = (np.arange(4000) + 0.5) / 4000 * np.pi
        self._t, self._w = np.cos(th), np.sin(th) ** 2 * (2 / np.pi) * (np.pi / 4000)

    def g(self, r, t):
        k = self.beta * r
        Z = (np.exp(k * (self._t - 1)) * self._w).sum()
        return np.exp(k * (t - 1)) / Z

    def coefs(self, r, n):
        return cheb(self._t, n) @ (self.g(r, self._t) * self._w)


# the unit circle, where the oscillation's extremes lie
CX, CW = np.cos(np.linspace(0, 2 * np.pi, 1441)), np.sin(np.linspace(0, 2 * np.pi, 1441))
# CHOSEN: a truncated series that reaches 0 gives an unbounded log-ratio; it is floored here. Where the floor
# acts the oscillation is ~ln(1e9) and tanh(osc/4) is within 1e-2 of 1, so the entry reads saturated
GFLOOR = 1e-9


def tv(law, r1, r2, cphi):
    sphi = np.sqrt(max(0.0, 1 - cphi * cphi))
    return 0.5 * np.abs(law.g(r1, DX) - law.g(r2, DX * cphi + DW * sphi)).mean()


def osc(law, r1, r2, cphi):
    """tanh(osc/4) of the log-ratio of the two conditionals: the entry the box's boxInfl bounds."""
    sphi = np.sqrt(max(0.0, 1 - cphi * cphi))
    x, w = np.concatenate([DX, CX]), np.concatenate([DW, CW])
    L = np.log(np.maximum(law.g(r1, x), GFLOOR)) - np.log(np.maximum(law.g(r2, x * cphi + w * sphi), GFLOOR))
    return np.tanh((L.max() - L.min()) / 4)


def geom(p):
    """p = (rho, s[4], s'[4]) -> |a|, |a'|, cos phi with a = rho e0 + s, a' = rho e0 + s'."""
    rho = p[0]
    s = p[1:5] / np.linalg.norm(p[1:5])
    sp = p[5:9] / np.linalg.norm(p[5:9])
    a = s.copy(); a[0] += rho
    b = sp.copy(); b[0] += rho
    na, nb = np.linalg.norm(a), np.linalg.norm(b)
    return na, nb, float(a @ b / max(na * nb, 1e-12))


# DERIVED: rhomax=5.0 -- rho is the sum of the other five unit staples of the six (A = rho + s), so |rho| <= 5.
# CHOSEN: nrho=23 |rho| grid points, npair=300 staple pairs per point, refine=4 Nelder-Mead starts: a search
# budget; the sup read is a lower reading of the true sup whatever these are
def search(law, rlo, rhi, rhomax=5.0, nrho=23, npair=300, refine=4, seeds=None, metric=tv):
    """sup TV over geometries with |a|, |a'| in [rlo, rhi]. Returns (C, best params, top params)."""
    def val(p):
        # DERIVED: p[0] is |rho|, a magnitude, so it lies in [0, rhomax]
        if not (0 <= p[0] <= rhomax):
            return 0.0
        r1, r2, c = geom(p)
        if not (rlo <= r1 <= rhi and rlo <= r2 <= rhi):
            return 0.0
        return metric(law, r1, r2, c)
    cand = []
    if seeds is None:
        for rho in np.linspace(0, rhomax, nrho):  # NOT A READ: the |rho| grid of the search
            s = RNG.normal(size=(npair, 4)); sp = RNG.normal(size=(npair, 4))
            sp[: npair // 3] = -s[: npair // 3]           # the antipodal family, Wilson's worst case
            for i in range(npair):  # NOT A READ: the sampled staple pairs
                cand.append(np.concatenate([[rho], s[i], sp[i]]))
    else:
        cand = list(seeds)
    vals = np.array([val(p) for p in cand])
    order = np.argsort(-vals)
    best, bp = vals[order[0]], cand[order[0]]
    for i in order[:refine]:  # NOT A READ: Nelder-Mead from the best sampled geometries
        res = minimize(lambda p: -val(p), cand[i], method="Nelder-Mead",
                       options={"xatol": 1e-4, "fatol": 1e-7, "maxiter": 1500})
        if -res.fun > best:
            best, bp = -res.fun, res.x
    top = [cand[i] for i in order[:30]] + [bp]
    return best, bp, top


def merge(d, k):
    """Level k with the fine r bins merged outward into bins of at least min(TGT, links/12) links each."""
    cnt = d["cnt"][:, k].sum(0)
    tgt = min(TGT, cnt.sum() / 12)
    groups, cur, acc = [], [], 0.0
    for i in range(len(cnt)):  # NOT A READ: the merge of consecutive fine bins
        # DERIVED: empty fine bins before a group opens carry no links (a count, exact)
        if cnt[i] == 0 and not cur:
            continue
        cur.append(i); acc += cnt[i]
        if acc >= tgt:
            groups.append(cur); cur, acc = [], 0.0
    if cur:
        if groups and acc < tgt / 2:
            groups[-1] += cur
        else:
            groups.append(cur)
    M = np.zeros((len(groups), len(cnt)))
    for j, g in enumerate(groups):
        M[j, g] = 1.0
    out = {}
    for key, v in d.items():
        if key.endswith("Q") or key.startswith("L"):   # tercile splits; influence_local.py's moments
            continue
        x = v[:, k]
        out[key] = (np.einsum("jb,sb...->sj...", M, x))[:, None]
    return out


def level_read(d, k, beta=None, nfix=None, light=False, sizes=False, rrange=None):
    d, klev, k = merge(d, k), k, 0
    S = d["cnt"].shape[0]
    blocks = np.array_split(np.arange(S), min(NBLK, S))
    Uth = bin_chars(d["ch"].shape[-1])                    # (NMAX, NT)

    def coefs(sel, key):
        cnt = d["cnt"][sel, k].sum(0)
        h = d[key][sel, k].sum(0)                         # (NB, NT)
        with np.errstate(invalid="ignore", divide="ignore"):
            return cnt, (h @ Uth.T) / cnt[:, None], d["rsum"][sel, k].sum(0) / cnt
    allsel = np.arange(S)
    cnt, c, rm = coefs(allsel, "ch")
    _, cN, _ = coefs(allsel, "chN")
    # DERIVED: a populated bin holds at least one link (a count, exact)
    good = cnt > 0
    # the contiguous populated range around the most populated bin
    m = int(np.argmax(cnt)); lo = hi = m
    # DERIVED: 0 is the first bin index (array bound)
    while lo - 1 >= 0 and good[lo - 1]:
        lo -= 1
    while hi + 1 < len(cnt) and good[hi + 1]:
        hi += 1
    bins = np.arange(lo, hi + 1)
    jk = [coefs(np.setdiff1d(allsel, b), "ch")[1][bins] for b in blocks]
    nb = len(blocks)
    jk = np.array(jk)
    err = np.sqrt((nb - 1) / nb * ((jk - jk.mean(0)) ** 2).sum(0))      # (nbins, NMAX)
    # the truncation, calibrated on the null: chi^2 over the populated bins of each character, against the
    # largest chi^2 any character reaches on the shuffled-neighbourhood histograms
    def chi2(cc, key):
        jj = np.array([coefs(np.setdiff1d(allsel, b), key)[1][bins] for b in blocks])
        ee = np.sqrt((nb - 1) / nb * ((jj - jj.mean(0)) ** 2).sum(0))
        # DERIVED: a zero jackknife error is a division guard; such a term enters the chi^2 as 0, not as infinity
        return ((cc[bins] / np.where(ee > 0, ee, np.inf)) ** 2).sum(0)
    chi_d, chi_n = chi2(c, "ch"), chi2(cN, "chN")
    thr = ZCUT * chi_n.max()
    sig = np.where(chi_d > thr)[0]
    Nstar = int(sig.max() + 1) if len(sig) else 0
    if nfix is not None:
        Nstar = nfix
    rg = rm[bins]
    rlo, rhi = (float(rg[0]), float(rg[-1])) if rrange is None else rrange
    law = Law(rg, c[bins][:, :Nstar])
    C, bp, top = search(law, rlo, rhi)
    Cjk = [search(Law(rg, jk[i][:, :Nstar]), rlo, rhi, seeds=top, refine=1)[0] for i in range(nb)]
    Cjk = np.array(Cjk)
    Cerr = float(np.sqrt((nb - 1) / nb * ((Cjk - Cjk.mean()) ** 2).sum()))
    Cbc = float(nb * C - (nb - 1) * Cjk.mean())           # jackknife bias-corrected sup
    if light:
        return {"k": klev, "links": float(cnt.sum()), "Nstar": Nstar, "row18": 18 * float(C),
                "row18_err": 18 * Cerr, "row18_bc": 18 * Cbc, "r_range": [float(rg[0]), float(rg[-1])], "r_used": [rlo, rhi]}
    size_study = None
    if sizes:
        # the sup against sample size: disjoint shard groups of S/f shards, the same truncation and bins
        size_study = []
        for f in (8, 4, 2, 1):  # NOT A READ: the subsample fractions
            # DERIVED: a group of S/f shards needs at least one shard
            if S // f < 1:
                continue
            perm = np.random.default_rng(f).permutation(S)
            vals, xf = [], []
            lo_, hi_ = float(rg[0]), float(rg[-1])
            for g in range(f):  # NOT A READ: the disjoint groups
                sel = perm[g * (S // f):(g + 1) * (S // f)]
                cg = coefs(sel, "ch")[1][bins][:, :Nstar]
                vals.append(search(Law(rg, cg), lo_, hi_, nrho=12, npair=150, refine=2)[0])
                # cross-fit: the worst geometry chosen on one half of the group, its TV read on the other half
                # DERIVED: two halves of at least one shard each need two shards
                if len(sel) >= 2:
                    h = len(sel) // 2
                    halves = (sel[:h], sel[h:2 * h])
                    laws = [Law(rg, coefs(x, "ch")[1][bins][:, :Nstar]) for x in halves]
                    for a_, b_ in ((0, 1), (1, 0)):  # NOT A READ: both directions of the cross-fit
                        bpa = search(laws[a_], lo_, hi_, nrho=12, npair=150, refine=2)[1]
                        xf.append(tv(laws[b_], *geom(bpa)))
            vals, xf = np.array(vals), np.array(xf)
            size_study.append({"shards": int(S // f), "groups": f, "row18_mean": 18 * float(vals.mean()),
                               # DERIVED: a sample sd (ddof=1) needs at least two groups
                               "row18_sd": 18 * float(vals.std(ddof=1)) if f > 1 else None,
                               "row18_values": (18 * vals).tolist(),
                               "row18_xfit_mean": 18 * float(xf.mean()) if len(xf) else None,
                               # DERIVED: a sample sd (ddof=1) needs at least two cross-fit values
                               "row18_xfit_sd": 18 * float(xf.std(ddof=1)) if len(xf) > 1 else None})
            print(f"  size {S // f} shards x {f}: row18 {18 * vals.mean():.4f}"
                  # DERIVED: a sample sd (ddof=1) needs at least two groups
                  + (f" sd {18 * vals.std(ddof=1):.4f}" if f > 1 else "")
                  # DERIVED: a sample sd (ddof=1) needs at least two cross-fit values
                  + (f" xfit {18 * xf.mean():.4f} sd {18 * xf.std(ddof=1):.4f}" if len(xf) > 1 else ""),
                  file=sys.stderr, flush=True)
    Cnull = search(Law(rg, cN[bins][:, :Nstar]), rlo, rhi)[0]
    Co, bpo, topo = search(law, rlo, rhi, metric=osc, nrho=12, npair=150)
    Cojk = np.array([search(Law(rg, jk[i][:, :Nstar]), rlo, rhi, seeds=topo, refine=1, metric=osc)[0]
                     for i in range(nb)])
    Coerr = float(np.sqrt((nb - 1) / nb * ((Cojk - Cojk.mean()) ** 2).sum()))
    Conull = search(Law(rg, cN[bins][:, :Nstar]), rlo, rhi, metric=osc, nrho=12, npair=150)[0]
    r1, r2, cph = geom(bp)
    # staple sufficiency
    ct = c[bins][:, 0] / 2                                 # E[t | r] (U_1 = 2t)
    t2 = (c[bins][:, 1] + 1) / 4                           # E[t^2 | r] (U_2 = 4t^2 - 1)
    w = cnt[bins] / cnt[bins].sum()

    def tilt(key, nkey, sel):
        cn = d["cnt"][sel, k].sum(0)[bins]
        v = d[key][sel, k].sum(0)[bins] / cn
        nv = d[nkey][sel, k].sum(0)[bins] / cn
        eps = v / (nv * (1 - t2) / 3)
        return float((w * v).sum()), float((w * eps).sum())

    loc = {}
    for key, nkey in (("rect", "rectn"), ("adj", "adjn"), ("rectN", "rectn"), ("adjN", "adjn")):
        full = tilt(key, nkey, allsel)
        jj = np.array([tilt(key, nkey, np.setdiff1d(allsel, b)) for b in blocks])
        e = np.sqrt((nb - 1) / nb * ((jj - jj.mean(0)) ** 2).sum(0))
        loc[key] = {"mean_tilt": full[0], "mean_tilt_err": float(e[0]), "eps": full[1], "eps_err": float(e[1])}
    out = {"row18_bc": 18 * Cbc, "size_study": size_study, "k": klev, "links": float(cnt.sum()), "r_range": [rlo, rhi], "r_mode": float(rm[m]),
           "mean_t": float((w * ct).sum()), "Nstar": Nstar, "nbins": int(len(bins)),
           "chi2_data_n1_8": chi_d[:8].tolist(), "chi2_null_max": float(chi_n.max()),
           "C": float(C), "C_err": Cerr, "row18": 18 * float(C), "row18_err": 18 * Cerr,
           "C_null": float(Cnull), "row18_null": 18 * float(Cnull),
           "Cosc": float(Co), "Cosc_err": Coerr, "row18osc": 18 * float(Co), "row18osc_err": 18 * Coerr,
           "row18osc_null": 18 * float(Conull),
           "argmax": {"r1": r1, "r2": r2, "cos_phi": cph, "rho": float(bp[0])},
           "staple_sufficiency": loc,
           "c_n_bins": {"r": rg.tolist(), "c1": c[bins][:, 0].tolist(), "c1_err": err[:, 0].tolist(),
                        "c2": c[bins][:, 1].tolist(), "c3": c[bins][:, 2].tolist()}}
    # DERIVED: only level 0 (the unblocked links) has Wilson's exact conditional (docstring, Controls)
    if beta is not None and klev == 0:
        ex = Exact(beta)
        exc = np.array([ex.coefs(r, 4) for r in rg])       # exact c_1..c_4 at the bin mean r
        out["exact"] = {
            "C_in_range": float(search(ex, rlo, rhi)[0]),
            "C_all": float(search(ex, 0.0, 6.0)[0]),
            "Cosc_in_range": float(search(ex, rlo, rhi, metric=osc, nrho=12, npair=150)[0]),
            "Cosc_all": float(search(ex, 0.0, 6.0, metric=osc, nrho=12, npair=150)[0]),
            "c_read_minus_exact_over_err": ((c[bins][:, :4] - exc) / err[:, :4]).tolist(),
            "max_abs_dev_c1_c4": float(np.abs(c[bins][:, :4] - exc).max()),
        }
        out["exact"]["row18_in_range"] = 18 * out["exact"]["C_in_range"]
        out["exact"]["row18_all"] = 18 * out["exact"]["C_all"]
        out["exact"]["row18osc_in_range"] = 18 * out["exact"]["Cosc_in_range"]
        out["exact"]["row18osc_all"] = 18 * out["exact"]["Cosc_all"]
    return out


if __name__ == "__main__":
    path = sys.argv[1]
    # DERIVED: 2 is [beta_for_exact]'s position in the usage line
    beta =float(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2] != "-" else None
    # READ.npz may be several reads joined by "+": their shards are pooled at the levels they share
    ds = [dict(np.load(x)) for x in path.split("+")]
    metas = [json.loads(str(x.pop("meta"))) for x in ds]
    meta = dict(metas[0])
    meta["kmax"] = min(m["kmax"] for m in metas)
    meta["kmin"] = max(m.get("kmin", 0) for m in metas)
    meta["shards"] = sum(([f"{x}:{n}" for n in m["shards"]] for x, m in zip(path.split("+"), metas)), [])
    d = {key: np.concatenate([x[key][:, :meta["kmax"] + 1] for x in ds], 0) for key in ds[0]}
    res = {"read": path, "campaign": meta["campaign"], "beta": meta["params"]["beta"],
           "L": meta["params"]["dims"][0], "c": meta["c"], "nshards": len(meta["shards"]), "levels": []}
    # DERIVED: 3 is [levels]'s position in the usage line
    only = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else None
    sizes = os.environ.get("AGG_SIZES", "0") == "1"
    for k in range(meta.get("kmin", 0), meta["kmax"] + 1):  # NOT A READ: the block levels read
        if only is not None and k not in only:
            continue
        lv = level_read(d, k, beta, sizes=sizes)
        if "chQ" in d:
            # conditioning beyond |A|: the same read inside each tercile of a further neighbourhood scalar,
            # at the full read's truncation
            # (the sup depends on the r range searched, and the terciles populate different r ranges, so all
            # rows, the unsplit one included, are read on the r range common to the three terciles)
            lv["tercile_rows"] = {}
            for j, nm in enumerate(("q_rect", "q_adj")):  # NOT A READ: the two further scalars
                dqs = [{"cnt": d["cntQ"][:, :, j, m], "rsum": d["rsumQ"][:, :, j, m],
                        "ch": d["chQ"][:, :, j, m], "chN": d["chQ"][:, :, j, m]} for m in range(3)]
                rngs = [level_read(dq, k, nfix=0, light=True)["r_range"] for dq in dqs]
                common = (max(x[0] for x in rngs), min(x[1] for x in rngs))
                rows = [level_read(dq, k, nfix=lv["Nstar"], light=True, rrange=common) for dq in dqs]
                full = level_read(d, k, nfix=lv["Nstar"], light=True, rrange=common)
                lv["tercile_rows"][nm] = {"common_r": list(common), "unsplit": full, "terciles": rows}
                print(f"  {nm} r in [{common[0]:.2f},{common[1]:.2f}] unsplit {full['row18']:.4f}+-{full['row18_err']:.4f}"
                      f" terciles: " + " ".join(f"{x['row18']:.4f}+-{x['row18_err']:.4f}" for x in rows),
                      file=sys.stderr, flush=True)
            lv["tercile_edges"] = meta.get("edges", {}).get(str(k))
        res["levels"].append(lv)
        print(f"k={k} N*={lv['Nstar']} r=[{lv['r_range'][0]:.2f},{lv['r_range'][1]:.2f}] "
              f"C={lv['C']:.5f}+-{lv['C_err']:.5f} row18={lv['row18']:.4f} bc={lv['row18_bc']:.4f} null={lv['row18_null']:.4f} "
              f"osc18={lv['row18osc']:.4f}+-{lv['row18osc_err']:.4f} oscnull={lv['row18osc_null']:.4f} "
              f"rect eps={lv['staple_sufficiency']['rect']['eps']:.4f} adj eps={lv['staple_sufficiency']['adj']['eps']:.4f}"
              + (f" exact_in={lv['exact']['row18_in_range']:.4f} exact_all={lv['exact']['row18_all']:.4f}"
                 f" exactosc_in={lv['exact']['row18osc_in_range']:.4f} exactosc_all={lv['exact']['row18osc_all']:.4f}"
                 if "exact" in lv else ""), file=sys.stderr, flush=True)
    print(json.dumps(res, indent=1))
