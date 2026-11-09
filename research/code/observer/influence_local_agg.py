"""The rectangle and adjoint rows of the coarse view's Dobrushin influence, from influence_local.py's moments.

Per merged r bin (fine bins merged to at least min(TGT, links/12) links, as influence_agg.py) and pooled over
the populated r range, nothing fitted, every coefficient a solution of moment equations:

  * perpendicular tilts lam_B(t) = aB + bB t (rectangle) and lam_W(t) = aW + bW t (adjoint), the 4x4 moment
    system of influence_local.py; the adjoint quadrupole mu(t) = mu0 + mu1 t from its 2x2 system;
  * the parallel dependence kappa_X,n = d c_n / d X for X = b_par (rectangle) and Q (adjoint invariant):
    the regression of U_n(t) on (r, b_par, Q) with the within-fine-bin cross moments pooled (r partialled out).

The TV influence of one partner, to first order in the couplings (a change d of a density g gives
TV = (1/2) E|d|):

  * a rectangle slot. A partner link's change moves one unit rectangle staple, so |d b| <= 2. Its
    perpendicular part tilts u by lam_B <u, d b_perp>: TV = (1/2) |d b_perp| E_g[|lam_B| sqrt(1-t^2)] / 2
    (E|<w, e>| = 1/2 for w uniform on S^2). Its parallel part moves c_n by kappa_B,n d b_par:
    TV = (1/2) |d b_par| E_Haar|sum_n kappa_B,n U_n|. With q = E_g[|lam_B| sqrt(1-t^2)]/4 and
    p = E_Haar|sum kappa U|/2 per unit change, the sup over |d b| <= 2 is 2 sqrt(p^2 + q^2).
    The row has 90 slots (18 rectangles x 5 links; a link in several rectangles has the sum of its slots);
  * an adjoint slot (a plaquette partner moves one staple s_p): |d W_perp| <= 1 (each <a^, s> s_perp has
    norm <= 1/2), |d Q| <= 1, and the quadrupole's traceless change has E|w^T dT0 w| <= sqrt(2/15) * 2 sqrt(2/3).
    The slot is the sum of the three parts; the row has 18 slots.

The partners' rows add to the plaquette row of influence_agg.py by the triangle inequality.
Errors: delete-one-block jackknife over shards (NBLK blocks). Null: the same on the permuted-link moments.
Control (a read with INF_SYN): the exact couplings and slot values of the synthetic kernel are printed beside
the read; for the rectangle the exact sup TV between the two Wilson laws is computed too.

    python influence_local_agg.py READ.npz[+READ2.npz...] [level_position] [nuse] > out.json
nuse: characters entering the parallel part (the plaquette read's N*, or larger).
"""
import json
import sys

import numpy as np

import influence_agg as IA

# CHOSEN: jackknife blocks over shards, the value of influence_agg.NBLK (restated here, not imported)
NBLK = 16
# CHOSEN: links per merged r bin, the value of influence_agg.TGT (restated here, not imported)
TGT = 5e5
ET = np.sqrt(2.0 / 15.0) * 2 * np.sqrt(2.0 / 3.0)    # DERIVED: bound on E|w^T dT0 w| for one staple change
LOC = None


def load(path):
    ds = [dict(np.load(x)) for x in path.split("+")]
    metas = [json.loads(str(x.pop("meta"))) for x in ds]
    d = {k: np.concatenate([x[k] for x in ds], 0) for k in ds[0]}
    return d, metas


def groups_of(cnt):
    tgt = min(TGT, cnt.sum() / 12)
    # DERIVED: a populated bin holds at least one link (a count, exact)
    good = cnt > 0
    m = int(np.argmax(cnt)); lo = hi = m
    # DERIVED: 0 is the first bin index (array bound)
    while lo - 1 >= 0 and good[lo - 1]:
        lo -= 1
    while hi + 1 < len(cnt) and good[hi + 1]:
        hi += 1
    groups, cur, acc = [], [], 0.0
    for i in range(lo, hi + 1):  # NOT A READ: merge consecutive fine bins
        cur.append(i); acc += cnt[i]
        if acc >= tgt:
            groups.append(cur); cur, acc = [], 0.0
    if cur:
        if groups and acc < tgt / 2:
            groups[-1] += cur
        else:
            groups.append(cur)
    return groups


TH = (np.arange(4000) + 0.5) / 4000 * np.pi
HW = np.sin(TH) ** 2 / (np.sin(TH) ** 2).sum()        # Haar weight of theta
UH = IA.cheb(np.cos(TH), 8)


def coeffs(d, sel, li, bins, pre, nuse):
    """The couplings on the fine bins `bins` from shards `sel`."""
    L = d[pre][sel, li].sum(0)[:, bins].sum(-1)            # (nkeys,)
    v = dict(zip(LOC, L))
    M = np.array([[v["zBB0"], v["zBB1"], v["zBW0"], v["zBW1"]],
                  [v["zBB1"], v["zBB2"], v["zBW1"], v["zBW2"]],
                  [v["zBW0"], v["zBW1"], v["zWW0"], v["zWW1"]],
                  [v["zBW1"], v["zBW2"], v["zWW1"], v["zWW2"]]])
    aB, bB, aW, bW = np.linalg.solve(M, [v["yB0"], v["yB1"], v["yW0"], v["yW1"]])
    mu0, mu1 = np.linalg.solve([[v["zT0"], v["zT1"]], [v["zT1"], v["zT2"]]], [v["yT0"], v["yT1"]])
    n = d[pre][sel, li].sum(0)[LOC.index("n")][bins]          # per fine bin
    X = d[pre + "X"][sel, li].sum(0)[:, bins]                   # (3, nb)
    XX = d[pre + "XX"][sel, li].sum(0)[:, :, bins]
    U = d[pre + "U"][sel, li].sum(0)[:, bins]                   # (NK, nb)
    UX = d[pre + "UX"][sel, li].sum(0)[:, :, bins]              # (NK, 3, nb)
    # DERIVED: a fine bin with no links has no within-bin moments to pool (a count, exact)
    ok = n > 0
    nn = np.where(ok, n, 1)
    Cxx = (XX - X[:, None] * X[None] / nn)[:, :, ok].sum(-1)
    Cxu = (UX - U[:, None] * X[None] / nn)[:, :, ok].sum(-1)    # (NK, 3)
    kap = np.linalg.solve(Cxx, Cxu.T).T                         # (NK, 3): d U_n / d (r, b_par, Q)
    return {"aB": aB, "bB": bB, "aW": aW, "bW": bW, "mu0": mu0, "mu1": mu1,
            "kB": kap[:, 1], "kQ": kap[:, 2]}


def slots(cf, th_hist, nuse):
    """Slot TVs given the couplings and the theta histogram (NT,) of the r bin."""
    nt = len(th_hist)
    tc = np.cos((np.arange(nt) + 0.5) * np.pi / nt)
    w = th_hist / th_hist.sum()
    s1 = np.sqrt(1 - tc * tc)
    q = 0.25 * (w * np.abs(cf["aB"] + cf["bB"] * tc) * s1).sum()
    p = 0.5 * (HW * np.abs(cf["kB"][:nuse] @ UH[:nuse])).sum()
    qW = 0.25 * (w * np.abs(cf["aW"] + cf["bW"] * tc) * s1).sum()
    pQ = 0.5 * (HW * np.abs(cf["kQ"][:nuse] @ UH[:nuse])).sum()
    tT = 0.5 * ET * (w * np.abs(cf["mu0"] + cf["mu1"] * tc) * (1 - tc * tc)).sum()
    rect = 2 * np.sqrt(p * p + q * q)
    adj = qW + pQ + tT
    return {"rect_perp": q, "rect_par": p, "rect_slot": rect, "adj_W": qW, "adj_Q": pQ, "adj_T": tT,
            "adj_slot": adj, "rect_row": 90 * rect, "adj_row": 18 * adj, "row": 90 * rect + 18 * adj}


def read(d, li, pre, nuse, sel, groups):
    allb = np.concatenate(groups)
    cfp = coeffs(d, sel, li, allb, pre, nuse)
    chk = "chN" if pre == "LN" else "ch"
    out = {"pooled": cfp, "bins": []}
    best = None
    for g in groups:  # NOT A READ: the merged r bins
        h = d[chk][sel, li].sum(0)[g].sum(0)
        sp = slots(cfp, h, nuse)                    # pooled couplings, this bin's t law
        cg = coeffs(d, sel, li, np.array(g), pre, nuse)
        sg = slots(cg, h, nuse)                     # this bin's couplings
        out["bins"].append({"pooled_coupling": sp, "bin_coupling": sg, "coef": cg})
        if best is None or sp["row"] > best["row"]:
            best = sp
    out["pooled_max"] = best
    out["bin_max"] = {k: max(b["bin_coupling"][k] for b in out["bins"]) for k in best}
    return out


def flat(x, prefix=""):
    o = {}
    if isinstance(x, dict):
        for k, v in x.items():
            o.update(flat(v, prefix + k + "."))
    elif isinstance(x, list):
        for i, v in enumerate(x):
            o.update(flat(v, prefix + str(i) + "."))
    else:
        a = np.atleast_1d(np.asarray(x, float))
        for i, v in enumerate(a):
            o[prefix + str(i)] = float(v)
    return o


def unflat_err(full, jks):
    keys = list(full)
    J = np.array([[j[k] for k in keys] for j in jks])
    nb = len(jks)
    e = np.sqrt((nb - 1) / nb * ((J - J.mean(0)) ** 2).sum(0))
    return dict(zip(keys, e))


def exact_control(syn, rlo, rhi, nuse):
    bp, br, ba = syn
    ex = IA.Exact(1.0)
    # linear-response slot values with the exact couplings, over the bins' k = bp r
    rows = []
    for r in np.linspace(rlo, rhi, 12):  # NOT A READ: the r range of the read
        k = bp * r
        dk = 1e-4
        dc = (ex.coefs(k + dk, 8) - ex.coefs(k - dk, 8)) / (2 * dk)
        g = ex.g(k, np.cos(TH))
        hist = g * np.sin(TH) ** 2
        cf = {"aB": br, "bB": 0.0, "aW": 0.0, "bW": 2 * ba, "mu0": ba, "mu1": 0.0, "kB": br * dc,
              "kQ": ba * (UH @ (HW * g * np.cos(TH) ** 2) - ex.coefs(k, 8) * (HW * g * np.cos(TH) ** 2).sum())}
        rows.append(slots(cf, hist, nuse))
    best = max(rows, key=lambda x: x["row"])
    # the full (not linearised) sup TV of a rectangle slot: Wilson at K against Wilson at K + 2 br e
    full = 0.0
    # CHOSEN: the full-TV control is computed only for a positive rectangle coupling; br <= 0 reports 0 here
    # (the change K -> K + 2 br e is as valid for br < 0, so this is a restriction, not a derivation)
    if br > 0:
        for r in np.linspace(rlo, rhi, 12):  # NOT A READ: the r range of the read
            k = bp * r
            for psi in np.linspace(0, np.pi, 37):  # NOT A READ: the direction of the change
                K2 = np.array([k + 2 * br * np.cos(psi), 2 * br * np.sin(psi)])
                k2 = np.linalg.norm(K2)
                full = max(full, IA.tv(ex, k, k2, K2[0] / k2))
    return {"couplings": {"aB": br, "bB": 0.0, "aW": 0.0, "bW": 2 * ba, "mu0": ba, "mu1": 0.0},
            "kQ_2_weak": ba / 4, "linear_response_max": best, "rect_slot_full_tv": full}


if __name__ == "__main__":
    path = sys.argv[1]
    # DERIVED: 2 is [level_position]'s position in the usage line; default the first level read
    li = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    # DERIVED: 3 is [nuse]'s position in the usage line. CHOSEN: default 3 characters, a typical plaquette N*
    nuse = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    d, metas = load(path)
    LOC = metas[0]["local_keys"]
    S = d["cnt"].shape[0]
    allsel = np.arange(S)
    groups = groups_of(d["cnt"][:, li].sum(0))
    blocks = np.array_split(np.arange(S), min(NBLK, S))
    res = {"read": path, "level": metas[0]["levels"][li], "nsub": metas[0]["nsub"], "c": metas[0]["c"],
           "origins": metas[0]["origins"], "synthetic": metas[0]["synthetic"], "nshards": S,
           "links": float(d["cnt"][:, li].sum()), "nuse": nuse, "ngroups": len(groups)}
    rm = d["rsum"][:, li].sum(0) / np.maximum(d["cnt"][:, li].sum(0), 1)
    rlo, rhi = float(rm[groups[0][0]]), float(rm[groups[-1][-1]])
    res["r_range"] = [rlo, rhi]
    for pre, nm in (("L", "data"), ("LN", "null")):  # NOT A READ: data and the permuted null
        full = read(d, li, pre, nuse, allsel, groups)
        jk = [flat(read(d, li, pre, nuse, np.setdiff1d(allsel, b), groups)) for b in blocks]
        err = unflat_err(flat(full), jk)
        res[nm] = {"value": flat(full), "err": err}
        f, e = res[nm]["value"], err
        pk = lambda k: f"{f[k]:.5f}+-{e[k]:.5f}"
        print(f"[{nm}] links {res['links']:.3g} aB {pk('pooled.aB.0')} bB {pk('pooled.bB.0')} aW {pk('pooled.aW.0')} "
              f"bW {pk('pooled.bW.0')} mu0 {pk('pooled.mu0.0')} kB1 {pk('pooled.kB.0')} kB2 {pk('pooled.kB.1')} "
              f"kQ1 {pk('pooled.kQ.0')} kQ2 {pk('pooled.kQ.1')}", file=sys.stderr)
        print(f"[{nm}] pooled-max rect_row {pk('pooled_max.rect_row.0')} adj_row {pk('pooled_max.adj_row.0')} "
              f"row {pk('pooled_max.row.0')} | bin-max rect_row {pk('bin_max.rect_row.0')} adj_row {pk('bin_max.adj_row.0')}",
              file=sys.stderr, flush=True)
    if metas[0]["synthetic"]:
        res["exact"] = exact_control(metas[0]["synthetic"], rlo, rhi, nuse)
        x = res["exact"]["linear_response_max"]
        print(f"[exact] rect_row {x['rect_row']:.5f} adj_row {x['adj_row']:.5f} row {x['row']:.5f} "
              f"full-TV rect slot x90 {90 * res['exact']['rect_slot_full_tv']:.5f}", file=sys.stderr)
    print(json.dumps(res, indent=1))
