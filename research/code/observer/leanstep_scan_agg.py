"""Read leanstep_scan_gpu.py output: the physical connected correlator G(t) r0^5 at every step count, the
observer's own scale n^2 <e>(n), and the correlator at the step count where that scale matches a reference.

Per spacing and checkpoint n: G(t) r0^5 = (r0/a)^5 <S(0) S(D)>_c / L^3 (ed_agg.corr, jackknife over shards,
ed_agg.jk) read at t/r0 = D_ref / r0a_ref by log-linear interpolation between the two neighbouring lattice
times (as ed_agg.py); <e4>, the four-dimensional plaquette energy density per site; its n^2 <e4>; <e3> (spatial).
Matching: the reference (first spacing, step n_ref) fixes w* = n_ref^2 <e4>(n_ref); on every other spacing n* is
where n^2 <e4> crosses w*, linear between the two bracketing checkpoints, and G at n* is the same linear
interpolation of G between them (no model is fitted). The same for the alternative match <e4> (r0/a)^4.

    [SUB=1] python leanstep_scan_agg.py n_ref TMAX DIR_1 r0a_1 DIR_2 r0a_2 ...   (r0a may be lo:hi)
SUB=1 reads corr_sub in place of corr; MATCH=e3 matches on the spatial density (for the spatial step, whose
temporal links stay unsmeared) in place of e4 (the n2e4 and e4r4 columns then hold the e3 values).
"""
import glob
import os
import json
import sys

import numpy as np

from ed_agg import corr, jk


def load(d):
    fs = sorted(glob.glob(f"{d}/*.npz"))
    z = [np.load(f) for f in fs]
    n = z[0]["n"]
    S = np.stack([x["S"] for x in z], 1)          # (k, shard, chain, T)
    e4 = np.stack([x["e4"] for x in z], 1).mean((1, 2))
    e3 = np.stack([x["e3"] for x in z], 1).mean((1, 2))
    return n, S, e4, e3, len(fs)


def corr_sub(X):
    """corr less its value at D = T/2: removes the constant the ensemble-mean subtraction leaves (minus the
    variance of the mean, large when the shards are autocorrelated); the true G(T/2) is below the noise."""
    c = corr(X)
    return c - c[-1]


def g_at(S_k, r0a, times, f=corr):
    c, e = jk(S_k, f)
    tl = np.arange(len(c)) / r0a
    G, E = c * r0a ** 5, e * r0a ** 5
    out = []
    for t in times:
        i = max(min(np.searchsorted(tl, t), len(tl) - 1), 1)
        # CHOSEN: a float-equality tolerance; t on a lattice time takes that time's value without interpolating
        if abs(tl[i - 1] - t) < 1e-12:
            out.append((G[i - 1], E[i - 1]))
            continue
        # DERIVED: log-linear interpolation needs both bracketing values positive (log is undefined otherwise)
        if G[i - 1] <= 0 or G[i] <= 0:
            out.append((np.nan, np.nan))
            continue
        w = (t - tl[i - 1]) / (tl[i] - tl[i - 1])
        out.append((np.exp((1 - w) * np.log(G[i - 1]) + w * np.log(G[i])), (1 - w) * E[i - 1] + w * E[i]))
    return np.array(out)  # (len(times), 2)


def cross(x, y, target):
    for j in range(len(x) - 1):
        # DERIVED: a sign change (or a zero) of y - target between two checkpoints brackets the crossing
        if (y[j] - target) * (y[j + 1] - target) <= 0:
            w = (target - y[j]) / (y[j + 1] - y[j])
            return j, w
    return None, None


if __name__ == "__main__":
    nref, tmax = int(sys.argv[1]), int(sys.argv[2])
    FN = corr_sub if os.environ.get("SUB") == "1" else corr
    specs = [(sys.argv[i], [float(v) for v in sys.argv[i + 1].split(":")]) for i in range(3, len(sys.argv), 2)]
    r_ref = specs[0][1][0]
    times = np.arange(tmax + 1) / r_ref
    res = {"times": times.tolist(), "spacings": []}
    ref = None
    for d, r0s in specs:
        n, S, e4, e3, nsh = load(d)
        for r0a in r0s:
            Gs = np.stack([g_at(S[k], r0a, times, FN) for k in range(len(n))])  # (k, t, 2)
            em = e3 if os.environ.get("MATCH") == "e3" else e4
            w4 = n ** 2 * em
            u4 = em * r0a ** 4
            rec = {"dir": d, "r0a": r0a, "nshards": nsh, "n": n.tolist(), "e4": e4.tolist(), "e3": e3.tolist(),
                   "n2e4": w4.tolist(), "e4r4": u4.tolist(), "G": Gs[..., 0].tolist(), "Gerr": Gs[..., 1].tolist()}
            if ref is None:
                k = list(n).index(nref)
                ref = {"w": w4[k], "u": u4[k]}
                rec["ref"] = {"n": nref, "n2e4": w4[k], "e4r4": u4[k], "G": Gs[k, :, 0].tolist(),
                              "Gerr": Gs[k, :, 1].tolist()}
            for key, y, tgt in (("match_n2e4", w4, ref["w"]), ("match_e4r4", u4, ref["u"])):
                j, w = cross(n, y, tgt)
                if j is None:
                    rec[key] = None
                    continue
                G = (1 - w) * Gs[j, :, 0] + w * Gs[j + 1, :, 0]
                E = (1 - w) * Gs[j, :, 1] + w * Gs[j + 1, :, 1]
                rec[key] = {"nstar": float(n[j] + w * (n[j + 1] - n[j])), "G": G.tolist(), "Gerr": E.tolist()}
            res["spacings"].append(rec)
    print(json.dumps(res))
    f = lambda a: " ".join(f"{v:7.3f}" for v in a)
    print("# t/r0 " + f(times), file=sys.stderr)
    for rec in res["spacings"]:
        print(f"# {rec['dir']} r0/a={rec['r0a']} shards={rec['nshards']}", file=sys.stderr)
        for k, nn in enumerate(rec["n"]):
            print(f"  n={nn:4d} n2e4={rec['n2e4'][k]:7.3f} e4r4={rec['e4r4'][k]:7.3f}  G " + f(rec["G"][k])
                  + "  err " + f(rec["Gerr"][k]), file=sys.stderr)
        for key in ("match_n2e4", "match_e4r4"):
            m = rec.get(key)
            if m:
                print(f"  {key}: n*={m['nstar']:.2f} G " + f(m["G"]) + "  err " + f(m["Gerr"]), file=sys.stderr)
