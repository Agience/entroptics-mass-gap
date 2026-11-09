"""Aggregate rot_read.py: the connected energy-density two-point function along hypercubic orbits, and its
anisotropy at equal Euclidean separation, with jackknife errors over chains.

Per ensemble directory of `*_ch{c}_c{c}_n{n}_rot.npy` rows [mean e, mean e^2, <e e(+u)>_v for v in VECS]:
    G(v) = <e(x) e(x+v)> - <e>^2,  <e> the ensemble mean (the subtraction is inside every jackknife sample).
The anisotropy is read two ways, with no fit:
  * equal length: R = G(v) / G(|v| e_0) for integer vectors v off the axes with |v| an integer (PAIRS);
  * diagonals: R = G(k d) / G_axis(k |d|) for d = (1,1,0,0), (1,1,1,0), the on-axis function at the
    non-integer length k |d| read by log-linear interpolation between the two neighbouring integer lengths;
    for d = (1,1,1,1), |k d| = 2k is an integer and no interpolation enters.
Distances are reported in lattice units, in units of the observer's resolution l = a sqrt(n) (the smearing radius
scales as sqrt(n) steps), and, where given, of r0.
Blocks: the chain index (independent chains); the delete-one-block jackknife.

    python rot_agg.py OUT_JSON LABEL:DIR:n[:r0_over_a] [LABEL:DIR:n[:r0_over_a] ...]
"""
import glob
import json
import math
import os
import re
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
VECS = None


def load_vecs():
    """VECS from rot_read.py's source, without running its module-level command-line code."""
    src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "rot_read.py"), encoding="utf-8").read()
    body = src[src.index("VECS = ["):]
    body = body[:body.index("]\n") + 1]
    ns = {}
    exec(body, ns)
    return ns["VECS"]


# DERIVED: each pair is an on-axis vector (k, 0, 0, 0) and an off-axis integer vector of the same Euclidean length
# (|b|^2 = k^2, checked entry by entry), so the ratio isolates the anisotropy at equal separation. Which equal-length
# vectors are listed is limited to those rot_read.VECS measures
PAIRS = [((2, 0, 0, 0), (1, 1, 1, 1)), ((3, 0, 0, 0), (2, 2, 1, 0)), ((4, 0, 0, 0), (2, 2, 2, 2)),
         ((5, 0, 0, 0), (3, 4, 0, 0)), ((5, 0, 0, 0), (4, 2, 2, 1)), ((6, 0, 0, 0), (4, 4, 2, 0)),
         ((6, 0, 0, 0), (5, 3, 1, 1)), ((6, 0, 0, 0), (3, 3, 3, 3)), ((7, 0, 0, 0), (6, 3, 2, 0)),
         ((7, 0, 0, 0), (4, 4, 4, 1)), ((8, 0, 0, 0), (4, 4, 4, 4)), ((9, 0, 0, 0), (6, 6, 3, 0)),
         ((9, 0, 0, 0), (8, 4, 1, 0)), ((10, 0, 0, 0), (6, 8, 0, 0)), ((10, 0, 0, 0), (5, 5, 5, 5)),
         ((12, 0, 0, 0), (8, 8, 4, 0)), ((12, 0, 0, 0), (6, 6, 6, 6))]


def blocks_of(d):
    rows = {}
    for f in sorted(glob.glob(os.path.join(d, "*_rot.npy"))):
        ch = int(re.search(r"_ch(\d+)_", os.path.basename(f)).group(1))
        rows.setdefault(ch, []).append(np.load(f))
    return [np.array(rows[k]) for k in sorted(rows)]


def gfun(rows):
    """G(v) for every v from a stack of rows (configurations)."""
    m = rows[:, 0].mean()
    return rows[:, 2:].mean(axis=0) - m * m


def axis_at(G, idx, r):
    """The on-axis G at length r: exact at an integer, log-linear between the neighbouring integers."""
    lo, hi = int(math.floor(r)), int(math.ceil(r))
    if lo == hi:
        return G[idx[(lo, 0, 0, 0)]]
    g0, g1 = G[idx[(lo, 0, 0, 0)]], G[idx[(hi, 0, 0, 0)]]
    # DERIVED: log-linear interpolation needs both values positive (log is undefined otherwise)
    if g0 <= 0 or g1 <= 0:
        return float("nan")
    t = r - lo
    return math.exp((1 - t) * math.log(g0) + t * math.log(g1))


def reads(G, idx):
    out = {}
    for a, b in PAIRS:
        if a in idx and b in idx:
            out[f"{b}/{a}"] = (float(math.sqrt(sum(x * x for x in b))), G[idx[b]] / G[idx[a]])
    for d in [(1, 1, 0, 0), (1, 1, 1, 0), (1, 1, 1, 1)]:
        for k in range(1, 9):
            v = tuple(k * x for x in d)
            r = k * math.sqrt(sum(d))
            if v in idx and (int(math.ceil(r)), 0, 0, 0) in idx:
                out[f"{v}/axis"] = (r, G[idx[v]] / axis_at(G, idx, r))
    return out


def ensemble(d, n, r0a):
    blocks = blocks_of(d)
    allrows = np.concatenate(blocks)
    idx = {v: i for i, v in enumerate(VECS)}
    G = gfun(allrows)
    full = reads(G, idx)
    nb = len(blocks)
    jk = []
    Gjk = []
    for b in range(nb):
        rows = np.concatenate([blocks[c] for c in range(nb) if c != b])
        g = gfun(rows)
        Gjk.append(g)
        jk.append(reads(g, idx))
    Gjk = np.array(Gjk)
    gerr = np.sqrt((nb - 1) / nb * ((Gjk - Gjk.mean(axis=0)) ** 2).sum(axis=0))
    ell = math.sqrt(n)
    res = {"dir": d, "n": n, "configs": int(len(allrows)), "blocks": nb, "mean_e": float(allrows[:, 0].mean()),
           "G": {str(v): [float(G[i]), float(gerr[i])] for v, i in idx.items()}, "anisotropy": {}}
    for key, (r, val) in full.items():
        vals = np.array([j[key][1] for j in jk])
        err = math.sqrt((nb - 1) / nb * ((vals - vals.mean()) ** 2).sum())
        ent = {"r_lat": r, "r_over_l": r / ell, "ratio": float(val), "err": float(err)}
        if r0a:
            ent["r_over_r0"] = r / r0a
        res["anisotropy"][key] = ent
    return res


if __name__ == "__main__":
    VECS = load_vecs()
    out = {}
    for spec in sys.argv[2:]:
        parts = spec.split(":")
        label, d, n = parts[0], parts[1], int(parts[2])
        # DERIVED: 3 is the optional r0_over_a field's position in LABEL:DIR:n[:r0_over_a] (usage line)
        r0a = float(parts[3]) if len(parts) > 3 else None
        out[label] = ensemble(d, n, r0a)
        e = out[label]
        print(f"== {label}: n={n} configs={e['configs']} blocks={e['blocks']} <e>={e['mean_e']:.5f}")
        for key, a in sorted(e["anisotropy"].items(), key=lambda kv: kv[1]["r_lat"]):
            extra = f" r/r0={a['r_over_r0']:.2f}" if "r_over_r0" in a else ""
            print(f"  {key:28s} r={a['r_lat']:6.3f} r/l={a['r_over_l']:.3f}{extra}  R={a['ratio']:.4f} +- {a['err']:.4f}")
    with open(sys.argv[1], "w") as f:
        json.dump(out, f, indent=1)
