"""Aggregate of the four-chain beta 2.70 reads: the energy-density correlator and the cube-energy moments.

Reads the committed per-measurement arrays in research/data/observer/obs4_cube/ (copied unchanged from the
campaign's output): each file is one measurement of the four
chains, shape (chain, T) for the slice sums of obs4_read_gpu.py (n = 113) and (chain, ncubes) for the cube
sums of cube_read_gpu.py (n = 105, cube side 11). It runs no simulation.

Correlator: G(t) r0^5 = (r0/a)^5 <S(0) S(D)>_c / L^3 (ed_agg.corr), read at the beta 2.50 lattice times
t/r0 = D / 6.1 by log-linear interpolation between the two neighbouring beta 2.70 lattice times, as
ed_agg.py does; r0/a = 11.87 at beta 2.70. Cube moments: <X^{2p}>, p = 1..6, over every cube of every chain
and measurement (observer_summaries.cube); the per-p root (<X^{2p}>_{2.70} / <X^{2p}>_{2.50})^{1/(2p)}
against the beta 2.50 entry of cube_moments.json. Errors: delete-one-chain jackknife (ed_agg.jk), the
chains being the independent units; a root's error is propagated from the two moments' errors. `cube_first5`
repeats the cube read on the first five measurements of each chain (cube_mc/ and the first file of cube_mc2/),
the read plot_observer.py's beta 2.70 moment table was typed from.

The beta 2.50 column (`correlator_beta250`): the twelve per-shard files of leanstep_scan_gpu.py on the 32^4
beta 2.50 campaign (four-direction step, c = 0.15, step counts 20..44; copied unchanged from
the campaign's output into obs4_cube/scan_b250_4d_c0.15/ with their SHA256SUMS),
read at step count n = 30 (n^2 <e4> = 5.39, the observer's own scale, the reference the beta 2.70 n = 113 is
matched to) as G(t) r0^5 at t/r0 = D / r0a for D = 0..4, r0/a = 6.12 the centre of the Sommer range
6.03-6.21, jackknife over shards (leanstep_scan_agg.load, ed_agg.corr, ed_agg.jk). Each row also gives the
beta 2.70 value at the same D and their difference in combined errors.

    python aggregate_obs4_cube.py [OUT.json]     (default research/data/observer/obs4_cube_agg_270.json)
"""
import glob
import json
import os
import sys

import numpy as np

from ed_agg import corr, jk

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.normpath(os.path.join(HERE, "..", "..", "data", "observer"))
# DERIVED: the fit-free Sommer reads r0/a that the paper's correlator table uses (section 10, Scales):
# 11.87 at beta_W = 2.70 (r0_su2_L64_b2.70.json) and 6.1 at beta_W = 2.50, which sets the table's physical times.
R0A_270 = 11.87
# DERIVED: r0/a = 6.1 at beta_W = 2.50 (r0_su2_*.json), the scale of the table's physical times
R0A_250 = 6.1
# DERIVED: the ends of the fit-free Sommer range r0/a at beta_W = 2.50 (r0_su2_L32_b2.50.json, section 10, Scales)
R0A_250_RANGE = (6.03, 6.21)
# CHOSEN: the reference step count of the beta 2.50 scan (leanstep_scan_agg.py's n_ref), where n^2 <e4> = 5.39 is
# the observer's own scale; the beta 2.70 step count n = 113 was matched to it. Another checkpoint reads another radius
N_REF_250 = 30


def stack(sub):
    fs = []
    for d in sub:
        fs += sorted(f for f in glob.glob(os.path.join(DATA, "obs4_cube", d, "links_*.npy")) if "tmp" not in f)
    X = np.stack([np.load(f) for f in fs])  # (measurement, chain, ...)
    return np.swapaxes(X, 0, 1), [os.path.relpath(f, DATA).replace(os.sep, "/") for f in fs]  # (chain, measurement, ...)


def correlator():
    X, fs = stack(["obs4_mc", "obs4_mc2"])
    c, e = jk(X, corr)
    G, E = c * R0A_270 ** 5, e * R0A_270 ** 5
    tl = np.arange(len(c)) / R0A_270
    rows = []
    for D in range(5):
        t = D / R0A_250
        i = max(min(int(np.searchsorted(tl, t)), len(tl) - 1), 1)
        # CHOSEN: 1e-12, float equality of a lattice time and a requested time; any value far below the spacing 1/r0a works
        if abs(tl[i - 1] - t) < 1e-12:
            g, err = G[i - 1], E[i - 1]
        else:
            w = (t - tl[i - 1]) / (tl[i] - tl[i - 1])
            g = float(np.exp((1 - w) * np.log(G[i - 1]) + w * np.log(G[i])))
            err = (1 - w) * E[i - 1] + w * E[i]
        rows.append({"t_r0": t, "G_r0^5": float(g), "err": float(err), "sigma": float(g / err)})
    return {"files": fs, "nchains": X.shape[0], "nmeas": X.shape[1], "T": X.shape[2], "r0a": R0A_270,
            "G_lattice_r0^5": G.tolist(), "err_lattice": E.tolist(), "at_beta250_times": rows}


def correlator_beta250(c270):
    """The beta 2.50 column of the correlator table, from the committed scan files (see the module docstring)."""
    from leanstep_scan_agg import load
    d = os.path.join(DATA, "obs4_cube", "scan_b250_4d_c0.15")
    n, S, e4, _, nf = load(d)
    k = int(np.flatnonzero(n == N_REF_250)[0])
    # DERIVED: 2, the midpoint of the two ends of the Sommer range
    r0a = sum(R0A_250_RANGE) / 2
    c, e = jk(S[k], corr)
    rows = []
    for D, r270 in enumerate(c270["at_beta250_times"]):
        g, err = float(c[D] * r0a ** 5), float(e[D] * r0a ** 5)
        rows.append({"D": D, "t_r0": D / r0a, "G_r0^5": g, "err": err,
                     "G_r0^5_at_range_ends": [float(c[D] * r ** 5) for r in R0A_250_RANGE],
                     "beta270_G_r0^5": r270["G_r0^5"], "beta270_err": r270["err"],
                     "diff_in_sigma": (r270["G_r0^5"] - g) / float(np.hypot(err, r270["err"]))})
    fs = sorted(glob.glob(os.path.join(d, "*.npz")))
    return {"files": [os.path.relpath(f, DATA).replace(os.sep, "/") for f in fs], "nshards": nf,
            "n": int(n[k]), "n2e4": float(n[k] ** 2 * e4[k]), "r0a": r0a, "r0a_range": list(R0A_250_RANGE),
            "rows": rows}


def cube(nmeas=None):
    X, fs = stack(["cube_mc", "cube_mc2"])
    if nmeas is not None:  # the first nmeas measurements of every chain, in file order
        X, fs = X[:, :nmeas], fs[:nmeas]
    ps = np.arange(1, 7)

    def mom(Y):
        return np.array([(Y.astype(np.float64) ** (2 * p)).mean() for p in ps])

    m, e = jk(X, mom)
    ref = [r for r in json.load(open(os.path.join(DATA, "cube_moments.json"))) if r["dir"].endswith("su2_L32_b2.50")][0]
    m250, e250 = np.array(ref["moment"]), np.array(ref["moment_err"])
    root = (m / m250) ** (1.0 / (2 * ps))
    sroot = root / (2 * ps) * np.sqrt((e / m) ** 2 + (e250 / m250) ** 2)
    return {"files": fs, "nchains": X.shape[0], "nmeas": X.shape[1], "ncubes": int(X[0, 0].size), "p": ps.tolist(),
            "moment": m.tolist(), "moment_err": e.tolist(), "mean": float(X.mean()),
            "ref_beta250": {"source": "cube_moments.json", "dir": ref["dir"], "moment": m250.tolist(),
                            "moment_err": e250.tolist(), "mean": ref["mean"]},
            "root": root.tolist(), "root_err": sroot.tolist()}


if __name__ == "__main__":
    # DERIVED: 1, argv[0] is the script, so one extra argument names the output
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(DATA, "obs4_cube_agg_270.json")
    c270 = correlator()
    res = {"producer": "research/code/observer/aggregate_obs4_cube.py", "correlator": c270, "cube": cube(),
           "cube_first5": cube(5), "correlator_beta250": correlator_beta250(c270)}
    with open(out, "w", encoding="utf-8") as f:
        json.dump(res, f, indent=1)
    for r in res["correlator"]["at_beta250_times"]:
        print(f"t/r0={r['t_r0']:.3f}  G r0^5={r['G_r0^5']:.2f} +- {r['err']:.2f}")
    for r in res["correlator_beta250"]["rows"]:
        print(f"beta 2.50 t/r0={r['t_r0']:.3f}  G r0^5={r['G_r0^5']:.2f} +- {r['err']:.2f}"
              f"  (beta 2.70 minus beta 2.50: {r['diff_in_sigma']:+.2f} sigma)")
    c = res["cube"]
    for p, mm, ee, rr, sr in zip(c["p"], c["moment"], c["moment_err"], c["root"], c["root_err"]):
        print(f"p={p}  <X^2p>={mm:.4g} +- {ee:.2g}  root={rr:.3f} +- {sr:.3f}")
    print(f"mean cube energy {c['mean']:.3f} (beta 2.50: {c['ref_beta250']['mean']:.3f})")
    c5 = res["cube_first5"]
    print("first five measurements: moments " + ", ".join(f"{m:.4g}" for m in c5["moment"])
          + "; roots " + ", ".join(f"{r:.3f}" for r in c5["root"]))
