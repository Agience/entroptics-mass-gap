"""The 0++ glueball mass from glueball_read.py outputs: vacuum-subtracted correlator matrix over smearing levels,
generalised eigenvalues, effective masses, jackknife over chains. No fit.

    C_ij(t) = < (O_i(t0) - <O_i>) (O_j(t0 + t) - <O_j>) >,  averaged over t0 and configurations, symmetrised;
    <O_i> the ensemble mean (subtracted inside every jackknife sample);
    GEVP  C(t) v = lambda(t) C(tref) v, lambda_0 the largest;  a m_eff(t) = log(lambda_0(t) / lambda_0(t + 1));
    single-level  a m_i(t) = log(C_ii(t) / C_ii(t + 1)).
Basis: the levels in LEVELS (default all). Every error is a delete-one-block jackknife, differences of effective
masses included (so their correlation enters).

The plateau read: the first t > tref at which (i) m_eff(t) and m_eff(t + 1) agree, |m(t) - m(t + 1)| <= its
jackknife error, and (ii) there is no significant fall over the next two, m(t) - m(t + k) <= 2 sigma for k = 2, 3
(the points that exist and are finite). The value quoted there is m_eff(t). Without such a t the read reports the
lowest supported upper reading: m_eff at the largest t whose relative error is at most RESOLVED (default 0.25).
The trend m(t) - m(t + 2) is reported at every t.

Blocks: (family, chain), a family being one directory argument; a campaign continued in another directory (e.g. _mc
and _mc2) is joined with '+' so their chains share blocks. MAXBLOCK=k splits every block of more than k configurations
into consecutive blocks of k (the configurations of a chain in file order, i.e. Monte Carlo time).

    [LEVELS=i,j,..] [TREF=0] [TMAX=..] [MAXBLOCK=k] [RESOLVED=0.25] python glueball_agg.py OUT.json r0_over_a dirA[+dirA2] [dirB ...]
"""
import glob
import json
import math
import os
import sys

import numpy as np
import scipy.linalg as sla


def load(spec):
    blocks = {}
    for fam, group in enumerate(spec):
        for d in group.split("+"):
            for f in sorted(glob.glob(os.path.join(d, "*_glue.npz"))):
                z = np.load(f)
                for ch in range(z["S"].shape[0]):
                    blocks.setdefault((fam, ch), []).append(z["S"][ch])
                levels = z["levels"].tolist()
    keys = sorted(blocks)
    out = [np.stack(blocks[k]) for k in keys]  # each (config, level, T)
    mb = int(os.environ.get("MAXBLOCK", 0))
    if mb:
        out = [X[i:i + mb] for X in out for i in range(0, len(X), mb)]
        out = [X for X in out if len(X)]
    return out, keys, levels


def corr(X, sel, tmax):
    """C(t) for t = 0..tmax from configurations X (config, level, T), vacuum subtracted with X's own mean."""
    d = X[:, sel, :] - X[:, sel, :].mean(axis=(0, 2), keepdims=True)
    T = d.shape[2]
    C = np.empty((tmax + 1, len(sel), len(sel)))
    for t in range(tmax + 1):  # NOT A READ: the time separations
        M = np.einsum("cit,cjt->ij", d, np.roll(d, -t, axis=2)) / (d.shape[0] * T)
        C[t] = 0.5 * (M + M.T)
    return C


def masses(C, tref):
    tm = C.shape[0] - 1
    lam = np.full(tm + 1, np.nan)
    for t in range(tm + 1):
        try:
            lam[t] = sla.eigh(C[t], C[tref], eigvals_only=True).max()
        except (np.linalg.LinAlgError, ValueError):
            pass
    with np.errstate(invalid="ignore", divide="ignore"):
        mg = np.log(lam[:-1] / lam[1:])
        ms = np.log(np.einsum("tii->ti", C)[:-1] / np.einsum("tii->ti", C)[1:]).T  # (level, t)
    return mg, ms


if __name__ == "__main__":
    out, r0a, spec = sys.argv[1], float(sys.argv[2]), sys.argv[3:]
    blocks, keys, levels = load(spec)
    sel = [int(v) for v in os.environ["LEVELS"].split(",")] if os.environ.get("LEVELS") else list(range(len(levels)))
    tref = int(os.environ.get("TREF", 0))
    resolved = float(os.environ.get("RESOLVED", 0.25))
    T = blocks[0].shape[2]
    tmax = int(os.environ.get("TMAX", min(12, T // 2)))
    allX = np.concatenate(blocks)
    mg, ms = masses(corr(allX, sel, tmax), tref)
    nb = len(blocks)
    jg, js = [], []
    for b in range(nb):  # NOT A READ: delete-one-block jackknife
        g, s = masses(corr(np.concatenate([blocks[c] for c in range(nb) if c != b]), sel, tmax), tref)
        jg.append(g)
        js.append(s)
    jg, js = np.array(jg), np.array(js)
    err = lambda J: np.sqrt((nb - 1) / nb * np.nansum((J - np.nanmean(J, axis=0)) ** 2, axis=0))
    eg, es = err(jg), err(js)
    nt = len(mg)
    dif = lambda t, u: (mg[t] - mg[u], float(err(jg[:, t] - jg[:, u])))
    trend = [dif(t, t + 2) if t + 2 < nt else (float("nan"), float("nan")) for t in range(nt)]
    plateau = None
    for t in range(tref + 1, nt - 1):
        d1, s1 = dif(t, t + 1)
        if not (np.isfinite(d1) and abs(d1) <= s1):
            continue
        ok = True
        for k in (2, 3):
            if t + k < nt and np.isfinite(mg[t + k]):
                dk, sk = dif(t, t + k)
                ok = ok and dk <= 2 * sk
        if ok:
            plateau = t
            break
    # DERIVED: a non-positive effective mass is no mass reading, and the relative-error test below divides by it.
    # (The cut that decides is RESOLVED, a chosen relative error defaulting to 0.25, read from the environment.)
    res_t = [t for t in range(tref + 1, nt) if np.isfinite(mg[t]) and mg[t] > 0 and eg[t] <= resolved * mg[t]]
    rep = {"dirs": spec, "r0_over_a": r0a, "levels": [levels[i] for i in sel], "tref": tref, "configs": int(len(allX)),
           "blocks": nb, "maxblock": int(os.environ.get("MAXBLOCK", 0)), "T": int(T),
           "m_eff_gevp": mg.tolist(), "m_eff_gevp_err": eg.tolist(),
           "trend_m_t_minus_m_t2": [list(map(float, x)) for x in trend],
           "m_eff_level": ms.tolist(), "m_eff_level_err": es.tolist(), "plateau_t": plateau}
    print(f"configs {len(allX)} blocks {nb} levels {rep['levels']} tref {tref} r0/a {r0a}")
    for t in range(nt):
        lv = " ".join(f"{ms[i, t]:.3f}({es[i, t]:.3f})" for i in range(len(sel)))
        print(f"t={t:2d} t/r0={t / r0a:.2f}  gevp a m = {mg[t]:.4f} +- {eg[t]:.4f}  m(t)-m(t+2) = {trend[t][0]:+.4f} +- {trend[t][1]:.4f}   levels: {lv}")
    if plateau is not None:
        am, dam = float(mg[plateau]), float(eg[plateau])
        rep.update({"read": "plateau", "t": plateau, "a_m": am, "a_m_err": dam, "m_r0": am * r0a, "m_r0_err": dam * r0a})
        print(f"plateau at t = {plateau}: a m = {am:.4f} +- {dam:.4f}, m r0 = {am * r0a:.3f} +- {dam * r0a:.3f}")
    elif res_t:
        t = res_t[-1]
        am, dam = float(mg[t]), float(eg[t])
        rep.update({"read": "upper", "t": t, "a_m": am, "a_m_err": dam, "m_r0": am * r0a, "m_r0_err": dam * r0a})
        print(f"no plateau; lowest supported upper reading (largest t with error <= {resolved:.0%}) t = {t}: "
              f"a m = {am:.4f} +- {dam:.4f}, m r0 = {am * r0a:.3f} +- {dam * r0a:.3f}")
    else:
        print("no plateau and no resolved effective mass")
    json.dump(rep, open(out, "w"), indent=1)
