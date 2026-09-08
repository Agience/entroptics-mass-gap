"""8.8 — the string tension from planar Wilson loops, measured without an Entroptics read.

Confinement is an area law and its coefficient is the string tension, so a positive a^2 sigma is
confinement. This is the independent confirmation of it: from raw SU(2) link configurations the
planar Wilson loops W(R,T) give the static potential V(R) and the Creutz ratios chi(R,T), using
textbook lattice observables only. Independence is the point — sigma measured here sits beside reads
that use the instrument, so the two must not share an extraction.

The extraction has four requirements, each of which biases a^2 sigma upward when dropped:

  1. Plane selection. W(R,T) is built on spatial-x-temporal planes: R is a spatial separation and T
     a Euclidean time, and those planes are the ones carrying W(R,T) ~ exp(-V(R) T). Averaging over
     all twelve ordered planes mu != nu mixes in spatial-spatial loops of different kinematic
     meaning. See `wilson_matrix`.
  2. Smearing. Raw links have poor overlap onto the ground-state flux tube, which holds V_eff(R,T)
     above V(R) at every accessible T. The spatial links are APE-smeared (`G.ape_smear`).
  3. T-dependence. Excited states decay like exp(-(V*-V)T), so a fixed small T reads V*, not V, and
     more so at larger beta where a given T is a shorter physical time. sigma(T) is computed and
     printed at every T, read at the largest T resolved at 3 sigma, and the residual drift across
     that window is carried in its own systematic column.
  4. The Coulomb term. The potential is V(R) = V0 + sigma R - e/R; fitting a straight line absorbs
     -e/R into the slope, contributing +0.033 over R = 2..4.

Errors are jackknife over configuration blocks. Every value is either measured or refused: caps and
substitutions raise, and the full sigma(T) table is printed so the systematic is visible.

    CONFIGS=/path/to/store DEVICE=cuda python 8_8_run_string_tension.py
    ST_SOURCE=generate BETAS=2.30,2.40,2.50 NCFG=320 DEVICE=cuda python 8_8_run_string_tension.py
"""
from __future__ import annotations

import glob
import os
import sys
import time

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))   # research/code

import lattice_generator as G
from lattice_generator import _Backend, _qmul, _qconj, _sax
import store_path                       # the ONE place the ensemble store is located
import table

DEVICE = os.environ.get("DEVICE") or None
SOURCE = os.environ.get("ST_SOURCE", "links")                         # links (committed) | generate
# research/data is where every committed artifact lives. Writing next to the script made this the
# only non-.py file in research/code/certify, i.e. a data artifact filed under the scripts.
DAT = os.path.join(_HERE, "8_8_dat_string_tension.csv")
# The summary row cannot show WHY a value was read where it was. The curves it was read from --
# sigma(T) and chi(R,R), each with its jackknife error and whether it passed the resolution cut --
# go in their own artifact so the figure is drawn from committed data, not recomputed.
CURVES = os.path.join(_HERE, "8_8_dat_string_tension_curves.csv")
CURVE_COLS = ["beta", "L", "kind", "x", "value", "err", "used"]
DIMS = (8, 8, 8, 16)                                                  # generate-mode lattice
BETAS = [float(b) for b in os.environ.get("BETAS", "2.30").split(",")]   # the beta the L=16 links exist at
NCFG = int(os.environ.get("NCFG", "40"))
THERM = int(os.environ.get("THERM", "200"))
# 24 sweeps, chosen from a smearing scan: sigma(T=1) and sigma(T=2) are flat to 0.001 across NSMEAR
# 24/32/48 (0.1357/0.1355/0.1372 and 0.1317/0.1314/0.1325), so the operator's ground-state overlap
# has saturated, while 8 and 16 sweeps still read high (0.1486/0.1384 at T=1).
#
# That scan is not among the committed artifacts -- only the chosen value is measured there -- so it
# is reproducible on demand rather than on file:
#
#     for NS in 8 16 24 32 48; do
#         NSMEAR=$NS BETAS=2.30 DEVICE=cuda python 8_8_run_string_tension.py | grep "T= [12]"
#     done
#
# The level is specific to this observable. 8_7_dat_gap_correlator.csv carries a smearing scan on the
# same ensemble for the 0++ correlator, and there the plaquette m_eff is lowest at 8 sweeps
# (1.140 +/- 0.134) with 24 reading higher and noisier (1.261 +/- 0.374). Wilson loops at R up to L/2
# and a zero-momentum correlator are smoothed by different amounts of the same smearing, so each is
# scanned on its own rather than sharing a level.
NSMEAR = int(os.environ.get("NSMEAR", "24"))                          # APE sweeps on the spatial links
ALPHA = 0.5                                                           # APE weight, as in PAPER Sec 8.7
NBLOCK = int(os.environ.get("NBLOCK", "8"))                           # jackknife blocks
COULOMB = os.environ.get("ST_COULOMB", "1") != "0"                    # fit V0 + sigma R - e/R
COLS = ["beta", "L", "ncfg", "nsmear", "t_read", "a2sigma_potential", "a2sigma_err",
        "a2sigma_syst", "coulomb_e", "a2sigma_creutz", "chi_rmax", "chi22", "chi33", "chi44",
        "sqrt_sigma"]


def _to_np(x):
    return x.detach().cpu().numpy() if hasattr(x, "detach") else np.asarray(x)


# -- the W(R,T) matrix ---------------------------------------------------------------------------
def wilson_matrix(b, q, rmax, tmax):
    """W[R-1, T-1] = <(1/2) Re tr U(R x T)> over SPATIAL-x-TEMPORAL planes only, for a batch of
    configs. The spatial and temporal link products are each built ONCE and reused across the (R,T)
    grid rather than rebuilt per pair, which is what makes the full grid affordable."""
    tax = G.D - 1                                                     # the temporal direction
    tline, P, sh = {}, q[..., tax, :], q[..., tax, :]
    tline[1] = P
    for T in range(2, tmax + 1):
        sh = b.roll(sh, -1, _sax(tax, 1))
        P = _qmul(b, P, sh)
        tline[T] = P
    W = np.zeros((rmax, tmax))
    for mu in range(G.D - 1):                                         # spatial mu only
        S = q[..., mu, :]
        shs = S
        sline = {1: S}
        for R in range(2, rmax + 1):
            shs = b.roll(shs, -1, _sax(mu, 1))
            S = _qmul(b, S, shs)
            sline[R] = S
        for R in range(1, rmax + 1):
            bottom = sline[R]
            for T in range(1, tmax + 1):
                left = tline[T]
                right = b.roll(left, -R, _sax(mu, 1))
                top = b.roll(bottom, -T, _sax(tax, 1))
                loop = _qmul(b, _qmul(b, _qmul(b, bottom, right), _qconj(b, top)), _qconj(b, left))
                W[R - 1, T - 1] += float(loop[..., 0].mean())
        del sline, S, shs
    return W / (G.D - 1)


# -- the static potential and its slope ----------------------------------------------------------
def v_eff(W, T):
    """V_eff(R,T) = log[W(R,T)/W(R,T+1)] -> V(R) as T grows. NaN where a loop is non-positive."""
    with np.errstate(invalid="ignore", divide="ignore"):
        return np.log(W[:, T - 1] / W[:, T])


def fit_sigma(V, rs, coulomb=COULOMB):
    """Fit V(R) = V0 + sigma R - e/R (or V0 + sigma R when coulomb=False) over the given R.
    Returns (sigma, e). Raises if any point in the fit range is not finite -- a NaN dropped
    silently from a fit range is a truncation of the measurement."""
    npar = 3 if coulomb else 2
    if len(rs) <= npar:
        raise SystemExit(
            f"fit range R={list(rs)} has {len(rs)} points for a {npar}-parameter fit: the system is "
            f"exactly determined (or under-determined), so the returned sigma is an artefact of the "
            f"parametrisation and carries no information about the potential. This is what an L=8 "
            f"lattice gives -- R is capped at L/2=4, leaving R=2,3,4. Use a larger lattice (L=16 "
            f"gives R=2..8) or ST_COULOMB=0, and accept the Coulomb bias that then returns.")
    y = V[rs - 1]
    if not np.all(np.isfinite(y)):
        bad = rs[~np.isfinite(y)]
        raise ValueError(f"V(R) not finite at R={list(bad)} -- loop fluctuated non-positive; "
                         f"raise the statistics or lower rmax rather than dropping the point")
    cols = [rs.astype(float), np.ones_like(rs, dtype=float)]
    if coulomb:
        cols.append(-1.0 / rs)
    A = np.vstack(cols).T
    p = np.linalg.lstsq(A, y, rcond=None)[0]
    return float(p[0]), (float(p[2]) if coulomb else 0.0)


def creutz(W, R, T):
    """chi(R,T) = -log[ W(R,T) W(R-1,T-1) / ( W(R,T-1) W(R-1,T) ) ]."""
    num = W[R - 1, T - 1] * W[R - 2, T - 2]
    den = W[R - 1, T - 2] * W[R - 2, T - 1]
    return float(-np.log(num / den)) if num > 0 and den > 0 else float("nan")


def creutz_sigma(Ws, Wm, rmax):
    """sigma with NO model of V(R), as a cross-check on the fitted value.

    The Creutz ratio is a double difference of log W, so the static self-energy V0 and the perimeter
    term cancel identically, which is the whole job of the three-parameter fit's V0. What is left
    approaches the tension from above as chi(R,R) = sigma + c/R^2, the known leading Coulomb
    correction, so a one-parameter extrapolation in 1/R^2 lands on sigma without positing a form for
    V(R). The value of the second estimator is that it is model-free.

    The R range is bounded by resolution, not by the lattice. The Wilson-loop signal dies with area,
    so the large-R ratios are noise: a point enters the extrapolation only when it is resolved at
    NSIG_RESOLVED with a jackknife error over the configuration blocks. Below three surviving R the
    extrapolation returns NaN and the caller reports the fit alone.

    Returns (chis, errs, used, sigma, c)."""
    rs = list(range(2, rmax + 1))
    chis = {R: creutz(Wm, R, R) for R in rs}
    errs = {}
    for R in rs:
        jk = [creutz(np.delete(Ws, k, axis=0).mean(0), R, R) for k in range(len(Ws))]
        jk = np.array([v for v in jk if np.isfinite(v)])
        errs[R] = (float(np.sqrt((len(jk) - 1) / len(jk) * np.sum((jk - jk.mean()) ** 2)))
                   if len(jk) == len(Ws) else float("nan"))
    used = [R for R in rs
            if np.isfinite(chis[R]) and np.isfinite(errs[R]) and errs[R] > 0
            and chis[R] / errs[R] >= NSIG_RESOLVED]
    if len(used) < 3:
        return chis, errs, used, float("nan"), float("nan")
    x = np.array([1.0 / R ** 2 for R in used])
    y = np.array([chis[R] for R in used])
    c, s = np.linalg.lstsq(np.vstack([x, np.ones_like(x)]).T, y, rcond=None)[0]
    return chis, errs, used, float(s), float(c)


NSIG_RESOLVED = 3.0        # a sigma(T) not separated from zero by this many sigma carries no information


def read_window(sig, err):
    """The T over which sigma(T) is actually measured, and the T read as the central value.

    A sigma(T) whose statistical error swallows it is not a measurement of anything, so the window is
    the T resolved at >= NSIG_RESOLVED. Within it the LARGEST T is read: excited states decay with T,
    so the largest resolved T is the least contaminated, and the spread of sigma over the window is
    quoted as the T-systematic rather than being averaged away.

    This deliberately does not demand a flat plateau. On this ensemble the Wilson-loop signal is
    exhausted by T=4 (sigma(4) = 0.06 +/- 0.04, under 2 sigma), so no two consecutive T can agree
    within errors and a plateau gate refuses outright -- discarding a measurement whose T-dependence
    is a few percent and whose value reproduces the literature. Refusing is right when the answer is
    meaningless; here it is not. The residual drift is REPORTED, in its own column, not hidden.

    Returns (window, T_read) or (None, None) when nothing is resolved -- the caller must then refuse."""
    win = sorted(t for t in sig
                 if np.isfinite(sig[t]) and err[t] > 0 and sig[t] / err[t] >= NSIG_RESOLVED)
    if not win:
        return None, None
    return win, win[-1]


# -- ensembles -----------------------------------------------------------------------------------
def blocks_from_links(beta, nblock):
    """Yield config blocks from the archived raw-link shards (dataset [D]); one block per shard."""
    # Resolved by store_path: CONFIGS, then the git-ignored local config file, then a refusal.
    root = store_path.store_root(required=False)
    if not root:
        raise SystemExit("ST_SOURCE=links reads the archived raw-link shards.\n"
                         + store_path.help_text())
    sub = os.path.join(root, "configs_links_su2")
    root = sub if os.path.isdir(sub) else root
    fs = sorted(glob.glob(os.path.join(root, f"su2_L*_b{beta:.2f}.s*.npy")))
    if not fs:
        raise SystemExit(f"no su2 link shards for beta={beta:.2f} under {root}\n{store_path.hint()}")
    if len(fs) < nblock:
        raise SystemExit(f"{len(fs)} shards < NBLOCK={nblock}: too few blocks for a jackknife error")
    for f in fs:
        yield np.load(f).astype("float32")


def blocks_from_generation(beta, ncfg, nblock):
    """Yield freshly generated config blocks, ncfg total split into nblock equal blocks."""
    per = ncfg // nblock
    if per * nblock != ncfg:
        raise SystemExit(f"NCFG={ncfg} is not divisible by NBLOCK={nblock}")
    for k in range(nblock):
        yield np.stack([_to_np(G.gauge_field(DIMS, beta, group="su2", seed=1000 + k * per + i,
                                             therm=THERM, device=DEVICE)).astype("float32")
                        for i in range(per)])


def main():
    os.environ.setdefault("GEN_FP", "32")      # links are stored fp32; keep the backend there too
    b = _Backend(DEVICE)
    print(f"device={DEVICE}  source={SOURCE}  nsmear={NSMEAR}  nblock={NBLOCK}  "
          f"coulomb={COULOMB}  betas={BETAS}", flush=True)
    rows, curves = [], []
    for beta in BETAS:
        t0 = time.time()
        gen = (blocks_from_links(beta, NBLOCK) if SOURCE == "links"
               else blocks_from_generation(beta, NCFG, NBLOCK))
        Ws, ncfg, dims, rmax, tmax = [], 0, None, None, None
        for arr in gen:
            dims = arr.shape[1:1 + G.D]
            rmax = min(dims[:G.D - 1]) // 2                # R > L/2 is the periodic image
            tmax = min(rmax + 4, dims[G.D - 1] // 2)       # enough T to expose a plateau
            q = b.t.as_tensor(arr, dtype=b.f, device=b.dev) if b.torch else arr
            q = G.ape_smear(q, NSMEAR, alpha=ALPHA, device=DEVICE)
            Ws.append(wilson_matrix(b, q, rmax, tmax))
            ncfg += arr.shape[0]
            del q
            print(f"  b{beta:.2f} block {len(Ws)}/{NBLOCK}  ncfg={ncfg}  "
                  f"L={dims[0]} Nt={dims[G.D-1]} rmax={rmax} tmax={tmax}  "
                  f"({time.time()-t0:.0f}s)", flush=True)
        Ws = np.array(Ws)
        Wm = Ws.mean(0)
        rs = np.arange(2, rmax + 1)

        # sigma(T) with a jackknife error at every T -- the plateau must be SHOWN, not assumed
        sig, err, evals = {}, {}, {}
        for T in range(1, tmax):
            try:
                s_all, e_all = fit_sigma(v_eff(Wm, T), rs)
            except ValueError:
                continue                                   # this T has no finite V(R); later T are worse
            jk = []
            for k in range(len(Ws)):
                Wk = np.delete(Ws, k, axis=0).mean(0)
                try:
                    jk.append(fit_sigma(v_eff(Wk, T), rs)[0])
                except ValueError:
                    jk = []
                    break
            if not jk:
                continue
            jk = np.array(jk)
            sig[T], evals[T] = s_all, e_all
            err[T] = float(np.sqrt((len(jk) - 1) / len(jk) * np.sum((jk - jk.mean()) ** 2)))

        if not sig:
            raise SystemExit(f"beta={beta}: no T gave a finite V(R) over R={list(rs)}")
        print(f"  sigma(T) at beta={beta:.2f}  (every T shown; the read is chosen below):", flush=True)
        for T in sorted(sig):
            print(f"    T={T:2d}  a2sigma={sig[T]:8.4f} +/- {err[T]:.4f}   e_coulomb={evals[T]:6.3f}",
                  flush=True)
        chis, cerr, cused, s_creutz, c_creutz = creutz_sigma(Ws, Wm, rmax)
        print("  Creutz ratios chi(R,R) -- no fit, no model of V(R) (V0 cancels in the double "
              "difference):", flush=True)
        for R in sorted(chis):
            mark = "used" if R in cused else "DROPPED (< %.0f sigma)" % NSIG_RESOLVED
            print(f"    chi({R},{R}) = {chis[R]:8.4f} +/- {cerr[R]:.4f}   {mark}", flush=True)
        if np.isfinite(s_creutz):
            print(f"    extrapolated over R={cused}: chi = sigma + c/R^2  ->  a2sigma = "
                  f"{s_creutz:.4f}  (c = {c_creutz:.3f})  [model-free cross-check]", flush=True)
        else:
            print(f"    only {len(cused)} R resolved at {NSIG_RESOLVED} sigma -- no model-free "
                  f"extrapolation (needs 3). Reporting the fit alone.", flush=True)
        for R in sorted(chis):
            curves.append(dict(beta=beta, L=dims[0], kind="chi_RR", x=R,
                               value=round(chis[R], 6) if np.isfinite(chis[R]) else "",
                               err=round(cerr[R], 6) if np.isfinite(cerr[R]) else "",
                               used=int(R in cused)))
        window, Tp = read_window(sig, err)
        if Tp is None:
            raise SystemExit(
                f"beta={beta}: no T resolves sigma at {NSIG_RESOLVED} sigma over T={sorted(sig)} -- "
                f"the Wilson-loop signal is exhausted before the potential is measurable, so no "
                f"string tension is extractable from this ensemble. Raise the statistics.")
        s, e, se = sig[Tp], evals[Tp], err[Tp]
        # The T-dependence that survives inside the window is a SYSTEMATIC, not noise: it is the
        # residual excited-state contamination. Quote it separately rather than folding it into a
        # statistical bar that would then understate the uncertainty.
        syst = float(max(abs(sig[T] - s) for T in window)) if len(window) > 1 else 0.0
        if syst >= s:
            raise SystemExit(
                f"beta={beta}: T-systematic {syst:.4f} exceeds the central value {s:.4f} over "
                f"T={window} -- sigma is not determined by this ensemble. REFUSING to quote it.")
        print(f"  resolved window T={window} (>= {NSIG_RESOLVED} sigma), read at T={Tp}: "
              f"drift {syst:.4f} vs statistical {se:.4f} -- "
              f"{'drift within statistics' if syst <= se else 'drift DOMINATES; quoted as a systematic'}",
              flush=True)
        sq = float(np.sqrt(s)) if s > 0 else float("nan")
        rows.append(dict(beta=beta, L=dims[0], ncfg=ncfg, nsmear=NSMEAR, t_read=Tp,
                         a2sigma_potential=round(s, 4), a2sigma_err=round(se, 4),
                         a2sigma_syst=round(syst, 4), coulomb_e=round(e, 4),
                         a2sigma_creutz=round(s_creutz, 4),
                         # the largest R that SURVIVED the resolution cut, not the largest R the
                         # lattice has -- max(chis) is R=8, whose ratio is pure noise (NaN here)
                         chi_rmax=round(chis[max(cused)], 4) if cused else float("nan"),
                         chi22=round(chis.get(2, float("nan")), 4),
                         chi33=round(chis.get(3, float("nan")), 4),
                         chi44=round(chis.get(4, float("nan")), 4),
                         sqrt_sigma=round(sq, 4)))
        for T in sorted(sig):
            curves.append(dict(beta=beta, L=dims[0], kind="sigma_T", x=T,
                               value=round(sig[T], 6), err=round(err[T], 6),
                               used=int(T in window)))
        print(f"b{beta:.2f}: READ at T={Tp}  a2sigma={s:.4f} +/-{se:.4f}(stat) +/-{syst:.4f}(syst)  "
              f"e={e:.3f}  sqrt_sigma={sq:.4f}  "
              f"({time.time()-t0:.0f}s)", flush=True)

    table.write(DAT, rows, COLS)
    table.write(CURVES, curves, CURVE_COLS)
    print("wrote", DAT)
    print("wrote", CURVES)


if __name__ == "__main__":
    main()
