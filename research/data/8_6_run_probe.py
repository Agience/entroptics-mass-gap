"""8_6_run_probe.py -- deterministic system identification of the entroptics read (PAPER Sec 8.6).

No Monte Carlo, no vacuum sampling. We feed CONTROLLED analytic inputs to the reader and read
the deterministic output, then BUILD the input->output function from the observed change (the
transfer function of the instrument). Each read is a deterministic functional of the signal's own
correlation operator, so one controlled input gives one clean output: no ensemble average, this
is O(reads) -- seconds, not hours.

Discipline: the probe is INSTRUMENT CHARACTERIZATION, not a paper config-read, so (with the
maintainer's sign-off) it reads the library ``Aperture`` DIRECTLY -- the inputs are already 2-D
(T, F), so no wrapper reduction is needed, and the direct read exposes the full param surface
(phi_T / phi_F, sigma_T / sigma_F, attenuation, dominance, ...). Inputs are analytic fields fed
WHOLE (no hand centering, folding, or handed scale). The only fits are of the read OUTPUTS versus
the controlled knob -- the transfer function itself, the deliverable -- never a computation between
the data and the read. Where an exact invariant exists we lead with it, so the law needs no fit.

Four probes, two validating the backbone and two attacking the open a priori:

  P1  DMD gap transfer       rate = -log|mu_1|          EXACT identity -- the gap read inverts the
                             operator (PAPER Thm 9.2 / [E Sec 9]).
  P2  Abbe aperture          a_delta * rho = const       the diffraction-limit transfer function:
                             the aperture is the reciprocal correlation length (PAPER Sec 4).
  P3  confinement transfer   order parameter & vortex     A1 side: the confinement reads (dominance,
                             tension mu vs signal strength  contrast) are smooth, BOUNDED, monotone
                             order-parameter functionals; mu has a ceiling (the uniform-bound shape).
  P4  A2 rotation isotropy    a_delta(theta); axis ratio   two-axis SO(4) target: an isotropic field
                             reads EXACTLY rotation-invariant at every spacing; an anisotropic field's
                             axis aperture ratio tracks the correlation-length ratio (the read sees it).

Runs on numpy (default) or torch (--device cuda); reads go through the front door, so a torch field
stays on the GPU through the reductions.

    python 8_6_run_probe.py                 # all four probes, numpy
    python 8_6_run_probe.py --device cuda   # dense sweeps on the GPU
    python 8_6_run_probe.py --only P4       # one probe
"""
from __future__ import annotations

import argparse
import math
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))                       # research/data
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))  # research/code

import entroptics_adapter as entroptics                       # the wrapper module (re-exports the library front door)
import table                            # generic CSV writer

Aperture = entroptics.Aperture          # library front door; our inputs are already 2-D (T, F)

DAT = os.path.join(_HERE, "8_6_dat_probe.csv")


# ══════════════════════════════════════════════════════════════════════════════
# helpers
# ══════════════════════════════════════════════════════════════════════════════
def _dev(W, device):
    """Optionally move a constructed field to a torch device; the read stays on-device."""
    if not device:
        return W
    import torch
    return torch.as_tensor(np.ascontiguousarray(W), device=device, dtype=torch.float64)


def _f(x):
    return float(x)


def _power_law(x, y):
    """Transfer-function inference (the requested equation) on the read OUTPUTS: least-squares
    y = k x^p in log-log, with R^2. Characterizes the instrument response; never in the read path."""
    x = np.asarray(x, float); y = np.asarray(y, float)
    m = (x > 0) & (y > 0)
    lx, ly = np.log(x[m]), np.log(y[m])
    p, b = np.polyfit(lx, ly, 1)
    yhat = p * lx + b
    ss = float(np.sum((ly - yhat) ** 2)); tot = float(np.sum((ly - ly.mean()) ** 2))
    return float(p), float(math.exp(b)), (1.0 - ss / tot if tot > 0 else 1.0)


# ══════════════════════════════════════════════════════════════════════════════
# P1 -- DMD gap transfer: rate = -log|mu_1| (exact identity)
# ══════════════════════════════════════════════════════════════════════════════
def _operator(alphas, thetas):
    """A real block-diagonal one-step operator A with prescribed mode magnitudes
    |mu_k| = exp(-alpha_k) and frequencies theta_k (2x2 rotation-scaling blocks)."""
    K = len(alphas)
    A = np.zeros((2 * K, 2 * K))
    for k, (a, th) in enumerate(zip(alphas, thetas)):
        r = math.exp(-a)
        A[2 * k:2 * k + 2, 2 * k:2 * k + 2] = r * np.array(
            [[math.cos(th), -math.sin(th)], [math.sin(th), math.cos(th)]])
    return A


def _trajectory(A, T):
    """X[t] = A^t x0, x0 = 1 (excites every block) -- a (T, F) linear trajectory."""
    F = A.shape[0]
    x = np.ones(F)
    X = np.empty((T, F))
    for t in range(T):
        X[t] = x
        x = A @ x
    return X


def probe_p1_gap(device=None, T=40):
    """Feed a linear trajectory whose dominant (slowest) mode magnitude is exp(-Delta); the gap
    read rates().dominant must return Delta exactly (it inverts the operator). Modes are kept close
    in rate and T short, so the trajectory never spans more dynamic range than float64 resolves."""
    deltas = np.round(np.linspace(0.10, 1.20, 12), 4)
    rows, read = [], []
    for d in deltas:
        alphas = [float(d), float(d) + 0.4, float(d) + 0.8]           # dominant alpha = Delta
        thetas = [0.40, 1.30, 2.40]
        X = _trajectory(_operator(alphas, thetas), T)
        got = _f(Aperture(_dev(X, device)).rates().dominant)
        read.append(got)
        rows.append(dict(probe="P1_gap", x=float(d), y=got, residual=float(got - d)))
    read = np.asarray(read)
    err = float(np.max(np.abs(read - deltas)))
    print("\n== P1  DMD gap transfer:  rate = -log|mu_1|  (exact identity) ==")
    for d, g in zip(deltas, read):
        print(f"   Delta_in={d:5.3f}   rate_out={g:8.6f}   resid={g - d:+.2e}")
    print(f"   -> max |rate_out - Delta_in| = {err:.2e} nats  "
          f"({'EXACT (read inverts the operator)' if err < 1e-6 else 'near-exact'})")
    return rows


# ══════════════════════════════════════════════════════════════════════════════
# P2 -- Abbe aperture: a_delta * rho = const (the diffraction-limit transfer function)
# ══════════════════════════════════════════════════════════════════════════════
def _corr_field(rho, T=768, F=48):
    """A deterministic AR(1) field with temporal (axis-0) correlation length rho:
    W[t] = exp(-1/rho) W[t-1] + d[t], d a FIXED broadband deterministic innovation (no RNG).
    Its ordered-axis autocorrelation is ~ exp(-|tau|/rho). Fed whole -- the library centers."""
    rc = math.exp(-1.0 / rho)
    s = np.arange(T)[:, None]
    f = np.arange(F)[None, :]
    d = np.cos(2 * np.pi * s * (f + 1) / T) + np.sin(2 * np.pi * s * (2 * f + 1) / (2 * T))
    W = np.empty((T, F))
    W[0] = d[0]
    for t in range(1, T):
        W[t] = rc * W[t - 1] + d[t]
    return W


def probe_p2_abbe(device=None):
    """Ramp the correlation length rho (kept << the window so it is well resolved); read the
    aperture a_delta and the recovered length xi through the front door. The EXACT law is the
    invariant a_delta * rho = const (the aperture is the reciprocal length); report the product
    across the ramp, then the inferred power (slope -1) as a cross-check."""
    rhos = np.round(np.geomspace(6.0, 26.0, 12), 3)   # above the read's own resolution floor (~6)
    rows, a_d, xi = [], [], []
    for r in rhos:
        ap = Aperture(_dev(_corr_field(float(r)), device))
        ad = _f(ap.a_delta); x = _f(ap.correlation_length)
        a_d.append(ad); xi.append(x)
        rows.append(dict(probe="P2_abbe", x=float(r), y=ad, correlation_length=x))
    a_d = np.asarray(a_d); xi = np.asarray(xi)
    prod = a_d * rhos
    cv = float(prod.std() / prod.mean())
    p_ad, k_ad, r2_ad = _power_law(rhos, a_d)
    print("\n== P2  Abbe aperture:  a_delta * rho = const ==")
    for r, ad, x in zip(rhos, a_d, xi):
        print(f"   rho_in={r:6.2f}   a_delta={ad:8.4f}   xi_out={x:7.2f}   a_delta*rho={ad * r:7.4f}")
    print(f"   -> INVARIANT a_delta*rho = {prod.mean():.4f}  (spread {cv:.2%} over rho in "
          f"[{rhos[0]:.0f},{rhos[-1]:.0f}])")
    print(f"   -> inferred a_delta = {k_ad:.3f} * rho^({p_ad:+.3f})   R^2={r2_ad:.4f}   (Abbe slope -1)")
    return rows


# ══════════════════════════════════════════════════════════════════════════════
# P3 -- confinement order-parameter transfer function (A1 side)
# ══════════════════════════════════════════════════════════════════════════════
def _snr_field(s, T=193, F=32):
    """A coherent low-rank SIGNAL of strength s on a FIXED deterministic broadband background (no
    RNG). At s=0 the read sees only the background (disorder floor); as s grows a coherent mode
    orders the field. This is the controlled order parameter of the confinement read."""
    xb = np.arange(T)[:, None]; fb = np.arange(F)[None, :]
    bg = (np.cos(2 * np.pi * xb * (7 * fb + 3) / T) + np.sin(2 * np.pi * xb * (11 * fb + 5) / T)
          + np.cos(2 * np.pi * xb * (17 * fb + 1) / (2 * T)))
    sig = np.outer(np.cos(2 * np.pi * np.arange(T) / 23.0), np.cos(2 * np.pi * np.arange(F) / 7.0))
    return bg + s * sig


def probe_p3_confinement(device=None):
    """Ramp the coherent signal strength s (the order knob); read the vortex tension
    mu = attenuation = log(lambda1/max(lambda2,floor)) [nats, the A1 order parameter directly
    comparable to kappa_0 = (1/4)ln3], the normalized order parameter dominance = (lambda1-1)/(N-1)
    in [0,1], and contrast. Establishes the confinement read as a smooth, BOUNDED, monotone
    functional: mu rises with order and, for a DISORDER-floor input (s = 0), sits at 0 -- the shape
    the uniform bound mu < kappa_0 needs (mu does not run away in the disordered phase)."""
    ss = np.round(np.geomspace(0.05, 32.0, 16), 4)
    ss = np.r_[0.0, ss]
    rows, dom, con, mu = [], [], [], []
    for s in ss:
        ap = Aperture(_dev(_snr_field(float(s)), device))
        d = _f(ap.dominance); c = _f(ap.contrast); m = _f(ap.attenuation)
        dom.append(d); con.append(c); mu.append(m)
        rows.append(dict(probe="P3_confinement", x=float(s), y=d, contrast=c, mu=m))
    dom = np.asarray(dom); mu = np.asarray(mu); con = np.asarray(con)
    k0 = 0.25 * math.log(3.0)
    print("\n== P3  confinement order-parameter transfer function (A1 side) ==")
    print(f"   {'s':>7} {'mu(nats)':>9} {'dominance':>10} {'contrast':>9}   vs kappa_0={k0:.3f}")
    for s, m, d, c in zip(ss, mu, dom, con):
        flag = "  < kappa_0" if m < k0 else "  > kappa_0"
        print(f"   {s:7.3f} {m:9.4f} {d:10.4f} {c:9.3f} {flag}")
    mono = bool(np.all(np.diff(dom) >= -1e-9))
    below = ss[mu < k0]
    print(f"   -> dominance monotone {mono}, bounded in [0,1]: {dom.min():.3f} -> {dom.max():.3f}")
    print(f"   -> vortex tension mu < kappa_0 for s <= {below.max() if below.size else 0:.3f} "
          f"(disorder floor s=0 reads mu={mu[0]:.3f}); mu is a smooth monotone functional of order")
    return rows


# ══════════════════════════════════════════════════════════════════════════════
# P4 -- A2 rotation isotropy (two-axis SO(4) target)
# ══════════════════════════════════════════════════════════════════════════════
def _ring_field(k0x, k0y=None, nang=128):
    """A closed-form, FULL-RANK stationary field: sum of nang equal-amplitude, zero-phase plane
    waves on the ellipse (k0x cos, k0y sin). k0y == k0x -> the ISOTROPIC ring (rotationally
    symmetric, correlation length ~ 1/k0). k0x != k0y -> controlled anisotropy: the correlation
    length along x is ~ 1/k0x, along y ~ 1/k0y. Returns a closure evaluatable on ANY grid
    (rotation = rotated sampling grid)."""
    k0y = k0x if k0y is None else k0y
    ang = np.linspace(0, 2 * np.pi, nang, endpoint=False)
    KX = k0x * np.cos(ang); KY = k0y * np.sin(ang)

    def phi(X, Y):
        X = np.asarray(X, float)[..., None]; Y = np.asarray(Y, float)[..., None]
        return np.sum(np.cos(KX * X + KY * Y), axis=-1)
    return phi


def _sample(phi, T, F, a, theta):
    """Sample phi EXACTLY on a (T x F) square lattice of spacing a, rotated by theta."""
    i = np.arange(T)[:, None]; j = np.arange(F)[None, :]
    x0 = i * a; y0 = j * a
    x = x0 * math.cos(theta) - y0 * math.sin(theta)
    y = x0 * math.sin(theta) + y0 * math.cos(theta)
    return phi(x, y)


def probe_p4_isotropy(device=None, T=192, F=192):
    """The read's two axes are T (ordered) and F (feature); A2 is their symmetry. Three reads:
      (a) T<->F cross-axis agreement on the ISOTROPIC field, read NATIVELY: phi_T vs phi_F and
          sigma_T vs sigma_F must agree (the read carries the vacuum's isotropy into the two axes;
          this is the paper's cross-axis agreement, here from first principles).
      (b) rotation invariance: a_delta(theta) on the isotropic field must be constant at every
          spacing (continuous SO(2) in the read, no hypercubic artifact to restore).
      (c) anisotropy detection: a SEPARABLE field with correlation-length ratio q = rho_F/rho_x --
          the axis fill ratio phi_T/phi_F must track q (the read SEES anisotropy, = 1 when q = 1).

    Every read here passes ``window=None`` (the whole frame), unlike P1-P3.  This is an INVARIANCE
    test: one read is compared across 25 rotations and 30 spacings of the same grid, so the extent
    must be the same at every point or the sweep measures the extent instead of the invariance.
    The default trailing window is derived from the data and so moves with the sweep parameter --
    on this 192-row grid entroptics 0.2.1 selects 173 rows at the coarsest spacing and 192
    elsewhere, which by itself reversed the coarse end of the (b) restoration trend.  ``window=None``
    is the library's frame-commensurate read (``entroptics/__init__``) and is what an invariance
    sweep has always meant here; P1-P3 sweep a physical parameter and read a stationary statistic
    through the intended bounded aperture, so they keep the default."""
    rows = []

    # (a) T<->F cross-axis agreement, native two-axis read on the isotropic field
    phi = _ring_field(1.0)
    ap = Aperture(_dev(_sample(phi, T, F, 0.4, 0.0), device), window=None)
    pT, pF, sT, sF = _f(ap.phi_T), _f(ap.phi_F), _f(ap.sigma_T), _f(ap.sigma_F)
    print("\n== P4  A2 two-axis (T<->F) symmetry ==")
    print(f"   (a) ISOTROPIC field, native cross-axis read:")
    print(f"        phi_T={pT:.4f}  phi_F={pF:.4f}  disagreement {abs(pT - pF) / (0.5 * (pT + pF)):.2%}")
    print(f"        sigma_T={sT:.4f}  sigma_F={sF:.4f}  disagreement {abs(sT - sF) / (0.5 * (sT + sF)):.2%}")
    rows.append(dict(probe="P4a_crossaxis", x=0.0, y=pT, a_axis=pF, a_diag=sT))

    # (b) rotation invariance + hypercubic restoration: variation of a_delta(theta) shrinks with a.
    # DENSE sweep: the variation is not merely small, it falls to MACHINE ZERO once the grid resolves
    # the field (a below the sampling threshold), so SO(4) is exact there, not only asymptotic.
    thetas = np.linspace(0.0, math.pi / 2, 25)
    def _aniso(k0, a):
        v = np.array([_f(Aperture(_dev(_sample(_ring_field(k0), T, F, a, th), device),
                                 window=None).a_delta) for th in thetas])
        return float((v.max() - v.min()) / v.mean())
    print("   (b) ISOTROPIC field, a_delta(theta) variation vs resolution (coarse -> fine = restoration):")
    # sweep EVENLY in points-per-wavelength ppw = 2 pi / a (k0 = 1); a = 2 pi / ppw. Store ppw as x.
    for ppw in np.linspace(4.0, 27.0, 30):
        a = 2 * math.pi / ppw
        var = _aniso(1.0, a)
        print(f"        ppw={ppw:5.2f} (a={a:.3f}): variation {var:.3e}")
        rows.append(dict(probe="P4b_restoration", x=float(ppw), y=float(var)))

    # (d) the sampling-threshold law: the spacing a*(k0) at which the read becomes EXACTLY isotropic
    # (variation < 1e-10) scales as 1/k0 -- the Nyquist relation a*.k0 = const. This is the arithmetic
    # mechanism of the restoration (band-limited + sub-Nyquist -> exact rotation-invariant read).
    print("   (d) sampling threshold a*(k0) where the read is EXACTLY isotropic (var < 1e-10):")
    for k0 in (0.5, 1.0, 1.5, 2.0):
        lo, hi = 0.05, 2.0
        for _ in range(20):
            mid = 0.5 * (lo + hi)
            if _aniso(k0, mid) < 1e-10: lo = mid
            else: hi = mid
        astar = 0.5 * (lo + hi)
        print(f"        k0={k0:.2f}: a*={astar:.4f}   a*.k0={astar * k0:.4f}")
        rows.append(dict(probe="P4d_nyquist", x=float(k0), y=float(astar)))

    # (c) anisotropy detection: full-rank elliptical field, axis fill ratio vs correlation ratio
    print("   (c) ELLIPTICAL (anisotropic) field, axis fill ratio phi_F/phi_T vs rho_x/rho_y:")
    k0 = 1.0
    ratios = np.round(np.linspace(1.0, 4.0, 7), 3)
    fr = []
    for q in ratios:
        ap = Aperture(_dev(_sample(_ring_field(k0 / q, k0), T, F, 0.3, 0.0), device), window=None)
        r = _f(ap.phi_F) / _f(ap.phi_T) if _f(ap.phi_T) else float("nan")
        fr.append(r)
        rows.append(dict(probe="P4c_anisotropic", x=float(q), y=float(r)))
    fr = np.asarray(fr)
    print(f"        {'rho_x/rho_y':>12} {'phi_F/phi_T':>12}")
    for q, r in zip(ratios, fr):
        print(f"        {q:12.2f} {r:12.4f}")
    slope = float(np.polyfit(ratios, fr, 1)[0])
    print(f"   -> isotropic point ratio {fr[0]:.4f} (~1 when q=1); read tracks anisotropy, "
          f"d(phi_F/phi_T)/d(rho_x/rho_y) = {slope:.3f}")
    return rows


PROBES = {"P1": probe_p1_gap, "P2": probe_p2_abbe,
          "P3": probe_p3_confinement, "P4": probe_p4_isotropy}


def main():
    ap = argparse.ArgumentParser(description="Deterministic system-ID of the entroptics read.")
    ap.add_argument("--device", default=None, help="torch device for the reads, e.g. cuda")
    ap.add_argument("--only", default=None, choices=list(PROBES), help="run one probe")
    args = ap.parse_args()

    which = [args.only] if args.only else list(PROBES)
    print(f"probe: deterministic system-ID  device={args.device or 'numpy'}  probes={which}")
    rows = []
    for key in which:
        rows += PROBES[key](device=args.device)

    cols = ["probe", "x", "y", "residual", "correlation_length", "contrast", "mu",
            "entropy", "a_axis", "a_diag"]
    table.write(DAT, [{c: r.get(c, "") for c in cols} for r in rows], cols)
    print(f"\nwrote {DAT}  ({len(rows)} rows)")


if __name__ == "__main__":
    main()
