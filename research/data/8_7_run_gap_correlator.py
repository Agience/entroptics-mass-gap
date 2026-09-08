"""8_7_run_gap_correlator.py -- the RAW correlator the gap read is taken from, measured directly.

Every gap number in Sec 8.6-8.7 (m_hi, Delta, the transfer pencil) is a decay rate extracted from the
zero-momentum connected correlator of a gauge-invariant operator. This script measures that correlator
itself -- no DMD, no Koopman fit, no Entroptics read, no noise floor -- so the input to those reads can
be inspected rather than assumed:

    O(t) = sum_x Op(x,t),   C(tau) = < dO(t) dO(t+tau) >,   m_eff(tau) = log[C(tau)/C(tau+1)]

for two operators (the action density phi(x) and the Sec 8.7 spatial-plaquette 0++ operator), across
APE-smearing levels, for every (L, beta) the raw links cover. ONLY_L and ONLY_BETA restrict the scan.

Why this exists
---------------
A decay rate is only a mass if the correlator has a PLATEAU: m_eff(tau) is monotone decreasing and
reaches E_0 from above, so a rate read before the plateau is an upper bound on the gap, not the gap.
On these ensembles the correlator falls to ~0.1-0.2 at tau=1 and into noise by tau~2-3 (the sign
flips), and m_eff never plateaus -- which is a property of the DATA and its statistics, not of any
particular read. The diagnostic number is C(1)/C(0): for a clean exponential it equals exp(-a*m) and
must rise steeply with beta as the lattice spacing falls. Measured, it is far below that and nearly
beta-independent, the signature of C(0) carrying uncorrelated variance the other lags do not:

    C(0) = signal + white noise,  C(tau>=1) = signal only
    =>  C(1)/C(0) ~ [signal/(signal+noise)] * exp(-a*m)

so -log[C(1)/C(0)] measures an operator-overlap ratio, not a mass, and barely moves with beta.

The comparison column is a*m_0++ = 3.59*sqrt(sigma) using this repo's OWN measured sigma
(8_8_dat_string_tension.csv) and the continuum SU(2) ratio m(0++)/sqrt(sigma) = 3.59(12)
(Lucini-Teper-Wenger 2004) -- a cited number, used here only to say what the correlator would have to
do, never fed into any read.

Writes 8_7_dat_gap_correlator.csv.

    CONFIGS=/path/to/entroptics-lattice DEVICE=cuda python 8_7_run_gap_correlator.py
(or set CONFIGS once for the machine in the git-ignored local config file at the repository root)
"""
from __future__ import annotations

import csv
import glob
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(_HERE, "..", "code")))

import lattice_generator as G
from lattice_generator import _Backend, _qmul, _qconj, _sax
import entroptics_adapter as W          # jackknife comes from the library, through the front door
import store_path                       # the ONE place the ensemble store is located
import table

DEVICE = os.environ.get("DEVICE") or None
DAT = os.path.join(_HERE, "8_7_dat_gap_correlator.csv")
TENSION = os.path.join(_HERE, "8_8_dat_string_tension.csv")
SPATIAL = (0, 1, 2)
ALPHA = 0.5
SMEARS = tuple(int(x) for x in os.environ.get("SMEARS", "0,8,24").split(","))
NCFG = int(os.environ.get("NCFG", "256"))          # configs per coupling (shards of 64)
NBIN = int(os.environ.get("NBIN", "8"))            # jackknife bins
NLAG = int(os.environ.get("NLAG", "6"))
# Configurations per smearing pass. O(t) is computed per configuration, so the ensemble is chunked
# and the resulting (n, T) arrays concatenated: identical to smearing the whole ensemble at once,
# at bounded memory. The budget is in lattice sites, so the chunk shrinks as the volume grows.
SITES_PER_CHUNK = int(os.environ.get("SITES_PER_CHUNK", "6_000_000"))
M0_OVER_SQRT_SIGMA = 3.59                          # Lucini-Teper-Wenger 2004, SU(2); cited, not read
COLS = ["operator", "beta", "L", "ncfg", "nsmear", "tau", "C_over_C0", "C_err",
        "m_eff", "m_eff_err", "a_m_0pp_expected"]


def _root():
    # Resolved by store_path: CONFIGS, then the git-ignored local config file, then a refusal --
    # which now says what the store IS and where to get it, not just the name of a variable.
    r = store_path.store_root(required=False)
    if not r:
        raise SystemExit(store_path.help_text())
    sub = os.path.join(r, "configs_links_su2")
    return sub if os.path.isdir(sub) else r


def plaquette_0pp(b, q):
    """The Sec 8.7 operator: sum of spatial-plaquette real traces per time slice."""
    O = None
    for i in SPATIAL:
        for j in SPATIAL:
            if j <= i:
                continue
            Ui, Uj = q[..., i, :], q[..., j, :]
            plaq = _qmul(b, _qmul(b, Ui, b.roll(Uj, -1, _sax(i, 1))),
                         _qmul(b, _qconj(b, b.roll(Ui, -1, _sax(j, 1))), _qconj(b, Uj)))
            s = plaq[..., 0].sum(dim=(1, 2, 3)) if hasattr(plaq, "dim") else plaq[..., 0].sum((1, 2, 3))
            O = s if O is None else O + s
    return O.detach().cpu().numpy() if hasattr(O, "detach") else np.asarray(O)


def action_0pp(b, q):
    """The action-density operator, zero-momentum projected: O(t) = sum_x phi(x,t)."""
    d = G.action_density(q, group="su2", device=DEVICE)
    d = d.detach().cpu().numpy() if hasattr(d, "detach") else np.asarray(d)
    return d.sum(axis=(1, 2, 3))


def cbar(O, nlag):
    """C(tau)/C(0) from a set of per-configuration O(t). The vacuum is the ENSEMBLE mean, not a
    per-configuration time mean, matching 8_7_run_transfer_gap."""
    d = O - O.mean()
    c = np.array([np.mean(d * np.roll(d, -t, axis=1)) for t in range(nlag + 1)])
    return c / c[0]


def correlator(O, nlag):
    """(C, C_err, m_eff, m_eff_err) over lags, errors by delete-one-bin jackknife.

    The resampling is the library's ``jackknife`` rather than a local copy: it is a domain-agnostic
    read with no closed-form interval, so the bin construction and the (G-1)/G factor live in one
    place and cannot drift from the transfer-pencil errors of 8_7_run_transfer_gap. m_eff is
    resampled as its own read, so its error carries the correlation between adjacent lags instead of
    propagating two independent ones."""
    C = np.empty(nlag + 1)
    Ce = np.empty(nlag + 1)
    for t in range(nlag + 1):
        C[t], Ce[t] = W.jackknife(O, lambda sub, _t=t: float(cbar(sub, nlag)[_t]), n_bins=NBIN)
    me = np.full(nlag, np.nan)
    mee = np.full(nlag, np.nan)
    for t in range(nlag):
        def _meff(sub, _t=t):
            c = cbar(sub, nlag)
            return float(np.log(c[_t] / c[_t + 1])) if c[_t] > 0 and c[_t + 1] > 0 else float("nan")
        v, e = W.jackknife(O, _meff, n_bins=NBIN)
        if np.isfinite(v) and np.isfinite(e):
            me[t], mee[t] = v, e
    return C, Ce, me, mee


def main():
    os.environ.setdefault("GEN_FP", "32")
    b = _Backend(DEVICE)
    sig = {}
    if os.path.exists(TENSION):
        for r in csv.DictReader(open(TENSION)):
            sig[float(r["beta"])] = float(r["a2sigma_potential"])
    root = _root()
    # Group by (L, beta): the store carries several volumes at the same coupling, and each is its
    # own ensemble. Concatenating across L is a shape error, and averaging across it would be a
    # different measurement.
    pairs = set()
    for f in glob.glob(os.path.join(root, "su2_L*_b*.s*.npy")):
        base = os.path.basename(f)
        pairs.add((int(base.split("_L")[1].split("_b")[0]),
                   float(base.split("_b")[1].split(".s")[0])))
    pairs = sorted(pairs)
    if not pairs:
        raise SystemExit(f"no su2 link shards under {root}")
    only_L = os.environ.get("ONLY_L")
    only_b = os.environ.get("ONLY_BETA")
    if only_L:
        pairs = [(L, b) for L, b in pairs if L in {int(x) for x in only_L.split(",")}]
    if only_b:
        pairs = [(L, b) for L, b in pairs if any(abs(b - float(x)) < 1e-9 for x in only_b.split(","))]
    print(f"device={DEVICE}  (L,beta)={pairs}  smears={SMEARS}  ncfg={NCFG}  nbin={NBIN}", flush=True)
    rows = []
    for L, beta in pairs:
        fs = sorted(glob.glob(os.path.join(root, f"su2_L{L}_b{beta:.2f}.s*.npy")))
        lk = np.concatenate([np.load(f).astype("float32") for f in fs], 0)[:NCFG]
        q0 = b.t.as_tensor(lk, dtype=b.f, device=b.dev) if b.torch else lk
        am = M0_OVER_SQRT_SIGMA * np.sqrt(sig[beta]) if beta in sig else float("nan")
        # sigma is measured at L=16; a*m_0++ is a physical scale, so the same value is the
        # comparison at every volume at this coupling.
        print(f"beta={beta:.2f}  L={L}  ncfg={lk.shape[0]}  expected a*m_0++={am:.3f}", flush=True)
        sites = int(np.prod(lk.shape[1:1 + G.D]))
        chunk = max(1, min(lk.shape[0], SITES_PER_CHUNK // sites))
        for ns in SMEARS:
            for name, op in (("action_density", action_0pp), ("plaquette_0pp", plaquette_0pp)):
                parts = []
                for k in range(0, lk.shape[0], chunk):
                    qc = q0[k:k + chunk]
                    qc = qc if ns == 0 else G.ape_smear(qc, ns, alpha=ALPHA, device=DEVICE)
                    parts.append(op(b, qc))
                    del qc
                O = np.concatenate(parts, 0)
                C, Cerr, me, meerr = correlator(O, NLAG)
                for t in range(NLAG + 1):
                    rows.append(dict(
                        operator=name, beta=beta, L=L, ncfg=int(lk.shape[0]), nsmear=ns, tau=t,
                        C_over_C0=round(float(C[t]), 6), C_err=round(float(Cerr[t]), 6),
                        m_eff=(round(float(me[t]), 6) if t < NLAG and np.isfinite(me[t]) else ""),
                        m_eff_err=(round(float(meerr[t]), 6) if t < NLAG and np.isfinite(meerr[t]) else ""),
                        a_m_0pp_expected=round(float(am), 4) if am == am else ""))
                print(f"   ns={ns:2d} {name:15s} C/C0: "
                      + " ".join(f"{float(C[t]):7.4f}" for t in range(min(5, NLAG + 1))), flush=True)
                del O, parts
    table.write(DAT, rows, COLS)
    print("wrote", DAT)


if __name__ == "__main__":
    main()
