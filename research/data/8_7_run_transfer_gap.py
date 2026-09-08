"""8.7 — the transfer gap on physical SU(2), reproducible from the archived links.

Reads the raw SU(2) links `su2_L16_b2.30.s*.npy` (configs_links_su2, this repo's dataset [D]), APE-smears the
spatial links, builds the zero-momentum 0++ operator O(t)=sum spatial-plaquette Re-trace, forms the CONNECTED
correlator C(tau)=<dO(t)dO(t+tau)> (ensemble vacuum-mean subtracted), and reads the Euclidean transfer operator's
gapped spectrum by the reflection-positive symmetric moment-pencil M = H0^{-1/2} H1 H0^{-1/2} (H0[i,j]=C(i+j),
H1[i,j]=C(i+j+1)) -- the physical instance of the moment-support bridge (sec 13): an ISOLATED transfer eigenvalue
lambda_1 = e^{-a m_0++} below the vacuum. Jackknife errors (32 bins). Writes 8_7_dat_transfer_gap.csv (correlator)
and 8_7_dat_transfer_pencil.csv (pencil). Device-flexible (CPU or CUDA via generator._Backend).

    CONFIGS=/path/to/entroptics-lattice python 8_7_run_transfer_gap.py
(or set CONFIGS once for the machine in the git-ignored local config file at the repository root)
"""
import os, sys, glob, math, csv
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'code'))
import numpy as np
import lattice_generator as G
from lattice_generator import _qmul, _qconj, _sax, _Backend
import entroptics_adapter as W          # the transfer-spectrum READ goes through the viewer (wrapper front door)
import store_path                       # the ONE place the ensemble store is located

SPATIAL = (0, 1, 2)
ALPHA = 0.5
BETA, L = 2.30, 16
SMEARS = (8, 16, 24, 32)
MOMENT_ORDERS = (2, 3, 4)      # pencil orders read from the correlator
# The reflection-positive pencil at order n is (n+1)x(n+1): H0 needs c_0..c_2n and the shifted H1
# needs c_1..c_(2n+1), so 2n+2 correlator values are required and NLAG is derived as 2n+1 from the
# highest order requested. connected_C computes each lag independently and normalises by c[0], so
# raising NLAG leaves every lower lag, and every lower moment order, exactly where it was.
NLAG, NBIN = 2 * max(MOMENT_ORDERS) + 1, 32

if NLAG + 1 < 2 * max(MOMENT_ORDERS) + 2:      # checked HERE, not after the ensemble is loaded
    raise SystemExit(
        f"8_7_run_transfer_gap: NLAG={NLAG} gives {NLAG + 1} correlator values, but moment order "
        f"n={max(MOMENT_ORDERS)} needs {2 * max(MOMENT_ORDERS) + 2}. Raise NLAG or lower the order."
    )
# Device resolution follows `_Backend`'s contract: None selects numpy, a device string selects
# torch. An unset DEV probes for CUDA and falls back to numpy; an explicit DEV=cuda is honoured and
# raises if the device is absent.


DEV = G.resolve_device(os.environ.get('DEV'))

# The store root comes from `store_path` -- `CONFIGS`, then the git-ignored local config file,
# then a refusal, with no path baked into this file. This one reads the raw link shards, which
# sit in `configs_links_su2` beneath the root, and accepts either form: the root, or the links
# directory directly, so one `CONFIGS=<store>` drives the whole tree.
_ROOT = store_path.store_root(required=False) or ''
# Prefer the named subdirectory when it EXISTS, rather than sniffing the root for shards: a
# single stray .npy left in the store root made the sniff match and the descent never happen,
# and the script then refused with 'no links under <root>' while the links sat one level down.
_LINKS = os.path.join(_ROOT, 'configs_links_su2')
ROOT = _LINKS if os.path.isdir(_LINKS) else _ROOT


# APE smearing and its spatial staple were defined here; they are gauge-field primitives, not
# figure code, and the string-tension certification needs the same kernel. Both now live in
# lattice_generator (G.ape_smear), verified bit-identical to the copy this replaced.


def operator_Ot(b, q):
    O = None
    for i in SPATIAL:
        for j in SPATIAL:
            if j <= i:
                continue
            Ui, Uj = q[..., i, :], q[..., j, :]
            plaq = _qmul(b, _qmul(b, Ui, b.roll(Uj, -1, _sax(i, 1))),
                        _qmul(b, _qconj(b, b.roll(Ui, -1, _sax(j, 1))), _qconj(b, Uj)))
            s = plaq[..., 0].sum(dim=(1, 2, 3)) if hasattr(plaq, 'dim') else plaq[..., 0].sum((1, 2, 3))
            O = s if O is None else O + s
    return O.detach().cpu().numpy() if hasattr(O, 'detach') else np.asarray(O)


def connected_C(O, nlag):
    d = O - O.mean()                                   # ensemble vacuum-mean (NOT per-config time-mean)
    c = np.array([np.mean(d * np.roll(d, -tau, axis=1)) for tau in range(nlag + 1)])
    return c / c[0]


# The transfer-spectrum read (reflection-positive moment pencil) and its jackknife error are the viewer's
# `W.hankel_spectrum` / `W.jackknife` -- domain-agnostic reads, relocated out of this script into the library.
# This script keeps only the DOMAIN signal construction above (gauge operator + ensemble-connected correlator).


def main():
    # The links are stored and loaded float32, so the backend is set to match. At its float64
    # default the staple accumulators are allocated in double, which upcasts the whole smearing and
    # doubles peak memory: 512 L=16 configs need 7.5 GB instead of 3.7 GB. Set before the backend is
    # constructed, since that is when it reads the knob.
    os.environ.setdefault('GEN_FP', '32')
    b = _Backend(DEV)
    fs = sorted(glob.glob(f'{ROOT}/su2_L{L}_b{BETA:.2f}.s*.npy'))
    if not fs:
        raise SystemExit(f"no su2_L{L}_b{BETA:.2f} links under {ROOT or '<no store configured>'}\n"
                         f"{store_path.hint()}")
    arr = np.concatenate([np.load(f) for f in fs], 0).astype('float32')
    # On a torch backend the array is moved to the device; on numpy it stays as it is. The branch
    # is on `b.torch`, the backend's own flag, so the data always lands where the reads will run.
    q0 = b.t.as_tensor(arr, dtype=b.f, device=b.dev) if b.torch else arr
    print(f"loaded {arr.shape[0]} configs from {len(fs)} shards {ROOT}", flush=True)
    corr_rows, pen_rows = [], []
    for ns in SMEARS:
        O = operator_Ot(b, G.ape_smear(q0, ns, alpha=ALPHA, device=DEV))
        C = connected_C(O, NLAG)
        Nc = O.shape[0]; d = O - O.mean(); bins = np.array_split(np.arange(Nc), NBIN)
        jkC = np.array([connected_C(O[np.setdiff1d(np.arange(Nc), bn)], NLAG) for bn in bins])
        errC = np.sqrt((NBIN - 1) * np.mean((jkC - jkC.mean(0)) ** 2, axis=0))
        for tau in range(NLAG + 1):
            corr_rows.append([ns, tau, round(float(C[tau]), 4), round(float(errC[tau]), 4)])
        for n in MOMENT_ORDERS:
            hs = W.hankel_spectrum(C, n)                       # viewer moment pencil (relocated read)
            l1, iso, psd = hs.leading, hs.isolation, hs.psd
            _, err = W.jackknife(O, lambda sub, n=n: W.hankel_spectrum(connected_C(sub, NLAG), n).leading, n_bins=NBIN)
            am = -math.log(l1) if 0 < l1 < 1 else float('nan')
            isor = round(iso, 1) if math.isfinite(iso) else float('nan')
            pen_rows.append([ns, n, round(l1, 4), round(err, 4), isor, round(psd, 3), round(am, 4)])
        print(f"APE {ns}: lambda1(n=3) = {pen_rows[-2][2]} +/- {pen_rows[-2][3]}", flush=True)
    here = os.path.dirname(__file__)
    T = int(O.shape[1])                                       # time extent of the last-smeared operator
    with open(os.path.join(here, '8_7_dat_transfer_gap.csv'), 'w', newline='') as fh:
        w = csv.writer(fh); w.writerow(['smearing', 'tau', 'C_over_C0', 'err']); w.writerows(corr_rows)
    with open(os.path.join(here, '8_7_dat_transfer_pencil.csv'), 'w', newline='') as fh:
        w = csv.writer(fh); w.writerow(['smearing', 'n_moment', 'lambda1', 'lambda1_err', 'isolation', 'H0_psd', 'a_m0pp']); w.writerows(pen_rows)
    with open(os.path.join(here, '8_7_dat_meta.csv'), 'w', newline='') as fh:            # geometry/count for the figure caption (not hand-typed)
        wm = csv.writer(fh); wm.writerow(['L', 'T', 'beta', 'nconfigs', 'smears', 'nlag', 'nbin'])
        wm.writerow([L, T, BETA, int(arr.shape[0]), '|'.join(map(str, SMEARS)), NLAG, NBIN])
    print(f"wrote 8_7_dat_transfer_gap.csv, 8_7_dat_transfer_pencil.csv, 8_7_dat_meta.csv ({arr.shape[0]} configs)", flush=True)


if __name__ == '__main__':
    main()
