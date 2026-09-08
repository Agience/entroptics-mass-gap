"""Figure for 8.7: the transfer gap on physical SU(2). Reads 8_7_dat_transfer_gap.csv,
8_7_dat_transfer_pencil.csv and 8_7_dat_meta.csv, plots (a) the connected 0++ correlator with jackknife
errors and (b) the reflection-positive moment-pencil transfer eigenvalue lambda_1 across EVERY moment
order n in {2,3,4} vs smearing -- the moment-order systematic is SHOWN, not hidden -- against the vacuum
(1) and the entropy-floor ceiling 3^{-1/4}. Saves 8_7_fig_transfer_gap.png."""
import os, csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

here = os.path.dirname(__file__)


def load(name):
    with open(os.path.join(here, name)) as fh:
        return list(csv.DictReader(fh))


corr = load('8_7_dat_transfer_gap.csv')
pen = load('8_7_dat_transfer_pencil.csv')
meta = load('8_7_dat_meta.csv')[0] if os.path.exists(os.path.join(here, '8_7_dat_meta.csv')) else \
    {'L': '16', 'T': '28', 'beta': '2.30', 'nconfigs': '?'}
smears = sorted({int(r['smearing']) for r in corr})
colors = plt.cm.viridis(np.linspace(0.15, 0.85, len(smears)))

fig, (axA, axB) = plt.subplots(1, 2, figsize=(10, 4.0))

# (a) connected correlator C(tau)/C(0), tau>=1
for s, c in zip(smears, colors):
    rows = [r for r in corr if int(r['smearing']) == s and int(r['tau']) >= 1]
    t = [int(r['tau']) for r in rows]
    C = [float(r['C_over_C0']) for r in rows]
    e = [float(r['err']) for r in rows]
    axA.errorbar(t, C, yerr=e, marker='o', ms=4, lw=1.2, capsize=2, color=c, label=f'APE {s}')
axA.axhline(0, color='0.6', lw=0.8, ls=':')
axA.set_xlabel(r'$\tau$ (lattice)'); axA.set_ylabel(r'$C(\tau)/C(0)$')
axA.set_title('(a) confined SU(2) 0++ connected correlator', fontsize=10)
axA.legend(fontsize=8, frameon=False)

# (b) pencil transfer eigenvalue lambda_1 for every moment order n in {2,3,4} -- the systematic is SHOWN,
#     with TRUE error bars (any that run off the axes are labelled, never silently clipped).
axB.axhline(1.0, color='0.3', lw=1.0, ls='--')
axB.text(34.5, 1.02, r'vacuum $\lambda=1$', fontsize=8, color='0.3', ha='right')
thr = 3 ** -0.25
axB.axhline(thr, color='crimson', lw=1.0, ls='--')
axB.text(34.5, thr + 0.015, r'entropy-floor ceiling $3^{-1/4}=0.76$', fontsize=8, color='crimson', ha='right')
YMAX = 1.28
nmarks = {2: ('o', '#4c72b0'), 3: ('s', '#0b1f4d'), 4: ('^', '#a83232')}
for nn, (mk, col) in nmarks.items():
    rows = sorted((r for r in pen if int(r['n_moment']) == nn), key=lambda r: int(r['smearing']))
    xs = np.array([int(r['smearing']) for r in rows], float) + (nn - 3) * 0.45   # x-jitter so the n don't overlap
    l1 = np.array([float(r['lambda1']) for r in rows])
    er = np.array([float(r['lambda1_err']) for r in rows])
    lo = np.minimum(er, l1)                                    # clamp the DRAWN bar to the axes...
    hi = np.minimum(er, YMAX - l1)
    axB.errorbar(xs, l1, yerr=[lo, hi], marker=mk, ms=5, lw=0, elinewidth=1.0, capsize=2, color=col, label=f'$n={nn}$')
    for x, y, e in zip(xs, l1, er):                            # ...and LABEL any bar that runs off the top
        if y + e > YMAX:
            axB.text(x, YMAX - 0.01, f'$\\pm${e:.1f}', fontsize=6, color=col, ha='center', va='top', rotation=90)
axB.set_xlabel('APE smearing sweeps'); axB.set_ylabel(r'transfer eigenvalue $\lambda_1=e^{-a m_{0^{++}}}$')
axB.set_title('(b) transfer gap across moment order $n$ (RP pencil)', fontsize=10)
axB.set_ylim(0.0, YMAX); axB.set_xlim(4, 36)
axB.legend(fontsize=8, frameon=False, loc='upper left', ncol=3, title='moment order $n$')

L, T, beta, nc = meta['L'], meta['T'], meta['beta'], meta['nconfigs']
fig.suptitle(f'8.7  The transfer gap on physical SU(2)  ($L={L}^3\\times{T}$, $\\beta={beta}$, {nc} configs)', fontsize=11)
fig.text(0.5, 0.005, 'Spread across $n$ and the large bars at heavy smearing are the moment-order systematic: '
                     r'the precise $a\,m_{0^{++}}$ needs the variational GEVP; the RP-pencil $H_0$ is PSD only as $a\to0$.',
         fontsize=7.2, color='0.35', ha='center')
fig.tight_layout(rect=[0, 0.04, 1, 0.96])
out = os.path.join(here, '8_7_fig_transfer_gap.png')
fig.savefig(out, dpi=150)
print('wrote', out)
