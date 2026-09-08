"""Figure for 8.7: the intensive margin across volume, read two ways.

Navy: the forward read m_hi(L) = rho'(1)(L) = e^{-Delta} from 8_7_dat_mhi_lscan.csv (connected DMD on
the action density, jackknife errors) across the SU(2) beta=2.30 volume tower, against the entropy-floor
ceiling 3^{-1/4} = e^{-kappa_0} = 0.76. Reflection positivity gives rho'(n) = rho'(1)^n, so one cut
rho'(1) < 1 carries the gap to every volume; the magnitude holds a plateau far below the ceiling for
L >= 12.

Gold: the variational read of Sec 8.7b on the same configurations, at the four volumes where raw links
exist, taken from 8_7_dat_gap_correlator.csv by the rule that section states -- the smallest m_eff
resolved to 25% anywhere in the (operator, smearing, tau) basis bounds the gap from above. The two agree
to <= 0.013 in m_hi across L = 12-20, at L=16 across different operators (the variational minimum is the
plaquette there, the forward read is the action density). They are not independent samples: same
configurations, and the same operator at L = 12 and 20. The overlay is skipped, and the figure still
draws, when the correlator artifact is absent.

Both edge points are annotated with their sigma. At L=8 the error bar runs outside [0, 1] and would
otherwise draw as a bare marker: the forward read is unresolved (+-1.08) where the variational read gives
0.220 +- 0.011, which is what marks that endpoint as the small-volume resolution edge. At L=32 the label
carries a sigma of a different kind, +-0.02, the tightest read in the tower.

Saves 8_7_fig_mhi_lscan.png."""
import os
import csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

here = os.path.dirname(__file__)
with open(os.path.join(here, '8_7_dat_mhi_lscan.csv')) as fh:
    rows = list(csv.DictReader(fh))


def variational_lscan(beta=2.30, tol=0.25):
    """m_hi from the Sec 8.7b variational read, at every volume where raw links exist.

    The same rule Sec 8.7b states: the smallest m_eff resolved to `tol` anywhere in the
    (operator, smearing, tau) basis is an upper bound on the gap, hence a lower bound on m_hi.
    Returns {} when the correlator artifact is absent, so this figure still draws without it."""
    path = os.path.join(here, '8_7_dat_gap_correlator.csv')
    if not os.path.exists(path):
        return {}
    with open(path) as fh:
        gr = list(csv.DictReader(fh))
    out = {}
    for r in gr:
        if abs(float(r['beta']) - beta) > 1e-9 or not r['m_eff'] or not r['m_eff_err']:
            continue
        v, e = float(r['m_eff']), float(r['m_eff_err'])
        if v <= 0 or e <= 0 or e / v > tol:
            continue
        k = int(r['L'])
        if k not in out or v < out[k][0]:
            out[k] = (v, e, r['operator'], int(r['nsmear']), int(r['tau']))
    return {k: (np.exp(-v), np.exp(-v) * e, op, ns, t) for k, (v, e, op, ns, t) in out.items()}


var = variational_lscan()

L = np.array([int(r['L']) for r in rows])
mhi = np.array([float(r['m_hi']) for r in rows])
err = np.array([float(r['m_hi_err']) for r in rows])
CEIL = 3 ** -0.25                                            # 0.7598 = e^{-kappa_0}
Lmax = int(L.max())

fig, ax = plt.subplots(figsize=(7.4, 4.3))

ax.axhspan(0, CEIL, color='#eef6ee', zorder=0)              # below-ceiling band: confined / intensive
ax.axhline(CEIL, color='crimson', lw=1.3, ls='--')
ax.text(Lmax + 0.3, CEIL + 0.013, r'entropy-floor ceiling  $3^{-1/4}=e^{-\kappa_0}=0.76$',
        fontsize=8.5, color='crimson', ha='right')

plat = (L >= 12) & (L <= 28)      # scaling window; L=8 (small-vol) and L=32 (large-vol) are resolution edges
edge = ~plat
plat_mean = float(np.mean(mhi[plat]))
ax.axhline(plat_mean, color='#2a7f2a', lw=1.0, ls=':')
ax.text(7.0, plat_mean + 0.018, rf'plateau $\approx {plat_mean:.2f}$', fontsize=8.5, color='#2a7f2a', ha='left')

ax.errorbar(L[plat], mhi[plat], yerr=err[plat], marker='o', ms=6, lw=1.3, capsize=3,
            color='#0b1f4d', label=r"$m_{\mathrm{hi}}(L)=\rho'(1)(L)$  (scaling window, $12\leq L\leq 28$)")
ax.errorbar(L[edge], mhi[edge], yerr=err[edge], marker='s', ms=6, lw=0, capsize=3,
            color='0.55', label=r'resolution edges ($L=8,\ 32$)')
# the edge error bars run outside [0, 1] and would otherwise draw as bare markers: state the sigma
for _x, _y, _e in zip(L[edge], mhi[edge], err[edge]):
    ax.annotate(rf'$\pm{_e:.2f}$', (_x, _y), textcoords='offset points', xytext=(0, -13),
                fontsize=7.5, color='0.45', ha='center')

if var:
    vL = np.array(sorted(var))
    vM = np.array([var[k][0] for k in vL])
    vE = np.array([var[k][1] for k in vL])
    ax.errorbar(vL, vM, yerr=vE, marker='D', ms=5.5, lw=1.2, ls='--', capsize=3, color='#b8860b',
                label=r'variational read (Sec 8.7b), same configs')

ax.set_xlabel(r'spatial extent  $L$   ($T=2L$,  $\beta=2.30$)')
ax.set_ylabel(r'dominant transfer magnitude  $m_{\mathrm{hi}}=e^{-\Delta}$')
ax.set_title(r'8.7  The intensive margin across volume: $m_{\mathrm{hi}}(L)$ below the entropy floor', fontsize=11)
ax.set_xlim(6.5, Lmax + 1.5)
ax.set_ylim(0, 1.0)
ax.set_xticks(sorted(int(x) for x in L))
ax.legend(fontsize=8.5, frameon=False, loc='lower right')
fig.text(0.5, 0.012,
         r"Reflection positivity gives $\rho'(n)=\rho'(1)^n$: one cut $\rho'(1)<1$ carries the gap to every volume; "
         r"for $12\leq L\leq 28$ the magnitude holds a plateau far below the ceiling — the intensive margin.",
         fontsize=7.4, color='0.35', ha='center')
fig.tight_layout(rect=[0, 0.045, 1, 1])
out = os.path.join(here, '8_7_fig_mhi_lscan.png')
fig.savefig(out, dpi=150)
print('wrote', out, '| L =', list(int(x) for x in L), '| m_hi =', [round(float(x), 3) for x in mhi],
      '| plateau(12<=L<=28) =', round(plat_mean, 3), '| ceiling =', round(CEIL, 3))
if var:
    print('  variational overlay:', [(k, round(float(var[k][0]), 3), var[k][2],
                                      'ns=%d' % var[k][3], 'tau=%d' % var[k][4]) for k in sorted(var)])
