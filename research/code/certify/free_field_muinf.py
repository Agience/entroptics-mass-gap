"""The weak-coupling (beta -> infinity) tension mu_inf(L), by exact Wick contraction -- no Monte Carlo.

Asymptotic freedom makes the beta -> infinity gauge field free, so the action density is `:F^2:` of a
Gaussian field and the confinement read's whitened spatial correlation is the CIRCULANT built from
its structure factor (PAPER Sec 8.6). The connected correlation is the Wick double-contraction

    C_s(r) = 2 sum_{a,b} <F_a(0) F_b(r)>^2 ,     a, b over the six F_{mu nu} components,

with <F F> built from the free lattice propagator on an L^4 torus (Feynman gauge, zero mode
dropped, forward-difference field strength). Whitening gives rho(d) = C_s(d)/C_s(0) along a lattice
axis; the structure factor is lambda_k = sum_d rho(d) cos(2 pi k d / L) over the full ring, and the
tension is the top-two gap

    mu_inf(L) = log(lambda_0 / lambda_1) .

Every constant Sec 8.6 quotes for the weak end comes from this table and nothing else:

  * mu_inf(8) = 0.0326, the below-floor value the Lean `FreeField.muInf_lt_floor` carries;
  * mu_inf(L) ~ 2.1/L^2 -> 0, so the tension vanishes into the continuum;
  * M_2 = 0.111, whose 2 pi^2 M_2 = 2.19 is the small-k coefficient the crossover read is held against;
  * the lattice axes identical to 4e-17 and lambda_2 a degenerate doublet to 3e-16 -- the SO(4)
    multiplet (A2), exact rather than fitted.

The value is N-independent: the free field is N decoupled copies, so the colour factor cancels in
the whitening. With the ensemble store configured the script also reads the measured top-two gap
on the released ensembles at the same L, for the comparison Sec 8.6 draws; without it the exact
half still runs, which is the half the paper's constants come from.

Deterministic: no RNG, no fit, no sampling anywhere in the exact half.
"""
import csv
import glob
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code
import console  # noqa: F401  -- UTF-8 stdout
import store_path

# The six independent field-strength components on a four-dimensional lattice.
PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

LS = (4, 6, 8, 10, 12, 16, 20, 24, 32)
NCAP = 256
HOPS = ["configs_densebeta", "configs_phase1", "configs_betasweep", "configs_ladder",
        "configs_paper83"]
# The released ensembles this is compared against, at the L where the free field is quoted.
MEASURED = (("su2", 8, [0.5, 0.8, 1.0, 1.2, 1.4, 1.6, 1.8, 2.0, 2.2, 2.3, 2.4, 2.6, 2.8]),
            ("su3", 6, [5.0, 5.25, 5.5, 5.75, 6.0, 6.25, 6.5, 6.75, 7.0]),
            ("su3", 8, [5.5, 5.7, 5.9, 6.0, 6.1, 6.3]))

_DATA = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "data")
# Two artifacts, because they are two kinds of thing: the exact table names no ensemble and is
# reproducible anywhere, while the comparison names the released ones it read and is checkable
# against the store.
OUT_EXACT = os.path.join(_DATA, "8_6_dat_free_field_muinf.csv")
OUT_MEASURED = os.path.join(_DATA, "8_6_dat_free_field_measured.csv")


def _f_correlator(L):
    """<F_a(0) F_b(r)> for every separation r on the L^4 torus, one array per component pair.

    In momentum space the forward-difference field strength is
    F_{mu nu}(k) = p_mu A_nu - p_nu A_mu with p_mu = e^{i k_mu} - 1, and the Feynman-gauge
    propagator is delta_{alpha beta} / khat^2 with khat^2 = sum_mu |p_mu|^2. Contracting gives the
    bracket below; the inverse transform carries it to position space.
    """
    k = 2.0 * np.pi * np.arange(L) / L
    P = []
    for mu in range(4):
        shape = [1, 1, 1, 1]
        shape[mu] = L
        P.append((np.exp(1j * k) - 1.0).reshape(shape))
    khat2 = np.broadcast_to(sum(np.abs(P[mu]) ** 2 for mu in range(4)), (L,) * 4).copy()
    khat2[0, 0, 0, 0] = np.inf                       # the zero mode carries no fluctuation

    def delta(x, y):
        return 1.0 if x == y else 0.0

    M = {}
    for (mu, nu) in PAIRS:
        for (rho, sig) in PAIRS:
            T = (P[mu] * np.conj(P[rho]) * delta(nu, sig)
                 - P[mu] * np.conj(P[sig]) * delta(nu, rho)
                 - P[nu] * np.conj(P[rho]) * delta(mu, sig)
                 + P[nu] * np.conj(P[sig]) * delta(mu, rho))
            M[(mu, nu), (rho, sig)] = np.fft.ifftn(np.broadcast_to(T, (L,) * 4) / khat2)
    return M


def free_field(L):
    """The exact free-field row at L: the tension, its scaling, the moment, and the two exactness checks."""
    M = _f_correlator(L)
    imag = max(float(np.abs(v.imag).max()) for v in M.values())   # the correlator is real
    C = sum(2.0 * v.real ** 2 for v in M.values())

    axes = []
    for mu in range(4):
        idx = [np.zeros(L, dtype=int) for _ in range(4)]
        idx[mu] = np.arange(L)
        axes.append(C[tuple(idx)] / C[(0,) * 4])
    axes = np.array(axes)
    axis_spread = float(np.abs(axes - axes[0]).max())

    rho = axes[0]
    d = np.arange(L)
    lam = np.array([float((rho * np.cos(2 * np.pi * kk * d / L)).sum()) for kk in range(L)])
    return dict(L=L,
                mu_inf=float(np.log(lam[0] / lam[1])),
                mu_inf_L2=float(np.log(lam[0] / lam[1])) * L * L,
                lambda_0=lam[0], lambda_1=lam[1],
                doublet_split=float(abs(lam[1] - lam[L - 1])),
                axis_spread=axis_spread, max_imag=imag,
                M2=float((rho * np.minimum(d, L - d) ** 2).sum() / rho.sum()))


def _profiles(arr, maxlag):
    """The canonical direct-lag whitened profile of `ym_crossover_confinement_of_grid`, at this L."""
    a = arr - arr.mean()
    P = np.zeros((arr.shape[0], maxlag + 1))
    P[:, 0] = (a * a).mean(axis=(1, 2, 3, 4))
    for ax in (1, 2, 3):
        for lag in range(1, maxlag + 1):
            P[:, lag] += (a * np.roll(a, -lag, axis=ax)).mean(axis=(1, 2, 3, 4))
    P[:, 1:] /= 3.0
    return P


def measured(base, group, L, beta):
    """log(S(0)/S(2 pi / L)) on a released ensemble, the same functional as the exact half."""
    files = []
    for hop in HOPS:
        files += glob.glob(f"{base}/{hop}/{group}_L{L}_b{beta:.2f}.s*.npy")
    if not files:
        return None
    arr = np.concatenate([np.load(f) for f in files], 0)[:NCAP]
    rho_half = _profiles(arr, L // 2).mean(0)
    rho_half = rho_half / rho_half[0]
    ring = np.array([rho_half[lag] if lag <= L // 2 else rho_half[L - lag] for lag in range(L)])
    d = np.arange(L)
    lam0 = float(ring.sum())
    lam1 = float((ring * np.cos(2 * np.pi * d / L)).sum())
    return float(np.log(lam0 / lam1)), int(arr.shape[0])


def main():
    kappa0 = 0.25 * np.log(3.0)
    exact_rows = []

    print("== exact free field, mu_inf(L) = log(lambda_0/lambda_1) on the L^4 Wick circulant ==")
    print(f"{'L':>4} {'mu_inf':>11} {'mu*L^2':>9} {'M2':>8} {'axis spread':>13} "
          f"{'doublet split':>15} {'max Im':>10}")
    for L in LS:
        r = free_field(L)
        exact_rows.append(dict(L=L, mu_inf=f"{r['mu_inf']:.6f}", mu_inf_L2=f"{r['mu_inf_L2']:.4f}",
                               M2=f"{r['M2']:.6f}", lambda_0=f"{r['lambda_0']:.6f}",
                               lambda_1=f"{r['lambda_1']:.6f}",
                               axis_spread=f"{r['axis_spread']:.3e}",
                               doublet_split=f"{r['doublet_split']:.3e}",
                               max_imag=f"{r['max_imag']:.3e}"))
        print(f"{L:>4} {r['mu_inf']:>11.6f} {r['mu_inf_L2']:>9.4f} {r['M2']:>8.4f} "
              f"{r['axis_spread']:>13.2e} {r['doublet_split']:>15.2e} {r['max_imag']:>10.2e}")
    exact = {int(r["L"]): float(r["mu_inf"]) for r in exact_rows}
    print(f"\n  mu_inf(8) = {exact[8]:.4f} < kappa_0 = {kappa0:.4f}   "
          f"(the Lean `FreeField.muInf_lt_floor` value)")
    print(f"  mu_inf(L)*L^2 -> {exact_rows[-1]['mu_inf_L2']}, so mu_inf(L) -> 0: the tension vanishes.")

    with open(OUT_EXACT, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=["L", "mu_inf", "mu_inf_L2", "M2", "lambda_0",
                                           "lambda_1", "axis_spread", "doublet_split", "max_imag"])
        w.writeheader()
        w.writerows(exact_rows)
    print(f"\nwrote {OUT_EXACT}")

    base = store_path.store_root(required=False)
    if not base:
        # The exact half is the half the paper's constants come from and it has already been
        # written. Refusing here would leave the committed comparison in place, unchanged, which
        # is the correct outcome on a machine with no store.
        print("\n(no ensemble store configured: the measured comparison is skipped and its "
              "committed artifact left as it is)\n" + store_path.hint())
        return

    print("\n== measured top-two gap on the released ensembles, same functional ==")
    print(f"{'group':>6} {'L':>3} {'beta':>6} {'n':>5} {'mu':>10} {'/mu_inf(L)':>11} "
          f"{'/kappa_0':>9}")
    meas_rows = []
    for group, L, betas in MEASURED:
        for beta in betas:
            got = measured(base, group, L, beta)
            if got is None:
                continue
            mu, n = got
            meas_rows.append(dict(group=group, L=L, beta=f"{beta:.2f}", nconfigs=n,
                                  mu=f"{mu:.6f}", mu_over_muinf=f"{mu / exact[L]:.3f}",
                                  mu_over_kappa0=f"{mu / kappa0:.3f}"))
            print(f"{group:>6} {L:>3} {beta:>6.2f} {n:>5} {mu:>10.6f} "
                  f"{mu / exact[L]:>11.3f} {mu / kappa0:>9.3f}")

    if not meas_rows:
        raise SystemExit(
            f"{__file__}: the store at {base} matched none of the released ensembles this "
            f"comparison reads. Every row comes from them, so there is nothing to write, and "
            f"writing the header alone would replace the committed comparison with an empty one "
            f"and still exit 0.\n{store_path.hint()}")

    biggest = max(float(r["mu"]) for r in meas_rows)
    print(f"\n  every released coupling sits under the floor: max mu = {biggest:.4f}, "
          f"a factor {kappa0 / biggest:.2f} below kappa_0 = {kappa0:.4f}.")

    with open(OUT_MEASURED, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=["group", "L", "beta", "nconfigs", "mu",
                                           "mu_over_muinf", "mu_over_kappa0"])
        w.writeheader()
        w.writerows(meas_rows)
    print(f"wrote {OUT_MEASURED}")


if __name__ == "__main__":
    main()
