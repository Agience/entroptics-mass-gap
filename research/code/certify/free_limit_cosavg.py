"""The weak-coupling limit of `cosAvgEven`, as a lattice sum. A SENSITIVITY CHECK, NOT A RESULT.

READ THIS FIRST. What is computed here is a MODEL of the beta -> infinity plaquette correlator, not
the free Yang-Mills one. It therefore cannot establish anything and it cannot refute anything
either: a model that disagrees with a hypothesis has refuted the model. Its only job is to say
whether the full calculation is worth doing and roughly where the answer sits. The full calculation
keeps the `F_{mu nu} = d_mu A_nu - d_nu A_mu` index structure, which this drops.

## What `cosAvgEven` is in the weak-coupling limit

`ApertureRoute.cosAvgEven a beta = sum_d p d * cos (theta d)` with `p d = rho(d)/sum rho` and
`theta d = 2 pi circLag(d)/T`, `T = a.1 + 1`. Since cosine is even and `circLag d = min d (T-d)`,

    cosAvgEven = sum_d rho(d) cos(2 pi d/T) / sum_d rho(d) = rhohat(1)/rhohat(0),

the first Matsubara mode of the zero-spatial-momentum plaquette correlator over its zero mode.

As beta -> infinity the Wilson measure concentrates on flat connections and the fluctuation field is
Gaussian. `wilsonDensity g = 1 - (1/N) Re tr g` is QUADRATIC in that field at leading order, so the
CONNECTED correlator of two plaquette densities is a product of two propagators -- a one-loop bubble.
Projected to zero spatial momentum and Fourier transformed in t, that is

    rhohat(n) = B(omega_n) = (1/V) sum_{k != 0, k != -q} 1 / ( khat^2 * (k+q)hat^2 ),
    q = (0,0,0,omega_n),  omega_n = 2 pi n / T,  khat^2 = 4 sum_mu sin^2(k_mu/2),

and `cosAvgEven -> B(omega_1)/B(0)`, a PURE NUMBER fixed by the lattice geometry alone. No coupling
appears in it, which is the whole point: if that number sits below the floor `3^(-1/4)` then no
amount of coupling saves a FIXED aperture at weak coupling.

The zero modes are dropped because the gauge propagator has none -- a constant gauge field is pure
gauge. That is a physical exclusion, not a regulator choice, and the sum is finite without it.

## WHICH ROW IS THE RELEVANT ONE -- and it is not the one I first assumed

`Complete.wilsonCorrAt N beta d = WilsonBridge.corrClay (N+1) beta d`, built on
`WilsonHypercubic.bd (d := 4) (n := N+1)`: a periodic FOUR-dimensional lattice of extent `N+1` in
EVERY direction. The aperture is not a temporal extent over a separate spatial box -- it is the whole
symmetric hypercube. So the table to read is the SYMMETRIC one, `L = T`, and only that one.

I had argued the hypothesis must fail at weak coupling because a fixed aperture with `beta -> inf`
means a shrinking physical box. On ELONGATED boxes this model agrees: at `L = 4`, `T = 32` the ratio
is 0.297, far below the floor. On SYMMETRIC boxes it does the opposite -- 0.872 at N=4 rising to
0.924 at N=16, above the floor throughout and INCREASING with refinement. Refining a symmetric box
keeps it symmetric, so the elongated intuition never applied. Recorded because the concern was mine
and it was wrong in the geometry that matters.
"""
import os

os.environ.setdefault("OMP_NUM_THREADS", "2")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "2")
os.environ.setdefault("MKL_NUM_THREADS", "2")

import numpy as np

FLOOR = 3.0 ** (-0.25)


def khat2(idx, dims):
    """khat^2 = 4 sum_mu sin^2(pi n_mu / L_mu) on the lattice Brillouin zone."""
    out = np.zeros(idx[0].shape)
    for n, L in zip(idx, dims):
        out = out + 4.0 * np.sin(np.pi * n / L) ** 2
    return out


def bubble(dims, n_t):
    """B(omega_n) with the external momentum along the LAST axis (time)."""
    grids = np.meshgrid(*[np.arange(L) for L in dims], indexing="ij")
    k2 = khat2(grids, dims)
    shifted = list(grids)
    shifted[-1] = (grids[-1] + n_t) % dims[-1]
    kq2 = khat2(shifted, dims)
    # CHOSEN: floating-point zero. The gauge propagator has NO zero mode -- a constant gauge
    # field is pure gauge -- so this excludes exactly the modes that are absent physically,
    # and the tolerance only distinguishes them from rounding. Not a regulator.
    good = (k2 > 1e-12) & (kq2 > 1e-12)
    return float((1.0 / (k2[good] * kq2[good])).sum() / np.prod(dims))


def self_test():
    """The probe must be able to return a value BELOW the floor, or it cannot detect failure.

    A one-dimensional-in-time lattice with a huge spatial box makes the zero mode dominate B(0)
    utterly while B(omega_1) stays finite, so the ratio must collapse towards zero. If this does not
    drop below the floor, the estimator is incapable of reporting a failure and nothing below it
    means anything.
    """
    r = bubble((2, 2, 2, 64), 1) / bubble((2, 2, 2, 64), 0)
    assert r < FLOOR, "estimator cannot produce a sub-floor value (got %.4f)" % r

    # The bubble is maximal at ZERO external momentum: Cauchy-Schwarz on the two propagator factors.
    # That much is analytic and is a real check.
    b0, b1, b2 = (bubble((4, 4, 4, 16), n) for n in (0, 1, 2))
    # DERIVED: Cauchy-Schwarz on the two propagator factors puts the bubble's maximum at zero
    # external momentum, and each term of the sum is positive. Both are analytic.
    assert b0 > b1 > 0 and b0 > b2 > 0, "B(0) must dominate (%g %g %g)" % (b0, b1, b2)

    # It is NOT monotone beyond that, and the reason is a lattice artifact this model cannot shed:
    # B(w2) = 0.0802 exceeds B(w1) = 0.0515 on a 4^3 x 16 box. Dropping the zero modes removes, at
    # external momentum n, the mode k_t = -n; so at EVEN n the mode k_t = -n/2 survives with BOTH
    # propagators near the infrared, while at odd n no such pairing exists. The alternation is the
    # exclusion's, not the physics'. It is also why B(0) here is not a trustworthy denominator, and
    # so why this file is a sensitivity check and not a result.
    assert b2 > b1, "the even/odd alternation recorded above has changed (%g vs %g)" % (b2, b1)

    # A FALSIFIED ASSUMPTION, kept because it is the interesting part. I expected the ratio to RISE
    # with the time extent, on the single-mass reasoning that cosAvg ~ m^2/(m^2 + (2 pi/T)^2) and so
    # a longer box makes the criterion easier. It FALLS: 0.7579 at T=8 against 0.2968 at T=32, on a
    # fixed L=4 box. The reasoning fails because the weak-coupling correlator has NO mass -- it is a
    # power law, m = 0 -- and at m = 0 that formula gives 0 for every T. So "a bigger aperture helps"
    # is a statement about a MASSIVE correlator and says nothing about the free end.
    a = bubble((4, 4, 4, 8), 1) / bubble((4, 4, 4, 8), 0)
    b = bubble((4, 4, 4, 32), 1) / bubble((4, 4, 4, 32), 0)
    assert b < a, "the T-dependence recorded above has changed (%.4f -> %.4f)" % (a, b)
    print("self-test: sub-floor reachable (%.4f); bubble falls in external momentum; "
          "ratio falls with T (%.4f -> %.4f)\n" % (r, a, b))


def main():
    self_test()
    print("MODEL ONLY -- scalar bubble, no F_{mu nu} index structure. Cannot refute the hypothesis.")
    print("floor 3^(-1/4) = %.7f\n" % FLOOR)
    print("  L    T    B(w1)/B(0)   vs floor")
    for L in (4, 6, 8):
        for T in (4, 6, 8, 12, 16, 24, 32, 48, 64):
            dims = (L, L, L, T)
            r = bubble(dims, 1) / bubble(dims, 0)
            print("  %-4d %-4d %10.6f   %s" % (L, T, r, "ABOVE" if r > FLOOR else "below"))
        print()

    print("Symmetric boxes (L = T), the shape a fixed physical box keeps under refinement:")
    for N in (4, 6, 8, 10, 12, 16):
        r = bubble((N, N, N, N), 1) / bubble((N, N, N, N), 0)
        print("  N=%-3d %10.6f   %s" % (N, r, "ABOVE" if r > FLOOR else "below"))


if __name__ == "__main__":
    main()
