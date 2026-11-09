"""Unit checks for `MassGap.FixedAperture`: the fine end inside a fixed physical aperture.

The aperture has fixed physical side L; the spacing a = L / N refines inside it (N lattice sites per
side). The Lean tools of `ApertureGap` bound the slice transfer kernel by its cross ratio:
`CrossRatio K t` means |K(x,y)K(x',y') - K(x,y')K(x',y)| <= t (K(x,y)K(x',y') + K(x,y')K(x',y)).
The least such t is tanh(D/2), D the Hilbert projective diameter
D = sup log [K(x,y)K(x',y') / (K(x,y')K(x',y))]. `crossRatio_iter` composes it: n steps of a
kernel with constant t give t^n.

1. 2D heat-kernel U(1) and SU(2), gauge-projected (the state of one time slice is its holonomy).
   The one-step kernel at spacing a is the holonomy heat kernel at time t = kappa L a; n steps are
   the same kernel at time kappa L (n a). So the kernel over a fixed physical slab tau = n a is the
   same at every zoom N: its cross-ratio constant is zoom-independent. The one-step constant t_1(N)
   tends to 1 as N grows, and the composed bound t_1^N over the same physical slab tends to 1: the
   one-step-and-compose route loses the uniformity the slab kernel has.
2. The existing sup/inf constant `apTheta` (`RectTransfer.kTmin`): 1 - apTheta <= 2 kTmin^2 with
   kTmin = exp(-beta (spMax + 2 tpMax)), spMax + 2 tpMax = 30 |TT| in 4D (|TT| = N^3 cross-section
   sites). On the one-loop SU(2) line at fixed L, N (1 - apTheta) -> 0 faster than any power: the
   slab bound apTheta^N -> 1 (`FixedAperture.apTheta_slab_tendsto_one`). The 2D Wilson analog
   (kTmin = exp(-4 beta N), beta = 4 / (g^2 a^2)) does the same.
3. 4D free photon (noncompact Gaussian model; the control that must fail (B)). The cross ratio of
   the slab kernel over tau = L on the lowest box mode (|p| = 2 pi / L), at per-link amplitude pi / 2,
   is beta pi^2 (N^3 / 2) sinh(eps) / sinh(N eps), cosh(eps) = 1 + 2 sin^2(pi / N): it grows like N^2.
   The projective diameter of the fixed-physical-slab kernel is extensive in the number of sites: the
   sup over configurations sees coherent O(1) link fluctuations over the whole box. This is numerical
   evidence, not a Lean statement. The periodic box gap itself (Euclidean transfer energy of the
   lowest momentum) is 2 asinh(sin(pi/N)) N / L -> 2 pi / L at every zoom ((A) holds at fixed L) and
   -> 0 as L grows at fixed spacing ((B) fails). Lean's `FixedAperture.gU1` is the same mode with the
   Hamiltonian dispersion (2/a) sin(pi a/L); the two agree to relative order (a/L)^2.
4. 2D SU(2) heat kernel: the box gap is 3 kappa L at every zoom ((A) holds with no loss) and grows
   with L ((B) holds). It is the energy of one unit of flux around the periodic box (a torelon), not a
   glueball; (A) and (B) do not tell the two apart, only the volume link does.

Boundary conditions: periodic throughout (Lean and Python).

Each section runs in under 10 seconds; the script asserts it. No Monte Carlo.
"""
import math
import time

import numpy as np

# CHOSEN: the grid of class angles. 160 interior points resolve the diameter to about 1 % at the
# smallest heat time below; the scaling, not the third digit, is what is read.
G = 160
# CHOSEN: the zooms read, N = L / a lattice sites per side.
NS = (4, 8, 16, 32, 64)
# CHOSEN: units kappa = 1, L = 1, slab tau = L. The model is exact at every choice.
KAPPA, L = 1.0, 1.0


# CHOSEN: M = 6 Poisson images per side; for |phi| <= 2 pi the first omitted image (|m| = 7) is at
# most e^{-(12 pi)^2 / (4 t)}, below double precision against the leading term at every t <= 1 used.
def log_theta(phi, t, M=6):
    """log of the U(1) heat kernel sum_n e^{-t n^2} e^{i n phi}, in the Poisson (positive) form."""
    m = np.arange(-M, M + 1)
    e = -((phi[..., None] + 2 * np.pi * m) ** 2) / (4 * t)
    mx = e.max(axis=-1)
    return 0.5 * math.log(math.pi / t) + mx + np.log(np.exp(e - mx[..., None]).sum(axis=-1))


def diameter(logk):
    """Hilbert projective diameter of a positive kernel given as log K on a grid."""
    # sup over (x, x', y, y') of logK(x,y) + logK(x',y') - logK(x,y') - logK(x',y).
    # For fixed (y, y') this is sup_x [f(x)] - inf_x [f(x)] with f(x) = logK(x,y) - logK(x,y').
    best = 0.0
    for j in range(logk.shape[1]):
        f = logk - logk[:, j:j + 1]
        best = max(best, float((f.max(axis=0) - f.min(axis=0)).max()))
    return best


def u1_logk(t):
    th = (np.arange(G) + 0.5) * 2 * np.pi / G - np.pi
    return log_theta(th[:, None] - th[None, :], t)


def su2_logk(t):
    # Class kernel sum_{n>=1} chi_n(x) chi_n(y) e^{-t (n^2-1)} = e^t [th(x-y) - th(x+y)] / (4 sin x sin y);
    # the diagonal factors drop out of the cross ratio.
    th = (np.arange(G) + 0.5) * np.pi / G
    A = log_theta(th[:, None] - th[None, :], t)
    B = log_theta(th[:, None] + th[None, :], t)
    return A + np.log(-np.expm1(B - A))


def section1():
    t0 = time.time()
    print("1. 2D heat kernel, gauge-projected: one-step vs fixed-slab cross-ratio constants (tau = L)")
    for name, lk, e1 in (("U(1)", u1_logk, 1.0), ("SU(2)", su2_logk, 3.0)):
        Dslab = diameter(lk(KAPPA * L * L))
        print(f"   {name}: slab kernel D = {Dslab:.4f}, t_slab = tanh(D/2) = {math.tanh(Dslab / 2):.6f}"
              f" at every N; eigen ratio e^(-{e1:g} kappa L^2) = {math.exp(-e1 * KAPPA * L * L):.6f}")
        prev = None
        for N in NS:
            a = L / N
            D1 = diameter(lk(KAPPA * L * a))
            q = math.exp(-D1)
            log1mt = math.log(2.0) - D1 - math.log1p(q)        # log(1 - t_1), 1 - tanh(D/2) = 2/(e^D + 1)
            logcomp = N * math.log1p(-2 * q / (1 + q))         # log(t_1^N)
            gap_slab = -math.expm1(logcomp)                    # 1 - t_1^N: what the composed bound leaves
            print(f"     N={N:3d}: one-step D = {D1:9.3f}, log10(1 - t_1) = {log1mt / math.log(10):9.3f},"
                  # DERIVED: the guard against log10 of zero when 1 - t_1^N underflows, not a magnitude.
                  f" log10(1 - t_1^N) = {math.log10(gap_slab) if gap_slab > 0 else float('-inf'):9.3f}"
                  f"  (slab: log10(1 - t_slab) = {math.log10(1 - math.tanh(Dslab / 2)):.3f})")
            if prev is not None:
                assert D1 > prev
            prev = D1
        # CHOSEN: 0.999 as "the composed bound is lost"; at N = 64 it reads 1 - 10^-129 or closer to 1,
        # so any cut short of 1 reads the same.
        assert math.exp(logcomp) > 0.999
    dt = time.time() - t0
    print(f"   ({dt:.2f} s)")
    # CHOSEN: the 10 s run-time budget per section stated in the module docstring; it sees no number.
    assert dt < 10


# CHOSEN: g^2(L) = 2 at the aperture scale, an O(1) coupling where one-loop running starts; the
# faster-than-any-power fall of N (1 - apTheta) does not depend on it.
def onel_beta(N, gL2=2.0):
    """SU(2) one-loop beta = 4 / g^2(a), 1/g^2(a) = 1/g^2(L) + 2 b0 log(L/a), b0 = 22 / (48 pi^2)."""
    b0 = 22.0 / (48.0 * math.pi ** 2)
    return 4.0 * (1.0 / gL2 + 2.0 * b0 * math.log(N))


def section2():
    t0 = time.time()
    print("2. existing constant apTheta: 1 - apTheta <= 2 kTmin^2; slab of N steps")
    for N in NS:
        b = onel_beta(N)
        lk4 = -b * 30.0 * N ** 3                 # log kTmin, 4D: spMax + 2 tpMax = 30 |TT|, |TT| = N^3
        b2 = 4.0 * N * N / (1.0 * L * L)         # 2D Wilson: beta = 4 / (g^2 a^2), g = 1
        lk2 = -4.0 * b2 * N                      # 2D analog: kTmin = exp(-4 beta N)
        l4 = (math.log(2 * N) + 2 * lk4) / math.log(10)
        l2 = (math.log(2 * N) + 2 * lk2) / math.log(10)
        print(f"   N={N:3d}: 4D beta={b:.3f} log10 N(1-apTheta) <= {l4:14.1f};"
              f"  2D analog log10 N(1-theta) <= {l2:12.1f}")
        assert l4 < -10 and l2 < -10
    dt = time.time() - t0
    print(f"   ({dt:.2f} s)")
    # CHOSEN: the 10 s run-time budget per section stated in the module docstring; it sees no number.
    assert dt < 10


def section3():
    t0 = time.time()
    print("3. 4D free photon (Gaussian model, beta = 1): slab cross ratio on the lowest box mode, tau = L")
    beta = 1.0
    prev = None
    for N in NS:
        eps = math.acosh(1 + 2 * math.sin(math.pi / N) ** 2)    # lattice energy of |p| = 2 sin(pi/N)
        cr = beta * math.pi ** 2 * (N ** 3 / 2) * math.sinh(eps) / math.sinh(N * eps)
        gapL = eps * N / L                                       # box gap in units of 1/L
        print(f"   N={N:3d}: log cross ratio >= {cr:10.2f} (/N^2 = {cr / N ** 2:.4f}),"
              f" box gap * L = {gapL:.4f} (2 pi = {2 * math.pi:.4f})")
        if prev is not None:
            assert cr > prev
        prev = cr
    lim = beta * math.pi ** 3 / math.sinh(2 * math.pi)
    print(f"   cross ratio / N^2 -> beta pi^3 / sinh(2 pi) = {lim:.4f}")
    assert abs(cr / NS[-1] ** 2 - lim) < 0.05 * lim
    dt = time.time() - t0
    print(f"   ({dt:.2f} s)")
    # CHOSEN: the 10 s run-time budget per section stated in the module docstring; it sees no number.
    assert dt < 10


def section4():
    print("4. box gaps in units of 1/L0 (L0 = 1) as L grows: U(1) photon 2 pi/L -> 0; 2D SU(2) 3 kappa L grows")
    for Lb in (1.0, 2.0, 4.0, 8.0, 16.0):
        print(f"   L={Lb:5.1f}: photon {2 * math.pi / Lb:8.4f}   2D SU(2) {3 * KAPPA * Lb:8.4f}")


if __name__ == "__main__":
    section1()
    section2()
    section3()
    section4()
