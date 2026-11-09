"""Numerical checks for `MassGap/CondGap.lean`: the conditional UV gap, input (i) of `LayerRate`.

No Monte Carlo. Everything is exact (Bessel functions, character expansion) or a deterministic
discretisation whose error is shown against an exact value.

Part A, 2D, the conditional per-step transfer of the new modes given a spatial block field.
  Temporal gauge, one doubled spatial link (sites 0, 1, 2), coarse link V = U_0 U_1 at every time.
  On the fibre {U_0 U_1 = V} the fine slice is (X, X^{-1} V); with the block field equal at t, t+1
  the one-step kernel is w(X Y^{-1}) w(X^{-1} Y) = w(X Y^{-1})^2, a convolution by w^2, w the
  plaquette weight. Its L2 rate is the largest nontrivial character ratio:
      U(1):  I_1(2b)/I_0(2b),      SU(2):  I_2(2b)/I_1(2b),
  with w = exp(b cos theta) (Wilson action b (1 - Re tr U / N)). Checked against a direct
  diagonalisation (U(1), Z_n discretisation) and a direct quadrature (SU(2) class functions).
  These new modes are gauge-variant (the residual gauge transformation at the middle site moves X
  transitively on the fibre), so the gauge-invariant new-mode space is {constants}: rate 0.

Part B, 2D, the fibre Poincare constant of the block fibre (which tool covers which regime).
  U(1): two plaquettes with fixed sum theta_V: the fibre is a circle with von Mises density,
  kappa = 2 b cos(theta_V/2). SU(2): fibre {P1 P2 = V}, density exp(kappa cos gamma) on the unit S^3,
  kappa = 2 b cos(alpha/2), tr V = 2 cos alpha. Poincare constant of the diffusion
  (Laplace-Beltrami minus grad V) computed by finite differences in the Schrodinger form, checked at
  kappa = 0 (circle: 1, unit S^3: 3). Bakry-Emery: Ric + min Hess = 0 - kappa (circle),
  2 - kappa (unit S^3).

Part C, 4D free (Gaussian) limit.
  C1: the lowest transfer exponent of the Fourier new layer (some |p_i| >= pi/2) on N^3,
      cosh E = 1 + sum 4 sin^2(p_j/2): E_min = arccosh 2 when 4 | N.
  C2: the conditional Gaussian process of the fine field given the 2^3 spatial block averages at
      every time: its lag-one canonical correlation (the per-step maximal correlation of the new
      modes in the conditional measure, Gaussian: Lancaster), c = -log rho, against arccosh 2.

Run: python research/code/cond_gap_checks.py
"""
from __future__ import annotations

import time

import numpy as np
from entroptics_adapter import matrix_pencil
from scipy.linalg import eigh_tridiagonal
from scipy.special import ive

T0 = time.time()
ARCCOSH2 = float(np.arccosh(2.0))


def header(s):
    print()
    print(s)
    print("-" * len(s))


# ---------------------------------------------------------------- Part A
header("A. 2D gauge-variant new mode (temporal-gauge midpoint), conditional per-step rate")


def u1_rate(b):
    return ive(1, 2 * b) / ive(0, 2 * b)


def su2_rate(b):
    return ive(2, 2 * b) / ive(1, 2 * b)


# cross-check U(1): Z_n discretisation of the kernel exp(2b cos(x - y)), normalised rows
# CHOSEN: Z_512; the Z_n eigenvalue matches the Bessel ratio to round-off once n is well above the
# kernel width at b = 32, and the dense diagonalisation stays well under a second.
n = 512
x = 2 * np.pi * np.arange(n) / n
for b in (0.5, 4.0, 32.0):
    K = np.exp(2 * b * (np.cos(x[:, None] - x[None, :]) - 1.0))
    K /= K.sum(axis=1, keepdims=True)
    # the one-step kernel against the uniform state (orthonormal point basis up to 1/n): Gram identity
    ev = np.sort(np.abs(matrix_pencil(np.eye(n), K).evals))[::-1]
    # CHOSEN: agreement tolerance; the discretisation error is at round-off (about 1e-15), so any
    # value from 1e-13 to well below the rates themselves reads the same.
    assert abs(ev[1] - u1_rate(b)) < 1e-9, (b, ev[1], u1_rate(b))
# cross-check SU(2): class-function quadrature, Haar weight (2/pi) sin^2 theta
th = np.linspace(0, np.pi, 200001)
for b in (0.5, 4.0, 32.0):
    wgt = np.exp(2 * b * (np.cos(th) - 1)) * np.sin(th) ** 2
    lam = np.trapezoid(wgt * np.cos(th), th) / np.trapezoid(wgt, th)  # chi_{1/2}/2 = cos theta
    # CHOSEN: quadrature tolerance on 200001 trapezoid nodes; the error is about 1e-16 on this smooth
    # periodic integrand, so any value well below the rates reads the same.
    assert abs(lam - su2_rate(b)) < 1e-7, (b, lam, su2_rate(b))
print("cross-checks: U(1) Z_512 kernel and SU(2) quadrature agree with the Bessel ratios")
print(f"{'beta':>8} {'U(1) gap':>12} {'beta*gap':>9} {'SU(2) gap':>12} {'beta*gap':>9}")
rowsA = []
for b in (0.5, 1, 2, 4, 8, 16, 32, 64, 128, 256):
    gu, gs = -np.log(u1_rate(b)), -np.log(su2_rate(b))
    rowsA.append((b, gu, gs))
    print(f"{b:8.1f} {gu:12.5f} {b*gu:9.4f} {gs:12.5f} {b*gs:9.4f}")
# DERIVED: 0.25 and 0.75 are the limits beta*gap -> 1/4 (U(1)) and 3/4 (SU(2)) of the Bessel ratios.
# CHOSEN: bands 2e-3 and 5e-3 above the O(1/beta) remainder at beta = 256 (read 2.4e-4 and 7.3e-4).
assert abs(256 * rowsA[-1][1] - 0.25) < 2e-3 and abs(256 * rowsA[-1][2] - 0.75) < 5e-3
print("the gap tends to 0 like 1/(4 beta) (U(1)), 3/(4 beta) (SU(2)): NOT uniform in beta.")
# U(1) with a block field that changes by d between the slices: kappa_eff = 2 b cos(d/2)
d = np.linspace(0, np.pi, 7)
print("U(1), beta = 16, block-field step d:", " ".join(
    f"d={di:.2f}:{-np.log(ive(1, 2*16*np.cos(di/2)) / ive(0, 2*16*np.cos(di/2)) + 1e-300):.4f}"
    for di in d[:-1]), "| d=pi: rate 0")
print("gauge-invariant new modes on the fibre: the middle-site gauge transformation X -> X g^{-1}")
print("is transitive on {U_0 U_1 = V}, so the invariant functions are constants: W = {0}, rate 0")
print("at every beta (U(1) and SU(2), open line or circle).")

# ---------------------------------------------------------------- Part B
header("B. 2D fibre Poincare constant: Bakry-Emery bound versus the exact constant")


def tri_eigs(diag, off, k):
    return eigh_tridiagonal(diag, off, select="i", select_range=(0, k - 1))[0]


# CHOSEN: 4000 grid points; the tridiagonal solve is cheap, and the grid resolves the Gaussian well of
# width kappa^-1/2 up to kappa = 1024 (the ratio check below reads 0.9994).
def poincare_circle(kappa, n=4000):
    """Poincare constant of von Mises(kappa) on the circle: second eigenvalue of
    -u'' + (kappa^2 sin^2/4 - kappa cos/2) u, periodic (ground state 0)."""
    s = -np.pi + 2 * np.pi * (np.arange(n) + 0.5) / n
    h = 2 * np.pi / n
    W = kappa ** 2 * np.sin(s) ** 2 / 4 - kappa * np.cos(s) / 2
    # periodic Laplacian: dense is too slow at n=4000; use Dirichlet at s = +-pi on a doubled check
    # for small kappa we use the exact Fourier answer instead (below), so Dirichlet is exact enough
    # where the density at s = pi is below 1e-12 relative.
    diag = 2 / h ** 2 + W
    off = -np.ones(n - 1) / h ** 2
    ev = tri_eigs(diag, off, 2)
    return ev[1] - ev[0]


# CHOSEN: 800 grid points for the dense periodic operator; dense cost grows as n^3, and at kappa = 0 it
# reproduces the exact constant 1 to 5e-6.
def poincare_circle_fourier(kappa, n=800):
    """Moderate kappa: the same Schrodinger operator with the periodic finite-difference Laplacian
    (dense), exact boundary condition; used where the density at s = pi is not negligible."""
    s = -np.pi + 2 * np.pi * (np.arange(n) + 0.5) / n
    h = 2 * np.pi / n
    W = kappa ** 2 * np.sin(s) ** 2 / 4 - kappa * np.cos(s) / 2
    H = np.diag(2 / h ** 2 + W) - np.diag(np.ones(n - 1), 1) / h ** 2 \
        - np.diag(np.ones(n - 1), -1) / h ** 2
    H[0, -1] = H[-1, 0] = -1 / h ** 2
    # NOT A READ: diagonalises the defined finite-difference Schrodinger operator of the fibre diffusion (a generator, not a two-time correlator pair), checked against the exact kappa = 0 value; no measured field enters
    ev = np.linalg.eigvalsh(H)
    return ev[1] - ev[0]


# CHOSEN: 6000 radial grid points (tridiagonal, cheap); at kappa = 0 it reproduces the exact constant 3
# to 3e-7.
def poincare_s3(kappa, n=6000):
    """Poincare constant of exp(kappa cos gamma) on the unit S^3: min over the l = 0 (second) and
    l = 1 (first) radial eigenvalues of -u'' + (kappa^2 sin^2/4 - 3 kappa cos/2 - 1 + l(l+1)/sin^2) u
    on (0, pi), Dirichlet."""
    g = np.pi * np.arange(1, n + 1) / (n + 1)
    h = np.pi / (n + 1)
    base = kappa ** 2 * np.sin(g) ** 2 / 4 - 1.5 * kappa * np.cos(g) - 1
    off = -np.ones(n - 1) / h ** 2
    e0 = tri_eigs(2 / h ** 2 + base, off, 2)
    e1 = tri_eigs(2 / h ** 2 + base + 2 / np.sin(g) ** 2, off, 1)
    return min(e0[1], e1[0]) - e0[0]


# DERIVED: 1 is the exact Poincare constant of the flat unit circle (kappa = 0). CHOSEN: the 1e-4
# discretisation band; the read error is 5e-6.
assert abs(poincare_circle_fourier(0.0) - 1) < 1e-4
# DERIVED: 3 is the first nonzero Laplace-Beltrami eigenvalue l(l+2) at l = 1 on the unit S^3. CHOSEN:
# the 2e-3 discretisation band; the read error is 3e-7.
assert abs(poincare_s3(0.0) - 3) < 2e-3
for kap in (20.0, 30.0):  # Dirichlet at s = pi is exact to e^{-2 kappa} here
    a, bq = poincare_circle(kap), poincare_circle_fourier(kap)
    # CHOSEN: relative agreement band between the two discretisations; the read is 1e-4 at kappa = 30.
    assert abs(a - bq) / bq < 2e-3, (kap, a, bq)
print("checks: circle kappa=0 gives 1, unit S^3 kappa=0 gives 3; Dirichlet FD agrees with periodic FD")
print(f"{'kappa':>8} {'U1 lam':>10} {'lam/kappa':>9} {'BE (U1)':>9} {'S3 lam':>10} {'lam/kappa':>9} {'BE (S3)':>9}")
for kap in (0.5, 1, 2, 4, 16, 64, 256, 1024):
    # CHOSEN: the switch to the Dirichlet solver at kappa = 20, where the two solvers are checked to agree
    # above and the density at s = pi is e^{-2 kappa}; not a result, a choice of solver.
    lu = poincare_circle_fourier(kap) if kap <= 20 else poincare_circle(kap)
    ls = poincare_s3(kap)
    print(f"{kap:8.1f} {lu:10.4f} {lu/kap:9.4f} {-kap:9.1f} {ls:10.4f} {ls/kap:9.4f} {2-kap:9.1f}")
lu_big, ls_big = poincare_circle(1024.0), poincare_s3(1024.0)
# CHOSEN: a band around the Gaussian-concentration limit lambda/kappa -> 1 at kappa = 1024 (reads
# 0.9994 and 1.0005); it separates growth like kappa from any other power.
assert 0.97 < lu_big / 1024 < 1.01 and 0.97 < ls_big / 1024 < 1.01
print("the exact constant grows like kappa (Gaussian concentration, variance 1/kappa); the")
print("Bakry-Emery bound is positive only for kappa < 0 (circle) / kappa < 2 (S^3): strong coupling.")
print("block-field dependence, kappa = 2 beta cos(theta_V/2), beta = 64 (U(1)):")
for tv in (0.0, np.pi / 2, 0.9 * np.pi, 0.99 * np.pi, np.pi):
    kap = 2 * 64 * np.cos(tv / 2)
    # CHOSEN: the same solver switch at kappa = 20 as in the table above.
    lu = poincare_circle_fourier(kap) if kap <= 20 else poincare_circle(kap)
    print(f"   theta_V = {tv:5.3f}: kappa = {kap:8.3f}, lambda/beta = {lu/64:.4f}")
print("small coarse field: lambda/beta -> 2 cos(theta_V/2); at theta_V = pi the fibre is flat and")
print("lambda = 1 (lambda/beta -> 0): the large-field region.")
# exact law of the coarse plaquette theta_V = theta_1 + theta_2: density prop. to I_0(2 b cos(theta_V/2))
tv = np.linspace(-np.pi, np.pi, 200001)
for b in (4.0, 16.0, 64.0):
    k = 2 * b * np.abs(np.cos(tv / 2))
    dens = ive(0, k) * np.exp(k - 2 * b)  # I_0(k) e^{-2b}, no overflow
    tail = np.trapezoid(np.where(np.abs(tv) > 0.9 * np.pi, dens, 0), tv) / np.trapezoid(dens, tv)
    lam_tail = poincare_circle_fourier(2 * b * np.cos(0.45 * np.pi)) / b
    print(f"   beta = {b:5.1f}: P(|theta_V| > 0.9 pi) = {tail:.3e}; lambda/beta at the edge = {lam_tail:.4f}")
print("the large-field probability falls like exp(-2 beta (1 - cos(theta_V/2))); the rescaled fibre")
print("constant 2 cos(theta_V/2) tends to 0 as theta_V -> pi, so a bound uniform in V needs the")
print("large-field set handled separately (Balaban small-field / large-field split).")

# ---------------------------------------------------------------- Part C
header("C1. 4D free field: lowest transfer exponent of the Fourier new layer")
print(f"arccosh 2 = log(2 + sqrt 3) = {ARCCOSH2:.6f}; e^-arccosh2 = 2 - sqrt3 = {2-np.sqrt(3):.6f}")
for N in (4, 6, 8, 10, 16, 32, 64):
    p = 2 * np.pi * np.arange(N) / N
    p = np.where(p > np.pi, p - 2 * np.pi, p)
    P = np.stack(np.meshgrid(p, p, p, indexing="ij"), -1).reshape(-1, 3)
    new = (np.abs(P) >= np.pi / 2 - 1e-12).any(axis=1)
    om2 = (4 * np.sin(P / 2) ** 2).sum(axis=1)
    E = np.arccosh(1 + om2[new] / 2)
    print(f"  N = {N:3d}: E_min(new) = {E.min():.6f}  (min omega^2 = {om2[new].min():.4f})")
    assert E.min() >= ARCCOSH2 - 1e-12
    # DERIVED: the parity test 4 | N of the docstring, where the momentum pi/2 is on the grid; not a magnitude.
    if N % 4 == 0:
        # CHOSEN: round-off tolerance for the exact value arccosh 2 in float64.
        assert abs(E.min() - ARCCOSH2) < 1e-12

header("C2. 4D free field conditioned on the 2^3 spatial block averages: lag-one rate")


# CHOSEN: T = 64 time frequencies and an infrared regulator m2 = 1e-6 for the massless zero mode; the
# lag-one rate matches arccosh 2 to under 1e-6 with them (asserted below).
def cond_rate(N, T=64, m2=1e-6):
    """Max over coarse momenta of the lag-one canonical correlation of the 8 fine aliases given
    the block-average time series."""
    pc = 2 * np.pi * np.arange(N // 2) / N  # fine momenta in the first half; aliases add pi
    w = 2 * np.pi * np.arange(T) / T
    s2w = 4 * np.sin(w / 2) ** 2
    eps = np.array([[a, b, c] for a in (0, 1) for b in (0, 1) for c in (0, 1)])
    best = 0.0
    for q1 in pc:
        for q2 in pc:
            for q3 in pc:
                pa = np.array([q1, q2, q3])[None, :] + np.pi * eps  # 8 aliases
                h = np.prod((1 + np.exp(1j * pa)) / 2, axis=1)  # block-average symbol
                om2 = (4 * np.sin(pa / 2) ** 2).sum(axis=1)
                G = 1.0 / (om2[None, :] + s2w[:, None] + m2)  # (T, 8)
                Sh = G * h[None, :]  # S h, S diagonal
                hSh = (np.abs(h) ** 2 * G).sum(axis=1)  # (T,)
                Sc = np.einsum("ta,ab->tab", G, np.eye(8)) - \
                    np.einsum("ta,tb->tab", Sh, Sh.conj()) / hSh[:, None, None]
                C0 = Sc.mean(axis=0)
                C1 = (Sc * np.exp(1j * w)[:, None, None]).mean(axis=0)
                # the lag-0 / lag-1 conditional covariance pair, Hermitian, read through its real
                # embedding z -> (Re z, Im z) (each eigenvalue appears twice)
                emb = lambda X: np.block([[X.real, -X.imag], [X.imag, X.real]])  # noqa: E731
                ev = matrix_pencil(emb(C0), emb(C1)).evals
                best = max(best, float(np.abs(ev).max()))
    return best


for N in (4, 8, 16):
    r = cond_rate(N)
    print(f"  N = {N:3d}: rho = {r:.6f}, c = -log rho = {-np.log(r):.6f}  (arccosh 2 = {ARCCOSH2:.6f})")
    # CHOSEN: agreement tolerance against arccosh 2, set above the effect of the T = 64 sum and the m2
    # regulator; the printed values agree to all six digits.
    assert abs(-np.log(r) - ARCCOSH2) < 1e-6
print("the conditional new modes are gapped in lattice units with c = arccosh 2 at every N.")

el = time.time() - T0
print(f"\nall checks passed in {el:.1f} s")
# CHOSEN: a 10-second run-time budget; it decides speed, not a result.
assert el < 10
