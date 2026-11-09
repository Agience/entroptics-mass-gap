"""Checks for `MassGap.MatchAt`: is the Kotecky-Preiss match true at the fixed length?

Exact quadrature and closed forms only; no Monte Carlo. Run time under 10 seconds (asserted).

Conventions. Standard Wilson coupling: S = beta sum_p (1 - Re tr U_p / N), so g^2 = 2N / beta
(`GaugeRunning.gSqG_SU`; the Lean coupling of the tree is beta_std / 2). Two-loop running as in
`GaugeRunning.aRunStdG`: a Lambda = (b0 g^2)^(-51/121) exp(-1/(2 b0 g^2)), b0 = 11 N / (48 pi^2).

1. Plaquette weights. The normalised plaquette weight is f(U) + 1 = e^{-S_p(U)} / c0(beta); the
   strong-coupling polymer of a set X of plaquettes has |w(X)| <= u^|X|, u = sup |f| (every
   factor bounded by its sup). Also the fundamental character coefficient t_F(beta):
   SU(2) I_2/I_1 (closed form), SU(3) by Weyl integration on a 2-torus grid (spectral accuracy;
   cross-checked against the small-beta series t_F = beta/18 + ...).
2. The KP threshold for the pure Wilson action (no tails). Two sufficient conditions:
   (a) `matchAt_of_count` with entropy z = e * Delta per plaquette (Delta = 20 plaquettes share a
       link with a given one in 4D; connected sets of size n through a given one number at most
       (e Delta)^n) and cost tau = -log u: 4 z e^{1 + kappa} u <= 1;
   (b) the direct per-site KP sum  sum_{n >= 6} (e Delta)^n u^n e^{a n} (1 + n e^{kappa n}) <= a,
       a in (0, 1] optimised (closed surfaces have n >= 6 plaquettes).
   The beta_std at which each holds, for SU(2) and SU(3), against the tree's own proved
   strong-coupling region (pruned `PotSharpCluster.pot_cluster_full_sharp`: Lean beta <= 1/20,
   i.e. beta_std <= 1/10, SU(2), local potential norm <= 1/16; a heat-bath/Knabe route).
3. The intermediate regime. g^2 at the KP threshold against g^2 = O(1); the two-loop length ratio
   a(beta_KP) / a(beta) and its number of doublings, with the one-loop/two-loop spread as the
   measure of how far outside the perturbative window the extrapolation is. The two-loop spacing
   peaks at g^2 = 121/(102 b0) (25.5 for SU(2)) and falls beyond, so it cannot even be extrapolated
   to the KP region; the largest ratio it gives from g^2 = 1 is printed. Strong-coupling
   tension at the threshold: sigma a^2 = -log t_F (leading order), so a sqrt(sigma) there.
4. Edge cost as an activity bound. A flux-tube polymer of length ell chunks has area 4 ell
   plaquettes and activity ~ t^{4 ell} = e^{-4 (sigma r*^2) ell} with sigma r*^2 = -log t. The count
   route needs the cost per chunk tau >= log z + 1 + kappa + log 4: sigma r*^2 = O(1) is not enough
   with the crude entropy; the length at which it is (in units of 1/sqrt(sigma)) is printed.
   U(1) control: at weak coupling sigma = 0, the cost per chunk of the Coulomb phase is not
   produced by coarse-graining (Migdal-Kadanoff flow, section 5) and every route fails.
5. Route (1) and (3) in a model flow: the Migdal-Kadanoff recursion (b = 2, d = 4: bond moving
   f -> f^4, then t_n -> t_n^4 under decimation), on class functions of SU(2) and U(1). It is an
   approximation, not a bound on the true RG. SU(2): every beta flows to t -> 0 and reaches the KP
   region after a number of steps that grows with beta (printed); once inside, the flow stays
   inside and improves (the stability of route (3) at the trivial fixed point). U(1): at large
   beta the flow does not reach the KP region (Coulomb phase), as the control requires.
6. Route (2), few states: the cost per chunk needed for k readable states per chunk,
   c >= log(zs k) + log 4 + 1 + kappa, for k = 2 .. 2^20; the full fibre (k = infinity) has none.
"""
from __future__ import annotations

import math
import time

import numpy as np
from scipy.special import iv

T0 = time.time()
E = math.e
# DERIVED: 4 links per plaquette, each in 2 (d - 1) = 6 plaquettes in d = 4, so 4 x 5 = 20 others.
DELTA = 20                     # plaquettes sharing a link with a given plaquette, 4D
Z_ENT = E * DELTA              # connected-set entropy per plaquette
# CHOSEN: kappa = 0 asks for plain clustering, no extra decay; any kappa > 0 only makes both conditions stricter.
KAPPA = 0.0                    # decay rate demanded beyond KP (kappa = 0: plain clustering threshold)
# DERIVED: the smallest closed plaquette surface is the boundary of one cube, 6 plaquettes.
NMIN = 6                       # smallest closed surface


# ---------------------------------------------------------------- 1. plaquette weights
def su2_tF(beta):
    return iv(2, beta) / iv(1, beta)


def su2_u(beta):
    """sup |f| for SU(2): weight e^{beta (tr U / 2)} / c0, c0 = 2 I_1(beta) / beta."""
    c0 = 2.0 * iv(1, beta) / beta
    return max(math.exp(beta) / c0 - 1.0, 1.0 - math.exp(-beta) / c0)


# CHOSEN: a 256 x 256 grid on the SU(3) torus; the periodic rule is exact for trigonometric
# polynomials of degree below 256, so the checks at the c0 and <|chi_F|^2> lines read 0 error.
_G = 256
_th = 2 * np.pi * np.arange(_G) / _G
_T1, _T2 = np.meshgrid(_th, _th, indexing="ij")
_T3 = -_T1 - _T2
_TR = np.exp(1j * _T1) + np.exp(1j * _T2) + np.exp(1j * _T3)
_VDM = (np.abs(np.exp(1j * _T1) - np.exp(1j * _T2)) ** 2 * np.abs(np.exp(1j * _T1) - np.exp(1j * _T3)) ** 2
        * np.abs(np.exp(1j * _T2) - np.exp(1j * _T3)) ** 2)
_VDM = _VDM / _VDM.mean()       # Haar measure of SU(3) on the torus, normalised


def su3_moments(beta):
    wgt = np.exp(beta / 3.0 * _TR.real)
    c0 = float((wgt * _VDM).mean())
    cF = float((wgt * _TR.conj().real * _VDM).mean())   # <chi_F^*> weighted, real by symmetry
    return c0, cF / (3.0 * c0)


def su3_tF(beta):
    return su3_moments(beta)[1]


def su3_u(beta):
    c0, _ = su3_moments(beta)
    rmin = float((_TR.real / 3.0).min())                 # min of Re tr U / 3 on SU(3) = -1/2
    return max(math.exp(beta) / c0 - 1.0, 1.0 - math.exp(beta * rmin) / c0)


# ---------------------------------------------------------------- 2. KP thresholds
def count_route_ok(u, kappa=KAPPA):
    # DERIVED: the count-route condition 4 z e^{1 + kappa} u <= 1 of `matchAt_of_count` (docstring, 2a).
    return 4.0 * Z_ENT * math.exp(1.0 + kappa) * u <= 1.0


_A = np.linspace(0.005, 1.0, 200)[:, None]
_N = np.arange(NMIN, 300)[None, :]


def direct_kp_ok(u, kappa=KAPPA):
    q = Z_ENT * u * np.exp(_A)                       # one row per a
    # DERIVED: the series sum_n (q e^kappa)^n converges only for q e^kappa < 1; a convergence guard.
    if not np.any(q * math.exp(kappa) < 1):
        return False
    with np.errstate(over="ignore", invalid="ignore"):
        s = np.sum(q ** _N * (1 + _N * np.exp(kappa * _N)), axis=1)
    # DERIVED: the same convergence condition q e^kappa < 1, row by row, beside the KP sum <= a.
    good = (q[:, 0] * math.exp(kappa) < 1) & (s <= _A[:, 0])
    return bool(np.any(good))


# CHOSEN: the bisection bracket beta_std in [1e-6, 3]; the assert below checks it brackets the threshold.
def threshold(ufun, ok, lo=1e-6, hi=3.0):
    """Largest beta with ok(u(beta)) (u increases with beta), by bisection."""
    assert ok(ufun(lo)) and not ok(ufun(hi))
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        lo, hi = (mid, hi) if ok(ufun(mid)) else (lo, mid)
    return lo


def a_two_loop(g2, N):
    b0 = 11 * N / (48 * math.pi ** 2)
    return (b0 * g2) ** (-51 / 121) * math.exp(-1 / (2 * b0 * g2))


def a_one_loop(g2, N):
    b0 = 11 * N / (48 * math.pi ** 2)
    return math.exp(-1 / (2 * b0 * g2))


# ---------------------------------------------------------------- 5. Migdal-Kadanoff
_TH = np.linspace(1e-6, np.pi - 1e-6, 4001)
_MU2 = (2 / np.pi) * np.sin(_TH) ** 2
_DTH = _TH[1] - _TH[0]


def su2_chi(n):          # n = 2j, dimension n + 1
    return np.sin((n + 1) * _TH) / np.sin(_TH)


# CHOSEN: 60 SU(2) characters (spins j < 30) kept in the Migdal-Kadanoff flow.
NREP = 60
_CHI2 = np.array([su2_chi(n) for n in range(NREP)])


# CHOSEN: 60 Migdal-Kadanoff steps; the latest entry into the KP region read is step 23.
def mk_su2(beta, steps=60, ustar=None):
    """MK on SU(2): returns the list of sup|f| along the flow, from Wilson at beta_std."""
    t = np.array([iv(n + 1, beta) / iv(1, beta) for n in range(NREP)])
    us = []
    for _ in range(steps):
        f = 1 + sum((n + 1) * t[n] * _CHI2[n] for n in range(1, NREP))
        us.append(float(np.max(np.abs(f - 1))))
        F = np.clip(f, 0, None) ** 4                       # bond moving, factor b^{d-2} = 4
        Z0 = float(np.sum(F * _MU2) * _DTH)
        tm = np.array([float(np.sum(F * _CHI2[n] * _MU2) * _DTH) / ((n + 1) * Z0) for n in range(NREP)])
        t = tm ** 4                                         # decimation of b^2 = 4 plaquettes
        t[0] = 1.0
    return us


_PH = np.linspace(-np.pi, np.pi, 4001)[:-1]


# CHOSEN: 60 Migdal-Kadanoff steps, as for SU(2); "never enters" below means within these 60.
def mk_u1(beta, steps=60):
    nmax = 80
    t = np.array([iv(n, beta) / iv(0, beta) for n in range(nmax)])
    us = []
    for _ in range(steps):
        f = 1 + 2 * sum(t[n] * np.cos(n * _PH) for n in range(1, nmax))
        us.append(float(np.max(np.abs(f - 1))))
        F = np.clip(f, 0, None) ** 4
        Z0 = float(F.mean())
        tm = np.array([float((F * np.cos(n * _PH)).mean()) / Z0 for n in range(nmax)])
        t = tm ** 4
        t[0] = 1.0
    return us


def first_inside(us, ok):
    for i, u in enumerate(us):
        if ok(u):
            return i
    return None


def main():
    print("1. plaquette weights")
    for b in (0.05, 0.1, 0.5, 1.0, 2.0, 2.5):
        print(f"   SU(2) beta_std={b:5.2f}  t_F={su2_tF(b):.5f}  u=sup|f|={su2_u(b):.5f}")
    for b in (0.05, 0.1, 0.5, 1.0, 5.7, 6.0):
        print(f"   SU(3) beta_std={b:5.2f}  t_F={su3_tF(b):.5f}  u=sup|f|={su3_u(b):.5f}")
    # checks: small-beta series t_F ~ beta/4 (SU(2)), beta/18 (SU(3)); SU(3) quadrature
    # CHOSEN: 1e-3 slack on the leading series term at beta = 1e-3; the next term moves it by 1e-8.
    assert abs(su2_tF(1e-3) / 1e-3 - 0.25) < 1e-3
    # CHOSEN: 1e-3 slack on the leading series term at beta = 1e-3; the next term moves it by 5e-6.
    assert abs(su3_tF(1e-3) / 1e-3 - 1 / 18) < 1e-3
    c0, _ = su3_moments(0.0)
    # CHOSEN: float64 slack; c0(0) = 1 by the normalisation of _VDM.
    assert abs(c0 - 1) < 1e-12
    # CHOSEN: float64 slack on the orthonormality <|chi_F|^2> = 1, exact on the 256 grid.
    assert abs(float((np.abs(_TR) ** 2 * _VDM).mean()) - 1) < 1e-9     # <|chi_F|^2> = 1

    print("2. KP thresholds, pure Wilson action (no tails), kappa = 0")
    res = {}
    for name, uf, N in (("SU(2)", su2_u, 2), ("SU(3)", su3_u, 3)):
        bc = threshold(uf, count_route_ok)
        bd = threshold(uf, direct_kp_ok)
        res[name] = (bc, bd, N)
        print(f"   {name}: count route beta_std <= {bc:.5f} (g^2 >= {2 * N / bc:8.1f});"
              f"  direct KP sum beta_std <= {bd:.5f} (g^2 >= {2 * N / bd:8.1f})")
        assert bc <= bd
    print("   tree's proved strong-coupling region (pruned PotSharpCluster): SU(2) beta_std <= 0.1,"
          f" g^2 >= 40, t_F = {su2_tF(0.1):.5f}")

    print("3. the intermediate regime (SU(2), two-loop extrapolation)")
    bc, bd, N = res["SU(2)"]
    sig_a2 = -math.log(su2_tF(bd))
    print(f"   at the direct-KP threshold beta_std={bd:.4f}: strong-coupling sigma a^2 = -log t_F ="
          f" {sig_a2:.3f}, a sqrt(sigma) = {math.sqrt(sig_a2):.3f}")
    for g2 in (0.5, 1.0, 2.0, 4.0):
        for target, lab in ((2 * N / bd, "direct KP"), (40.0, "beta_std 0.1")):
            r2 = a_two_loop(target, N) / a_two_loop(g2, N)
            r1 = a_one_loop(target, N) / a_one_loop(g2, N)
            print(f"   g^2 {g2:4.1f} -> {lab:12s} (g^2={target:7.1f}): length ratio two-loop {r2:10.3e}"
                  f" ({math.log2(r2):5.1f} doublings), one-loop {r1:10.3e}; spread x{r1 / r2:6.2f}")
    # the two-loop spacing is not monotone: d log a / d g^2 = 0 at g^2 = 121 / (102 b0)
    b0 = 11 * N / (48 * math.pi ** 2)
    gmax = 121 / (102 * b0)
    print(f"   two-loop a(g^2) peaks at g^2 = 121/(102 b0) = {gmax:.1f} and decreases beyond: the"
          " formula has no strong-coupling end, every ratio above with target g^2 > "
          f"{gmax:.1f} is past its turning point")
    assert a_two_loop(gmax * 1.01, N) < a_two_loop(gmax, N) and a_two_loop(gmax * 0.99, N) < a_two_loop(gmax, N)
    assert 2 * N / 0.1 > gmax                        # even the tree's beta_std <= 0.1 lies past it
    rmax = a_two_loop(gmax, N) / a_two_loop(1.0, N)
    print(f"   largest two-loop length ratio from g^2 = 1: {rmax:.3e} ({math.log2(rmax):.1f} doublings)")

    print("4. edge cost as an activity bound")
    need = math.log(Z_ENT) + 1 + KAPPA + math.log(4)
    print(f"   count route needs cost per plaquette-chunk tau >= log(e Delta) + 1 + log 4 = {need:.3f}")
    print(f"   flux tube of length ell chunks: activity t^(4 ell) = exp(-4 (sigma r*^2) ell); per chunk"
          f" cost sigma r*^2; needs sigma r*^2 >= {need:.2f} -> r* >= {math.sqrt(need):.2f}/sqrt(sigma)"
          f" = {math.sqrt(need) * 0.4485:.2f} fm at sqrt(sigma) = 440 MeV")
    for s in (0.5, 1.0, 2.0, 4.0):
        print(f"   sigma r*^2 = {s:3.1f}: 4 z e^(1+kappa-tau) = {4 * Z_ENT * math.exp(1 - s):9.2f}"
              # DERIVED: the count-route condition 4 z e^{1 + kappa - tau} <= 1 (kappa = 0), as in count_route_ok.
              f"  -> {'KP' if 4 * Z_ENT * math.exp(1 - s) <= 1 else 'no KP'}")
    # DERIVED: the count-route condition fails when 4 z e^{1 + kappa - tau} > 1; it reads 217 here.
    assert 4 * Z_ENT * math.exp(1 - 1.0) > 1           # sigma r*^2 = O(1) is not enough
    # DERIVED: the same count-route condition at tau = 0; it reads 591.
    assert 4 * Z_ENT * math.exp(1 - 0.0) > 1          # U(1) weak coupling, sigma = 0: fails

    print("5. Migdal-Kadanoff model flow (b = 2, d = 4); KP test = direct KP sum on u = sup|f|")
    for b in (1.0, 2.0, 2.5, 3.0, 4.0, 6.0):
        us = mk_su2(b)
        i = first_inside(us, direct_kp_ok)
        stay = i is not None and all(direct_kp_ok(u) for u in us[i:])
        mono = i is not None and all(us[k + 1] <= us[k] + 1e-12 for k in range(i, len(us) - 1))
        print(f"   SU(2) beta_std={b:3.1f} (g^2={4 / b:4.2f}): u_0={us[0]:.3f}; enters KP at step"
              f" {i} (length 2^{i} a); stays inside {stay}; u decreasing inside {mono}")
        assert i is not None and stay and mono
    for b in (0.5, 1.0, 2.0, 4.0):
        us = mk_u1(b)
        i = first_inside(us, direct_kp_ok)
        print(f"   U(1)  beta={b:3.1f}: u_0={us[0]:.3f}, u_60={us[-1]:.4f}; enters KP at step {i}")
    assert first_inside(mk_u1(4.0), direct_kp_ok) is None   # Coulomb phase: never coarse

    print("6. route (2): cost per chunk for k readable states (zs = e Delta shapes)")
    for k in (2, 4, 16, 256, 2 ** 20):
        print(f"   k = {k:8d}: c >= {math.log(Z_ENT * k) + math.log(4) + 1 + KAPPA:.3f}")
    print("   full fibre of a continuous SU(N) chunk: k = infinity, no finite cost suffices")

    dt = time.time() - T0
    print(f"time {dt:.2f} s")
    # CHOSEN: the 10 s run-time budget stated in the module docstring; it sees no number.
    assert dt < 10


if __name__ == "__main__":
    main()
