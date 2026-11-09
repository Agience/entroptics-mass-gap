"""Checks for `MassGap.FluxTube`: does centre flux spread classically?

Exact linear algebra, closed forms, exhaustive enumeration and one deterministic minimisation; no
Monte Carlo. Run time under 10 seconds (asserted).

1. `U(1)`: the quadratic energy of a flux Phi split n ways is at least Phi^2/n with equality at the
   equal split (`quad_split_ge`, `quad_split_equal`); the Wilson action of the even split,
   `u1Spread Phi n = n (1 - cos(Phi/n))`, is at most Phi^2/2/n (`u1Spread_le`) and tends to 0.
2. `SU(2)`, `SU(3)` (k = 1, 2) and `SU(4)` thick centre vortices built as actual matrices: the strip links of
   `stripLink`, each plaquette holonomy L_{j+1} L_j^{-1} equal to `vortexPlaq`, the loop holonomy the
   centre element, the total Wilson action at most `vortexConst / n` (`vortex_action_le`), with
   `vortexConst = 2 pi^2 k^2 m / (m+1)^2` (`vortexConst_eq`); for SU(2) the action equals
   `u1Spread pi n` (`su2_vortex_eq_u1`). The thin vortex costs 1 - cos(2 pi k / N)
   (`thin_vortex_action`).
3. A two-dimensional core: on an L x L plaquette grid, an axial-gauge SU(2) configuration with
   uniform plaquette angle pi / w^2 on a w x w core and 0 outside. The holonomy of the boundary loop is
   -1, the action is w^2 (1 - cos(pi / w^2)), and the action per unit sheet area falls like 1/w^2.
4. Within the torus of SU(2), the equal split minimises sum (1 - cos phi_i) subject to
   sum phi_i = pi (deterministic minimisation from a grid of starts; checked against the analytic
   lower bound 2/n from 1 - cos phi >= 2 phi^2 / pi^2 on [-pi, pi]). This is a check, not a Lean
   statement.
5. A finite gauge group: Z_2 and Z_3 with the Wilson cost 1 - Re z. Exhaustive enumeration over all
   assignments of n plaquette values (n <= 12 for Z_2, n <= 8 for Z_3) with non-trivial product: the
   minimum action is the single-plaquette gap (2 and 1.5) at every n (`finite_flux_cannot_spread`).
6. The table: action per unit sheet area vs core width w, for SU(2) (Z_2 flux), U(1) (real flux
   2 pi, whose holonomy e^{2 pi i} = 1 is trivial, hence 0 at w = 1), and Z_2 gauge theory.
"""
from __future__ import annotations

import itertools
import math
import time

import numpy as np
from scipy.optimize import minimize

T0 = time.time()
PI = math.pi


def wilson(U):
    """1 - Re tr U / N."""
    return 1.0 - np.trace(U).real / U.shape[0]


def torus(phi):
    return np.diag(np.exp(1j * np.asarray(phi, dtype=float)))


def centre_angles(m, k):
    N = m + 1
    a = np.full(N, 2 * PI * k / N)
    a[-1] -= 2 * PI * k
    return a


def u1_spread(Phi, n):
    return n * (1 - math.cos(Phi / n))


def section1():
    print("1. U(1): quadratic energy and spreading")
    Phi = 2 * PI
    for n in (1, 2, 3, 5, 8, 13):
        equal = n * (Phi / n) ** 2
        # CHOSEN: float64 slack on an exact identity of numbers of size <= 40.
        assert abs(equal - Phi ** 2 / n) < 1e-12
        # structured unequal splits: geometric weights r^i, normalised to sum Phi
        for r in (0.5, 0.9, 1.1, 2.0):
            w = np.array([r ** i for i in range(n)])
            phi = Phi * w / w.sum()
            assert (phi ** 2).sum() >= Phi ** 2 / n - 1e-12
        assert u1_spread(Phi, n) <= Phi ** 2 / 2 / n + 1e-12
    rows = [(n, u1_spread(Phi, n), Phi ** 2 / 2 / n) for n in (1, 4, 16, 64, 256, 1024)]
    for n, a, b in rows:
        print(f"   n = {n:5d}: u1Spread(2 pi, n) = {a:.6f}  <=  Phi^2/2/n = {b:.6f}")
    # CHOSEN: 0.02 as "the action has spread towards 0". It sits close to the read: at n = 1024 the
    # value is 0.019277 (Phi^2/2/n = 0.019277), 4 % under the cut.
    assert rows[-1][1] < 0.02


def section2():
    print("2. SU(N) thick centre vortex on a strip (actual matrices)")
    for m, k in ((1, 1), (2, 1), (2, 2), (3, 1)):
        N = m + 1
        th = centre_angles(m, k)
        omega = np.exp(2j * PI * k / N)
        # CHOSEN: float64 slack; the centre angles sum to 0 exactly.
        assert abs(th.sum()) < 1e-12
        assert np.allclose(torus(th), omega * np.eye(N))
        C = (th ** 2).sum() / (2 * N)
        C_closed = 2 * PI ** 2 * k ** 2 * m / N ** 2
        # CHOSEN: float64 slack on the closed form `vortexConst_eq`, an exact identity.
        assert abs(C - C_closed) < 1e-12
        thin = wilson(omega * np.eye(N))
        # CHOSEN: float64 slack on the exact thin-vortex cost of `thin_vortex_action`.
        assert abs(thin - (1 - math.cos(2 * PI * k / N))) < 1e-12
        line = []
        for n in (1, 2, 4, 8, 16, 64, 256):
            links = [torus((j / n) * th) for j in range(n + 1)]
            assert np.allclose(links[0], np.eye(N))
            plaq = [links[j + 1] @ np.linalg.inv(links[j]) for j in range(n)]
            P = torus(th / n)
            assert all(np.allclose(p, P) for p in plaq)
            # CHOSEN: float64 slack; det P = 1 exactly because the angles sum to 0.
            assert abs(np.linalg.det(P) - 1) < 1e-12
            assert np.allclose(P.conj().T @ P, np.eye(N))
            prod = np.eye(N, dtype=complex)
            for p in plaq:
                prod = p @ prod
            assert np.allclose(prod, omega * np.eye(N))
            assert np.allclose(links[n], omega * np.eye(N))
            act = sum(wilson(p) for p in plaq)
            assert act <= C / n + 1e-12
            if (m, k) == (1, 1):
                # CHOSEN: float64 slack on the exact identity `su2_vortex_eq_u1`.
                assert abs(act - u1_spread(PI, n)) < 1e-12
            line.append((n, act))
        print(f"   SU({N}), k = {k}: thin vortex {thin:.4f}; vortexConst = {C:.4f};"
              f" action at n = 1, 16, 256: {line[0][1]:.4f}, {line[4][1]:.5f}, {line[6][1]:.6f}")


def axial_core(L, w):
    """Abelian SU(2) configuration on an L x L plaquette grid: plaquette angle pi/w^2 on a centred w x w
    core, 0 elsewhere. Axial gauge: horizontal links 1 (angle 0), vertical link angles chosen so that
    the plaquette (x, y) angle is v[x+1, y] - v[x, y] with v[0, y] = 0."""
    F = np.zeros((L, L))
    x0 = (L - w) // 2
    F[x0:x0 + w, x0:x0 + w] = PI / w ** 2
    v = np.zeros((L + 1, L))
    for x in range(L):
        v[x + 1] = v[x] + F[x]
    return F, v


def su2(a):
    return np.diag([np.exp(1j * a), np.exp(-1j * a)])


def section3():
    print("3. a w x w core in one transverse plane (SU(2), axial gauge)")
    L = 40
    for w in (1, 2, 4, 8, 16):
        F, v = axial_core(L, w)
        # plaquette holonomies from links: U_p = U_h(x,y) U_v(x+1,y) U_h(x,y+1)^-1 U_v(x,y)^-1, U_h = 1
        act = 0.0
        for x in range(L):
            for y in range(L):
                Up = su2(v[x + 1, y]) @ np.linalg.inv(su2(v[x, y]))
                assert np.allclose(Up, su2(F[x, y]))
                act += wilson(Up)
        # boundary loop: bottom and top horizontal links are 1, right vertical column minus left
        hol = np.eye(2, dtype=complex)
        for y in range(L):
            hol = su2(v[L, y]) @ hol
        for y in reversed(range(L)):
            hol = np.linalg.inv(su2(v[0, y])) @ hol
        assert np.allclose(hol, -np.eye(2))
        exact = w ** 2 * (1 - math.cos(PI / w ** 2))
        # CHOSEN: float64 slack on an exact closed form, wider (1e-10) for a sum over L^2 = 1600
        # plaquettes; 1e-12 on the upper bound pi^2/2/w^2, which the action meets only in the limit.
        assert abs(act - exact) < 1e-10 and act <= PI ** 2 / 2 / w ** 2 + 1e-12
        print(f"   w = {w:2d}: boundary holonomy -1; action per unit sheet area {act:.6f}"
              f"  (w^2 * action = {act * w ** 2:.4f}, pi^2/2 = {PI ** 2 / 2:.4f})")


def section4():
    print("4. torus of SU(2): the equal split is the minimum (check, not a Lean statement)")
    for n in (2, 3, 4, 6):
        f = lambda p: np.sum(1 - np.cos(p))
        cons = {"type": "eq", "fun": lambda p: np.sum(p) - PI}
        best = math.inf
        grid = np.linspace(-1.0, 2.0, 4)
        # CHOSEN: the full 4^n grid of starts up to n = 4, 4^2 starts beyond (padded with 0.5); it
        # bounds the minimiser's run time.
        for start in itertools.product(grid, repeat=n if n <= 4 else 2):
            s = np.array(list(start) + [0.5] * (n - len(start)))
            # DERIVED: the guard against dividing by a zero sum when rescaling the start, not a magnitude.
            s = s / s.sum() * PI if abs(s.sum()) > 1e-9 else np.full(n, PI / n)
            r = minimize(f, s, constraints=[cons], bounds=[(-PI, PI)] * n, method="SLSQP")
            if r.success:
                best = min(best, r.fun)
        eq = u1_spread(PI, n)
        assert best >= eq - 1e-7 and best >= 2 / n - 1e-9
        print(f"   n = {n}: min over starts {best:.6f}; equal split {eq:.6f}; lower bound 2/n = {2 / n:.4f}")


def section5():
    print("5. finite gauge groups: exhaustive enumeration, the floor holds at every n")
    for N, nmax in ((2, 12), (3, 8)):
        gap = 1 - math.cos(2 * PI / N)
        cost = [1 - math.cos(2 * PI * a / N) for a in range(N)]
        mins = []
        for n in range(1, nmax + 1):
            best = math.inf
            for assign in itertools.product(range(N), repeat=n):
                # DERIVED: a product of Z_N elements is non-trivial iff the exponents do not sum to 0 mod N.
                if sum(assign) % N != 0:
                    best = min(best, sum(cost[a] for a in assign))
            mins.append(best)
            # CHOSEN: float64 slack; the minimum is a finite sum of exact costs.
            assert abs(best - gap) < 1e-12
        print(f"   Z_{N}: minimum action of a non-trivial flux over n = 1..{nmax} plaquettes:"
              f" {sorted(set(round(x, 12) for x in mins))} (gap {gap:.3f})")


def section6():
    print("6. action per unit sheet area vs core width w")
    print("      w    SU(2) Z_2 flux    U(1) real flux 2pi (holonomy trivial)    Z_2 gauge")
    ws = [1, 2, 3, 4, 6, 8, 12, 16, 24, 32]
    su = [w ** 2 * (1 - math.cos(PI / w ** 2)) for w in ws]
    u1 = [w ** 2 * (1 - math.cos(2 * PI / w ** 2)) for w in ws]
    for w, a, b in zip(ws, su, u1):
        print(f"   {w:4d}    {a:14.6e}    {b:14.6e}    {2.0:9.3f}")
    slope_su = math.log(su[-1] / su[-2]) / math.log(ws[-1] / ws[-2])
    slope_u1 = math.log(u1[-1] / u1[-2]) / math.log(ws[-1] / ws[-2])
    print(f"   log-log slope at w = 24..32: SU(2) {slope_su:.4f}, U(1) {slope_u1:.4f} (both -> -2)")
    # DERIVED: -2 from 1 - cos x ~ x^2/2 with x = c / w^2. CHOSEN: 1e-3 slack; the O(w^-4)
    # correction at w = 24..32 is far below it (the slopes print as -2.0000).
    assert abs(slope_su + 2) < 1e-3 and abs(slope_u1 + 2) < 1e-3


if __name__ == "__main__":
    section1()
    section2()
    section3()
    section4()
    section5()
    section6()
    dt = time.time() - T0
    print(f"all checks passed in {dt:.2f} s")
    # CHOSEN: the 10 s run-time budget stated in the module docstring; it sees no number.
    assert dt < 10
