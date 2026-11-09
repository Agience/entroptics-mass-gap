"""Checks for `MassGap.VortexCondense`: centre-vortex condensation, Tomboulis-Yaffe, the floor.

Exact character sums, quadrature and closed forms only; no Monte Carlo. Run time under 10 seconds
(asserted).

1. The Lean statements on numbers: `area_of_ty` (e <= exp(-s A) gives e^{mn/A} <= exp(-s mn)),
   `condenses_of_const`, the interface example `ty_floor_without_condensation` (W = e^{-mn},
   e = 1/2, boxes (K+1)!), `coulomb_no_condensation` (F >= c P/A with P >= A).
2. 2D SU(2) on the L x L torus, Wilson action exp(-beta (1 - tr U / 2)), exact. With
   t_n = I_{n+1}(beta)/I_1(beta) (n = 2j): Z = sum_n t_n^A, Z_- = sum_n (-1)^n t_n^A (one twisted
   plaquette, chi_j(-U) = (-1)^{2j} chi_j(U)), and for a contractible loop of area A_C the disc and
   the one-holed torus glue to Z <W> = (1/2) sum_{k, j = k +- 1} (k+1)/(j+1) t_k^{A_C} t_j^{A - A_C}.
   Checked: Z_- <= Z (zR <= 1); F_v -> 0 as 2 t_1^A; the Tomboulis-Yaffe inequality
   <W(C)> <= (1 - Z_-/Z)^{A_C/A} on every tiling rectangle (m | L, n | L, m, n < L) and its failure
   on non-tiling rectangles of large area; the rate -log(1 - Z_-/Z)/A against the exact tension
   -log t_1; the area law of small loops. 2D U(1) is a second confining case (2D has no Coulomb
   phase), so the U(1) control is read in the 4D proxy.
3. 4D Migdal-Kadanoff proxy (b = 2, d = 4, as in `no_transition_flow_checks.py`, imported, not
   copied). A PROXY ONLY: an approximation, not a bound on the true RG, not the 4D Wilson measure.
   After k steps the twist plane of a box of side 2^k is one coarse plaquette; its vortex ratio is
   read on the one-plaquette 2-torus, z_k = sum_n (-1)^n w_n t_n / sum_n w_n t_n (w_n = 1 for SU(2),
   n = 2j; w_n = 2 for U(1), n >= 1, twist angle pi), F_k = -log z_k. SU(2): F_k decays, log F_k
   against the lattice area 4^k; U(1) at weak coupling: F_k settles at a positive value (no
   condensation), at strong coupling it decays.
"""
from __future__ import annotations

import math
import time

import numpy as np
from scipy.special import iv

import no_transition_flow_checks as ntf
from check_driver import run_sections

T0 = time.time()


# ---------------------------------------------------------------- 1. Lean statements on numbers
def section1():
    print("1. the Lean statements on numbers")
    rng = np.random.default_rng(11)
    for _ in range(200):
        La, Lb = rng.integers(2, 30, 2)
        m, n = rng.integers(1, La), rng.integers(1, Lb)
        s = rng.uniform(-0.5, 2.0)
        e = math.exp(-s * La * Lb) * rng.uniform(0, 1)
        assert e ** (m * n / (La * Lb)) <= math.exp(-s * m * n) * (1 + 1e-12)
    print("   area_of_ty: e <= exp(-s La Lb) gives e^(mn/(La Lb)) <= exp(-s mn) on 200 random draws")
    # condenses_of_const: F <= C e^{-rho A}; for rho' < rho, eventually F <= e^{-rho' A}
    C, rho = 50.0, 0.3
    for rp in (0.1, 0.2, 0.29):
        A0 = math.log(C) / (rho - rp)
        A = np.arange(1, 4000)
        ok = np.all(C * np.exp(-rho * A[A > A0]) <= np.exp(-rp * A[A > A0]) * (1 + 1e-12))
        assert ok
        print(f"   condenses_of_const, C = {C}, rho = {rho}: rate {rp} holds from A > {A0:.1f}")
    # the interface example: W = e^{-mn}, e = 1/2 on boxes (K+1)!
    for K in range(1, 6):
        Lk = math.factorial(K + 1)
        A = Lk * Lk
        for m in range(1, min(Lk, 30)):
            for n in range(1, min(Lk, 30)):
                # DERIVED: the divisibility test m | L, n | L that defines a tiling rectangle; not a magnitude.
                if Lk % m == 0 and Lk % n == 0:
                    assert math.exp(-m * n) <= 0.5 ** (m * n / A)
    print("   ty_floor_without_condensation: e^-mn <= (1/2)^(mn/A) on every tiling rectangle of boxes"
          " (K+1)!, K = 1..5; tension 1; e = 1/2 > exp(-rho A) once A > log 2 / rho")
    # coulomb_no_condensation: F = c P / A with P = A^2 / 4 (L3 L4 >= L1 L2): F grows, never <= e^{-rho A}
    c = 0.05
    for A in (16, 64, 256, 1024):
        F = c * (A * A / 4) / A
        assert F >= c and 1 - math.exp(-F) >= 1 - math.exp(-c)
    print(f"   coulomb_no_condensation: F = c L3L4/A >= c = {c}; 1 - e^-F >= {1 - math.exp(-c):.4f}")


# ---------------------------------------------------------------- 2. 2D SU(2) exact
# CHOSEN: 70 SU(2) representations (n = 0..69) in the character sums; t_n falls factorially in n at beta <= 8, so the dropped terms are far below the tolerances read here.
JM = 70


def t2(beta):
    return [iv(n + 1, beta) / iv(1, beta) for n in range(JM)]


def torus2d(t, A, AC=None):
    """Z, the electric weight 1 - Z_-/Z (computed without cancellation) and <W> of area AC."""
    Z = sum(t[n] ** A for n in range(JM))
    el = 2 * sum(t[n] ** A for n in range(1, JM, 2)) / Z
    zr = sum((-1) ** n * t[n] ** A for n in range(JM)) / Z
    W = None
    if AC is not None:
        num = 0.0
        for k in range(JM - 1):
            for j in (k - 1, k + 1):
                # DERIVED: keeps the neighbour index j = k +- 1 inside the truncation 0..JM-1; an index guard.
                if 0 <= j < JM:
                    num += (k + 1) / (j + 1) * t[k] ** AC * t[j] ** (A - AC)
        W = num / (2 * Z)
    return Z, el, zr, W


def section2():
    print("2. 2D SU(2) torus, exact character sums")
    out = {}
    for beta in (1.0, 2.5, 4.0, 8.0):
        t = t2(beta)
        sig = -math.log(t[1])
        # zR <= 1, F_v -> 0 as 2 t_1^A, rate -> sigma
        rows = []
        for L in (2, 4, 8, 12, 16):
            A = L * L
            _, el, zr, _ = torus2d(t, A)
            # DERIVED: Z_- <= Z (docstring: zR <= 1), and the electric weight is a sum of non-negative terms over Z, so it is >= 0.
            assert zr <= 1 and el >= 0
            Fv = -math.log1p(-el)
            rows.append((L, Fv, -math.log(el) / A))
            # CHOSEN: 0.2 relative tolerance on the asymptotic F_v ~ 2 t_1^A, and A < 16 exempts the 2 x 2 torus, where the asymptotic form is not claimed.
            assert abs(Fv / (2 * t[1] ** A) - 1) < 0.2 or A < 16
        print(f"   beta = {beta}: tension -log t_1 = {sig:.4f}; (L, F_v, -log(1-Z_-/Z)/A): "
              + "  ".join(f"({L}, {F:.3g}, {r:.4f})" for L, F, r in rows))
        assert abs(rows[-1][2] - sig) < 0.01 * sig + 0.02
        # Tomboulis-Yaffe on tiling and non-tiling rectangles
        tile_viol, nontile_viol, tile_n, worst = 0, 0, 0, 0.0
        for L in (4, 6, 8, 12):
            A = L * L
            for m in range(1, L):
                for n in range(1, L):
                    _, el, _, W = torus2d(t, A, m * n)
                    rhs = el ** (m * n / A)
                    # DERIVED: the divisibility test m | L, n | L that defines a tiling rectangle; not a magnitude.
                    tile = L % m == 0 and L % n == 0
                    if tile:
                        tile_n += 1
                        worst = max(worst, W / rhs)
                        tile_viol += W > rhs * (1 + 1e-12)
                    else:
                        nontile_viol += W > rhs * (1 + 1e-12)
        print(f"        TY on {tile_n} tiling rectangles (L = 4, 6, 8, 12): violations {tile_viol},"
              f" max W/bound {worst:.4f}; non-tiling rectangles violating it: {nontile_viol}")
        # DERIVED: Tomboulis-Yaffe holds on every tiling rectangle, so the violation count must be 0.
        assert tile_viol == 0
        out[beta] = nontile_viol
        # area law of small loops at large A: W ~ t_1^{mn}
        A = 24 * 24
        for m, n in ((1, 1), (2, 3), (4, 4)):
            _, el, _, W = torus2d(t, A, m * n)
            # CHOSEN: 1e-6 relative tolerance on the area law W = t_1^(mn) for small loops on the 24 x 24 torus, where the finite-torus corrections are powers of t_n^A.
            assert abs(W / t[1] ** (m * n) - 1) < 1e-6
    # DERIVED: the claim is that every beta has at least one non-tiling violation (a count > 0), which is what makes the tiling restriction load-bearing; the counts read 24 and 25.
    assert all(v > 0 for v in out.values())          # the tiling restriction is load-bearing
    print("   small loops on the 24 x 24 torus: W(m, n) = t_1^(mn) to 1e-6 at (1,1), (2,3), (4,4)")
    # 2D U(1), twist angle pi: Z = sum_n t_n^A over n in Z, t_n = I_n/I_0
    for beta in (1.0, 4.0):
        tu = [iv(n, beta) / iv(0, beta) for n in range(80)]
        for L in (4, 16):
            A = L * L
            Z = 1 + 2 * sum(tu[n] ** A for n in range(1, 80))
            el = 4 * sum(tu[n] ** A for n in range(1, 80, 2)) / Z
            # DERIVED: el = 1 - Z_pi/Z lies strictly in (0, 1) when 0 < Z_pi < Z; the bounds of the quantity, not a tolerance.
            assert 0 < el < 1
        print(f"   2D U(1) beta = {beta}: 1 - Z_pi/Z at L = 16 is {el:.3g} (2D U(1) also confines)")


# ---------------------------------------------------------------- 3. 4D MK proxy
def mk_vortex(t, group):
    if group == "SU(2)":
        Z = 1 + float(np.sum(t[1:]))
        el = 2 * float(np.sum(t[1::2])) / Z
    else:
        Z = 1 + 2 * float(np.sum(t[1:]))
        el = 4 * float(np.sum(t[1::2])) / Z
    return el, -math.log1p(-el)


def section3():
    print("3. 4D Migdal-Kadanoff proxy (b = 2, d = 4); an approximation, not the 4D Wilson measure")
    res = {}
    for group, init, step, betas in (
            ("SU(2)", lambda b: np.array([iv(n + 1, b) / iv(1, b) for n in range(ntf.NREP)]),
             ntf.su2_step, (1.0, 2.5, 4.0)),
            ("U(1)", lambda b: np.array([iv(n, b) / iv(0, b) for n in range(ntf.NU1)]),
             ntf.u1_step, (0.5, 2.0, 4.0))):
        for b in betas:
            t = init(b)
            Fs = []
            for k in range(30):
                if abs(t[1]) < ntf.T_FLOOR:
                    break
                Fs.append(mk_vortex(t, group)[1])
                _, t = step(t)
            # DERIVED: the guard against log of zero, not a magnitude.
            rate = [-math.log(F) / 4 ** k for k, F in enumerate(Fs) if F > 0]
            print(f"   {group} beta = {b}: tracked {len(Fs)} steps; F_k: "
                  + " ".join(f"{F:.3g}" for F in Fs[:12])
                  + (f"; -log F_k / 4^k at the last three: " + " ".join(f"{r:.3g}" for r in rate[-3:])))
            res[(group, b)] = Fs
    for b in (1.0, 2.5, 4.0):
        Fs = res[("SU(2)", b)]
        # DERIVED: the flow stops once t_1 < T_FLOOR = 1e-12; the step before reads F ~ 2 t_1, which
        # at beta = 1 is 7.5e-6, so 1e-4 is the bound the tracked flows all meet
        assert Fs[-1] < 1e-4 and all(Fs[k + 1] < Fs[k] for k in range(1, len(Fs) - 1)), (b, Fs)
    for b in (2.0, 4.0):
        Fs = res[("U(1)", b)]
        # CHOSEN: 0.1 as "positive" and 1e-6 as "settled"; the weak-coupling U(1) flows read 8.65 and 18.5, far above 0.1, and agree step to step in every printed digit.
        assert Fs[-1] > 0.1 and abs(Fs[-1] - Fs[-2]) < 1e-6           # settles, positive
    # CHOSEN: 1e-6 as "decayed" for strong-coupling U(1); the read is 1.8e-10, far below it.
    assert res[("U(1)", 0.5)][-1] < 1e-6                               # strong-coupling U(1)
    print("   SU(2): F_k decreasing from step 1 and below 1e-4 at the last tracked step;"
          " U(1) at beta = 2, 4: F_k settles at a positive value; U(1) at beta = 0.5 decays")


def main():
    # CHOSEN: the 10 s run-time budget the module docstring states; the run takes under 1 s.
    run_sections((section1, section2, section3), T0, budget_s=10)


if __name__ == "__main__":
    main()
