"""Unit checks for `MassGap.NoTransition`: the author's three reasons why the edge cost cannot fade between
the coarse and the fine end of the line, read on cases computable in seconds.

1. Running is one-way (`oneLoop_coupling_strictMonoOn`, `u1_not_oneWayRunning`). The one-loop coupling
   g^2(r) = 1/invCoup(r), invCoup(r) = u0 - 2 b0 log(r/r0), strictly increases on (0, 1/Lambda) for
   b0 > 0 and is constant at b0 = 0. The force of a Cornell potential V = s r - c/r is nonincreasing in
   r (as concavity requires, Bachas 1986; cited, the script checks only the model potential) while r^2 V'(r) increases; for the Coulomb potential (the free photon)
   r^2 V'(r) is constant: it passes the weak (nondecreasing) form and fails the strict form.
2. The line form of link 1 (`u1_oneWay_no_floor`, `oneWay_not_sufficient`, `oneWay_allows_jump`): the
   U(1) step profile and fade(k) = 1/(k+1) are antitone with no floor; a finite jump keeps a floor.
3. Links 1 and 3 through the running (`invCoup_eq_of_rStar`, `af_line`, `coupling_at_observer_const`):
   for b0 != 0, on the line u0 = us + 2 b0 log(L/a) the transmuted length is L and the coupling at the
   observer's distance is the same at every spacing. At b0 = 0 the transmuted length is undefined; the
   U(1) contrast is the constant coupling of section 1.
4. Link 3 (`floor_iff_pos_and_tail`, `oneScaleRatio_iff`): a floor is pointwise positivity plus a
   tail floor; xi <= D l at every zoom is the floor 1/D on l/xi.
5. Group facts (`center_ZN_top`, `center_U1_top`, `center_SU_ne_top`, `fundamental_edge_cannot_end`):
   Z_N and U(1) commute; for SU(N), N = 2..6, the signed transposition fails to commute with the phase
   element; omega * 1 has determinant 1; the centre phase omega^k is 1 iff N | k.

Not reached: the fine-end limit of the gap ratio of 4D SU(N) (`NoFadeAtFineEnd`). No 10-second
computation decides it.

Each section runs in under 10 seconds; the script asserts it.
"""
import math

import numpy as np

from fine_end_checks import BUDGET, timed  # noqa: E402,F401  (the per-section wall-clock ceiling and its timer)

# CHOSEN: floating-point tolerance for identities, far above double rounding at these sizes.
TOL = 1e-12


def inv_coup(b0, r0, u0, r):
    return u0 - 2.0 * b0 * math.log(r / r0)


def r_star(b0, r0, u0, us):
    # DERIVED: the guard against division by 2 b0 below; r* is defined only for b0 != 0, not a magnitude.
    assert b0 != 0, "the transmuted length is defined only for b0 != 0"
    return r0 * math.exp((u0 - us) / (2.0 * b0))


def section_running():
    print("1. running is one-way")
    b0 = 11 * 3 / (48 * math.pi ** 2)  # DERIVED: one-loop b0 = 11 N/(48 pi^2) at N = 3.
    r0, u0 = 1.0, 2.0  # CHOSEN: reference distance and inverse coupling, any positive values.
    rL = r_star(b0, r0, u0, 0.0)
    rs = np.linspace(rL * 1e-3, rL * (1 - 1e-6), 2000)
    g2 = np.array([1.0 / inv_coup(b0, r0, u0, r) for r in rs])
    # DERIVED: strict increase of g^2 is the sign test of `oneLoop_coupling_strictMonoOn`, not a magnitude.
    assert np.all(np.diff(g2) > 0), "one-loop g^2 must increase strictly on (0, 1/Lambda)"
    # DERIVED: g^2 > 0 below 1/Lambda, where invCoup > 0; a sign test, not a magnitude.
    assert np.all(g2 > 0)
    g2_u1 = np.array([1.0 / inv_coup(0.0, r0, u0, r) for r in rs])
    assert np.all(np.abs(np.diff(g2_u1)) < TOL), "b0 = 0: g^2 constant"
    print(f"   SU(3) one loop: g^2 rises from {g2[0]:.4f} to {g2[-1]:.3e} below 1/Lambda = {rL:.4f}")
    # Cornell and Coulomb: force and r^2 * force.
    s, c = 1.0, 0.3  # CHOSEN: Cornell tension and Coulomb coefficient (typical units sigma = 1).
    r = np.linspace(0.05, 10.0, 4000)
    F_cornell = s + c / r ** 2
    F_coulomb = c / r ** 2
    # DERIVED: nonincreasing force is the sign of successive differences, not a magnitude.
    assert np.all(np.diff(F_cornell) <= 0), "force nonincreasing (Bachas concavity)"
    # DERIVED: strict increase of r^2 F is the sign of successive differences, not a magnitude.
    assert np.all(np.diff(r ** 2 * F_cornell) > 0), "r^2 F increases for Cornell"
    assert np.all(np.abs(np.diff(r ** 2 * F_coulomb)) < TOL), "r^2 F constant for Coulomb"
    print("   Cornell: F falls, r^2 F rises; Coulomb (free photon): r^2 F constant -> weak form passes, strict fails")


def section_line():
    print("2. link 1 on the line")
    K = 10000  # CHOSEN: number of zooms read; any large value.
    k = np.arange(K)
    fade = 1.0 / (k + 1.0)
    # DERIVED: antitone (differences <= 0) and positive (1/(k+1) > 0) are sign tests, not magnitudes.
    assert np.all(np.diff(fade) <= 0) and np.all(fade > 0)
    # CHOSEN: a finite read can only show the minimum falls below a level; at K = 10000 it is 1e-4,
    # a factor 10 under the 1e-3 cut.
    assert fade.min() < 1e-3, "fade has no floor"
    k1 = 50  # CHOSEN: the zoom of the U(1) transition in the step profile.
    u1 = np.where(k < k1, 1.0, 0.0)
    # DERIVED: antitone is differences <= 0; min 0.0 is the step profile's value past k1 (no floor).
    assert np.all(np.diff(u1) <= 0) and u1.min() == 0.0
    jump = np.where(k < k1, 2.0, 1.0)
    # DERIVED: antitone is differences <= 0; min 1.0 is the jump profile's lower value (the floor it keeps).
    assert np.all(np.diff(jump) <= 0) and jump.min() == 1.0
    # under monotonicity the infimum is the fine-end value
    assert abs(fade.min() - fade[-1]) < TOL
    print(f"   fade: antitone, positive, min {fade.min():.1e}; U(1) step: antitone, min 0; jump: floor 1")


def section_line_of_constant_physics():
    print("3. links 1 and 3 through the running")
    b0 = 11 * 3 / (48 * math.pi ** 2)  # DERIVED: as in section 1.
    us, L, r_obs = 0.5, 1.0, 0.3  # CHOSEN: target inverse coupling, transmuted length, observer distance.
    vals = []
    for p in range(0, 30):
        a = 2.0 ** -p
        u0 = us + 2 * b0 * math.log(L / a)
        assert abs(r_star(b0, a, u0, us) - L) < 1e-9 * L, "af_line"
        lhs = inv_coup(b0, a, u0, r_obs)
        rhs = us - 2 * b0 * math.log(r_obs / r_star(b0, a, u0, us))
        # CHOSEN: tolerance on an exact identity (`invCoup_eq_of_rStar`), loose against double rounding
        # of logs up to log 2^29.
        assert abs(lhs - rhs) < 1e-9, "invCoup_eq_of_rStar"
        vals.append(lhs)
    spread = max(vals) - min(vals)
    # CHOSEN: tolerance on a spread that is exactly zero (`coupling_at_observer_const`); the read is 4.4e-16.
    assert spread < 1e-9, "coupling at the observer's distance is the same at every spacing"
    print(f"   30 spacings 1 .. 2^-29: coupling at observer {vals[0]:.6f}, spread {spread:.1e}; bare u0 grows")


def section_one_scale():
    print("4. link 3")
    K = 2000  # CHOSEN: number of zooms read.
    k = np.arange(K)
    rng = np.random.default_rng(0)  # CHOSEN: seed; the check holds for every positive sequence.
    f = np.exp(rng.normal(size=K))
    Kt = 300  # CHOSEN: tail start.
    floor = min(f[:Kt].min(), f[Kt:].min())
    # DERIVED: floor > 0 is the pointwise positivity of exp, the first half of `floor_iff_pos_and_tail`.
    assert floor == f.min() and floor > 0
    xi = 1.0 + k / 10.0
    ell = 2.0 + k / 10.0
    D = (xi / ell).max()
    ratio = (1 / xi) / (1 / ell)
    assert abs(ratio.min() - 1 / D) < TOL, "oneScaleRatio_iff: floor = 1/D"
    xi_bad = (1.0 + k / 10.0) ** 2
    # CHOSEN: the level a finite read must fall below to show no floor; l/xi_bad ~ 10/k reads 0.005 at
    # K = 2000, only a factor 2 under the cut (K below about 1000 would fail it).
    assert ((1 / xi_bad) / (1 / ell)).min() < 0.01, "xi growing faster than l: no floor"
    print(f"   tail + initial min = global min; floor of l/xi = 1/D = {1 / D:.4f}")


def section_group():
    print("5. group facts")
    for N in range(2, 7):
        # Z_N: abelian
        assert all((a + b) % N == (b + a) % N for a in range(N) for b in range(N))
        w = np.exp(2j * np.pi / N)
        Z = w * np.eye(N)
        # CHOSEN: tolerance on det(omega * 1) = omega^N = 1; the read is below 1e-15.
        assert abs(np.linalg.det(Z) - 1) < 1e-12
        S = np.zeros((N, N), complex)
        perm = list(range(N)); perm[0], perm[1] = 1, 0
        for i, j in enumerate(perm):
            S[j, i] = 1.0
        # DERIVED: index 0 carries the sign -1 that cancels the transposition's det -1, so det S = 1.
        S = S @ np.diag([-1.0 if j == 0 else 1.0 for j in range(N)])
        # CHOSEN: tolerance on det S = 1, which the construction gives exactly (the read is 0).
        assert abs(np.linalg.det(S) - 1) < 1e-12 and np.allclose(S @ S.conj().T, np.eye(N))
        # DERIVED: indices 0 and 1 (the swapped pair) carry phases i and -i, so det P = 1 and P is not central.
        P = np.diag([1j if j == 0 else (-1j if j == 1 else 1.0) for j in range(N)])
        # CHOSEN: any cut in (0, 2 sqrt 2) separates; the commutator norm is 2 sqrt 2 at every N read.
        assert np.linalg.norm(S @ P - P @ S) > 1.0, "signed transposition is not central"
        for kk in range(0, 3 * N):
            # CHOSEN: 1e-9 separates omega^k = 1 (rounding) from |omega^k - 1| >= 2 sin(pi/N) >= 1 at N <= 6.
            # DERIVED: kk % N == 0 is the divisibility N | k of the statement, not a magnitude.
            assert (abs(w ** kk - 1) < 1e-9) == (kk % N == 0)
    th = np.linspace(0, 2 * np.pi, 50)
    assert all(abs(np.exp(1j * a) * np.exp(1j * b) - np.exp(1j * b) * np.exp(1j * a)) < TOL for a in th for b in th)
    print("   Z_N, U(1) abelian; SU(N) N=2..6 centre proper; omega^k = 1 iff N | k")


if __name__ == "__main__":
    timed("running", section_running)
    timed("line", section_line)
    timed("line of constant physics", section_line_of_constant_physics)
    timed("one scale", section_one_scale)
    timed("group", section_group)
    print("all checks passed")
