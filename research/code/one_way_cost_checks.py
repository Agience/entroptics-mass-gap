"""Checks for `MassGap.OneWayCost`: does the chunk cost run one way, and in which model?

Exact sums, quadrature and closed forms only; no Monte Carlo. Run time under 10 seconds (asserted).

1. The Lean statements on numbers. The confining reading s_k = 4^k s_0 (`Scales 4`, the tension read
   in chunk units) breaks the uncapped `RunsOneWay b` at the first step with b s_k^2 > 3 s_k
   (`tension_not_runsOneWay`) and meets the capped `RunsOneWayTo (3/T) T` at every step
   (`tension_runsOneWayTo`); the lower bound `runsOneWayTo_lower` and the `K` of
   `uniform_steps_of_runsOneWayTo`; the window of `not_runsOneWayTo_of_nonpert`
   (exp(-a/s) <= 6 s^3 / a^3).
2. Migdal-Kadanoff (b = 2, d = 4: bond moving f -> f^4, decimation t_n -> t_n^4) for SU(2), with the
   quadrature of `no_transition_flow_checks.py` (imported, not copied). A model of the RG, not a bound
   on it and not a statement about the 4D Wilson measure. Read: the running coefficient
   b_k = (s_{k+1} - s_k)/s_k^2 of s = -log t_F along Wilson starts and along the heat-kernel family
   (the best constant of `BondMoveCost` on each), below and above T = kpCost.
3. Migdal-Kadanoff for U(1), by exact Fourier convolution of the coefficient sequence (no
   quadrature). On the Villain family c_n = e^{-tau n^2} the step is known in closed form through
   Poisson summation over the 3-dimensional lattice {k in Z^4 : sum k = 0}; its leading term is
   s' - s = 32 exp(-3 pi^2 / (4 s)). Read: the increment along Wilson starts against that form; the
   number of steps the Villain family needs to reach s = 1 (an estimate: the integral of ds / (s' - s)
   along the family); the running coefficient tending to 0 as s -> 0.
"""
from __future__ import annotations

import math
import os
import sys
import time

import numpy as np
from scipy.special import iv

T0 = time.time()
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import no_transition_flow_checks as ntf  # noqa: E402  (quadrature of the MK step for SU(2))
from check_driver import run_sections  # noqa: E402

Z_ENT = ntf.Z_ENT
T_KP = ntf.kp_cost(Z_ENT)


# ---------------------------------------------------------------- 1. Lean statements on numbers
def section1():
    print("1. the Lean statements on numbers")
    T = T_KP
    for s0 in (0.05, 0.25, 1.0):
        s = [s0 * 4 ** k for k in range(30)]
        for b in (0.01, 0.15, 1.0):
            # uncapped: first k with s_k + b s_k^2 > s_{k+1} = 4 s_k, i.e. b s_k > 3
            kbad = next(k for k in range(29) if s[k] + b * s[k] ** 2 > s[k + 1])
            # DERIVED: s_k + b s_k^2 > 4 s_k is b s_k > 3 (s_k > 0), the failure condition of
            # `tension_not_runsOneWay`; 3 = 4 - 1 from the doubling s_{k+1} = 4 s_k.
            assert b * s[kbad] > 3 and all(b * s[k] <= 3 for k in range(kbad))
        bc = 3 / T
        ok = all(min(s[k] + bc * s[k] ** 2, T) <= s[k + 1] + 1e-12 for k in range(29))
        assert ok
    print(f"   s_k = 4^k s_0: uncapped RunsOneWay b fails at the first k with b s_k > 3 (every b, s_0"
          f" tried); capped RunsOneWayTo (3/T) T holds at every step, T = kpCost = {T:.4f}")
    # runsOneWayTo_lower and the K of uniform_steps_of_runsOneWayTo on the extremal sequence
    for b, s0 in ((0.15, 0.4), (0.05, 0.2)):
        K = math.ceil((T - s0) / (b * s0 ** 2))
        y = s0
        for k in range(K + 5):
            assert y >= min(s0 + k * b * s0 ** 2, T) - 1e-12
            y = min(y + b * y ** 2, T)
        print(f"   b = {b}, s_0 = {s0}: the proof's K = {K}; min(s_k + b s_k^2, T) reaches T at step"
              f" {_capped_steps(s0, b, T)}")
    # exp(-a/s) <= 6 s^3/a^3
    for a in (0.5, 3 * math.pi ** 2 / 4):
        for s in np.linspace(0.01, 5, 200):
            assert math.exp(-a / s) <= 6 * s ** 3 / a ** 3 + 1e-300
    print("   exp(-a/s) <= 6 s^3/a^3 on a grid of s in [0.01, 5], a = 0.5 and 3 pi^2/4")


def _capped_steps(s0, b, T):
    k, y = 0, s0
    while y < T:
        k, y = k + 1, min(y + b * y ** 2, T)
    return k


# ---------------------------------------------------------------- 2. SU(2) Migdal-Kadanoff
# CHOSEN: an upper limit on steps; every Wilson start read (beta <= 6) stops at ntf.T_FLOOR first,
# after at most 25 steps.
def su2_flow(t, steps=40):
    s = []
    for _ in range(steps):
        if abs(t[1]) < ntf.T_FLOOR:
            break
        s.append(-math.log(t[1]))
        _, t = ntf.su2_step(t)
    return s


def su2_heat(s):
    """Heat-kernel SU(2) weight with t_F = e^{-s}: t_n = exp(-tau n(n+2)/4), tau = 4 s / 3."""
    tau = 4 * s / 3
    return np.array([math.exp(-tau * n * (n + 2) / 4) for n in range(ntf.NREP)])


def section2():
    print("2. SU(2), Migdal-Kadanoff (a model, not the 4D Wilson RG)")
    T = T_KP
    res = {}
    for beta in (1.0, 2.5, 4.0, 6.0):
        t = np.array([iv(n + 1, beta) / iv(1, beta) for n in range(ntf.NREP)])
        s = su2_flow(t)
        bk = [(s[k + 1] - s[k]) / s[k] ** 2 for k in range(len(s) - 1)]
        below = [bk[k] for k in range(1, len(bk)) if s[k] < T]
        above = [(s[k], bk[k]) for k in range(len(bk)) if s[k] >= T]
        capped = all(min(s[k] + min(below) * s[k] ** 2, T) <= s[k + 1] + 1e-12
                     for k in range(1, len(s) - 1))
        res[beta] = (bk, below, above, capped)
        print(f"   Wilson beta = {beta}: s_0 = {s[0]:.3f}, b_0 = {bk[0]:+.4f}; min b_k over k >= 1 with"
              f" s_k < T: {min(below):.4f} ({len(below)} steps); capped RunsOneWayTo (that b) T from"
              f" step 1: {capped}; above T: b_k = " + " ".join(f"{x:.3f}@s={y:.1f}" for y, x in above[-3:]))
    # heat-kernel family: one MK step from each, the best constant of BondMoveCost on the family
    grid = np.linspace(0.02, T, 60)
    bh = []
    for s in grid:
        _, t2 = ntf.su2_step(su2_heat(s))
        bh.append((-math.log(t2[1]) - s) / s ** 2)
    bh = np.array(bh)
    print(f"   heat-kernel family, s in [0.02, {T:.2f}]: one-step running coefficient min {bh.min():.4f}"
          f" (at s = {grid[bh.argmin()]:.2f}), at s = 0.02: {bh[0]:.4f}, at s = T: {bh[-1]:.4f}")
    # large s: the strong law s' = 4 (s - log 4) gives b_k = (3 s - 4 log 4)/s^2 -> 0, so no b > 0
    # serves every step (the uncapped form fails; `not_runsOneWay_of_linear`)
    nlaw = 0
    for beta in res:
        for y, x in res[beta][2]:
            nlaw += 1
            # CHOSEN: tolerance on the strong-end law b = (3 s - 4 log 4)/s^2 above T; the read is
            # 2.5e-6, far inside it.
            assert abs(x - (3 * y - 4 * math.log(4)) / y ** 2) < 0.03
    print(f"   above T the running coefficient follows (3 s - 4 log 4)/s^2 (checked at {nlaw} steps),"
          f" which tends to 0: at s = 30, 100 it is {(90 - 4 * math.log(4)) / 900:.3f},"
          f" {(300 - 4 * math.log(4)) / 1e4:.4f}")
    # DERIVED: the non-emptiness guard, so the law check above ran on at least one step; not a magnitude.
    assert nlaw >= 1
    # assertions (on the model only)
    for beta in (1.0, 2.5, 4.0, 6.0):
        bk, below, above, capped = res[beta]
        # CHOSEN: a positive lower bound on b_k below T; the reads are 0.263, 0.169, 0.156, 0.151, so
        # beta = 6 sits within a factor 1.5 of the cut (and min b_k falls as beta grows).
        assert min(below) > 0.1 and capped
    for beta in (2.5, 4.0, 6.0):
        # DERIVED: b_0 < 0 is the sign test "step 0 falls", not a magnitude.
        assert res[beta][0][0] < 0                      # step 0 out of the Wilson action falls
    # CHOSEN: the same 0.1 lower bound on the heat-kernel family; the read is 0.167 (at s = 0.02).
    assert bh.min() > 0.1
    return res, bh


# ---------------------------------------------------------------- 3. U(1) Migdal-Kadanoff
# CHOSEN: U(1) coefficient cutoff n < 60; the dropped terms are below double precision for the Wilson
# betas (<= 4) and Villain taus (>= 0.6) read.
NU = 60


def u1_step_exact(t):
    """One MK step on U(1) by exact convolution: t_n (n >= 0, t_0 = 1) -> (c^{*4}_n / c^{*4}_0)^4."""
    c = np.concatenate([t[:0:-1], t])                  # c_{-N+1..N-1}
    c4 = np.convolve(np.convolve(c, c), np.convolve(c, c))
    mid = len(c4) // 2
    tm = c4[mid:mid + len(t)] / c4[mid]
    return tm ** 4


# CHOSEN: Poisson sum truncated to |m_i| <= 4; the largest dropped term (|w|^2 = 12.75) is ~e^{-84} at tau = 1.5, and
# section 3 checks the form against direct convolution to 1e-6 relative.
def villain_R(tau, M=4):
    """Poisson form of R = c_1(f^4) e^{tau/4} / c_0(f^4) for f Villain, c_n = e^{-tau n^2}:
    R = sum_m e^{-pi^2 |w|^2 / tau} cos(pi S / 2) / sum_m e^{-pi^2 |w|^2 / tau},
    m in Z^3 x {0}, S = m_1 + m_2 + m_3, |w|^2 = |m|^2 - S^2/4. Returns (1 - R, exact)."""
    r = np.arange(-M, M + 1)
    m1, m2, m3 = np.meshgrid(r, r, r, indexing="ij")
    S = m1 + m2 + m3
    w2 = m1 ** 2 + m2 ** 2 + m3 ** 2 - S ** 2 / 4
    e = np.exp(-math.pi ** 2 * w2 / tau)
    num = float(np.sum(e * np.cos(math.pi * S / 2)))
    den = float(np.sum(e))
    # 1 - R = sum e (1 - cos) / den, computed without cancellation
    return float(np.sum(e * (1 - np.cos(math.pi * S / 2)))) / den, num / den


def villain_ds(s):
    """s' - s on the Villain family at s = tau: -4 log R."""
    one_minus_R, _ = villain_R(s)
    return -4 * math.log1p(-one_minus_R)


def section3():
    print("3. U(1), Migdal-Kadanoff by exact convolution (a model, not the 4D Wilson RG)")
    A = 3 * math.pi ** 2 / 4
    # the Poisson form against direct convolution on the Villain family, where floats resolve it
    for tau in (0.6, 1.0, 1.5):
        t = np.exp(-tau * np.arange(NU) ** 2)
        ds_direct = -math.log(u1_step_exact(t)[1]) - tau
        ds_pois = villain_ds(tau)
        lead = 32 * math.exp(-A / tau)
        print(f"   Villain tau = {tau}: s' - s direct {ds_direct:.6e}, Poisson {ds_pois:.6e},"
              f" leading 32 e^(-3 pi^2/(4 s)) {lead:.6e}")
        assert abs(ds_direct - ds_pois) <= 1e-6 * ds_pois + 1e-13
        # CHOSEN: compare with the leading form only at tau <= 1, the range on which the bound in the
        # DERIVED note below is evaluated; tau = 1.5 is printed, not asserted.
        if tau <= 1.0:
            # DERIVED: the next Poisson terms are e^{-pi^2/tau} against e^{-3pi^2/(4tau)}, relative
            # size 6/8 e^{-pi^2/(4 tau)} <= 0.07 at tau <= 1, plus the denominator's 8 e^{-3pi^2/(4tau)}
            assert abs(ds_pois - lead) <= 0.15 * lead
    # Wilson starts: increment per step against the leading form
    out = {}
    for beta in (0.5, 1.0, 2.0, 4.0):
        t = np.array([iv(n, beta) / iv(0, beta) for n in range(NU)])
        s, reached = [], None
        for k in range(60):
            # CHOSEN: track while t_F > 1e-12 (s < 27.6), the same floor as ntf.T_FLOOR.
            if t[1] < 1e-12:
                break
            s.append(-math.log(t[1]))
            if reached is None and s[-1] >= T_KP:
                reached = k
            t = u1_step_exact(t)
        ds = [s[k + 1] - s[k] for k in range(len(s) - 1)]
        # CHOSEN: read the increment from step 12 on; the Wilson weight relaxes to the near-Villain
        # trajectory by a factor ~1/16 per step, so by step 12 the transient is below 1e-12
        tail = [(s[k], ds[k], 32 * math.exp(-A / s[k])) for k in range(12, len(ds))]
        out[beta] = (s, ds, reached, tail)
        msg = f"   Wilson beta = {beta}: s_0 = {s[0]:.4f}, s_12 = {s[min(12, len(s) - 1)]:.6f},"
        msg += f" s_last = {s[-1]:.6f};"
        if reached is not None:
            msg += f" s >= kpCost at step {reached}"
        else:
            # DERIVED: ds[k] < 0 is the sign test "s falls", not a magnitude.
            # CHOSEN: beta < 4 only selects the printed message; at beta = 4 the increments are at rounding.
            neg = (f"s falls up to step {max(k for k in range(len(ds)) if ds[k] < 0)}" if beta < 4
                   else "s falls, then moves by rounding only (|increment| < 1e-15)")
            msg += (f" never reaches kpCost in {len(s)} steps; {neg},"
                    f" increment at the last step {ds[-1]:.3e} (leading Villain form"
                    f" {tail[-1][2]:.3e})")
        print(msg)
    # running coefficient on the Villain family -> 0 as s -> 0; steps needed to reach s = 1
    for s in (0.5, 0.264, 0.128, 0.05):
        # CHOSEN: below s = 0.09 the leading form 32 e^{-A/s} is used; it sits between the read values
        # 0.128 and 0.05, where the two forms agree to relative ~e^{-pi^2/(4s)} (~1e-12 at the cut).
        ds = villain_ds(s) if s > 0.09 else 32 * math.exp(-A / s)
        print(f"   Villain s = {s}: s' - s = {ds:.3e}, running coefficient (s'-s)/s^2 = {ds / s ** 2:.3e}")
    for s0 in (0.5, 0.264, 0.128):
        # number of steps along the family: integral of ds / (32 e^{-A/s}), closed form to leading
        # order: the integral is dominated by its lower end, (s0^2 / (32 A)) e^{A / s0}
        xs = np.linspace(s0, 1.0, 20001)
        integrand = np.exp(A / xs - A / s0) / 32
        n_rel = float(np.sum((integrand[1:] + integrand[:-1]) / 2 * np.diff(xs)))
        log10_n = math.log10(n_rel) + (A / s0) / math.log(10)
        print(f"   Villain from s_0 = {s0}: about 10^{log10_n:.1f} steps to reach s = 1")
    # assertions on the model
    assert out[0.5][2] is not None                     # strong coupling: reaches kpCost
    for beta in (1.0, 2.0, 4.0):
        s, ds, reached, tail = out[beta]
        assert reached is None
        assert all(d > -1e-13 for d in ds[12:])         # one way (to rounding) after the transient
        # CHOSEN: 1e-3 sits two decades under the SU(2) b_k (>= 0.15); the largest read is 1.1e-4 (beta = 1).
        assert max(d / x ** 2 for d, x in zip(ds[12:], s[12:])) < 1e-3   # no b of the SU(2) size
        assert all(d < 1e-3 * x ** 2 for d, x in zip(ds[12:], s[12:]))
    for beta in (1.0, 2.0):
        # the increment is of the nonperturbative size: a fixed fraction of 32 e^{-3pi^2/(4s)}
        # CHOSEN: "a fixed fraction" read as the band (0.1, 1); the ratios are 0.52 (beta = 1) and 0.19
        # (beta = 2), the latter within a factor 1.9 of the lower edge.
        assert all(0.1 < d / l < 1 for (_, d, l) in out[beta][3])
    return out


def main():
    # CHOSEN: the 10 s run-time budget the module docstring states; the run takes under 1 s.
    run_sections((section1, section2, section3), T0, budget_s=10)


if __name__ == "__main__":
    main()
