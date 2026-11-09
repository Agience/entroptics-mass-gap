"""Unit checks for `MassGap.ApertureInvariance`: is the law of the aperture's readings at fixed physical
scale the same at every zoom?

The Lean module proves the transfer: if the zoom-k laws of the readings are within a fixed factor of a
reference law that clusters (`ApertureInvariant`), they cluster at the same physical rate at every zoom
(`gap_of_apertureInvariant`), and a confined reference with a protected power sector at some zoom
excludes invariance (`not_apertureInvariant_of_powerSector`). With the observer as the constant, the
gap is a ratio to the observer's own reading and holding that reading fixed is a choice of unit
(`observer_constant_vacuous`, `u1_line_does_not_fix_ratio`). This script reads the invariance on cases
computable in seconds:

1. 2D SU(2), exact by characters (Wilson action, g = 1, beta = 4/a^2). The reading is the holonomy U
   of one cell of physical area A. Its law (a class function on SU(2)) is fixed by the normalised
   character moments m_j = E[chi_j(U)]/d_j = (I_{2j+1}(beta)/I_1(beta))^(A/a^2); the continuum law is
   the heat kernel, m_j = exp(-j(j+1) A/2). Readings of disjoint cells are independent at every zoom
   (2D, infinite volume), so their connected correlation is 0 at every zoom: exactly invariant.
   Asserted: the moments approach the continuum law, the log-deviation falls like a^2, and one factor
   C bounds every moment ratio across the whole ladder of zooms, the coarse end included.
2. 2D U(1), exact (e = 1, beta = 1/a^2): m_q = (I_q(beta)/I_0(beta))^(A/a^2) -> exp(-q^2 A/2). Also
   invariant: 2D U(1) has no transition and confines at every beta.
3. 4D U(1), no exact test of the transition. Coarse end: strong coupling, leading order, W(R,T) = u^(RT),
   u = I_1/I_0(beta): Creutz ratio chi(R) = -log u at every R (area law). Fine end: the free photon on
   16^4 (direct mode sums, no FFT): chi(R) falls like 1/R^2 (perimeter law plus Coulomb). The observer's
   unit drops out of the ratio chi(2R)/chi(R): 1 at the coarse end, about 1/4 at the fine end. Holding
   the observer's reading chi(R) fixed by the choice of unit leaves this ratio unchanged; the two ends
   are not one law up to a unit, which is what `ApertureInvariant` excludes for a theory with a
   transition between its ends.
4. Where the coarse end sits (`dyBeta_not_strong`: every zoom of the sequence has beta >= 1). The
   two-loop spacing aRun(N=2, beta) = aRunStd(2 beta), extended below beta = 1, is about 47 times
   coarser at beta = 1/20 than at beta = 1, but it is not monotone: it peaks at beta ~ 0.078 and falls
   to 0 as beta -> 0, and beta = 1/20 is on the falling side. The two-loop map gives no unit at the
   strong-coupling end; the unit there is the observer's.

Not reached: 4D SU(N), invariance of the reading law from beta <= 1/20 to beta -> infinity (no phase
transition along the path). No 10-second computation decides it.

Each section runs in under 10 seconds; the script asserts it.
"""
import math
import os
import sys
import time

import numpy as np
from scipy.special import ive

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from non_abelian_forget_checks import creutz, photon_G_plane, photon_wilson  # noqa: E402

# CHOSEN: a run-time budget in seconds, not a result; it decides only whether a section is too slow.
BUDGET = 10.0  # CHOSEN: the per-section wall-clock ceiling from the task brief, in seconds.
# CHOSEN: the cell's physical area; with it A/a^2 is an integer on the ladder PS. Any positive value works.
AREA = 1.0  # CHOSEN: the physical area of the aperture's cell, in units g = 1 (any positive value).
PS = range(0, 7)  # CHOSEN: zooms a = 2^-p, p = 0..6 (a = 1 to 1/64); A/a^2 is then an integer.


def timed(name, fn):
    t0 = time.perf_counter()
    out = fn()
    dt = time.perf_counter() - t0
    print(f"   [{name}: {dt:.2f} s]")
    assert dt < BUDGET, f"{name} took {dt:.1f} s"
    return out


def ratio_I(n_top, n_bot, beta):
    """I_{n_top}(beta) / I_{n_bot}(beta), overflow-free (the exponential scalings cancel)."""
    return ive(n_top, beta) / ive(n_bot, beta)


def ladder(moment, cont, labels):
    """Log-deviations of the moments from the continuum law along the zoom ladder."""
    rows = []
    for p in PS:
        a = 2.0 ** -p
        devs = [math.log(moment(lab, a)) - math.log(cont(lab)) for lab in labels]
        rows.append((a, devs))
    return rows


def report(rows, labels, name):
    print(f"   {name}: log(m(a)/m_cont) per moment")
    for a, devs in rows:
        print(f"     a = {a:<9.6g} " + "  ".join(f"{lab}:{d:+.2e}" for lab, d in zip(labels, devs)))
    dmax = [max(abs(d) for d in devs) for _, devs in rows]
    slopes = [math.log(dmax[i] / dmax[i + 1]) / math.log(2) for i in range(len(dmax) - 1)]
    C = math.exp(max(max(abs(d) for d in devs) for _, devs in rows))
    print(f"     max |dev| per zoom: " + ", ".join(f"{d:.2e}" for d in dmax))
    print(f"     local order log2(dev(a)/dev(a/2)): " + ", ".join(f"{s:.2f}" for s in slopes))
    print(f"     one factor C over the whole ladder (coarse end included): C = {C:.4f}")
    return dmax, slopes, C


def section1():
    print("1. 2D SU(2): holonomy law of a fixed physical cell, exact by characters")
    js = [0.5, 1.0, 1.5, 2.0, 2.5, 3.0]

    def run():
        def moment(j, a):
            beta = 4.0 / a ** 2
            return ratio_I(int(round(2 * j + 1)), 1, beta) ** (AREA / a ** 2)
        return ladder(moment, lambda j: math.exp(-j * (j + 1) * AREA / 2), js)

    rows = timed("2D SU(2) moments", run)
    dmax, slopes, C = report(rows, [f"j={j:g}" for j in js], "SU(2)")
    assert all(dmax[i + 1] < dmax[i] for i in range(len(dmax) - 1)), "approach is not monotone"
    # CHOSEN: closeness cut at the finest zoom a = 1/64, where the read is 1.8e-4 (7.3e-4 at a = 1/32,
    # 2.9e-3 at a = 1/16); any cut from about 2e-4 to 3e-3 passes the same ladder.
    assert dmax[-1] < 1e-3, "fine end not at the continuum law"
    # DERIVED: 2.0 is the order O(a^2) of the approach named in the docstring. CHOSEN: the 0.1 band
    # around it; the read is 2.00, and an O(a) approach (1.0) lies far outside it.
    assert abs(slopes[-1] - 2.0) < 0.1, "approach is not O(a^2)"
    # CHOSEN: a ceiling on the one factor C; the read is 1.71. Invariance asks only that C be finite.
    assert C < 10.0, "no fixed factor over the ladder"
    print("   connected correlation of two disjoint cells: 0 at every zoom (independent in 2D)")
    return dmax, C


def section2():
    print("2. 2D U(1): holonomy law of a fixed physical cell, exact (no transition in 2D)")
    qs = [1, 2, 3, 4]

    def run():
        def moment(q, a):
            beta = 1.0 / a ** 2
            return ratio_I(q, 0, beta) ** (AREA / a ** 2)
        return ladder(moment, lambda q: math.exp(-q * q * AREA / 2), qs)

    rows = timed("2D U(1) moments", run)
    dmax, slopes, C = report(rows, [f"q={q}" for q in qs], "U(1)")
    assert all(dmax[i + 1] < dmax[i] for i in range(len(dmax) - 1))
    # CHOSEN: the same three cuts as section 1 (1e-3, the 0.1 band around order 2.0, C < 10); the
    # reads are 9.8e-4, 2.00 and 6.44. The first sits just inside its cut.
    assert dmax[-1] < 1e-3 and abs(slopes[-1] - 2.0) < 0.1 and C < 10.0
    return dmax, C


def section3():
    print("3. 4D U(1): coarse (strong coupling) vs fine (free photon) at the same physical aperture")

    def run():
        L, rmax = 16, 7
        G, d = photon_G_plane(L, rmax)
        W = {}
        for R in range(0, 6):
            for T in range(0, 6):
                # DERIVED: a loop of zero extent is the empty loop, W = 1; a test of the label, not a magnitude.
                W[(R, T)] = 1.0 if (R == 0 or T == 0) else photon_wilson(G, d, R, T)
        return W

    W = timed("4D free photon loops on 16^4", run)
    chi = {R: creutz(W, R) for R in range(2, 6)}
    beta_s = 0.5  # CHOSEN: a strong coupling; at leading order every beta gives the same ratio 1.
    u = ratio_I(1, 0, beta_s)
    chi_s = -math.log(u)
    r_fine = chi[4] / chi[2]
    print(f"   coarse end, leading order, beta = {beta_s}: chi(R) = -log u = {chi_s:.4f} at every R;"
          f" chi(4)/chi(2) = 1")
    for R in range(2, 6):
        print(f"   fine end (photon): chi({R}) = {chi[R]:.5f}   R^2 chi = {R * R * chi[R]:.4f}")
    print(f"   fine end: chi(4)/chi(2) = {r_fine:.4f} (Coulomb 1/R^2 would give 0.25)")
    for R in (2, 3, 4, 5):
        lw = -math.log(W[(R, R)])
        print(f"   photon -log W({R},{R}): /perimeter = {lw / (4 * R):.4f}, /area = {lw / R ** 2:.4f};"
              f" strong coupling /area = {chi_s:.4f}")
    # The observer holds chi(2) fixed by the unit a: chi_phys(2) = chi(2)/a^2 = r0. The unit-free ratio
    # chi(4)/chi(2) is untouched by that choice and differs between the ends.
    # CHOSEN: a cut between the coarse end's ratio 1 and Coulomb's 0.25; the read is 0.164.
    assert r_fine < 0.5, "photon Creutz ratio does not fall"
    assert all(chi[R + 1] < chi[R] for R in range(2, 5))
    print("   verdict: one reading held fixed, the ratio reading differs (1 vs %.2f): the two ends are"
          " not one law up to a unit" % r_fine)
    return r_fine


def a_run_std(N, beta):
    b = 24 * math.pi ** 2 * beta / (11 * N ** 2)
    return b ** (51 / 121) * math.exp(-(12 * math.pi ** 2 * beta) / (11 * N ** 2))


def section4():
    print("4. The strong-coupling region on the two-loop line")
    a_s = a_run_std(2, 2 * (1 / 20))
    a_1 = a_run_std(2, 2 * 1.0)
    bmax = 11 * 4 * (51 / 121) / (12 * math.pi ** 2) / 2  # argmax of aRun(2, .) in beta
    print(f"   aRun(2, 1/20) = {a_s:.4f}, aRun(2, 1) = {a_1:.4f}, aRun maximal at beta = {bmax:.4f}")
    zooms = math.log2(a_s / a_1)
    print(f"   extended below beta = 1 the formula puts beta = 1/20 {a_s / a_1:.1f} times coarser"
          f" ({zooms:.2f} halvings above the reference), but beta = 1/20 < {bmax:.4f}: it sits on the"
          f" branch where aRun falls to 0 as beta -> 0, so the two-loop map is no unit there")
    # DERIVED: 1/20 and 1 are the two ends of the strong-coupling stretch named in the docstring
    # (beta = 1/20, and dyBeta_not_strong's beta >= 1); the test places the argmax between them.
    assert a_s > a_1 and 1 / 20 < bmax < 1
    return a_s, a_1


if __name__ == "__main__":
    section1()
    section2()
    section3()
    section4()
    print("all aperture-invariance checks passed")
