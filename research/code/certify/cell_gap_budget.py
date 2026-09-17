"""The TRUE certified single-cell gap over the crossover range, and the perturbation budget it buys.

WHAT THIS ANSWERS. `CellSpectrum.gap_of_form_perturbation` reduces "the coupled transfer is gapped" to
one scalar: a bound `delta` on how far the coupled quadratic form sits from the decoupled one, with
`2*delta < mu` and `mu` the DECOUPLED gap. So the budget for `delta` is `mu/2`, and `mu` is whatever
lower bound on the cell gap is actually certified across the coupling range.

WHY THE SCAN'S OWN SUMMARY UNDERSTATES IT. `cell_pivot_certificate.py` tries the ABSOLUTE route first
and reports its shift as the gap, because that route bounds `E_0 <= 0` by the vacuum diagonal and
`E_1 >= mu` by the shift. Both halves are loose at small coupling: `E_0` is strictly negative there,
and `mu` is only the shift the caller happened to pass. The RELATIVE route computes both halves --
`E_1 >= t` at the largest Sturm shift leaving one negative pivot, `E_0 <= R(v)` at an exact Rayleigh
quotient -- and its bound is therefore never worse. This script asks the relative question at EVERY
coupling, including the ones the scan hands to the absolute route.

THE ANSWER IS AN INTERVAL, NOT A GRID. A per-point minimum is not a bound on `[lo, hi]`. The cell's
quadratic form is Lipschitz in the coupling with constant 2 per eigenvalue (`CellPerturb`), so the GAP
is Lipschitz with constant 4 (`cell_pivot_certificate.LIPSCHITZ`). Between adjacent anchors the
guaranteed gap is therefore the lower envelope of two tents, whose minimum is exactly
`(g_k + g_{k+1})/2 - 2h` at spacing `h` when the tents cross inside the segment. The reported budget
uses that envelope, not the grid minimum.

NEGATIVE CONTROL. Every certified bound is checked against a float diagonalisation of the same
tridiagonal: `E_0 <= e0_upper`, `E_1 >= sturm_shift`, `certified gap <= true gap`. A "lower bound"
that exceeds the truth is a defect, and this is where it would show.

    python cell_gap_budget.py                      # the range at the default resolution
    python cell_gap_budget.py --steps 330          # finer grid, smaller Lipschitz loss
"""
from __future__ import annotations

import argparse
import os
import sys
from fractions import Fraction as Q

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import beta_star_enclosure as BSE
import cell_pivot_certificate as CPC


# DERIVED: k counts the eigenvalues the control needs -- E_0 and E_1 are the two the certificate
# bounds, and the third is printed nowhere but keeps the slice non-degenerate at dim 1.
def true_spectrum(jmax: int, lam: Q, k: int = 3):
    """The `k` lowest eigenvalues of the same tridiagonal, in floats -- the negative control.

    Not part of any bound. It exists so that a certified LOWER bound that exceeds the truth, or a
    certified UPPER bound that falls below it, is caught rather than published.
    """
    n = CPC.dim(jmax)
    d = [float(CPC.diag(i)) for i in range(n)]
    e = [-float(lam)] * (n - 1)
    try:
        import numpy as np
        from scipy.linalg import eigh_tridiagonal  # type: ignore
        w = eigh_tridiagonal(np.array(d), np.array(e), eigvals_only=True)
        return [float(x) for x in w[:k]]
    except Exception:
        pass
    import numpy as np
    A = np.diag(np.array(d))
    for i in range(n - 1):
        A[i, i + 1] = A[i + 1, i] = e[i]
    w = np.linalg.eigvalsh(A)
    return [float(x) for x in w[:k]]


def best_trial(jmax: int, lam: Q, denom: int = 10 ** 8):
    """A rational trial vector near the ground state, found by diagonalising in floats.

    WHY NOT `cell_pivot_certificate.ground_state_trial`. That one power-iterates on `c*I - H` with
    `c = max(d) + 2|lam| + 1`, and at `jmax = 30` the largest Casimir is `930`, so consecutive
    eigenvalues of `c*I - H` differ by a part in `10^3`: 400 iterations amplify the ground direction
    by a factor `1.4`, not to convergence. Measured, its Rayleigh quotient at `lam = 0.16` is
    `+0.372` where `E_0 = -0.033` -- the bound is true and nearly worthless, and it is the entire
    reason the small-coupling end reads as a weak gap.

    THE FLOATS COST NOTHING. `e0_upper` re-evaluates the Rayleigh quotient in exact rationals, and the
    quotient of ANY nonzero vector is an upper bound on `E_0`. A direction found badly gives a weak
    bound, never a wrong one -- which is what the negative control in `main` re-checks anyway.
    """
    import numpy as np
    n = CPC.dim(jmax)
    d = np.array([float(CPC.diag(i)) for i in range(n)])
    e = np.full(n - 1, -float(lam))
    A = np.diag(d)
    for i in range(n - 1):
        A[i, i + 1] = A[i + 1, i] = e[i]
    w, V = np.linalg.eigh(A)
    v = V[:, 0]
    v = v / max(abs(v).max(), 1e-300)
    vr = [Q(round(float(x) * denom), denom) for x in v]
    # DERIVED: the Rayleigh quotient is undefined at the zero vector, which a coarse enough rounding
    # can produce. Not a smallness test -- it is the one direction `e0_upper` cannot take.
    if all(x == 0 for x in vr):
        return None
    return vr


def certified_gap(jmax: int, lam: Q, floor_hi: Q):
    """`(gap, t, e0, lifts)` -- the relative-route certified gap at this coupling.

    `t` is the largest Sturm shift leaving at most one negative pivot, so `E_1 >= t`
    (`atMostOne_eigenvalue_lt`). `e0` is an exact Rayleigh quotient, so `E_0 <= e0`
    (`exists_eigenvalue_le_of_form`). `gap = t - e0 <= E_1 - E_0`.

    `lifts` is `tail_lifts` asked AT `t` -- the shift this certificate uses, which is the only shift
    at which the tail question means anything.
    """
    t = CPC.largest_sturm_shift(jmax, lam)
    if t is None:
        return None, None, None, False
    # Both trial vectors are admissible; the SMALLER quotient is the better bound on `E_0`, and
    # taking the minimum means a bad direction from either source cannot make the answer worse.
    cands = [CPC.ground_state_trial(jmax, lam)]
    bt = best_trial(jmax, lam)
    if bt is not None:
        cands.append(bt)
    e0 = min(CPC.e0_upper(jmax, lam, v) for v in cands)
    lifts, _, _, _ = CPC.tail_lifts(jmax, lam, t)
    return t - e0, t, e0, lifts


def envelope_min(anchors):
    """The minimum over the whole interval of the Lipschitz lower envelope of the anchors.

    `anchors` is a list of `(lam, gap)` in increasing `lam`. The true gap obeys
    `gap(x) >= gap(lam_k) - L*|x - lam_k|` with `L = LIPSCHITZ`, so on each segment the guaranteed
    value is `max` of the two tents. Two tents of equal slope `L` cross at the point where
    `g_k - L*x = g_{k+1} - L*(h-x)`, giving the value `(g_k + g_{k+1})/2 - L*h/2`; when that crossing
    falls outside the segment the segment minimum is the smaller endpoint.

    DERIVED: `L*h/2` is not a resolution choice -- it is the exact worst case of the two-tent
    envelope at spacing `h`, so halving the grid halves the loss.
    """
    L = CPC.LIPSCHITZ
    worst = min(g for _, g in anchors)
    where = min(anchors, key=lambda p: p[1])[0]
    for (l0, g0), (l1, g1) in zip(anchors, anchors[1:]):
        h = l1 - l0
        x = (g0 - g1 + L * h) / (2 * L)
        # DERIVED: the crossing lies inside the segment exactly when `0 <= x <= h`; outside it one
        # tent dominates throughout and the segment minimum is the smaller endpoint. The endpoints
        # of the segment are its own, not a tolerance.
        cand = g0 - L * x if 0 <= x <= h else min(g0, g1)
        if cand < worst:
            # DERIVED: same two cases -- the crossing offset when it is interior, else the endpoint
            # (offset 0 or h) carrying the smaller value.
            worst, where = cand, l0 + (x if 0 <= x <= h else (0 if g0 < g1 else h))
    return worst, where


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--lo", default="0.16")
    ap.add_argument("--hi", default="6.76")
    ap.add_argument("--steps", type=int, default=60)
    ap.add_argument("--jmax", type=int, default=30)
    ap.add_argument("--show", type=int, default=20, help="how many small-lambda rows to print")
    a = ap.parse_args()

    lo, hi = Q(a.lo), Q(a.hi)
    klo, khi = BSE.kappa0_bounds()
    print(f"kappa_0 in [{float(klo):.7f}, {float(khi):.7f}]   jmax={a.jmax} (dim {CPC.dim(a.jmax)})")
    print(f"lambda in [{float(lo)}, {float(hi)}], {a.steps + 1} anchors, "
          f"spacing {float((hi - lo) / a.steps):.5f}")
    print()
    print(f"{'lambda':>9} {'abs mu':>10} {'E1 >= t':>11} {'E0 <= R':>11} {'certified':>11} "
          f"{'true gap':>11} {'slack':>10} {'tail':>6}")

    anchors = []
    bad = []
    for k in range(a.steps + 1):
        lam = lo + (hi - lo) * k / a.steps
        g, t, e0, lifts = certified_gap(a.jmax, lam, khi)
        if g is None:
            bad.append((lam, "no isolating shift"))
            continue
        w = true_spectrum(a.jmax, lam)
        true_gap = w[1] - w[0]
        # NEGATIVE CONTROL, three ways. A certified lower bound above the truth, or a certified upper
        # bound below it, is a defect in the certificate and not a tolerance question.
        if float(t) > w[1] + 1e-9:
            bad.append((lam, f"E1 bound {float(t)} exceeds true E1 {w[1]}"))
        if float(e0) < w[0] - 1e-9:
            bad.append((lam, f"E0 bound {float(e0)} below true E0 {w[0]}"))
        if float(g) > true_gap + 1e-9:
            bad.append((lam, f"certified gap {float(g)} exceeds true gap {true_gap}"))
        if not lifts:
            bad.append((lam, "tail does not lift at the certifying shift"))
        anchors.append((lam, g))
        if k < a.show or k == a.steps:
            # The ABSOLUTE route's largest shift at this coupling, printed beside the relative one so
            # the two can be compared directly. It is what the scan reports as the gap, and it is a
            # lower bound on the relative answer rather than a rival to it: the absolute route bounds
            # `E_0` by the vacuum diagonal `0`, so its claim `gap >= M` is the relative claim
            # `gap >= t - e0` with `t >= M` and `e0` replaced by the weaker `0`.
            M = CPC.largest_absolute_mu(a.jmax, lam, khi, Q(20))
            ms = f"{float(M):>10.5f}" if M is not None else f"{'-':>10}"
            print(f"{float(lam):>9.4f} {ms} {float(t):>11.5f} {float(e0):>11.5f} {float(g):>11.5f} "
                  f"{true_gap:>11.5f} {float(g) / true_gap:>9.4f} {'ok' if lifts else 'NO':>6}")

    print()
    gmin = min(g for _, g in anchors)
    lmin = min(anchors, key=lambda p: p[1])[0]
    print(f"grid minimum certified gap:       {float(gmin):.6f}  at lambda = {float(lmin):.4f}")
    env, ewhere = envelope_min(anchors)
    print(f"INTERVAL minimum (Lipschitz {int(CPC.LIPSCHITZ)}): {float(env):.6f}  near lambda = {float(ewhere):.4f}")
    print(f"  -> mu   = {float(env):.6f}   (the certified decoupled gap on the whole range)")
    print(f"  -> delta budget = mu/2 = {float(env) / 2:.6f}")
    print()
    # HOW MANY INTER-CELL BONDS THE BUDGET BUYS. `CellCouple.straddle_form_bound` proves one
    # straddling plaquette costs `2|lam|` in quadratic form (`adj_form_bound`'s constant), and
    # `CellCouple.coupling_form_le_bondCount`/`coupling_form_extensive` make `n` bonds cost exactly
    # `n` times that. `gap_of_form_perturbation` wants `2*delta < mu`, so the admitted bond count at
    # this coupling is `mu(lam) / (4*lam)` -- a number, not an asymptotic statement.
    print("bonds the form-perturbation route admits, per coupling "
          "(2*n*2|lam| < gap(lam), adj_form_bound's 2):")
    nmax_any = 0
    last_ok = None
    for lam, g in anchors:
        n = int(g / (4 * lam))
        nmax_any = max(nmax_any, n)
        # DERIVED: one bond is the smallest coupling a cell decomposition can have -- two cells that
        # touch. A route admitting none is a route that never leaves the single cell.
        if n >= 1:
            last_ok = lam
    print(f"  largest bond count admitted anywhere on the range: {nmax_any}")
    if last_ok is None:
        print("  NO coupling on the range admits even one inter-cell bond")
    else:
        print(f"  admitted at all only for lambda <= {float(last_ok):.4f}; "
              f"above that the route admits zero bonds")
    # One straddling plaquette costs `delta = 2|lam|` (`straddle_form_bound`), so a SINGLE bond costs
    # `2*delta = 4|lam|` -- the same constant the admitted-bond count above divides by, and it must be,
    # since `n < mu/(4*lam)` is exactly `2*n*2*lam < mu`. This line read `8 * lam` until 2026-09-17,
    # which is `2*delta` for TWO plaquettes and disagreed with the line it is meant to illustrate by a
    # factor of two. The verdict never depended on it: `4*lam` at the top coupling is 27.04 against
    # `mu = 4.87`, so the route is refused either way.
    print(f"  at lambda = {float(anchors[-1][0]):.4f} the single-bond cost is "
          f"2*delta = {float(4 * anchors[-1][0]):.4f} against mu = {float(anchors[-1][1]):.4f}")
    print()
    if bad:
        print(f"REFUSED: {len(bad)} check(s) failed")
        for lam, why in bad[:10]:
            print(f"  lambda={float(lam):.4f}: {why}")
        return 1
    print(f"all {len(anchors)} anchors pass the negative control "
          f"(certified <= true, tail lifts at the certifying shift)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
