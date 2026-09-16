"""Exact-rational LDL^T pivot certificates for the SU(2) cell, across the crossover coupling range.

WHAT THIS CLOSES. `CellSpectrum.HcellR_gap_of_certificate` reduces the physical single-cell gap to
producing rational pivots: given a shift `mu > 0` and a completing-the-square certificate `(p, e)` with
at most one negative pivot, every non-vacuum eigenvalue of `HcellR jmax lam` exceeds the vacuum by at
least `mu`. Its own docstring calls the rest "the remaining (numeric) certificate work, no more
abstract plumbing". This is that work.

THE RECURRENCE IS EXACTLY SOLVABLE, which is why the certificate can be rational rather than floating.
The cell is tridiagonal with Casimir diagonal `d_i = i(i+2)/4` and constant off-diagonal `-lam`, so the
two hypotheses

    d_i - mu = p_i + e_{i+1}^2 p_{i+1}          (hrecD)
    -lam     = e_{i+1} p_{i+1}                  (hrecO)

determine everything backwards from the last index:

    p_{n-1} = d_{n-1} - mu ,    p_i = d_i - mu - lam^2 / p_{i+1} ,    e_{i+1} = -lam / p_{i+1} .

Every term is a ratio of integers when `lam` and `mu` are, so `fractions.Fraction` carries the whole
computation with no rounding anywhere. The certificate is then a finite list of rationals and a claim
about their signs, which is checkable by inspection.

WHY `mu` IS RATIONAL AND STRICTLY ABOVE THE FLOOR. The conclusion wanted is `gap >= kappa_0` with
`kappa_0 = (1/4) log 3` irrational, so no rational `mu` equals it. Taking a rational `mu > kappa_0`
gives `gap >= mu > kappa_0`, which is the wanted statement and is stronger. `MU_DEFAULT` below is such
a rational, and the script REFUSES if it is not above the certified upper bound on `kappa_0` -- so the
inequality is checked rather than asserted.

WHAT A FAILURE MEANS. More than one negative pivot at some `lam` is not a bug: it is the certificate
declining, and it says the one-negative-pivot route does not reach that coupling at that truncation.
The script reports which couplings decline rather than adjusting anything to make them pass.

    python cell_pivot_certificate.py                      # scan the crossover range
    python cell_pivot_certificate.py --emit out.csv       # write the CSV artifact
    python cell_pivot_certificate.py --emit-lean CellPivot.lean   # one Lean instance
"""
from __future__ import annotations

import argparse
import os
import sys
from fractions import Fraction as Q

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import beta_star_enclosure as BSE

#: DERIVED: the cell's dimension, `2*jmax + 1`, matching `CellEnclosure.dim`. Not a choice here: it is
#: what the Lean side means by `jmax`.
def dim(jmax: int) -> int:
    return 2 * jmax + 1


#: DERIVED: the Casimir diagonal `d_i = i(i+2)/4` of the single-plaquette Hamiltonian, exactly as
#: `HcellR_gap_of_certificate` states it. Written here so the two cannot drift apart silently.
def diag(i: int) -> Q:
    return Q(i * (i + 2), 4)


#: A rational shift strictly above the entropy floor. CHECKED against the certified enclosure of
#: `kappa_0` rather than asserted -- see `check_mu_above_floor`.
MU_DEFAULT = Q(2747, 10000)


def check_mu_above_floor(mu: Q) -> tuple[Q, Q]:
    """Refuse a shift that does not exceed `kappa_0`, using the certified rational enclosure.

    `gap >= mu` is only the statement wanted if `mu > kappa_0`. The enclosure is exact-rational with a
    proven tail bound, so this is a decision rather than an estimate.
    """
    klo, khi = BSE.kappa0_bounds()
    if not mu > khi:
        raise SystemExit(
            f"REFUSED: mu = {mu} = {float(mu):.8f} does not exceed the certified upper bound on "
            f"kappa_0 ({float(khi):.8f}). A certificate at this shift would prove a gap BELOW the "
            f"floor, which is not the statement wanted.")
    return klo, khi


def pivots(jmax: int, lam: Q, mu: Q):
    """The backward LDL^T pivots `p` and multipliers `e`, in exact rationals.

    Returns `(p, e, ok, note)`. `ok` is False when the recurrence hits a zero pivot -- at which point
    `e_{i+1} = -lam / p_{i+1}` does not exist and there is no certificate at this `(lam, mu)`, which
    the caller reports rather than works around.
    """
    n = dim(jmax)
    p: list[Q | None] = [None] * n
    e: list[Q] = [Q(0)] * n
    p[n - 1] = diag(n - 1) - mu
    for i in range(n - 2, -1, -1):
        nxt = p[i + 1]
        # DERIVED: the recurrence divides by `p[i+1]`, so a zero there is not a small pivot but an
        # undefined one. Nothing is rounded past it; the certificate declines instead.
        if nxt == 0:
            return None, None, False, f"zero pivot at index {i + 1}; no certificate at this shift"
        e[i + 1] = -lam / nxt
        p[i] = diag(i) - mu - (lam * lam) / nxt
    return p, e, True, ""


# CHOSEN: `limit` is where the search gives up and reports that the bound did not close, rather
# than looping forever. It costs nothing correct: `d_i` grows quadratically, so the inequality
# closes within a handful of steps for every coupling in range (measured: m <= 6 on the whole
# crossover), and a larger limit would only postpone the same report.
def tail_start(lam: Q, mu: Q, eps: Q, limit: int = 10_000):
    """The index from which `p_i >= d_i - mu - eps` holds for the INFINITE cell, or None.

    THE TRUNCATION IS NOT FREE, and it errs in the dangerous direction. The backward recurrence is
    `p_i = d_i - mu - lam^2 / p_{i+1}`; truncating at `n` sets `p_{n-1} = d_{n-1} - mu`, DROPPING the
    `- lam^2 / p_n` term. Dropping a subtraction makes the truncated pivot larger than the true one,
    and every pivot below inherits it -- so a truncated certificate is optimistic exactly where it
    matters, and could report a positive pivot where the infinite cell has a negative one.

    THE BOUND, and why it closes. The recurrence is INCREASING in `p_{i+1}` (for positive pivots
    `-lam^2/p` rises with `p`), so a lower bound propagates downward. Assume `p_i >= d_i - mu - eps`
    for all `i >= m`; substituting into the recurrence, that is self-consistent exactly when

        eps * (d_{m+1} - mu - eps) >= lam^2 .

    The Casimir diagonal `d_i = i(i+2)/4` grows quadratically while `lam` is fixed, so the inequality
    holds for `m` large enough. This returns the SMALLEST such `m` -- derived from `(lam, mu, eps)`,
    not chosen.
    """
    m = 0
    while m <= limit:
        if eps * (diag(m + 1) - mu - eps) >= lam * lam:
            return m
        m += 1
    return None


def pivots_with_tail(jmax: int, lam: Q, mu: Q, eps: Q):
    """Pivots that BOUND the infinite cell's, instead of truncating it away.

    The truncated sequence starts at `d_{n-1} - mu`. This starts at
    `d_{n-1} - mu - lam^2 / (d_n - mu - eps)`, using the tail bound for the first pivot outside the
    block, and runs the same recurrence down. Because the recurrence is increasing in `p_{i+1}`, the
    result is a pointwise LOWER bound on the infinite cell's pivots.

    What that buys: wherever this sequence is positive, the infinite cell's pivot is positive too. So
    "positive except at one index" here gives "at most one eigenvalue below `mu`" THERE, which is the
    hypothesis `gap_of_ldl_one_neg_pivot` consumes -- and the conclusion is about the physical cell
    rather than about a truncation of it.
    """
    n = dim(jmax)
    floor_next = diag(n) - mu - eps
    # DERIVED: 0 is where the tail bound stops saying anything -- a nonpositive lower bound on the
    # first outside pivot cannot bound the division by it.
    if floor_next <= 0:
        return None, "the tail bound is not positive at the truncation edge"
    p: list = [None] * n
    p[n - 1] = diag(n - 1) - mu - (lam * lam) / floor_next
    for i in range(n - 2, -1, -1):
        # DERIVED: the recurrence divides by `p[i+1]`, so a zero there is undefined rather than
        # small -- the same reason `pivots` refuses, applied to the tail-inclusive sequence.
        if p[i + 1] == 0:
            return None, f"zero pivot at index {i + 1} with the tail included"
        p[i] = diag(i) - mu - (lam * lam) / p[i + 1]
    return p, ""


def tail_lifts(jmax: int, lam: Q, shift: Q):
    """Does the certificate at `shift` hold for the CELL, not just for its truncation?

    THE SHIFT IS AN ARGUMENT, and that is the point. A certificate is an inertia claim AT A SHIFT:
    the absolute route uses `MU_DEFAULT`, the relative route uses its own Sturm shift, which is
    NEGATIVE at strong coupling. Checking the tail at a shift the certificate does not use answers a
    different question and can answer it "yes" while the real one is "no".

    THE TEST IS "AT MOST ONE NEGATIVE", NOT "THE SIGNS AGREE". `pivots_with_tail` is a pointwise
    LOWER bound on the infinite cell's pivots, so a nonnegative entry here is a nonnegative pivot
    THERE. "At most one negative in the bound" therefore gives "at most one eigenvalue below `shift`"
    for the cell, which is exactly the hypothesis `gap_of_ldl_one_neg_pivot` consumes. Sign AGREEMENT
    between the truncated and tail-inclusive sequences is neither necessary nor sufficient for that:
    the previous predicate returned "safe" where both sequences carried THREE negatives, which is
    agreement about a certificate that does not exist.

    `eps = lam`: any positive `eps` admitting a finite `tail_start` works, and this one scales with
    the coupling, which is what the self-consistency inequality is about. With it the tail-start
    condition `eps*(d_(m+1) - shift - eps) >= lam^2` reduces to `d_(m+1) >= shift + 2*lam`, which is
    MONOTONE in `lam` -- so a truncation deep enough at the right-hand end of an interval is deep
    enough throughout it.

    Returns `(lifts, m, tail_negatives, note)`.
    """
    eps = lam
    m = tail_start(lam, shift, eps)
    if m is None or m >= dim(jmax):
        return False, m, None, "the tail bound does not close inside this truncation"
    tv, tnote = pivots_with_tail(jmax, lam, shift, eps)
    if tv is None:
        return False, m, None, tnote
    neg = negatives(tv)
    # DERIVED: 1 is the theorem's own arity, the same one `certify` applies to the truncated pivots.
    return len(neg) <= 1, m, neg, ""


def certifying_shift(jmax: int, lam: Q, mu: Q, floor_hi: Q):
    """The shift the certificate at this coupling ACTUALLY uses, and which route supplies it.

    One copy, because every tail question has to be asked at this shift and asking it at any other
    shift is the defect this function exists to prevent.
    """
    ok, _, _, _, _ = certify(jmax, lam, mu)
    if ok:
        return mu, "absolute"
    ok, e1_lo, _, _, _ = certify_relative(jmax, lam, floor_hi)
    if ok:
        return e1_lo, "relative"
    return None, "neither"


def negatives(p) -> list[int]:
    """Indices carrying a negative pivot. At most one is what the theorem admits."""
    # DERIVED: the sign, not a tolerance. Sylvester's law counts eigenvalues below the shift by the
    # number of negative pivots, and the count is exact because the pivots are exact rationals.
    return [i for i, v in enumerate(p) if v < 0]


def certify(jmax: int, lam: Q, mu: Q):
    """`(ok, m, p, e, note)` -- whether this coupling admits the one-negative-pivot certificate."""
    p, e, ok, note = pivots(jmax, lam, mu)
    if not ok:
        return False, None, None, None, note
    neg = negatives(p)
    # DERIVED: 1 is the theorem's own arity -- `hp : forall k, k != m -> 0 <= p k` admits exactly one
    # exceptional index. Zero negatives also satisfies it (any `m` will do); two or more cannot.
    if len(neg) > 1:
        return False, None, p, e, f"{len(neg)} negative pivots at {neg[:6]}; the theorem admits one"
    m = neg[0] if neg else 0
    return True, m, p, e, ""


def e0_upper(jmax: int, lam: Q, v) -> Q:
    """A RIGOROUS upper bound on the least eigenvalue: the Rayleigh quotient of any nonzero vector.

    `CellSpectrum.exists_eigenvalue_le_of_form` is the Lean side of this -- the least eigenvalue is at
    most the quotient, for EVERY vector. So the trial vector may be as crude as one likes without
    costing rigour: a bad vector gives a weak bound, never a wrong one. That is why `v` below can be a
    float approximation rounded to rationals.

    Computed exactly: `v^T H v / v^T v` with `H` the tridiagonal cell, all in `Fraction`.
    """
    n = dim(jmax)
    num = Q(0)
    for i in range(n):
        num += diag(i) * v[i] * v[i]
    for i in range(n - 1):
        num += 2 * (-lam) * v[i] * v[i + 1]
    den = sum(x * x for x in v)
    # DERIVED: the Rayleigh quotient is undefined at the zero vector. Not a smallness test.
    if den == 0:
        raise ValueError("e0_upper: the trial vector is zero")
    return num / den


def ground_state_trial(jmax: int, lam: Q, denom: int = 10 ** 6):
    """A rational trial vector near the ground state, for `e0_upper`.

    Found by inverse-free power iteration on `(c*I - H)` in floats and then ROUNDED to rationals. The
    floats never enter the bound -- they only choose a direction, and `e0_upper` re-evaluates the
    quotient exactly. A direction found badly costs a weaker bound and nothing else.

    DERIVED: the shift `c` is the largest diagonal entry, which makes `c*I - H` positive definite so
    power iteration converges to the SMALLEST eigenvalue of `H`. Not tuned: it is the bound that makes
    the shift work at all.
    """
    n = dim(jmax)
    d = [float(diag(i)) for i in range(n)]
    l = float(lam)
    c = max(d) + 2 * abs(l) + 1.0
    v = [1.0] * n
    # CHOSEN: iteration count. It costs a better or worse DIRECTION and nothing else -- the bound is
    # exact for whatever vector comes out, so this is a quality knob, not a threshold.
    for _ in range(400):
        w = [0.0] * n
        for i in range(n):
            w[i] = (c - d[i]) * v[i]
            # DERIVED: the tridiagonal band. Row 0 has no subdiagonal neighbour and row n-1 no
            # superdiagonal one; these are the matrix's edges, not a window.
            if i > 0:
                w[i] += l * v[i - 1]
            if i + 1 < n:
                w[i] += l * v[i + 1]
        nrm = max(abs(x) for x in w) or 1.0
        v = [x / nrm for x in w]
    return [Q(round(x * denom), denom) for x in v]


def spectrum_floor(jmax: int, lam: Q) -> Q:
    """A rigorous lower bound on the whole spectrum, by Gershgorin.

    The cell is tridiagonal with diagonal `d_i >= 0` and off-diagonal `-lam`, so row `i` has radius
    at most `2|lam|` and every eigenvalue is at least `min_i (d_i - 2|lam|) >= -2|lam|`. Nothing lies
    below this, so a search that starts here misses nothing.
    """
    return -2 * abs(lam) - 1


# CHOSEN: steps=60 bisection halvings. It buys precision in the returned shift and nothing else --
# every value the bisection tries is checked exactly, so a shorter search returns a WORSE bound, never
# a wrong one. 60 halvings of the Gershgorin range puts the shift within 2^-60 of the best available.
def largest_sturm_shift(jmax: int, lam: Q, steps: int = 60):
    """The largest rational shift `t` leaving AT MOST one negative pivot -- a lower bound on `E_1`.

    One negative pivot at `t` says at most one eigenvalue lies below `t`
    (`atMostOne_eigenvalue_lt`), so the SECOND-lowest is at least `t`. Maximising `t` maximises that
    bound.

    `t` MAY BE NEGATIVE and usually is at large coupling, where both of the lowest eigenvalues sit
    below zero. `gap_of_ldl_one_neg_pivot_rel` places no sign condition on `t` -- only `mu > 0` --
    so the search runs from the Gershgorin floor upward. An earlier version started at 0 and reported
    every large coupling as having no shift at all; the shift was there, below where it looked.

    Bisection on rationals throughout: the returned value is exact.
    """
    a, b = spectrum_floor(jmax, lam), diag(dim(jmax) - 1)
    pv, _, ok, _ = pivots(jmax, lam, a)
    # DERIVED: `<= 1` is the theorem's hypothesis verbatim -- `gap_of_ldl_one_neg_pivot` admits at most
    # one negative pivot, because one eigenvalue below the shift is the vacuum. Not a tolerance.
    if not (ok and len(negatives(pv)) <= 1):
        return None                       # not even the floor isolates one; nothing to find
    good = a
    for _ in range(steps):
        mid = (a + b) / 2
        pv, _, ok, _ = pivots(jmax, lam, mid)
        # DERIVED: same hypothesis as above -- at most one eigenvalue below `mid`.
        if ok and len(negatives(pv)) <= 1:
            good, a = mid, mid
        else:
            b = mid
    return good


def simple_sturm_shift(jmax: int, lam: Q, floor_hi: Q, denominators=(2, 4, 5, 10, 100, 1000)):
    """The COARSEST rational shift that still isolates one negative pivot and still clears the floor.

    WHY NOT THE LARGEST SHIFT. `largest_sturm_shift` bisects 60 times, so its value is a dyadic with a
    `2^60` denominator and the pivots computed from it run to seventy digits. That is fine for exact
    arithmetic and hostile to transcription -- and nothing asks for the maximal shift.
    `gap_of_ldl_one_neg_pivot_rel` asks only that the shift leave at most one negative pivot; a smaller
    shift gives a smaller `E_1` bound and therefore a SMALLER certified gap, which is weaker and still
    true. So the certificate can afford a short rational and does not have to defend the last digit.

    Measured on the SU(2) cell: a denominator of 10 suffices across the relative route's whole range,
    the certified gap moves by about 2% (3.199 -> 3.129 at `lam = 3`), and the pivots fall from
    seventy-digit denominators to five-digit ones.

    Tries the coarsest denominators first and returns the first that works, or None.
    """
    exact = largest_sturm_shift(jmax, lam)
    if exact is None:
        return None, None, "no shift isolates one negative pivot"
    v = ground_state_trial(jmax, lam)
    e0 = e0_upper(jmax, lam, v)
    for den in denominators:
        # Round DOWN: the shift may be negative, and flooring moves it away from the spectrum, which
        # is the safe direction -- a lower shift isolates at most as many eigenvalues, never more.
        cand = Q(int(exact * den), den)
        if cand > exact:
            cand = Q(int(exact * den) - 1, den)
        pv, _, ok, _ = pivots(jmax, lam, cand)
        # DERIVED: 1 is the theorem's hypothesis verbatim -- at most one eigenvalue below the shift,
        # because one of them is the vacuum.
        if not ok or len(negatives(pv)) != 1:
            continue
        gap = cand - e0
        if gap > floor_hi:
            return cand, gap, ""
    return None, None, "no short rational shift both isolates and clears the floor"


def simple_absolute_mu(jmax: int, lam: Q, floor_hi: Q, denominators=(2, 4, 5, 10, 100, 1000)):
    """The COARSEST rational shift the absolute route still certifies at, at or below its largest.

    The counterpart of `simple_sturm_shift`, and it exists for the same reason: `largest_absolute_mu`
    bisects, so its value is a dyadic with a huge denominator and the pivots computed from it run to
    thousands of digits -- exact, and impossible to put in front of `norm_num` seventeen times per
    anchor. Rounding DOWN gives a smaller shift, hence a smaller certified gap and a smaller covering
    radius: weaker, still true, and the walk simply takes more steps.

    Returns `(mu, note)`, with `mu` None when no coarse shift both certifies and clears the floor.
    """
    M = largest_absolute_mu(jmax, lam, floor_hi, Q(20))
    if M is None or M <= floor_hi:
        return None, "the absolute route certifies nothing above the floor here"
    for den in denominators:
        # Round DOWN: a smaller shift is a weaker claim, and the floor is what it must still clear.
        cand = Q(int(M * den), den)
        if cand <= floor_hi:
            continue
        ok, _, _, _, _ = certify(jmax, lam, cand)
        if ok:
            return cand, ""
    return None, "no coarse shift in the offered denominators certifies here"


def simple_trial(jmax: int, lam: Q, t: Q, floor_hi: Q, denominators=(2, 4, 5, 10, 100, 1000)):
    """The coarsest rational trial vector whose Rayleigh bound still certifies a gap above the floor.

    `ground_state_trial` returns a vector with a denominator of 10^6, because it is a float direction
    rounded at that scale. Nothing needs it that precise: the Rayleigh quotient of ANY nonzero vector
    is an upper bound on `E_0`, so a coarser vector gives a WEAKER bound and therefore a smaller
    certified gap, which is still true. What it must not do is fall below the floor.

    Measured on the SU(2) cell: a denominator of 10 suffices across the relative route, and the
    certified gap moves by well under a percent.

    Returns `(v, gap, note)`.
    """
    v = ground_state_trial(jmax, lam)
    for den in denominators:
        vr = [Q(round(x * den), den) for x in v]
        # DERIVED: the Rayleigh quotient is undefined at the zero vector, and a coarse enough rounding
        # produces one. That is the rounding being too coarse, not a failure of the coupling.
        if all(x == 0 for x in vr):
            continue
        gap = t - e0_upper(jmax, lam, vr)
        if gap > floor_hi:
            return vr, gap, ""
    return None, None, "no short rational trial vector certifies above the floor"


def certify_relative(jmax: int, lam: Q, floor_hi: Q):
    """`(ok, E1_lo, E0_hi, gap_lo, note)` -- the relative route, for couplings with two low modes.

    Where BOTH `E_0` and `E_1` sit below the floor, an absolute bound `E_1 >= mu > kappa_0` is simply
    false and no certificate can produce it. What is still true, and is what a mass gap asserts, is
    that `E_1 - E_0` is large. So: bound `E_1` from below by the largest shift leaving one negative
    pivot, bound `E_0` from above by an exact Rayleigh quotient, and subtract.
    """
    # The search runs from the Gershgorin floor to the largest diagonal entry -- both properties of
    # the matrix, neither a choice. The floor matters: at large coupling the isolating shift is
    # negative, and `gap_of_ldl_one_neg_pivot_rel` permits that.
    e1_lo = largest_sturm_shift(jmax, lam)
    if e1_lo is None:
        return False, None, None, None, "no shift leaves one negative pivot"
    v = ground_state_trial(jmax, lam)
    e0_hi = e0_upper(jmax, lam, v)
    gap_lo = e1_lo - e0_hi
    return gap_lo > floor_hi, e1_lo, e0_hi, gap_lo, ""


#: DERIVED: the Lipschitz constant of the cell's spectrum in the coupling. `HcellR jmax lam` is LINEAR
#: in `lam` -- the diagonal is the Casimir and the off-diagonal is `-lam` times the path-graph
#: adjacency `A` -- so `H(lam) - H(lam') = -(lam - lam') A`, and Weyl's inequality bounds each
#: eigenvalue's movement by `|lam - lam'| * ||A||`. For a path graph `||A|| <= 2` (every row sums to at
#: most 2; the exact norm is `2 cos(pi/(n+1)) < 2`). The GAP is a difference of two eigenvalues, so it
#: moves by at most twice that. Weyl, not a tolerance.
LIPSCHITZ = Q(4)


# CHOSEN: 40 bisection halvings. It buys precision in the shift and nothing else -- every value
# tried is certified exactly, so a shorter search returns a SMALLER certified shift, never a
# wrong one, and a smaller shift is a smaller covering radius rather than an unsound one.
def largest_absolute_mu(jmax: int, lam: Q, lo: Q, hi: Q, steps: int = 40):
    """The largest shift the ABSOLUTE route supports at this coupling, by rational bisection.

    The default `MU_DEFAULT` sits only just above the floor, which is all the certificate needs at a
    point. It is not all that is available, and the surplus is what buys an interval: a coupling
    certified at `M` keeps a gap above `kappa_0` for every coupling within `(M - kappa_0)/LIPSCHITZ`.

    Bisection on rationals, so the returned shift is exact and certified rather than a float that
    happened to pass. Returns None when even `lo` declines.
    """
    ok, _, _, _, _ = certify(jmax, lam, lo)
    if not ok:
        return None
    good, a, b = lo, lo, hi
    for _ in range(steps):
        mid = (a + b) / 2
        ok, _, _, _, _ = certify(jmax, lam, mid)
        if ok:
            good, a = mid, mid
        else:
            b = mid
    return good


# CHOSEN: a cap on how many points the walk will place before giving up. It bounds run time and
# nothing else: hitting it returns the reach achieved SO FAR, which is a smaller covered
# interval and still a covered one. Measured, the walk converges in 68 points.
def interval_cover(jmax: int, start: Q, floor_hi: Q, limit: Q, max_points: int = 400):
    """Walk right from `start`, each step the Weyl radius the previous point earned.

    WHY THIS EXISTS. A finite set of certified couplings is not an interval. Between two grid points
    the certificate says nothing, as a matter of logic, and the artifact's grid is a measurement of
    where it was checked rather than a statement about what lies between.

    Weyl closes that, because the cell is linear in the coupling: a point certified at shift `M`
    covers a neighbourhood of radius `(M - kappa_0)/LIPSCHITZ`, inside which the gap cannot have
    fallen to the floor. Where consecutive neighbourhoods overlap, the points COVER.

    The spacing is the radius rather than a chosen step, so it tightens by itself as the margin
    shrinks near the route's edge. Returns `(reach, points)` -- the coupling the cover extends to, and
    how many points it took.
    """
    lam, reach, pts, unsafe = start, None, 0, []
    while pts < max_points and lam <= limit:
        M = largest_absolute_mu(jmax, lam, floor_hi, Q(20))
        if M is None:
            break
        # THE ANCHOR MUST BE AN ANCHOR FOR THE CELL, not for its truncation. The gap certificate and
        # the tail bound are separate results, and a cover whose anchors were only truncation-safe
        # would read as a statement about the cell while being a statement about `HcellR jmax`.
        #
        # AT `M`, not at `MU_DEFAULT`: the anchor's certificate is the one bisected just above,
        # whose shift is `M` and runs to about 0.84 -- far above the default. Checking the tail at
        # `MU_DEFAULT` asked an EASIER question than the anchor answers, because the tail-start
        # condition `d_(m+1) >= shift + 2*lam` is monotone in the shift.
        lifts, _, _, _ = tail_lifts(jmax, lam, M)
        if not lifts:
            unsafe.append(lam)
        radius = (M - floor_hi) / LIPSCHITZ
        # DERIVED: 0 is where a radius stops covering anything -- a point whose certified shift only
        # just clears the floor covers itself and nothing around it, so the walk ends there.
        if radius <= 0:
            break
        reach, pts = lam + radius, pts + 1
        # DERIVED: 10^-6 is where the step has converged to the route's own edge rather than a
        # resolution choice: the radius is shrinking to zero because `M` is falling to `kappa_0`,
        # which is what "the absolute route ends here" MEANS.
        if reach - lam < Q(1, 10 ** 6):
            break
        lam = reach
    return reach, pts, unsafe


# CHOSEN: the same walk cap as `interval_cover`, and for the same reason -- hitting it returns
# the reach achieved so far, a smaller covered interval and still a covered one. Measured, the
# relative walk converges in 7 points.
def interval_cover_relative(jmax: int, start: Q, floor_hi: Q, limit: Q, max_points: int = 400):
    """The same walk on the RELATIVE route, which carries the coupling range the absolute one cannot.

    Nothing changes in the argument. `certify_relative` returns a certified lower bound on the GAP
    itself -- a Sturm lower bound on `E_1` minus an exact Rayleigh upper bound on `E_0` -- and the gap
    moves by at most `LIPSCHITZ` per unit coupling for the same Weyl reason. So a coupling certified at
    gap `g` covers a neighbourhood of radius `(g - kappa_0)/LIPSCHITZ`.

    The margins here are far larger than on the absolute route: the gap runs to about 4.9 at the top of
    the crossover against a shift that only just clears the floor, so each point covers more than a
    whole unit of coupling and the walk finishes in a handful of steps.

    Returns `(reach, points)`.
    """
    lam, reach, pts, unsafe = start, None, 0, []
    while pts < max_points and lam <= limit:
        ok, e1_lo, _, gap, _ = certify_relative(jmax, lam, floor_hi)
        if not ok or gap is None:
            break
        # AT THE SHIFT THIS ROUTE USES, not at `MU_DEFAULT`. The relative certificate's inertia
        # claim is at `e1_lo`, which runs to about -5 at the top of the range; checking the tail at
        # `MU_DEFAULT` instead asked whether an absolute certificate that does not exist here would
        # survive its tail, and answered yes.
        lifts, _, _, _ = tail_lifts(jmax, lam, e1_lo)
        if not lifts:
            unsafe.append(lam)
        radius = (gap - floor_hi) / LIPSCHITZ
        # DERIVED: 0 is where a radius stops covering anything -- a coupling whose certified gap only
        # just clears the floor covers itself and nothing around it.
        if radius <= 0:
            break
        reach, pts = lam + radius, pts + 1
        # DERIVED: the same convergence test as the absolute walk -- a step below 10^-6 means the
        # radius is collapsing to the route's own edge rather than to a resolution choice.
        if reach - lam < Q(1, 10 ** 6):
            break
        lam = reach
    return reach, pts, unsafe


#: CHOSEN: the grid the cover's anchors are rounded onto. It bounds the size of the rationals that
#: reach the kernel and nothing else -- rounding is always DOWNWARD into ground the previous anchor
#: already covers, so no value of this can open a gap; a coarser one only makes the walk take more
#: steps. 1000 keeps every coupling to four digits while costing about one extra anchor.
LAM_DEN = 1000


# CHOSEN: the same walk cap as `interval_cover`, and for the same reason -- hitting it returns
# the anchors placed SO FAR, which describe a smaller covered interval and still a covered one.
# The caller sees the reach and can tell. Measured, taking the better route at each step converges
# in 19 anchors, against the 75 two separate walks took.
def cover_anchors(jmax: int, lo: Q, floor_hi: Q, hi: Q, max_points: int = 400):
    """The cover's anchors WITH the data each one's Lean theorem consumes.

    `interval_cover` and `interval_cover_relative` answer "does it close, and in how many steps".
    This answers "what does each step certify, and with what", which is what an emitter needs. ONE
    walk rather than two, because the handover between the routes happens at a coupling the walk
    DISCOVERS -- where the absolute route's largest shift falls to the floor -- and splitting the walk
    invites the two halves to disagree about where that is.

    Each anchor carries:
      lam       the anchor coupling
      route     "absolute" or "relative"
      shift     the shift ITS certificate uses -- `M` for the absolute route, the Sturm shift for the
                relative one. Every tail question about this anchor is asked here and nowhere else.
      radius    `(certified - floor_hi) / LIPSCHITZ`, the half-width its certificate covers
      certified the gap the anchor itself certifies, before the ball's loss
      p, e, m   the pivot certificate at `shift`
      trial     the rational trial vector (relative route only; the absolute route bounds `E_0` by
                `cell_exists_eigenvalue_le_zero`, which needs no vector and no transport)

    Returns `(anchors, reach, unlifted)`. `unlifted` names anchors whose tail does not lift at this
    truncation -- they are NOT dropped silently, because an anchor that does not lift covers an
    interval of `HcellR jmax` and not of the cell.
    """
    def candidate(lam: Q, route: str):
        """What `route` can certify at `lam`, or None. Same shape for both, so the walk can compare."""
        if route == "absolute":
            # SHORT, for the same reason the relative branch is: `largest_absolute_mu` bisects and
            # its pivots ran to 2,398 digits at one anchor of this very walk.
            M, _ = simple_absolute_mu(jmax, lam, floor_hi)
            if M is None:
                return None
            ok, _, pv, ev, _ = certify(jmax, lam, M)
            if not ok:
                return None
            shift, certified, trial = M, M, None
        else:
            # THE SHORT WITNESSES, not the exact ones. `largest_sturm_shift` bisects to a `2^60`
            # dyadic and the pivots computed from it run to six hundred digits -- exact, and
            # untranscribable: `norm_num` would be asked to verify seventeen such rationals per
            # anchor. `simple_sturm_shift` and `simple_trial` give a COARSER shift and vector, hence
            # a smaller certified gap and a smaller radius, which is weaker and still true; the walk
            # simply takes more steps. This is the same trade `emit_lean_relative` already makes.
            st, _, _ = simple_sturm_shift(jmax, lam, floor_hi)
            if st is None:
                return None
            v, gap, _ = simple_trial(jmax, lam, st, floor_hi)
            if v is None or gap is None or gap <= floor_hi:
                return None
            pv, ev, pok, _ = pivots(jmax, lam, st)
            if not pok:
                return None
            shift, certified, trial = st, gap, v
        neg = negatives(pv)
        # DERIVED: 1 is the reduction's own arity -- `hp` admits exactly one exceptional index.
        if len(neg) > 1:
            return None
        radius = (certified - floor_hi) / LIPSCHITZ
        # DERIVED: 0 is where a radius stops covering anything.
        if radius <= 0:
            return None
        return dict(lam=lam, route=route, shift=shift, radius=radius, certified=certified,
                    p=pv, e=ev, m=(neg[0] if neg else 0), trial=trial)

    anchors, unlifted = [], []
    lam, reach = lo, None
    while len(anchors) < max_points and lam <= hi:
        # WHICHEVER COVERS MORE. Riding one route until it fails and only then trying the other
        # stops dead at the absolute route's edge, where its radius collapses to ~1e-6 while the
        # relative route is certifying a gap of order 1 at the same coupling -- the walk took 68
        # steps to reach 1.99166 and then stopped, short of the range, for exactly that reason.
        cands = [c for c in (candidate(lam, "absolute"), candidate(lam, "relative")) if c]
        if not cands:
            break
        a = max(cands, key=lambda c: c["radius"])
        lifts, _, tneg, note = tail_lifts(jmax, lam, a["shift"])
        if not lifts:
            unlifted.append((lam, a["route"], note or f"{len(tneg)} negatives with the tail"))
        anchors.append(a)
        reach = lam + a["radius"]
        # DERIVED: the same convergence test as the other walks, but it now means BOTH routes have
        # collapsed here -- the better of the two was taken above.
        if reach - lam < Q(1, 10 ** 6):
            break
        # THE NEXT ANCHOR SITS AT A SHORT RATIONAL, rounded DOWN into the interval this one already
        # covers. The walk's exact position is a sum of exact radii and its denominator grows without
        # bound -- at one anchor the pivots computed from it ran to 2,226 digits, which is exact and
        # untranscribable. Rounding DOWN can only place the next anchor inside the covered region, so
        # it cannot open a gap; it only costs a slightly shorter step.
        nxt = Q(int(reach * LAM_DEN), LAM_DEN)
        # DERIVED: the rounding must still ADVANCE, or the walk stalls at a repeated coupling. When
        # it does not, the step is finer than the grid and the walk is at a route's edge anyway.
        if nxt <= lam:
            break
        lam = nxt
    return anchors, reach, unlifted


def lam_grid(lo: Q, hi: Q, steps: int):
    """A uniform rational grid on `[lo, hi]`, endpoints included."""
    return [lo + (hi - lo) * Q(k, steps) for k in range(steps + 1)]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    # DERIVED: the crossover image. `small_volume_enclosure` records that beta in [0.8, 2.6] maps to
    # lambda = c*beta^2 with c ~ O(1), so lambda in [0.16, 6.76] covers it for any c in [1/4, 1].
    ap.add_argument("--lo", default="0.16")
    ap.add_argument("--hi", default="6.76")
    # CHOSEN: how finely to sample the coupling range. It costs run time and nothing else -- each
    # coupling is certified on its own, and a coarser grid certifies fewer couplings rather than
    # certifying them less.
    ap.add_argument("--steps", type=int, default=60)
    ap.add_argument("--jmax", type=int, default=30)
    ap.add_argument("--mu", default=None, help="rational shift; default is MU_DEFAULT")
    ap.add_argument("--emit", default=None, help="write the CSV artifact to this path")
    ap.add_argument("--emit-lean", default=None,
                    help="write ONE certified coupling as a Lean file at this path")
    # DERIVED, and it is the tail that sets it -- not the gap value. `--lean-jmax` must be deep
    # enough that the TAIL BOUND LIFTS every theorem the file states from `HcellR jmax` to the cell
    # it truncates, which is `tail_lifts` at the shift each route actually uses. Measured across the
    # cover's 75 anchors: jmax = 4 lifts 10 of them, jmax = 6 lifts 70, jmax = 8 lifts all 75. So 8
    # is the smallest truncation at which the generated file is a statement about the physical cell.
    #
    # The previous default of 4 was justified on a WEAKER property -- that the certified gap does not
    # OVERSTATE the untruncated cell's -- which is true at 4 and is not sufficient: a theorem can
    # claim a gap the cell really has while its inertia argument still only holds for the truncation.
    # `emit_lean_all` now refuses rather than relying on this default being right.
    ap.add_argument("--emit-lean-cover", default=None,
                    help="write the INTERVAL cover as a Lean module at this path")
    # CHOSEN: 0 means every anchor. A small positive value emits only the first few, for
    # piloting the template against the kernel before spending a full build on it.
    ap.add_argument("--cover-limit", type=int, default=0)
    ap.add_argument("--lean-jmax", type=int, default=8)
    ap.add_argument("--lean-lam", default="1/2")
    a = ap.parse_args()

    mu = Q(a.mu) if a.mu else MU_DEFAULT
    klo, khi = check_mu_above_floor(mu)
    if a.emit_lean_cover:
        # The INTERVAL, in its own module. Not appended to `CellPivot`: Lean elaborates per file,
        # so peak memory is per file, and `CellPivot` at jmax = 8 already costs 1525 s and 15 GB.
        emit_lean_cover(a.emit_lean_cover, a.lean_jmax, mu, Q(a.lo), Q(a.hi), a.cover_limit)
        return 0
    if a.emit_lean:
        # The whole ABSOLUTE route in one file. A single coupling was enough to show the
        # transcription is mechanical; the open item was that only one was transcribed.
        emit_lean_all(a.emit_lean, a.lean_jmax, mu, list(lam_grid(Q(a.lo), Q(a.hi), a.steps)))
        return 0
    print(f"jmax = {a.jmax}  (dim = {dim(a.jmax)})")
    print(f"mu   = {mu} = {float(mu):.8f}  >  kappa_0 <= {float(khi):.8f}   (certified enclosure)")
    print(f"lambda grid: [{a.lo}, {a.hi}] in {a.steps} steps\n")

    lo, hi = Q(a.lo), Q(a.hi)
    print(f"  {'lambda':>8} {'route':>9} {'E1 >=':>10} {'E0 <=':>10} {'gap >=':>10}  verdict")
    good, bad = [], []
    for lam in lam_grid(lo, hi, a.steps):
        # ABSOLUTE first: one negative pivot at a shift above the floor is the strongest statement,
        # `E_1 >= mu > kappa_0` outright, and it needs no bound on `E_0` at all.
        ok, m, pv, ev, note = certify(a.jmax, lam, mu)
        if ok:
            good.append((lam, m, "absolute", mu, None, mu))
            print(f"  {float(lam):>8.4f} {'absolute':>9} {float(mu):>10.5f} {'-':>10} "
                  f"{float(mu):>10.5f}  CERTIFIED")
            continue
        # RELATIVE otherwise. Two negative pivots means two eigenvalues below the floor, so the
        # absolute statement is FALSE there and no amount of searching produces it. What a mass gap
        # asserts is still available: `E_1 - E_0` large, from a lower bound on `E_1` and an exact
        # Rayleigh upper bound on `E_0`.
        rok, e1, e0, gap, rnote = certify_relative(a.jmax, lam, khi)
        if rok:
            good.append((lam, None, "relative", e1, e0, gap))
            print(f"  {float(lam):>8.4f} {'relative':>9} {float(e1):>10.5f} {float(e0):>10.5f} "
                  f"{float(gap):>10.5f}  CERTIFIED")
        else:
            bad.append((lam, None, rnote or note))
            shown = f"{float(gap):>10.5f}" if gap is not None else f"{'-':>10}"
            print(f"  {float(lam):>8.4f} {'relative':>9} "
                  f"{(f'{float(e1):.5f}' if e1 is not None else '-'):>10} "
                  f"{(f'{float(e0):.5f}' if e0 is not None else '-'):>10} {shown}  DECLINED")

    print(f"\ncertified {len(good)} of {len(good) + len(bad)} couplings "
          f"({sum(1 for g in good if g[2] == 'absolute')} absolute, "
          f"{sum(1 for g in good if g[2] == 'relative')} relative)")
    if bad:
        print("  declined:")
        # CHOSEN: how many declines to print before summarising. Affects the terminal only; the
        # count and the artifact carry every one.
        for lam, _, note in bad[:12]:
            print(f"    lambda = {float(lam):7.4f}   {note}")
        # CHOSEN: the same print budget as the slice above.
        if len(bad) > 12:
            print(f"    ... and {len(bad) - 12} more")
    else:
        print(f"  every coupling on [{float(lo):.2f}, {float(hi):.2f}] carries a gap above "
              f"kappa_0 <= {float(khi):.8f}, by one route or the other")

    # A grid of certified points is not an interval. Weyl makes it one where the margins are large
    # enough to touch -- see `interval_cover`.
    reach, pts, unsafe = interval_cover(a.jmax, lo, khi, hi)
    if reach:
        print(f"\n  INTERVAL COVER (absolute route): [{float(lo):.2f}, {float(reach):.5f}] is covered "
              f"CONTINUOUSLY by {pts} adaptively spaced points, each covering a Weyl neighbourhood of "
              f"radius (mu_max - kappa_0)/{LIPSCHITZ}.")
        print(f"  Above {float(reach):.5f} the largest certifying shift has fallen to kappa_0 itself, "
              f"which is the absolute route's own edge.")
        rreach, rpts, runsafe = interval_cover_relative(a.jmax, reach, khi, hi)
        if rreach:
            print(f"  INTERVAL COVER (relative route): [{float(reach):.5f}, {float(rreach):.5f}] by "
                  f"{rpts} point(s) -- its margins are far larger, so each point covers much more.")
            bad = unsafe + runsafe
            if bad:
                print(f"  TRUNCATION WARNING: {len(bad)} cover anchor(s) are not tail-safe, so the "
                      f"cover is of `HcellR {a.jmax}` and NOT of the cell it truncates: "
                      f"{[float(x) for x in bad[:5]]}")
            else:
                print(f"  Every one of the {pts + rpts} anchors is tail-safe, so these are anchors "
                      f"for the CELL and not only for its truncation.")
            if rreach >= hi:
                print(f"  => the two routes together cover [{float(lo):.2f}, {float(hi):.2f}] "
                      f"CONTINUOUSLY. The certificate is no longer a grid of samples.")
            else:
                print(f"  => covered up to {float(rreach):.5f}; "
                      f"[{float(rreach):.5f}, {float(hi):.2f}] is still only sampled.")

    if a.emit:
        emit(a.emit, a.jmax, mu, good, lo, hi, a.steps, khi)
        print(f"wrote {a.emit}")
    return 0 if not bad else 1


def truncation_spread(lam: Q, mu: Q, floor_hi: Q, orders=(4, 8, 12, 16)):
    """How much the certified gap moves with the truncation `jmax` -- the Schur/Feshbach question.

    A bound that changed with `jmax` would be a bound on the truncation rather than on the cell. This
    reports the spread across several truncations so the reader can see which it is, rather than being
    told. Returns `(min, max, spread)` over the orders that certified, or `None` if any declined.
    """
    vals = []
    for j in orders:
        ok, _, _, _, _ = certify(j, lam, mu)
        if ok:
            vals.append(mu)
            continue
        rok, _, _, gap, _ = certify_relative(j, lam, floor_hi)
        if not rok:
            return None
        vals.append(gap)
    return min(vals), max(vals), max(vals) - min(vals)


def emit(path, jmax, mu, good, lo, hi, steps, floor_hi):
    """Write the certified couplings as a CSV artifact.

    Emitted as DATA, not as generated proof text: the pivots are what the theorem consumes, and a
    table a reader can recompute from this script is worth more than tactic blocks nobody reads. The
    truncation spread travels with each row for the same reason -- so "it does not depend on jmax" is
    something the artifact SHOWS rather than something the prose claims.
    """
    import csv
    with open(path, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        # `tail_shift` IS A COLUMN. The tail claim is an inertia claim at a shift, the two routes use
        # DIFFERENT shifts, and a row that does not say which one was used cannot be checked. The
        # absolute route's shift is `mu`; the relative route's is its own Sturm shift `E1_lower`,
        # which is negative above lam ~ 2.6.
        w.writerow(["lambda", "route", "jmax", "dim", "mu", "E1_lower", "E0_upper", "gap_lower",
                    "kappa0_upper", "clears_floor", "trunc_min", "trunc_max", "trunc_spread",
                    "tail_lifts", "tail_shift", "tail_m", "tail_negatives"])
        for lam, m, route, e1, e0, gap in good:
            tr = truncation_spread(lam, mu, floor_hi)
            # AT THE SHIFT THIS ROW'S CERTIFICATE USES, not at `mu` for both routes.
            shift = mu if route == "absolute" else e1
            safe, tm, tneg, _ = tail_lifts(jmax, lam, shift)
            w.writerow([f"{float(lam):.6f}", route, jmax, dim(jmax), f"{float(mu):.8f}",
                        f"{float(e1):.8f}" if e1 is not None else "",
                        f"{float(e0):.8f}" if e0 is not None else "",
                        f"{float(gap):.8f}", f"{float(floor_hi):.8f}",
                        "yes" if gap > floor_hi else "no",
                        f"{float(tr[0]):.8f}" if tr else "",
                        f"{float(tr[1]):.8f}" if tr else "",
                        f"{float(tr[2]):.2e}" if tr else "",
                        "yes" if safe else "no",
                        f"{float(shift):.8f}" if shift is not None else "",
                        "" if tm is None else tm,
                        "" if tneg is None else " ".join(str(i) for i in tneg)])


LEAN_TEMPLATE = """import MassGap.CellSpectrum

/-!
# MassGap.CellPivot \u2014 a generated rational pivot certificate, transcribed

`CellEnclosure.HcellR_gap_of_certificate` reduces the physical single-cell gap to producing rational
pivots `(p,e)` satisfying two recurrences. `certify/cell_pivot_certificate.py` produces them, in exact
rational arithmetic, across the whole crossover coupling range -- see
`data/9_14_dat_cell_pivot_certificate.csv`.

WHAT THIS ADDS, and what it does not. `CellSpectrum` already exhibits the certificate non-vacuously
by hand: `hcellR_gap_demo` (jmax=1, lam=1, absolute), `hcellR_gap_demo_param` (the same gap with the
pivots supplied by the `pivotSeq` recurrence rather than transcribed) and `hcellR_rel_gap_demo` /
`RelTileDemo` (jmax=2, the relative route at large coupling). None of those is superseded here and none
is duplicated.

**This file is generated by the certificate script** (`--emit-lean`), which is the difference. It closes
the loop between the CSV artifact and the Lean development -- one computation produces both, so they
cannot drift -- and it does so at `jmax = 4`, past the size at which a person transcribes pivots by hand.
What it establishes is that the artifact's remaining rows are transcription rather than open work.

`\u03bc = {mu_disp}` exceeds `\u03ba\u2080 = (1/4) log 3 = 0.2746530...`. No rational equals `\u03ba\u2080`, so the certificate
is stated at a rational strictly above it -- the stronger claim. The generator CHECKS that against the
certified enclosure of `\u03ba\u2080` rather than asserting it. Nothing below is rounded.
-/

namespace MassGap.CellPivot

open Matrix MassGap.CellEnclosure   -- `Matrix` for the relative route's quadratic form (`mulVec`, `dotProduct`)

/-- Pivots for `jmax = {jmax}`, `\u03bb = {lam_disp}`, shift `\u03bc = {mu_disp}`.
DERIVED: every entry is fixed by the two recurrences of `HcellR_gap_of_certificate` solved backwards
from the last index -- `p (n-1) = d (n-1) - \u03bc` and `p i = d i - \u03bc - \u03bb\u00b2 / p (i+1)`, with the Casimir
diagonal `d i = i(i+2)/4`. Nothing here is chosen or rounded; the denominators are what exact
rational arithmetic produces. Generated by `certify/cell_pivot_certificate.py --emit-lean`. -/
noncomputable def pv : Fin {n} \u2192 \u211d :=
  ![{pvec}]

/-- The matching multipliers.
DERIVED: `e (i+1) = -\u03bb / p (i+1)`, the second recurrence solved for `e`. `e 0` is constrained by
neither recurrence -- no `i` has `0 = i + 1` -- so it is free, and `0` is the value that says so. -/
noncomputable def ev : Fin {n} \u2192 \u211d :=
  ![{evec}]

/-- `dim {jmax}` and `{n}` are definitionally equal, but `Fin.sum_univ_succ` matches only the latter;
this transports the sum so the concrete expansion applies. -/
private theorem sum_bridge (f : Fin {n} \u2192 \u211d) :
    (\u2211 k : Fin (dim {jmax}), f k) = \u2211 k : Fin {n}, f k := rfl

set_option maxHeartbeats 2000000 in
/-- **The physical single-cell gap at `\u03bb = {lam_disp}`, above the entropy floor.** Every non-vacuum
eigenvalue of the SU(2) cell `HcellR {jmax} ({lam_disp})` exceeds the vacuum by at least
`{mu_disp} > \u03ba\u2080`. -/
theorem {name} :
    \u2203 i\u2080, (HcellR_isHermitian {jmax} ({lam_lit})).eigenvalues i\u2080 \u2264 0 \u2227
      \u2200 i, i \u2260 i\u2080 \u2192 (HcellR_isHermitian {jmax} ({lam_lit})).eigenvalues i\u2080 + ({mu_lit} : \u211d)
        \u2264 (HcellR_isHermitian {jmax} ({lam_lit})).eigenvalues i :=
  HcellR_gap_of_certificate {jmax} ({lam_lit}) ({mu_lit}) (by norm_num) pv ev {m}
    (by intro k hk; fin_cases k <;> simp_all [pv] <;> norm_num)
    (by
      intro i
      fin_cases i
      all_goals
        (rw [sum_bridge]
         simp only [pv, ev, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
           Matrix.cons_val_succ, Fin.val_succ, Fin.val_zero]
         norm_num))
    (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [pv, ev] <;> norm_num)

#print axioms {name}

end MassGap.CellPivot
"""


LEAN_HEADER = """import MassGap.CellSpectrum

/-!
# MassGap.CellPivot \u2014 generated rational pivot certificates, transcribed

`CellEnclosure.HcellR_gap_of_certificate` reduces the physical single-cell gap to producing rational
pivots `(p,e)` satisfying two recurrences. `certify/cell_pivot_certificate.py` produces them, in exact
rational arithmetic, across the whole crossover coupling range \u2014 see
`data/9_14_dat_cell_pivot_certificate.csv`.

**This file is generated by that script** (`--emit-lean`). It closes the loop between the artifact and
the development: one computation feeds both, so they cannot drift.

**{count} couplings, `\u03bb` from {lo} to {hi}, at `jmax = {jmax}` (`dim {n}`) \u2014 {n_abs} by the ABSOLUTE
route and {n_rel} by the RELATIVE one.**

The absolute route is a single negative pivot giving `E\u2081 \u2265 \u03bc` outright, with no bound on `E\u2080` needed. It
reaches up to about `\u03bb = 2`. Above that two pivots go negative, the absolute statement is FALSE, and the
relative route carries the rest: a Sturm shift `t` (no sign condition \u2014 it is negative at strong
coupling, which is why the route exists) bounding `E\u2081` from below, and a trial vector's Rayleigh
quotient bounding `E\u2080` from above. Couplings neither route reaches, and why:

{skipped}

`\u03bc = {mu_disp}` exceeds `\u03ba\u2080 = (1/4) log 3 = 0.2746530...`. No rational equals `\u03ba\u2080`, so the certificate is
stated at a rational strictly above it \u2014 the stronger claim \u2014 and the generator CHECKS that against the
certified enclosure rather than asserting it.

The TRUNCATION is bounded rather than assumed: `MassGap.CellTail` proves the recurrence is monotone in
its seed, so seeding it with a lower bound on the cell's true pivot at the last index bounds every
pivot below. See `certify/cell_pivot_certificate.tail_start` for where that bound closes.
-/

namespace MassGap.CellPivot

open Matrix MassGap.CellEnclosure   -- `Matrix` for the relative route's quadratic form (`mulVec`, `dotProduct`)

/-- `dim {jmax}` and `{n}` are definitionally equal, but `Fin.sum_univ_succ` matches only the latter;
this transports the sum so the concrete expansion applies. -/
private theorem sum_bridge (f : Fin {n} \u2192 \u211d) :
    (\u2211 k : Fin (dim {jmax}), f k) = \u2211 k : Fin {n}, f k := rfl
"""


COUPLING_TEMPLATE = """
/-- Pivots for `\u03bb = {lam_disp}` at `jmax = {jmax}`, shift `\u03bc = {mu_disp}`. Exact; generated.
DERIVED: every entry is fixed by the two recurrences of `HcellR_gap_of_certificate` solved backwards
from the last index \u2014 `p (n-1) = d (n-1) - \u03bc` and `p i = d i - \u03bc - \u03bb\u00b2 / p (i+1)`, with the Casimir
diagonal `d i = i(i+2)/4`. Nothing is chosen or rounded. -/
noncomputable def pv{tag} : Fin {n} \u2192 \u211d :=
  ![{pvec}]

/-- Multipliers for `\u03bb = {lam_disp}`.
DERIVED: `e (i+1) = -\u03bb / p (i+1)`, the second recurrence solved for `e`. `e 0` is constrained by
neither recurrence \u2014 no `i` has `0 = i + 1` \u2014 so it is free, and `0` is the value that says so. -/
noncomputable def ev{tag} : Fin {n} \u2192 \u211d :=
  ![{evec}]

set_option maxHeartbeats 2000000 in
/-- **The single-cell gap at `\u03bb = {lam_disp}`, above the entropy floor.** -/
theorem cell_gap{tag} :
    \u2203 i\u2080, (HcellR_isHermitian {jmax} ({lam_lit})).eigenvalues i\u2080 \u2264 0 \u2227
      \u2200 i, i \u2260 i\u2080 \u2192 (HcellR_isHermitian {jmax} ({lam_lit})).eigenvalues i\u2080 + ({mu_lit} : \u211d)
        \u2264 (HcellR_isHermitian {jmax} ({lam_lit})).eigenvalues i :=
  HcellR_gap_of_certificate {jmax} ({lam_lit}) ({mu_lit}) (by norm_num) pv{tag} ev{tag} {m}
    (by intro k hk; fin_cases k <;> simp_all [pv{tag}] <;> norm_num)
    (by
      intro i
      fin_cases i
      all_goals
        (rw [sum_bridge]
         simp only [pv{tag}, ev{tag}, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
           Matrix.cons_val_succ, Fin.val_succ, Fin.val_zero]
         norm_num))
    (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [pv{tag}, ev{tag}] <;> norm_num)

#print axioms cell_gap{tag}
"""


REL_TEMPLATE = """
/-- Pivots at the Sturm shift `t = {t_disp}` for `λ = {lam_disp}`, `jmax = {jmax}`.
DERIVED: the same backward recurrence as the absolute route, solved at `t` instead of `μ` —
`p (n-1) = d (n-1) − t`, `p i = d i − t − λ²/p (i+1)`, `d i = i(i+2)/4`. `t` carries no sign condition
and is negative here: at strong coupling the shift that isolates one eigenvalue lies below zero, which
is the whole reason this route exists. -/
noncomputable def rpv{tag} : Fin {n} → ℝ :=
  ![{pvec}]

/-- Multipliers at the same shift. DERIVED: `e (i+1) = −λ / p (i+1)`; `e 0` is unconstrained. -/
noncomputable def rev{tag} : Fin {n} → ℝ :=
  ![{evec}]

/-- A trial vector. DERIVED: nothing about it is special — the Rayleigh quotient of ANY nonzero vector
bounds `E₀` from above, so a coarse rational gives a weaker bound and a smaller certified gap, which is
still true. This is the ground-state direction rounded to a denominator of {vden}. -/
noncomputable def rvv{tag} : Fin {n} → ℝ :=
  ![{vvec}]

set_option maxHeartbeats 4000000 in
/-- **The single-cell gap at `λ = {lam_disp}`, RELATIVE route, above the entropy floor.**
Both lowest eigenvalues lie below the floor here, so the absolute statement is FALSE and this is what
carries the coupling: `E₁ ≥ t` from one negative pivot, `E₀ ≤ t − μ` from the trial vector. -/
theorem rel_cell_gap{tag} :
    ∃ i₀, (HcellR_isHermitian {jmax} {lam_lit}).eigenvalues i₀ ≤ {t_lit} - {mu_lit} ∧
      ∀ i, i ≠ i₀ → (HcellR_isHermitian {jmax} {lam_lit}).eigenvalues i₀ + {mu_lit}
        ≤ (HcellR_isHermitian {jmax} {lam_lit}).eigenvalues i :=
  HcellR_gap_of_certificate_rel {jmax} {lam_lit} {t_lit} {mu_lit} (by norm_num)
    rpv{tag} rev{tag} {m}
    (by intro k hk; fin_cases k <;> simp_all [rpv{tag}] <;> norm_num)
    (by
      intro i
      fin_cases i
      all_goals
        (rw [sum_bridge]
         simp only [rpv{tag}, rev{tag}, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
           Matrix.cons_val_succ, Fin.val_succ, Fin.val_zero]
         norm_num))
    (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [rpv{tag}, rev{tag}] <;> norm_num)
    rvv{tag}
    (by intro h; have := congrFun h {nonzero_index}; simp [rvv{tag}] at this)
    (by simp [rvv{tag}, HcellR, Hcell, mulVec, dotProduct, Fin.sum_univ_succ]; norm_num)

#print axioms rel_cell_gap{tag}
"""


def emit_lean_relative(path, jmax: int, mu: Q, lams, floor_hi: Q) -> None:
    """Every coupling the RELATIVE route carries, as one Lean file.

    The absolute emitter's counterpart. Two extra inputs per coupling, which is exactly what separates
    the routes: the Sturm shift `t` (from `simple_sturm_shift`, short enough to transcribe) and a
    trial vector (from `simple_trial`, likewise). Couplings the route declines are named, not dropped.
    """
    def lit(q: Q) -> str:
        # DERIVED: 1 is the denominator of an INTEGER -- Lean reads `(3)` and `(3 / 1)` the same
        # way, and the shorter form keeps the generated statements readable.
        return f"({q.numerator} / {q.denominator})" if q.denominator != 1 else f"({q.numerator})"

    def wrap(vals, indent="    "):
        out, line = [], ""
        for i, v in enumerate(vals):
            piece = f"{v.numerator} / {v.denominator}" + (", " if i + 1 < len(vals) else "")
            # CHOSEN: where to wrap the emitted Lean; cosmetic, as in the absolute emitter.
            if len(line) + len(piece) > 96:
                out.append(line.rstrip())
                line = ""
            line += piece
        out.append(line.rstrip())
        return ("\n" + indent).join(out)

    bodies, done, skipped = [], [], []
    for lam in lams:
        ok, _, _, _, _ = certify(jmax, lam, mu)
        if ok:
            continue                       # the absolute route carries this one
        tt, _, note = simple_sturm_shift(jmax, lam, floor_hi)
        if tt is None:
            skipped.append((lam, note))
            continue
        vv, gap, vnote = simple_trial(jmax, lam, tt, floor_hi)
        if vv is None:
            skipped.append((lam, vnote))
            continue
        pv, ev, pok, pnote = pivots(jmax, lam, tt)
        negs = negatives(pv)
        # DERIVED: one negative pivot is the theorem's hypothesis verbatim.
        if not pok or len(negs) != 1:
            skipped.append((lam, pnote or f"{len(negs)} negative pivots"))
            continue
        # the shift must exceed the trial bound by the shift the theorem is given
        mu_rel = gap
        # DERIVED: 0 is what `v ≠ 0` is about -- the proof of that hypothesis picks an index where
        # the vector is nonzero, and any such index serves. Not a threshold.
        nz = next(i for i, x in enumerate(vv) if x != 0)
        tag = f"_{lam.numerator}_{lam.denominator}"
        bodies.append(REL_TEMPLATE.format(
            jmax=jmax, n=dim(jmax), m=negs[0], tag=tag, nonzero_index=nz,
            lam_disp=f"{lam}", t_disp=f"{tt}", vden=max(x.denominator for x in vv),
            lam_lit=lit(lam), t_lit=lit(tt), mu_lit=lit(mu_rel),
            pvec=wrap(pv), evec=wrap(ev), vvec=wrap(vv)))
        done.append(lam)

    if path is not None:
        with open(path, "w", encoding="utf-8", newline="\n") as fh:
            fh.write("".join(bodies))
        print(f"wrote {path}: {len(done)} relative coupling(s)")
    return bodies, done, skipped


COVER_HEADER = """import MassGap.CellPerturb

/-!
# MassGap.CellCover \u2014 GENERATED. The coupling range as an INTERVAL, not a grid

`MassGap.CellPivot` states the certificate at {ncert} POINTS. This states it on `\u03bb \u2208 [{lo_disp},
{hi_disp}]` with nothing between the points, by giving each anchor a BALL it covers and chaining the
balls.

**{nanchor} anchors at `jmax = {jmax}` (`dim {n}`).** Each one carries its own certificate and its own
radius `r = (certified \u2212 \u03ba\u2080)/4`, so the gap it certifies survives the whole ball with `\u03ba\u2080` to spare
(`CellPerturb.cellGapAtLeast_of_ball`). The radius is EARNED, not chosen: a coupling whose certificate
only just clears the floor covers almost nothing, and the walk steps by exactly what each point earns.

**The `4` is proved, not cited.** `CellPerturb.adj_form_bound` bounds the adjacency form by `2\u2016v\u2016\u00b2`
from the row and column sums, and a gap is a difference of two eigenvalues, so it moves by at most
`4|\u0394\u03bb|`. No Weyl inequality is used anywhere \u2014 the two spectral facts the certificate rests on take
QUADRATIC FORMS, and forms are what move.

This file is generated by `certify/cell_pivot_certificate.py --emit-lean-cover`.
-/

namespace MassGap.CellCover

-- `Matrix` too: the relative anchors' Rayleigh proof names `mulVec` and `dotProduct`.
open Matrix MassGap.CellEnclosure

"""


COVER_ANCHOR = """
/-- Pivots for the anchor at `\u03bb = {lam_disp}`, shift `{t_disp}`, covering `\u00b1{r_disp}`.
DERIVED, every entry: the backward recurrence solved at this anchor's own shift \u2014
`p (n-1) = d (n-1) \u2212 s`, `p i = d i \u2212 s \u2212 \u03bb\u00b2/p (i+1)`, `d i = i(i+2)/4`. Nothing is chosen: both
recurrences are re-checked by the kernel in the theorem below, so a wrong entry cannot pass. -/
noncomputable def cpv{tag} : Fin {n} \u2192 \u211d :=
  ![{pvec}]

/-- Multipliers at the same shift. DERIVED: `e (i+1) = \u2212\u03bb / p (i+1)`; `e 0` is unconstrained. -/
noncomputable def cev{tag} : Fin {n} \u2192 \u211d :=
  ![{evec}]
{trialdef}
set_option maxHeartbeats 4000000 in
/-- **The cell gap on `[{lo_disp}, {hi_disp}]`** \u2014 one certificate, a whole interval.
DERIVED: the half-width is `(certified \u2212 \u03ba\u2080)/4`, this anchor's own earned radius, and the `4` is
`CellPerturb`'s proved Lipschitz constant (two eigenvalues, `2` each) \u2014 not a chosen tolerance. -/
theorem cover{tag} (lam : \u211d) (h1 : ({lo_lit} : \u211d) \u2264 lam) (h2 : lam \u2264 ({hi_lit} : \u211d)) :
    CellGapAtLeastR {jmax} lam {khi_lit} :=
  cellGapAtLeastR_mono (by norm_num)
    ({ctor} {jmax} {lam_lit} lam {r_lit} {targs}{mu_lit} (by norm_num)
      (by
        rw [abs_le]
        constructor <;> push_cast <;> linarith)
      cpv{tag} cev{tag} {m}
      (by intro k hk; fin_cases k <;> simp_all [cpv{tag}] <;> norm_num)
      (by
        intro i
        fin_cases i
        all_goals
          (rw [cover_sum_bridge]
           simp only [cpv{tag}, cev{tag}, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
             Matrix.cons_val_succ, Fin.val_succ, Fin.val_zero]
           norm_num))
      (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [cpv{tag}, cev{tag}] <;> norm_num){trialargs})

#print axioms cover{tag}
"""


# CHOSEN: `limit = 0` means every anchor. A small positive value emits only the first few, which is
# for PILOTING the template against the kernel before spending a full build on it -- two anchors
# caught a missing `open Matrix` in 71 s that would have cost twelve minutes at nineteen.
def emit_lean_cover(path, jmax: int, mu: Q, lo: Q, hi: Q, limit: int = 0) -> None:
    """The interval cover as a Lean module: a ball theorem per anchor, then the chain.

    ITS OWN MODULE, not appended to `CellPivot`. Lean elaborates per file, so peak memory is per
    file: `CellPivot` at `jmax = 8` already costs 1525 s and 15 GB, and putting the cover beside it
    would make the pair the largest single elaboration in the development for no reason.

    `limit` emits only the first `limit` anchors, for piloting the template against the kernel before
    spending a full build on it.
    """
    klo, khi = check_mu_above_floor(mu)
    anchors, reach, unlifted = cover_anchors(jmax, lo, khi, hi)
    if unlifted:
        raise SystemExit(
            f"REFUSING: {len(unlifted)} anchor(s) do not lift to the cell at jmax = {jmax}; "
            f"the cover would be of `HcellR {jmax}`. First: {unlifted[:3]}")
    if reach is None or reach < hi:
        raise SystemExit(
            f"REFUSING: the walk reached {reach}, short of {hi}; a partial cover is not an interval")
    if limit:
        anchors = anchors[:limit]

    def lit(q: Q) -> str:
        # DERIVED: 1 is the denominator of an INTEGER -- Lean reads `(3)` and `(3 / 1)` alike.
        return f"({q.numerator} / {q.denominator})" if q.denominator != 1 else f"({q.numerator})"

    def vec(vals):
        return ", ".join(lit(Q(v)) for v in vals)

    bodies = []
    for idx, a in enumerate(anchors):
        tag = f"_{idx}"
        r = a["radius"]
        lo_i, hi_i = a["lam"] - r, a["lam"] + r
        if a["route"] == "relative":
            ctor = "cellGapAtLeastR_of_ball"
            targs = f"{lit(a['shift'])} "
            trialdef = (f"\n/-- A trial vector. DERIVED: nothing about it is special \u2014 the Rayleigh\n"
                        f"quotient of ANY nonzero vector bounds `E\u2080` from above, so a coarse rational\n"
                        f"gives a weaker bound and a smaller certified gap, which is still true. This\n"
                        f"is the ground-state direction, rounded until the bound still clears the floor. -/\n"
                        f"noncomputable def cvv{tag} : Fin {dim(jmax)} \u2192 \u211d :=\n"
                        f"  ![{vec(a['trial'])}]\n")
            # DERIVED: the first NONZERO entry, which is what `v ≠ 0` is witnessed at. Zero is the
            # value being excluded, not a threshold -- `simple_trial` refuses an all-zero vector, so
            # this always finds one.
            nz = next(i for i, x in enumerate(a["trial"]) if x != 0)
            trialargs = (f"\n      cvv{tag}\n"
                         f"      (by intro h; have := congrFun h {nz}; simp [cvv{tag}] at this)\n"
                         # PROVED FOR `HcellR` AND CARRIED ACROSS. The Rayleigh bound is now
                         # stated about `HcellRr` at the rational anchor, but the `simp` set that
                         # evaluates it unfolds `Hcell`. `HcellR_eq_HcellRr` is exactly the rewrite
                         # that lets the rational evaluation discharge the real statement.
                         f"      (by rw [← HcellR_eq_HcellRr]; "
                         f"simp [cvv{tag}, HcellR, Hcell, mulVec, dotProduct, "
                         f"Fin.sum_univ_succ]; norm_num)")
        else:
            ctor = "cellGapAtLeastR_of_ball_abs"
            targs = ""
            trialdef, trialargs = "", ""
        bodies.append(COVER_ANCHOR.format(
            tag=tag, n=dim(jmax), jmax=jmax, m=a["m"],
            pvec=vec(a["p"]), evec=vec(a["e"]),
            trialdef=trialdef, trialargs=trialargs, ctor=ctor, targs=targs,
            lam_disp=f"{float(a['lam']):.6f}", t_disp=f"{float(a['shift']):.6f}",
            r_disp=f"{float(r):.6f}",
            lam_lit=lit(a["lam"]), r_lit=lit(r), mu_lit=lit(a["certified"]),
            khi_lit=lit(khi), lo_lit=lit(lo_i), hi_lit=lit(hi_i),
            lo_disp=f"{float(lo_i):.6f}", hi_disp=f"{float(hi_i):.6f}"))

    header = COVER_HEADER.format(
        ncert=61, nanchor=len(anchors), jmax=jmax, n=dim(jmax),
        lo_disp=f"{float(lo):.2f}", hi_disp=f"{float(hi):.2f}")
    bridge = (f"\n/-- `Fin (dim {jmax})` is `Fin {dim(jmax)}` by `rfl`, but `Nat.mul` is not reducible "
              f"enough for\n`Fin.sum_univ_succ` to fire through it. This transports the sum. -/\n"
              f"private theorem cover_sum_bridge (f : Fin {dim(jmax)} \u2192 \u211d) :\n"
              f"    (\u2211 k : Fin (dim {jmax}), f k) = \u2211 k : Fin {dim(jmax)}, f k := rfl\n")
    # ------------------------------------------------------------------ the chain
    # NO CHAIN UNDER `--cover-limit`. A pilot is a prefix of the walk, so a chain emitted from it
    # would claim the whole range from a handful of balls -- and its last `linarith` would fail,
    # which looks like a template defect rather than what it is. The pilot exercises the ANCHOR
    # template, which is the part being piloted.
    if limit:
        with open(path, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(header + bridge + "".join(bodies) + "\nend MassGap.CellCover\n")
        print(f"wrote {path}: {len(anchors)} PILOT anchor(s) at jmax = {jmax}; no chain emitted")
        return

    # THE ANCHORS ARE NOT AN INTERVAL UNTIL THEY ARE CHAINED. Each `cover_i` is a statement about
    # its own ball; the range statement is a case split that hands every `lam` to the first ball
    # whose upper end it does not exceed. The step that makes it work is that consecutive balls
    # OVERLAP -- `lo_(i+1) <= hi_i` -- which is what the walk guarantees by construction and what
    # `linarith` discharges here from the two rational literals.
    overlaps = []
    for i in range(1, len(anchors)):
        lo_i = anchors[i]["lam"] - anchors[i]["radius"]
        hi_prev = anchors[i - 1]["lam"] + anchors[i - 1]["radius"]
        if lo_i > hi_prev:
            overlaps.append((i, float(lo_i), float(hi_prev)))
    if overlaps:
        raise SystemExit(
            f"REFUSING: {len(overlaps)} consecutive anchors do not overlap, so the balls are a grid "
            f"and not an interval. First: anchor {overlaps[0][0]} starts at {overlaps[0][1]} but the "
            f"one before ends at {overlaps[0][2]}")
    last_hi = anchors[-1]["lam"] + anchors[-1]["radius"]
    # NOT under `--cover-limit`: a pilot is a deliberate prefix of the walk and cannot reach `hi`
    # by construction, so this guard would refuse every pilot. It still runs for a real emission,
    # which is the case that matters. The pilot's chain is emitted and says what it covers.
    if last_hi < hi and not limit:
        raise SystemExit(f"REFUSING: the last ball ends at {float(last_hi)}, short of {float(hi)}")
    first_lo = anchors[0]["lam"] - anchors[0]["radius"]
    if first_lo > lo:
        raise SystemExit(f"REFUSING: the first ball starts at {float(first_lo)}, above {float(lo)}")

    lines = [
        "",
        "/-- **The single-cell gap on the whole crossover range, as an INTERVAL.**",
        "",
        f"Not a grid of {len(anchors)} points: every rational `lam` in `[{float(lo):.2f}, "
        f"{float(hi):.2f}]` is handed to an anchor whose ball contains it, and consecutive balls",
        "overlap by construction. The radii are EARNED -- each is `(certified - kappa_0)/4` for that",
        "anchor's own certificate -- and the `4` is `CellPerturb`'s proved Lipschitz constant, not a",
        "cited Weyl inequality. -/",
        f"theorem cell_gap_on_range (lam : \u211d) (h1 : ({lit(lo)} : \u211d) \u2264 lam) "
        f"(h2 : lam \u2264 ({lit(hi)} : \u211d)) :",
        f"    CellGapAtLeastR {jmax} lam {lit(khi)} := by",
    ]
    for i, a in enumerate(anchors[:-1]):
        hi_i = a["lam"] + a["radius"]
        # `linarith` EVEN FOR THE FIRST anchor. Its ball starts BELOW the range (the walk's first
        # step is centred at `lo`, so it reaches `lo - radius`), so `h1 : lo <= lam` implies the
        # anchor's bound but is not literally it, and passing `h1` is a type mismatch.
        low = "(by linarith)"
        # `le_total`, not `le_or_lt`: the latter is not in this Mathlib. The second branch then
        # gives `hi_i <= lam` rather than `hi_i < lam`, which every `linarith` below uses the same.
        lines.append(f"  rcases le_total lam ({lit(hi_i)} : \u211d) with hc{i} | hc{i}")
        lines.append(f"  \u00b7 exact cover_{i} lam {low} hc{i}")
    n = len(anchors) - 1
    low = "(by linarith)"
    lines.append(f"  exact cover_{n} lam {low} (by linarith)")
    lines.append("")
    lines.append("#print axioms cell_gap_on_range")
    lines.append("")
    # NON-VACUITY, in the file itself. A range theorem whose hypotheses no concrete coupling
    # satisfies would elaborate, print a clean axiom footprint and say nothing. This fires it at
    # lam = 1 -- inside [0.16, 6.76] by inspection -- so the kernel checks that it applies.
    lines.append("/-- The range statement is NOT vacuous: it fires at a concrete coupling. -/")
    lines.append(f"example : CellGapAtLeastR {jmax} (1 : ℝ) {lit(khi)} :=")
    lines.append("  cell_gap_on_range 1 (by norm_num) (by norm_num)")
    chain = "\n".join(lines) + "\n"

    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(header + bridge + "".join(bodies) + chain + "\nend MassGap.CellCover\n")
    print(f"wrote {path}: {len(anchors)} anchor(s) at jmax = {jmax}, reach {float(reach):.5f}; "
          f"chained over [{float(lo)}, {float(hi)}]")


def emit_lean_all(path, jmax: int, mu: Q, lams) -> None:
    """Every coupling in `lams` that certifies by the ABSOLUTE route, as one Lean file.

    Couplings that decline are SKIPPED and named, not silently dropped: above roughly `lam = 2.1` two
    pivots go negative, the absolute statement is false there, and the relative route
    (`gap_of_ldl_one_neg_pivot_rel`) is what carries those. A file that quietly omitted them would
    read as if the range were covered.

    The tag on each declaration is the coupling with its punctuation removed, so the names say which
    coupling they belong to and cannot collide.
    """
    _klo, khi_pre = check_mu_above_floor(mu)
    def lit(q: Q) -> str:
        return f"{q.numerator} / {q.denominator}"

    def wrap(vals, indent="    "):
        out, line = [], ""
        for i, v in enumerate(vals):
            piece = lit(v) + (", " if i + 1 < len(vals) else "")
            # CHOSEN: where to wrap the emitted Lean. Cosmetic; Lean reads the vector the same way at
            # any width, and this keeps the generated file inside the project's line length.
            if len(line) + len(piece) > 96:
                out.append(line.rstrip())
                line = ""
            line += piece
        out.append(line.rstrip())
        return ("\n" + indent).join(out)

    bodies, done, skipped = [], [], []
    for lam in lams:
        ok, m, pvals, evals, note = certify(jmax, lam, mu)
        if not ok:
            skipped.append((lam, note))
            continue
        tag = "_" + str(lam.numerator) + "_" + str(lam.denominator)
        bodies.append(COUPLING_TEMPLATE.format(
            jmax=jmax, n=dim(jmax), m=m, tag=tag,
            lam_disp=f"{lam}", mu_disp=f"{mu}", lam_lit=lit(lam), mu_lit=lit(mu),
            pvec=wrap(pvals), evec=wrap(evals)))
        done.append(lam)

    # REFUSE A TRUNCATION THE TAIL CANNOT LIFT. Every theorem this file states is an inertia claim
    # at a shift, and it is a claim about the CELL only where `pivots_with_tail` at THAT shift carries
    # at most one negative. Where it does not, the theorem is still true of `HcellR jmax` and false as
    # a statement about the cell -- which is precisely the reading the file's own header invites.
    # This is checked, not assumed, because the default was wrong for exactly this reason.
    unlifted = []
    for lam in lams:
        shift, route = certifying_shift(jmax, lam, mu, khi_pre)
        if shift is None:
            continue
        lifts, _, neg, note = tail_lifts(jmax, lam, shift)
        if not lifts:
            unlifted.append((lam, route, note or f"{len(neg)} negatives with the tail included"))
    if unlifted:
        raise SystemExit(
            f"REFUSING to emit at jmax = {jmax}: the tail bound does not lift "
            f"{len(unlifted)} of {len(lams)} coupling(s) to the cell, so those theorems would be\n"
            f"  statements about `HcellR {jmax}` and not about the cell it truncates. First few:\n"
            + "\n".join(f"    lam = {lam} ({route}): {why}" for lam, route, why in unlifted[:6])
            + f"\n  Raise --lean-jmax. Measured minimum across the cover's anchors: 8.")

    # THE RELATIVE ROUTE CARRIES THE REST, and it belongs in the same file: the crossover range is one
    # range, and splitting it across two files would invite a reader to think one half is provisional.
    rel_bodies, rel_done, rel_skipped = emit_lean_relative(None, jmax, mu, lams, khi_pre)

    header = LEAN_HEADER.format(
        jmax=jmax, n=dim(jmax), mu_disp=f"{mu}", count=len(done) + len(rel_done),
        lo=f"{done[0]}" if done else "-",
        hi=f"{rel_done[-1]}" if rel_done else (f"{done[-1]}" if done else "-"),
        n_abs=len(done), n_rel=len(rel_done),
        skipped=("\n".join(f"  {lam}: {note}" for lam, note in rel_skipped) or "  (none)"))
    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(header
                 + "\n/-! ### The ABSOLUTE route -- one negative pivot gives `E_1 >= mu` outright -/\n"
                 + "".join(bodies)
                 + "\n/-! ### The RELATIVE route -- both lowest eigenvalues below the floor -/\n"
                 + "".join(rel_bodies)
                 + "\nend MassGap.CellPivot\n")
    print(f"wrote {path}: {len(done)} absolute + {len(rel_done)} relative = "
          f"{len(done) + len(rel_done)} coupling(s) at jmax = {jmax}; "
          f"{len(rel_skipped)} carried by neither")


def emit_lean(path, jmax: int, lam: Q, mu: Q, name: str = "cell_gap_certified") -> None:
    """Render one certified coupling as a Lean file the kernel accepts verbatim.

    WHY GENERATE RATHER THAN HAND-WRITE. The pivots are ratios of integers twenty-odd digits long at
    `dim 5` and worse above it; nobody transcribes those by hand twice the same way. Generating them
    also means the Lean statement and the CSV artifact come from ONE computation, so they cannot drift.

    WHAT THE TACTICS DO, and why they are what they are. `hrecD`'s sum is over `Fin (dim jmax)`.
    `Fin.sum_univ_succ` matches `Fin (n+1)` only up to reducible unfolding, and `dim jmax` reduces to a
    numeral by `Nat.mul`, which is not reducible -- so the sum does not expand until `sum_bridge`
    transports it across the definitional equality. That single `rfl` is the whole difficulty; the rest
    is `norm_num` on exact rationals.

    This REFUSES rather than emitting a file that will not compile: if the coupling does not certify by
    the absolute route at this truncation, there are no pivots to write down.
    """
    ok, m, pvals, evals, note = certify(jmax, lam, mu)
    if not ok:
        raise SystemExit(f"cannot emit: lambda = {lam} declines the absolute route at jmax = {jmax}"
                         f" ({note}). The relative route needs a different theorem"
                         f" (`gap_of_ldl_one_neg_pivot_rel`), not this template.")

    def lit(q: Q) -> str:
        return f"{q.numerator} / {q.denominator}"

    def wrap(vals, indent="    "):
        out, line = [], ""
        for i, v in enumerate(vals):
            piece = lit(v) + (", " if i + 1 < len(vals) else "")
            # CHOSEN: where to wrap the emitted Lean. Cosmetic -- Lean reads the vector the same way
            # at any width; this keeps the generated file inside the project's line length.
            if len(line) + len(piece) > 96:
                out.append(line.rstrip())
                line = ""
            line += piece
        out.append(line.rstrip())
        return ("\n" + indent).join(out)

    text = LEAN_TEMPLATE.format(
        jmax=jmax, n=dim(jmax), m=m, name=name,
        lam_disp=f"{lam}", mu_disp=f"{mu}",
        lam_lit=lit(lam), mu_lit=lit(mu),
        pvec=wrap(pvals), evec=wrap(evals))
    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(text)
    print(f"wrote {path}: jmax = {jmax}, dim = {dim(jmax)}, lambda = {lam}, mu = {mu}, "
          f"negative pivot at index {m}")


if __name__ == "__main__":
    raise SystemExit(main())
