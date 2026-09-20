"""REFUTATION PROBE: is the free-field lag-two ratio bounded UNIFORMLY over the toron moduli space?

## What is being tested, and why it would matter

The remaining extent-six obligation is `rho(2) <= K rho(0)` with `K < lagTwoThresholdSix`
(`MassGap.LagTwoSix`), and the weak-coupling route reaches it through the Gaussian limit of the
Wilson measure. That limit is a Laplace expansion around the MINIMA of the action, which for SU(3)
on the four-torus are the flat connections -- commuting quadruples `(U_0,U_1,U_2,U_3)` modulo
simultaneous conjugation, a POSITIVE-DIMENSIONAL moduli space (torons), not an isolated point. A
degenerate Laplace expansion needs the measure induced on that space, and that is a research paper.

THE SUBSTITUTION THIS PROBE TESTS. The obligation is a RATIO. If the free ratio evaluated in EVERY
flat background is under the threshold, then the measure on the moduli space is never needed -- an
average of quantities each below a bound is below that bound, whatever the measure. "Perform a
degenerate Laplace expansion" would become "bound a ratio uniformly on a compact set".

TWO THINGS THAT SUBSTITUTION DOES NOT DO, both found by an adversarial reading of an earlier draft
and both measured or stated below rather than left implicit:

  * IT NEEDS A SECOND UNIFORM QUANTITY, not one. `wilsonCorrConn` subtracts `<phi><phi>` over the
    FULL measure, so `rho(d) = E_mu[rho_A(d)] + Var_mu(<phi>_A)`: the moduli integral adds a term
    that no per-background ratio contains. It is non-negative, `d`-independent, the same order in
    the coupling, and it moves the ratio TOWARD one. `disconnected_variance` bounds it over every
    law `mu` at once, by Popoviciu on the same compact set, and folds it into the verdict.

  * IT DOES NOT RETIRE THE EXPANSION ON THE ENHANCED-SYMMETRY STRATUM. Where a root's shift
    vanishes, that root's CONSTANT mode has `qhat^2 = 0`: a flat direction of the quadratic form,
    quartic at the next order because constant non-commuting `A` has `[A_mu, A_nu] != 0`. So the
    Gaussian formula this script evaluates is not valid AT that stratum, and the closure value
    computed here is the limit of a formula whose derivation fails at the limit point. The stratum
    has positive codimension, and the limit sits below the interior sup, so the verdict does not
    turn on it -- but it is a separate, quartic, obligation, not one the sup absorbs.

WHAT THIS SCRIPT CAN AND CANNOT DO. It can REFUTE. If the supremum it finds reaches or exceeds the
threshold, the substitution is dead and no further analysis is needed. If it does not, NOTHING is
established: the sweep failed to refute over the backgrounds actually visited, and no number
produced here may enter a proof or be fitted to. The rigorous statement, if anyone wants it, is a
theorem about the function defined below, not about this output.

## The object

Around a flat background the adjoint quadratic form is the COVARIANT Laplacian and nothing else: the
"spin" term of the fluctuation operator is proportional to the background field strength, which
vanishes identically on a flat connection. On the generic stratum a commuting quadruple is
simultaneously diagonalisable, `U_mu = diag(e^{i t_mu^1}, e^{i t_mu^2}, e^{i t_mu^3})` with
`sum_a t_mu^a = 0`, and the adjoint representation splits into the eight weights of su(3): six roots
`alpha_{ab}` with shift `phi_mu(ab) = t_mu^a - t_mu^b`, and two Cartan directions with shift zero.

In the sector of weight `w` the covariant difference operator is `e^{i(p_mu + phi_mu(w))} - 1`, so
every momentum in the free computation is SHIFTED by the weight's pairing with the toron angles:

    H_phi(d) = (1/V) sum_k e^{i q_2 d} (qhat_0^2 + qhat_1^2) / qhat^2,
    q_mu = 2 pi k_mu / n + phi_mu,   qhat_mu^2 = 4 sin^2(q_mu / 2).

THE SUM IS COMPLEX AWAY FROM `phi = 0`, AND THE IMAGINARY PART IS PART OF THE ANSWER. The shifted
grid `{p + phi}` is NOT symmetric under `q -> -q`, so the sine part

    S_phi(d) = (1/V) sum_k sin(q_2 d) (qhat_0^2 + qhat_1^2) / qhat^2

does not cancel. It vanishes identically at `phi = 0` -- and at every `phi` with `phi_2 = 0`, by the
same reflection -- which is exactly why a positive control at the trivial background CANNOT see it.
It is carried explicitly: the physical per-weight lag ratio is

    r(phi) = |H_phi(2)|^2 / |H_phi(0)|^2 = (C_phi(2)^2 + S_phi(2)^2) / C_phi(0)^2

where `C` is the cosine part. `H_phi(0)` is real because `sin 0 = 0`. Dropping `S` would understate
the ratio everywhere `phi_2 != 0`, so both parts are reported and the cosine-only value is printed
beside the full one.

WHY THE MODULUS AND NOT THE REAL PART. In the periodic background gauge the adjoint field is a
periodic function, so `<F^w(x) F^{-w}(0)> = e^{-i phi.x} H_phi(x)`, carrying a phase that is not
gauge invariant on its own. Wick pairs `w` with `-w`, and `H_{-phi} = conj(H_phi)`, so the two
phases cancel in the product and the observable sees `H_phi(d) H_{-phi}(d) = |H_phi(d)|^2`. Nothing
in the answer depends on the phase convention; the modulus is what survives it.

`phi = 0` is the trivial background and returns `certify/free_field_lag_two_ratio.py`'s exact
rational `D(2)/D(0) = 5875/259259`; that is this script's first positive control. `4 sin^2(q/2)` is
`2 - 2 cos q` rewritten -- the same number, evaluated without the cancellation that destroys every
significant digit of `2 - 2 cos q` as `q -> 0`, which is exactly the regime the degenerate locus
lives in.

THE GAUGE PARAMETER STILL DROPS OUT, and for exactly the reason it did at the trivial background.
`FreeFieldLagTwo.fieldStrength_pure_gauge_orthogonal` is the polynomial identity
`(a-1)(-(b-1)) + (b-1)(a-1) = 0` in two FREE variables; putting `a = e^{i q_0}`, `b = e^{i q_1}` with
shifted `q` uses no property of `q` at all. The alpha sweep below cross-checks the one-line
transverse formula against the full `mu,nu` double sum at SHIFTED momenta, and a deliberately
perturbed vertex must break that cross-check or it is vacuous.

## Two reductions that make the sweep finite, and both are checked numerically

REDUCTION ONE -- THE SUP IS OVER ONE SHIFT VECTOR, NOT THE WHOLE MODULI SPACE. Wick's theorem makes
the connected plaquette correlation a sum over weights of moduli squared,
`rho_A(d) = 2 sum_w |H_w(d)|^2`, so

    rho_A(2)/rho_A(0) = sum_w H_w(0)^2 r_w / sum_w H_w(0)^2,   r_w = |H_w(2)|^2 / H_w(0)^2

is a weighted AVERAGE of the per-weight ratios with strictly positive weights (`H_w(0)` is a sum of
non-negative terms). Hence `rho_A(2)/rho_A(0) <= max_w r_w`, and since any `phi` in R^4 arises as
`alpha_{12}` of some quadruple (`t_2 = (v-u)/3`, `t_1 = t_2+u`, `t_3 = t_2-v` solves it for any
`u,v`), the sup of `max_w r_w` over the moduli space is exactly `sup_{phi in T^4} r(phi)`. That is a
FOUR-dimensional sup, and it is conservative: the three roots are not independent
(`alpha_13 = alpha_12 + alpha_23`), so no quadruple puts all of them at the argmax, and the two
Cartan weights pin two of the eight terms at the trivial value whatever the background. Both
objects are reported, and the eight-dimensional average is swept on its own so the gap between them
can be read rather than asserted.

REDUCTION TWO -- THE DOMAIN IS A TORUS OF SIDE `2 pi / n`. Shifting one component of `phi` by
`2 pi / n` relabels `k_mu -> k_mu + 1` and leaves every term of both sums fixed, so `H_phi` is
periodic with period `2 pi / n` in each component. The fundamental domain is compact. It is also
where the degeneracy question is settled: `qhat^2 = 0` needs `q_mu = 0 mod 2 pi` for ALL four `mu`,
i.e. `phi in (2 pi / n) Z^4`, which inside the fundamental domain is the single point `phi = 0`.

## The degenerate locus, and why the ratio cannot diverge there

Where a nonzero adjoint weight pairs to zero with the toron angles a massive mode becomes massless,
and the suspicion is that `H(0)` and `H(2)` blow up. They cannot. Every term of both sums is
`(qhat_0^2 + qhat_1^2) / qhat^2` times a sinusoid, and `qhat_0^2 + qhat_1^2 <= qhat^2` with both
sides non-negative, so every term lies in `[-1, 1]` at every `phi` whatever. The transverse
numerator vanishes on the zero mode exactly when the denominator does; the term is `0/0` in form,
its limit along `phi = eps e` is `e_0^2 + e_1^2` in `[0,1]`, it enters `C(0)` and `C(2)` with the
same weight `1/V`, and it contributes nothing to `S(2)` (`sin(2 q_2) -> 0`). So the pieces do not
diverge, and the closure value at the degenerate point is the exact rational
`((D(2) + s/V) / (D(0) + s/V))^2` with `s = e_0^2 + e_1^2` in `[0,1]` -- increasing in `s` because
`D(2) < D(0)`, so its largest value is at `s = 1` and is computed in `Fraction`, not sampled.

That is an argument, not a measurement; the script checks it by approaching the locus along many
directions and reporting the limit of the RATIO, by asserting `|term| <= 1` on every sample, and by
evaluating exactly ON the locus, where the periodicity must restore the trivial value.

Run: `python research/code/remote_run.py certify/toron_lag_two_sup.py`
     `python research/code/remote_run.py certify/toron_lag_two_sup.py --quick`   (smoke test)
"""
from __future__ import annotations

import argparse
import itertools
import math
import os
import sys
import time
from fractions import Fraction

# CHOSEN: one thread. The compute host is shared with other live sessions. This kernel is
# elementwise numpy over arrays of a few million doubles, which no threaded BLAS touches at all, so
# threads would buy nothing here and could starve a neighbour. Set before numpy is imported, which
# is the only point at which it binds.
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS",
           "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

try:
    os.nice(19)
except (AttributeError, OSError):
    pass

import numpy as np                                                       # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import free_field_lag_two_ratio as FF                                    # noqa: E402

# DERIVED: four is the dimension of the Yang-Mills problem, not a tuning; `corrClay` fixes `d := 4`.
DIM = 4

# DERIVED: the two in-plane directions of the plaquette and the transverse direction the lag runs
# along, exactly as `WilsonBridge.corrClay` fixes them. Naming freedom on a periodic lattice, not a
# choice of magnitude.
PLANE = (0, 1)
# DERIVED: continues the line above -- direction two is the one the lag runs along, transverse to
# the plaquette plane, as `corrHyper 3 n 0 1 2` fixes it. It names an axis; it is not a magnitude.
LAG_DIR = 2

# DERIVED: the extent is `N+1` for `wilsonCorrAt N`, and the surviving obligation is at `N = 5`.
EXTENT = 6

# DERIVED: the lag the obligation is about -- `wilsonCorrAt 5 beta 2`.
LAG = 2

# DERIVED: the extent-four extent, carried only as a corroborating second lattice. The obligation is
# not stated there; `LagTwoBound.lagTwoThreshold` is a different, smaller threshold.
EXTENT_ALT = 4

# DERIVED: `LagTwoSix.lagTwoThresholdSix_gt` proves `0.0337 < lagTwoThresholdSix`. The threshold is
# used here as the LOWER bracket, i.e. rounded AGAINST the claim `sup < threshold`: anything that
# clears 0.0337 clears the true threshold, and anything that fails 0.0337 has not yet failed the
# true one. The true value is 0.03379588...; nothing here uses the extra digits.
THRESHOLD_SIX = 0.0337

# DERIVED: `LagTwoBound.lagTwoThreshold_gt` proves `0.018623 < lagTwoThreshold`, same direction.
THRESHOLD_FOUR = 0.018623

# The UPPER brackets, for the opposite comparison. A CLEARANCE claim (`bound < threshold`) must use
# the lower bracket above; a REFUTATION claim (`bound >= threshold`) must use an upper one, or a
# value between the bracket and the truth would be announced as a refutation it has not earned.
# DERIVED at extent four: `LagTwoBound.lagTwoThreshold_lt` proves `lagTwoThreshold < 0.018625`.
CEILING_FOUR = 0.018625
# CHOSEN at extent six, because the tree has no `lagTwoThresholdSix_lt` to derive it from.
# `LagTwoSix`'s header STATES `lagTwoThresholdSix = 0.03379588…`, and `0.0338` is above that; it is
# a stated value, not a theorem, and it is used only to make a refutation harder to announce.
CEILING_SIX = 0.0338

# CHOSEN: the batch width of the vectorised sweep. It divides the same total work into pieces and
# changes no result; it trades peak memory (`B * n^DIM` doubles per live array) against loop
# overhead. 2048 keeps the working set near a hundred megabytes on the shared host.
BATCH = 2048

# DERIVED, and the derivation is arithmetic, not a tolerance to taste. A zero mode is `q_mu = 0 mod
# 2 pi` in all four directions, which happens on `phi in (2 pi / n) Z^4`. There `q_mu` is computed as
# `2 pi k / n + phi_mu` in double precision and is a few ulps of `2 pi` away from zero, below
# `1e-14`, so `qhat^2 = sum 4 sin^2(q_mu/2)` lands below `1e-28` -- NOT at exactly zero, which is why
# testing `qhat^2 == 0` silently mistook such a point for an ordinary mode and returned one
# approach direction's limit as though it were a value. The closest deliberate approach anywhere in
# this script is `|phi| = 1e-11`, giving `qhat^2` near `1e-22`. Any bound strictly between `1e-28`
# and `1e-22` separates the two; this is their geometric midpoint. Both sides are asserted: the
# locus is detected (`control_degenerate_locus`) and the ladder is not (`zero_mode_limit`).
ZERO_MODE_GUARD = 1e-25

# CHOSEN: the agreement bound for the positive controls and the identity checks. It is a
# float-comparison tolerance on quantities of order one computed by summing ~1300 terms, about four
# orders above the accumulated double-precision rounding and far below any effect under discussion.
AGREE = 1e-11


def base_momenta(n: int) -> np.ndarray:
    """The `n^DIM` lattice momenta `2 pi k / n`, shape `(V, DIM)`.

    DERIVED: `2 pi k / n` is the periodic momentum of extent `n`; nothing in it is a parameter.
    """
    ks = np.array(list(itertools.product(range(n), repeat=DIM)), dtype=np.float64)
    return 2.0 * np.pi * ks / n


def _hat_sq(q: np.ndarray) -> np.ndarray:
    """`qhat^2 = 4 sin^2(q/2)`, the lattice momentum square, in the stable form. See the header."""
    s = np.sin(0.5 * q)
    return 4.0 * s * s


def weight_corr(phis: np.ndarray, base: np.ndarray, lag: int, *,
                defect: str | None = None):
    """`(C_phi(0), C_phi(lag), S_phi(lag))` for a batch of shift vectors, plus two instrument
    readings.

    `phis` is `(B, DIM)`. `C` is the cosine part and `S` the sine part of `H_phi`; `H_phi(0)` is
    real, so only `C(0)` is returned for the lag-zero end. Also returns the number of terms dropped
    as zero modes, and the largest `|term|` seen -- which the caller checks against one, since
    `qhat_0^2 + qhat_1^2 <= qhat^2` is an identity and a violation would mean the kernel is wrong.

    `defect` is the deliberate breakage that makes the sweep non-vacuous, and it is NOT a physical
    variant: `"unshifted_numerator"` and `"unshifted_denominator"` build the transverse numerator
    and the lattice Laplacian from the UNSHIFTED momenta, and `"real_part_only"` throws away `S`,
    which is the defect this script shipped in its first draft and which the trivial-background
    control cannot see. Each coincides with the real kernel at `phi = 0` and must differ from it
    away from `phi = 0`, or the sweep is measuring nothing about the background.

    `"unshifted_lag_phase"` is NOT in that list, because it is not a defect: see
    `control_lag_phase_rotation`. It is offered here so that identity can be checked.
    """
    den = None
    num = None
    cphase = None
    sphase = None
    for mu in range(DIM):
        shift = phis[:, mu][:, None]
        q = base[None, :, mu] + shift
        flat = base[None, :, mu] + 0.0 * shift
        h = _hat_sq(q)
        hd = _hat_sq(flat) if defect == "unshifted_denominator" else h
        den = hd if den is None else den + hd
        if mu in PLANE:
            hn = _hat_sq(flat) if defect == "unshifted_numerator" else h
            num = hn if num is None else num + hn
        if mu == LAG_DIR:
            qp = flat if defect == "unshifted_lag_phase" else q
            cphase = np.cos(lag * qp)
            sphase = np.zeros_like(qp) if defect == "real_part_only" else np.sin(lag * qp)
    live = den > ZERO_MODE_GUARD
    term = np.where(live, num / np.where(live, den, 1.0), 0.0)
    dropped = int(term.size - int(live.sum()))
    worst = float(np.abs(term).max()) if term.size else 0.0
    volume = base.shape[0]
    return (term.sum(axis=1) / volume, (cphase * term).sum(axis=1) / volume,
            (sphase * term).sum(axis=1) / volume, dropped, worst)


def ratio(phis: np.ndarray, base: np.ndarray, lag: int, **kw):
    """`r(phi) = |H_phi(lag)|^2 / H_phi(0)^2`, the per-weight lag ratio. `H_phi(0) > 0` always.

    Returns `(r, C(0), C(lag), S(lag), dropped, worst)`.
    """
    c0, cl, sl, dropped, worst = weight_corr(phis, base, lag, **kw)
    return (cl * cl + sl * sl) / (c0 * c0), c0, cl, sl, dropped, worst


def gauge_alpha_value(phi, n, lag, alpha, drop_second_plane_leg=False):
    """`H_phi(lag)` from the FULL covariant-gauge propagator at SHIFTED momenta, as a `mu,nu` sum.

    The same cross-check `free_field_lag_two_ratio.gauge_alpha_value` performs at the trivial
    background, carried onto the shifted grid: `P_{mu nu} = [delta - (1-alpha) L_mu conj(L_nu) /
    qhat^2] / qhat^2` with `L_mu = 1 - e^{-i q_mu}`, contracted with the field-strength vertex
    `v_0 = -(e^{i q_1} - 1)`, `v_1 = e^{i q_0} - 1`. Nothing is pre-simplified. Agreement with the
    one-line transverse formula at every alpha is the check; `drop_second_plane_leg` is the
    deliberate defect that must break it. Returns `(C, S)`, both parts.
    """
    volume = n ** DIM
    total = 0.0
    total_s = 0.0
    for k in itertools.product(range(n), repeat=DIM):
        q = [2.0 * math.pi * k[mu] / n + phi[mu] for mu in range(DIM)]
        hats = [4.0 * math.sin(0.5 * q[mu]) ** 2 for mu in range(DIM)]
        s = sum(hats)
        if s <= ZERO_MODE_GUARD:
            continue
        a = complex(math.cos(q[PLANE[0]]), math.sin(q[PLANE[0]]))
        b = complex(math.cos(q[PLANE[1]]), math.sin(q[PLANE[1]]))
        v = [0j] * DIM
        v[PLANE[0]] = -(b - 1.0)
        v[PLANE[1]] = a - 1.0
        if drop_second_plane_leg:
            v[PLANE[1]] = 0j
        lv = [1.0 - complex(math.cos(q[mu]), -math.sin(q[mu])) for mu in range(DIM)]
        m = 0j
        for mu in range(DIM):
            for nu in range(DIM):
                pr = (1.0 if mu == nu else 0.0) / s
                pr -= (1.0 - alpha) * lv[mu] * lv[nu].conjugate() / (s * s)
                m += v[mu].conjugate() * pr * v[nu]
        total += math.cos(lag * q[LAG_DIR]) * m.real
        total_s += math.sin(lag * q[LAG_DIR]) * m.real
    return total / volume, total_s / volume


# ---------------------------------------------------------------------------------------------
# Controls. Each one would FIRE if the instrument were broken, and each is reported before any
# sweep number is printed.
# ---------------------------------------------------------------------------------------------

def control_trivial_background(base, n, lag):
    """POSITIVE CONTROL ONE: at `phi = 0` the kernel must return the exact rational of the tree.

    `free_field_lag_two_ratio.field_strength_corr` computes `D(d)` in `fractions.Fraction` with no
    float anywhere. If the shifted kernel does not reproduce it at zero shift, every sweep number
    below is a reading of a different function and the run stops.

    Returns the trivial ratio and the exact CLOSURE value at the degenerate locus -- the largest
    limit of `r` as `phi -> 0`, `((D(lag) + 1/V)/(D(0) + 1/V))^2`, in `Fraction` and then floated
    once at the end. It is an exact rational because the dropped `0/0` term's limit along `phi =
    eps e` is `e_0^2 + e_1^2`, largest at one, and it lands on `C(0)` and `C(lag)` alike.
    """
    exact0 = FF.field_strength_corr(n, 0)
    exactl = FF.field_strength_corr(n, lag)
    volume = n ** DIM
    closure = ((exactl + Fraction(1, volume)) / (exact0 + Fraction(1, volume))) ** 2
    phis = np.zeros((1, DIM))
    r, c0, cl, sl, dropped, worst = ratio(phis, base, lag)
    print(f"  exact D(0)   = {exact0} = {float(exact0):.12f}   kernel {c0[0]:.12f}")
    print(f"  exact D({lag})   = {exactl} = {float(exactl):.12f}   kernel {cl[0]:.12f}")
    print(f"  exact D({lag})/D(0) = {exactl / exact0} = {float(exactl / exact0):.12f}")
    print(f"  exact (D({lag})/D(0))^2 = {float((exactl / exact0) ** 2):.12f}   "
          f"kernel {r[0]:.12f}   sine part S({lag}) = {sl[0]:.3e} (must be zero here)")
    print(f"  zero modes dropped at phi = 0: {dropped} of {base.shape[0]};  "
          f"max |term| = {worst:.6f}")
    print(f"  exact CLOSURE value at the degenerate locus ((D({lag})+1/V)/(D(0)+1/V))^2 = "
          f"{closure} = {float(closure):.12f}")
    assert abs(c0[0] - float(exact0)) < AGREE, (c0[0], float(exact0))
    assert abs(cl[0] - float(exactl)) < AGREE, (cl[0], float(exactl))
    assert abs(sl[0]) < AGREE, sl[0]
    assert abs(r[0] - float((exactl / exact0) ** 2)) < AGREE
    # DERIVED: one zero mode. `qhat^2 = 0` at `phi = 0` happens at `k = 0` and nowhere else on the
    # grid, so exactly one term of `V` is dropped. A different count means the guard is catching
    # momenta the lattice carries.
    assert dropped == 1, dropped
    return float((exactl / exact0) ** 2), float(closure)


def control_defects_fire(base, n, lag) -> None:
    """POSITIVE CONTROL TWO: the two deliberately broken kernels must AGREE at zero shift and
    DISAGREE away from it.

    A sweep whose kernel ignored the background would return the trivial value at every point and
    report a flat, reassuring sup. The three defects are built to be exactly that failure: two drop
    the shift from the transverse numerator and from the lattice Laplacian, and the third keeps only
    the real part of `H`. If any tracks the real kernel across the domain, the sweep is not
    measuring the background. The lag-phase variant is deliberately NOT here -- it is an identity,
    and `control_lag_phase_rotation` states it as one.
    """
    # CHOSEN as a probe location, not as a result: a shift with no component on the momentum grid
    # and no two components equal, so no accidental symmetry can make a defect agree. Any generic
    # point serves; this one is written out so the check is reproducible.
    probe = np.array([[0.31, 0.52, 0.17, 0.43]])
    zero = np.zeros((1, DIM))
    good_z = ratio(zero, base, lag)[0][0]
    good_p = ratio(probe, base, lag)[0][0]
    for defect in ("unshifted_numerator", "unshifted_denominator", "real_part_only"):
        dz = ratio(zero, base, lag, defect=defect)[0][0]
        dp = ratio(probe, base, lag, defect=defect)[0][0]
        assert abs(dz - good_z) < AGREE, (defect, dz, good_z)
        assert abs(dp - good_p) > AGREE, (
            f"the {defect} defect was NOT refuted at a generic shift: the sweep cannot see the "
            "background and every number below is vacuous")
        print(f"  defect {defect:22s}: agrees at phi=0 ({dz:.10f}), REFUTED at the probe "
              f"({dp:.10f} vs {good_p:.10f})")


def control_symmetries(base, n, lag) -> None:
    """POSITIVE CONTROL THREE: the two identities the reductions rest on, checked rather than
    assumed.

    PERIODICITY `phi_mu -> phi_mu + 2 pi / n` is the relabelling `k_mu -> k_mu + 1`; it makes the
    domain compact, and it says that every point of `(2 pi / n) Z^4` -- every lattice locus with
    extra adjoint zero modes -- is equivalent to `phi = 0`.

    CONJUGATION `H_{-phi} = conj(H_phi)` is the relabelling `k -> -k`. It is NOT evenness of `H`
    itself -- the sine part flips sign, and the check below requires it to, at a probe where the
    sine part is nonzero. It is `|H|` that is even, and that is what lets a root and its
    negative share one value of `|H|`, which is the weight bookkeeping `moduli_ratio` uses.
    """
    # CHOSEN as a probe location, not as a result; a generic point, as above.
    probe = np.array([0.31, 0.52, 0.17, 0.43])
    step = 2.0 * np.pi / n
    r0 = ratio(probe[None, :], base, lag)[0][0]
    for mu in range(DIM):
        shifted = probe.copy()
        shifted[mu] += step
        rs = ratio(shifted[None, :], base, lag)[0][0]
        assert abs(rs - r0) < AGREE, (mu, rs, r0)
    c0p, clp, slp = weight_corr(probe[None, :], base, lag)[:3]
    c0m, clm, slm = weight_corr(-probe[None, :], base, lag)[:3]
    # `H_{-phi} = conj(H_phi)`: the cosine parts agree and the sine parts are opposite, so `|H|`
    # and therefore `r` agree. The sine check would pass vacuously if `S` were zero, so it is
    # printed and required to be nonzero at this generic probe.
    assert abs(c0p[0] - c0m[0]) < AGREE and abs(clp[0] - clm[0]) < AGREE, (c0p, c0m, clp, clm)
    assert abs(slp[0] + slm[0]) < AGREE, (slp, slm)
    assert abs(slp[0]) > AGREE, ("the sine part vanishes at the generic probe, so the "
                                 "H_{-phi} = conj(H_phi) check is vacuous", slp[0])
    print(f"  r(phi) invariant under phi_mu -> phi_mu + 2pi/{n} in every direction, and "
          f"H_(-phi) = conj(H_phi) with S = {slp[0]:+.10f} != 0  (both to {AGREE:g})")


def control_gauge_parameter(base, n, lag) -> None:
    """POSITIVE CONTROL FOUR: the transverse formula equals the full `mu,nu` covariant-gauge sum at
    SHIFTED momenta, at every gauge parameter, and a perturbed vertex breaks that agreement.

    This is the shifted-momentum form of `fieldStrength_pure_gauge_orthogonal`. The identity is a
    polynomial one in two free variables, so it cannot fail; what CAN fail is the one-line
    transverse formula being the wrong contraction, and that is what the cross-check catches.
    """
    # CHOSEN as probe locations: zero shift, a generic shift, and a shift close to the degenerate
    # locus. They sample the check, they do not set anything.
    probes = [(0.0, 0.0, 0.0, 0.0), (0.31, 0.52, 0.17, 0.43), (1e-4, 2e-4, 3e-4, 4e-4)]
    # CHOSEN as probe values of the gauge parameter: Landau, Feynman and two arbitrary others,
    # matching `free_field_lag_two_ratio`. They must all give the same answer.
    alphas = (0.0, 1.0, 3.0, -2.5)
    broke = False
    for phi in probes:
        _, _, want_c, want_s, _, _ = ratio(np.array([phi]), base, lag)
        for alpha in alphas:
            got_c, got_s = gauge_alpha_value(phi, n, lag, alpha)
            assert abs(got_c - want_c[0]) < AGREE, (phi, alpha, "cos", got_c, want_c[0])
            assert abs(got_s - want_s[0]) < AGREE, (phi, alpha, "sin", got_s, want_s[0])
            bad_c, bad_s = gauge_alpha_value(phi, n, lag, alpha, drop_second_plane_leg=True)
            if abs(bad_c - want_c[0]) > AGREE or abs(bad_s - want_s[0]) > AGREE:
                broke = True
    assert broke, "the perturbed vertex was not refuted: the gauge cross-check is vacuous"
    print(f"  transverse formula = full mu,nu sum (BOTH parts) at alpha in {alphas} on "
          f"{len(probes)} shifts; perturbed vertex REFUTED as required")


def control_lag_phase_rotation(base, n, lag) -> None:
    """A CHECKED IDENTITY, not a defect: the toron shift of the LAG PHASE cannot change `|H|^2`.

    `e^{i q_2 d} = e^{i phi_2 d} e^{i p_2 d}`, so the shift contributes an overall factor of modulus
    one and `(C, S)` computed with the shifted phase is `(C, S)` computed with the unshifted phase
    ROTATED by `2 phi_2`. The modulus is therefore identical, and `r` sees the background only
    through the propagator `(qhat_0^2 + qhat_1^2)/qhat^2`, never through the lag exponential.

    This was found by trying to use the unshifted lag phase as a deliberate defect and having it
    refuse to fire. It is worth stating rather than deleting: it says the phase convention for the
    covariant correlator -- whether the background Wilson line is carried with the operator or left
    in the field -- cannot affect the answer, which is what a gauge-invariant observable requires.
    Both parts are printed, so a reader can see they differ while the modulus does not.
    """
    # CHOSEN as a probe location, not as a result; the same generic point as the other controls.
    probe = np.array([[0.31, 0.52, 0.17, 0.43]])
    r, c0, cl, sl, _, _ = ratio(probe, base, lag)
    rf, c0f, clf, slf, _, _ = ratio(probe, base, lag, defect="unshifted_lag_phase")
    assert abs(r[0] - rf[0]) < AGREE, (r[0], rf[0])
    assert abs(cl[0] - clf[0]) > AGREE, ("the two phase conventions agree part-by-part, so the "
                                         "rotation identity is vacuous here", cl[0], clf[0])
    print(f"  lag-phase rotation: parts differ (C {cl[0]:+.8f} vs {clf[0]:+.8f}, S {sl[0]:+.8f} vs "
          f"{slf[0]:+.8f}) and |H|^2 does NOT ({r[0]:.12f})")


def control_degenerate_locus(base, n, lag, trivial) -> None:
    """POSITIVE CONTROL FIVE: ON the degenerate locus the zero mode must be DETECTED, and the value
    must be the trivial one.

    `phi in (2 pi / n) Z^4` is a lattice zero-mode locus AND, by periodicity, the trivial background
    in disguise. So it is a two-sided check: if the guard misses the mode, the `0/0` term is
    evaluated as whatever the rounding of `sin(pi)` makes it -- which is `1`, one approach
    direction's limit -- and `r` comes back at the CLOSURE value instead of the trivial one. That is
    the defect the first draft of this script shipped, and this control is what catches it.
    """
    step = 2.0 * np.pi / n
    # CHOSEN as probe locations on the locus, not as results: one shift along a plaquette-plane
    # direction, one along the lag direction, one diagonal. Any integer vector would serve.
    for vec in ((1, 0, 0, 0), (0, 0, 1, 0), (1, 1, 1, 1), (n - 1, 1, n - 1, 1)):
        phi = np.array(vec, dtype=np.float64) * step
        r, c0, cl, sl, dropped, worst = ratio(phi[None, :], base, lag)
        # DERIVED: exactly one term. On `phi in (2pi/n)Z^4` the shifted grid is the unshifted grid
        # relabelled, so it carries the same single zero mode `q = 0` and no other. Any other count
        # means the guard is either missing it or swallowing momenta the lattice carries.
        assert dropped == 1, (vec, dropped, "the zero mode on the locus was not detected")
        assert abs(r[0] - trivial) < AGREE, (vec, r[0], trivial)
    print(f"  on the locus (2pi/{n})Z^4 the zero mode is detected and r returns the trivial value "
          f"{trivial:.12f}, as periodicity requires")


# ---------------------------------------------------------------------------------------------
# The sweep
# ---------------------------------------------------------------------------------------------

def grid_points(n, per_axis):
    """The regular grid over the fundamental domain `[0, 2 pi / n)^DIM`, shape `(per_axis^DIM, DIM)`."""
    axis = np.arange(per_axis, dtype=np.float64) * (2.0 * np.pi / n) / per_axis
    grids = np.meshgrid(*([axis] * DIM), indexing="ij")
    return np.stack([g.ravel() for g in grids], axis=1)


def sweep_points(phis, base, lag):
    """The ratio at every row of `phis`, in batches. Returns the array and two instrument readings."""
    out = np.empty(phis.shape[0])
    worst_term = 0.0
    dropped = 0
    for i in range(0, phis.shape[0], BATCH):
        chunk = phis[i:i + BATCH]
        r, _, _, _, dr, w = ratio(chunk, base, lag)
        out[i:i + chunk.shape[0]] = r
        worst_term = max(worst_term, w)
        dropped += dr
    # DERIVED: `(qhat_0^2 + qhat_1^2) <= qhat^2` with both non-negative makes every term of both
    # sums lie in `[-1, 1]`. A term above one means the kernel is not computing this object.
    assert worst_term <= 1.0 + AGREE, worst_term
    return out, dropped, worst_term


def refine(base, n, lag, phi0, step, shrink, rounds):
    """Coordinate pattern search upward from `phi0`, for the sup rather than a listed maximum.

    The grid and the random draw both report the best point they VISITED. If the sup sits between
    samples this finds it; if the sup is at the sampled point this returns it unchanged. No
    derivative and no external optimiser, so nothing here can be blamed on a library default.
    """
    phi = np.array(phi0, dtype=np.float64)
    best = float(ratio(phi[None, :], base, lag)[0][0])
    for _ in range(rounds):
        moved = True
        while moved:
            moved = False
            for mu in range(DIM):
                for sign in (+1.0, -1.0):
                    cand = phi.copy()
                    cand[mu] += sign * step
                    val = float(ratio(cand[None, :], base, lag)[0][0])
                    if val > best:
                        best, phi, moved = val, cand, True
        step *= shrink
    return best, phi


def zero_mode_limit(base, n, lag, rng, dirs):
    """Approach the degenerate locus `phi -> 0` along many directions; report the RATIO's limit.

    The locus is where a nonzero adjoint weight pairs to zero with the toron angles, so a mode that
    was massive becomes massless. The pieces and the ratio are both printed, because the question
    is whether the RATIO stays bounded while the pieces move -- and because printing only the ratio
    would hide a kernel in which neither piece moves at all.
    """
    # CHOSEN as a ladder of approach scales, not as a result: eleven decades from around the lattice
    # momentum spacing down to where the shifted momentum is a millionth of a millionth of it.
    # Reading the same limit across the whole ladder is the point; any single scale would not show
    # whether it is a limit.
    scales = [10.0 ** (-e) for e in range(1, 12)]
    print("    scale        min r          max r          min C(0)     max C(0)   max |S|   "
          "spread of r")
    for s in scales:
        e = rng.normal(size=(dirs, DIM))
        e /= np.linalg.norm(e, axis=1, keepdims=True)
        r, c0, cl, sl, dr, w = ratio(e * s, base, lag)
        # DERIVED: no terms at all. The ladder must stay OFF the locus, or it would be reading the
        # dropped value rather than approaching it. Zero is the count of dropped terms that says so,
        # and this is the other side of `control_degenerate_locus`.
        assert dr == 0, (s, dr, "the approach ladder was swallowed by the zero-mode guard")
        print(f"    {s:.0e}   {r.min():.12f}  {r.max():.12f}   {c0.min():.8f}  {c0.max():.8f}"
              f"   {np.abs(sl).max():.2e}  {r.max() - r.min():.3e}")
    # The two EXTREME directions of the dropped term, written out: the limit of the `0/0` term is
    # `e_0^2 + e_1^2`, so a direction in the plaquette plane gives one and a direction transverse to
    # it gives zero. These bracket the family above, and the gap between them is the whole size of
    # the discontinuity at the degenerate point.
    for name, e in (("in-plane   (e_0^2+e_1^2 = 1)", np.array([1.0, 0.0, 0.0, 0.0])),
                    ("transverse (e_0^2+e_1^2 = 0)", np.array([0.0, 0.0, 1.0, 0.0]))):
        # CHOSEN as the reading scale for the two named directions: the smallest of the ladder
        # above, so the printed value is the limit and not a point on the way to it.
        r, c0, cl, sl, dr, w = ratio(e[None, :] * scales[-1], base, lag)
        print(f"    {name}: C(0) = {c0[0]:.12f}  C({lag}) = {cl[0]:.12f}  "
              f"S({lag}) = {sl[0]:+.3e}  r = {r[0]:.12f}")


class Q3:
    """Exact arithmetic in `Q(sqrt 3)`: `a + b sqrt(3)` with `a, b` rational.

    WHY THIS EXISTS. The extent-six sweep's argmax sits at `phi = (pi/6, pi/6, 0, 0)`, where
    `qhat^2 = 2 - 2 cos(pi(2k+1)/6)` takes the values `2 -+ sqrt 3` and `2` -- irrational, so the
    `Fraction` arithmetic of `free_field_lag_two_ratio` does not reach it, but algebraic of degree
    two, so this does. It is a SECOND INSTRUMENT, not a speed-up: numpy floats and exact field
    arithmetic share no code path, and the check is that they agree.
    """

    __slots__ = ("a", "b")

    # DERIVED: the additive identity of the field, so that `Q3()` is zero and `Q3(x)` is the
    # rational `x`. Neither default is a magnitude.
    def __init__(self, a=0, b=0):
        self.a = Fraction(a)
        self.b = Fraction(b)

    def __add__(self, o):
        o = o if isinstance(o, Q3) else Q3(o)
        return Q3(self.a + o.a, self.b + o.b)

    def __sub__(self, o):
        o = o if isinstance(o, Q3) else Q3(o)
        return Q3(self.a - o.a, self.b - o.b)

    def __mul__(self, o):
        o = o if isinstance(o, Q3) else Q3(o)
        # DERIVED: `(a + b r)(c + d r) = (ac + 3 bd) + (ad + bc) r` with `r^2 = 3`. The three is the
        # radicand, not a parameter.
        return Q3(self.a * o.a + 3 * self.b * o.b, self.a * o.b + self.b * o.a)

    def __truediv__(self, o):
        o = o if isinstance(o, Q3) else Q3(o)
        # DERIVED: rationalise by the conjugate. `norm = c^2 - 3 d^2` is zero only for `o = 0`,
        # because `sqrt 3` is irrational; the three is again the radicand.
        norm = o.a * o.a - 3 * o.b * o.b
        # DERIVED: the additive identity. `norm` is the field norm and vanishes only at zero.
        if norm == 0:
            raise ZeroDivisionError("Q3 division by zero")
        return Q3((self.a * o.a - 3 * self.b * o.b) / norm, (self.b * o.a - self.a * o.b) / norm)

    def is_zero(self):
        # DERIVED: the additive identity in both coordinates; `1, sqrt 3` is a basis over Q.
        return self.a == 0 and self.b == 0

    def __float__(self):
        return float(self.a) + float(self.b) * math.sqrt(3.0)

    def __repr__(self):
        return f"({self.a} + {self.b}*sqrt3)"


def exact_ratio_half_period_plane(n, lag):
    """`r` at `phi = (pi/n, pi/n, 0, 0)` -- half a period in each plaquette-plane direction, none
    transverse -- computed EXACTLY in `Q(sqrt 3)`, for `n = 6`.

    At that shift `q_mu = pi(2 k_mu + 1)/n` for `mu` in the plane, so
    `qhat_mu^2 = 2 - 2 cos(pi(2k+1)/6)` runs over `{2 - sqrt3, 2, 2 + sqrt3}`; transverse the
    momenta are unshifted and `qhat^2` runs over `{0,1,3,4}`. The lag phase is `cos(2 pi k lag / 6)`,
    rational. The SINE part vanishes identically here, and that is not assumed: `phi_2 = 0` makes
    every term even under `k_2 -> -k_2` while `sin` is odd, and the sum is formed and checked.
    """
    if n != EXTENT:
        return None
    # DERIVED: `2 - 2 cos(pi(2k+1)/6)` for `k = 0..5`, in `Q(sqrt 3)`; the cosines are
    # `+-sqrt3/2, 0`. Values, not parameters.
    shifted = [Q3(2, -1), Q3(2, 0), Q3(2, 1), Q3(2, 1), Q3(2, 0), Q3(2, -1)]
    # DERIVED: `2 - 2 cos(2 pi k / 6)` for `k = 0..5` -- the same table
    # `free_field_lag_two_ratio.hat_sq` carries at extent six.
    plain = [Q3(v) for v in (0, 1, 3, 4, 3, 1)]
    # DERIVED: `cos(2 pi k lag / 6)` and `sin(2 pi k lag / 6)` at `lag = 2`, i.e. `cos(2 pi k / 3)`
    # and `sin(2 pi k / 3)`. The sine is `+-sqrt3/2`.
    cos_tab = [Q3(1), Q3(Fraction(-1, 2)), Q3(Fraction(-1, 2)), Q3(1), Q3(Fraction(-1, 2)),
               Q3(Fraction(-1, 2))]
    sin_tab = [Q3(0), Q3(0, Fraction(1, 2)), Q3(0, Fraction(-1, 2)), Q3(0), Q3(0, Fraction(1, 2)),
               Q3(0, Fraction(-1, 2))]
    # DERIVED: the lag this table is written for. `cos_tab` and `sin_tab` above are
    # `cos(2 pi k lag / 6)` and `sin(2 pi k lag / 6)` EVALUATED at `lag = 2`; at any other lag they
    # would be the wrong numbers, so the routine declines rather than returning them.
    if lag % n != 2:
        return None
    c0 = Q3(0)
    cl = Q3(0)
    sl = Q3(0)
    dropped = 0
    for k in itertools.product(range(n), repeat=DIM):
        hats = [shifted[k[0]], shifted[k[1]], plain[k[2]], plain[k[3]]]
        den = hats[0] + hats[1] + hats[2] + hats[3]
        if den.is_zero():
            dropped += 1
            continue
        term = (hats[PLANE[0]] + hats[PLANE[1]]) / den
        c0 = c0 + term
        cl = cl + cos_tab[k[LAG_DIR]] * term
        sl = sl + sin_tab[k[LAG_DIR]] * term
    volume = Q3(n ** DIM)
    c0, cl, sl = c0 / volume, cl / volume, sl / volume
    assert sl.is_zero(), ("the sine part is not exactly zero at phi_2 = 0", sl)
    # DERIVED: no zero mode at this shift. `q_0 = pi(2k+1)/6` is never a multiple of `2 pi`, so
    # `qhat_0^2 > 0` for every `k` and the whole grid is live.
    assert dropped == 0, dropped
    return (cl * cl + sl * sl) / (c0 * c0), c0, cl


def moduli_ratio(uv, base, lag):
    """`rho_A(2)/rho_A(0) = sum_w |H_w(2)|^2 / sum_w H_w(0)^2` over the eight adjoint weights.

    `uv` is `(B, 2*DIM)`: the two independent root shifts `u = alpha_12`, `v = alpha_23`; the third
    root is `u + v` and each root appears with its negative, which gives the same `|H|` (control
    three). The two Cartan weights carry shift zero.

    THIS IS THE CONNECTED CORRELATION IN A FIXED BACKGROUND. It is NOT the whole of `rho(d)` once
    the background is integrated over -- see `disconnected_variance`, which supplies the term that
    the moduli integral adds and this function cannot see.
    """
    u, v = uv[:, :DIM], uv[:, DIM:]
    zero = np.zeros((uv.shape[0], DIM))
    c0z, clz, slz = weight_corr(zero, base, lag)[:3]
    # DERIVED: the multiplicities of the su(3) adjoint weights -- two Cartan directions with zero
    # shift, and each of the three positive roots with its negative, which share a value of `|H|`
    # (control three).
    num = 2.0 * (clz ** 2 + slz ** 2)
    den = 2.0 * c0z ** 2
    for s in (u, v, u + v):
        c0, cl, sl = weight_corr(s, base, lag)[:3]
        num = num + 2.0 * (cl ** 2 + sl ** 2)
        den = den + 2.0 * c0 ** 2
    return num / den


def weight_sums(uv, base, lag):
    """`(T, S2)` over the eight adjoint weights: `T = sum_w H_w(0)` and `S2 = sum_w H_w(0)^2`.

    `T` carries the ONE-POINT function of the plaquette density in the background and `S2` its
    connected two-point function at lag zero. At Gaussian order the plaquette density is
    `(1/4N) sum_a (X^a)^2`, so

        <phi>_A = kappa * T        and        rho_A(0) = 2 * kappa^2 * S2

    with the SAME `kappa` -- one power of the coupling and the colour normalisation, identical for
    every background. THE FACTOR OF TWO IS WICK'S, not a convention: the connected correlation of a
    quadratic observable has two pairings. It cancels out of `moduli_ratio`, which is a ratio of two
    such objects, and it does NOT cancel out of `disconnected_variance`, which compares a one-point
    quantity with a two-point one. Everything that function needs is a ratio of `T` and `S2`, so
    `kappa` and the coupling cancel out of it -- which is why the term it measures does NOT go away
    at weak coupling.
    """
    u, v = uv[:, :DIM], uv[:, DIM:]
    zero = np.zeros((uv.shape[0], DIM))
    h = weight_corr(zero, base, lag)[0]
    # DERIVED: the su(3) adjoint multiplicities again -- two Cartan weights at zero shift, and each
    # positive root twice, with its negative.
    total = 2.0 * h
    sq = 2.0 * h * h
    for s in (u, v, u + v):
        hs = weight_corr(s, base, lag)[0]
        total = total + 2.0 * hs
        sq = sq + 2.0 * hs * hs
    return total, sq


def _pattern_search_uv(base, lag, uv0, step, shrink, rounds, pick, sense):
    """Coordinate pattern search over the eight-dimensional moduli parametrisation.

    `pick` selects `T` or `Q` from `weight_sums`, `sense` is `+1` to maximise and `-1` to minimise.
    Same shape as `refine`, over `2*DIM` coordinates instead of `DIM`.
    """
    uv = np.array(uv0, dtype=np.float64)
    best = sense * float(pick(weight_sums(uv[None, :], base, lag)))
    for _ in range(rounds):
        moved = True
        while moved:
            moved = False
            for mu in range(2 * DIM):
                for sign in (+1.0, -1.0):
                    cand = uv.copy()
                    cand[mu] += sign * step
                    val = sense * float(pick(weight_sums(cand[None, :], base, lag)))
                    if val > best:
                        best, uv, moved = val, cand, True
        step *= shrink
    return sense * best, uv


def disconnected_variance(base, n, lag, cfg, rng, sup_r, threshold):
    """THE TERM THE PER-BACKGROUND RATIO CANNOT SEE, and a measure-free bound on it.

    `WilsonBridge.wilsonCorrConn` subtracts `<phi_p0><phi_p>` with BOTH factors taken over the FULL
    measure. If the weak-coupling measure is a mixture over flat backgrounds `A` with law `mu`, the
    law of total covariance gives

        rho(d) = E_mu[rho_A(d)] + Var_mu(<phi>_A),

    and the second term is NOT the average of anything this script has computed. It is non-negative,
    and it is the SAME order in the coupling as the first (both are `kappa^2` times a background
    quantity), so weak coupling does not remove it. It is also `d`-INDEPENDENT, because a constant
    background is translation invariant and `<phi_p>_A` does not depend on `p`. Adding one constant
    to both ends of a ratio below one moves the ratio TOWARD one -- always against the claim.

    So the substitution needs TWO uniform quantities on the compact set, not one:

        rho(2)/rho(0) <= sup_A [rho_A(2)/rho_A(0)]  +  Var_mu(<phi>_A) / inf_A rho_A(0),

    and `Var_mu` is bounded over EVERY law `mu` by Popoviciu's inequality, `((max T - min T)/2)^2`
    with `T` ranging over the same compact moduli space. That keeps the argument measure-free, which
    is the whole point of the substitution -- it just costs a second sweep.

    Reported, never assumed: the extremes of `T` and `Q` are searched for, not derived, so the number
    below is as much a measurement as the sup is, and it can only refute.
    """
    zero = np.zeros((1, 2 * DIM))
    t_arr, q_arr = weight_sums(zero, base, lag)
    t_triv, q_triv = float(t_arr[0]), float(q_arr[0])
    tmin, tmax, qmin = t_triv, t_triv, q_triv
    argt_lo = argt_hi = argq = np.zeros(2 * DIM)
    for i in range(0, cfg["moduli"], BATCH):
        m = min(BATCH, cfg["moduli"] - i)
        uv = rng.random((m, 2 * DIM)) * (2.0 * np.pi / n)
        t, q = weight_sums(uv, base, lag)
        jlo, jhi, jq = int(np.argmin(t)), int(np.argmax(t)), int(np.argmin(q))
        if t[jlo] < tmin:
            tmin, argt_lo = float(t[jlo]), uv[jlo].copy()
        if t[jhi] > tmax:
            tmax, argt_hi = float(t[jhi]), uv[jhi].copy()
        if q[jq] < qmin:
            qmin, argq = float(q[jq]), uv[jq].copy()
    step0 = (2.0 * np.pi / n) / cfg["per_axis"] / cfg["refine_step_div"]
    tmin, _ = _pattern_search_uv(base, lag, argt_lo, step0, cfg["refine_shrink"],
                                 cfg["refine_rounds"], lambda tq: tq[0][0], -1.0)
    tmax, _ = _pattern_search_uv(base, lag, argt_hi, step0, cfg["refine_shrink"],
                                 cfg["refine_rounds"], lambda tq: tq[0][0], +1.0)
    qmin, _ = _pattern_search_uv(base, lag, argq, step0, cfg["refine_shrink"],
                                 cfg["refine_rounds"], lambda tq: tq[1][0], -1.0)
    # DERIVED: Popoviciu. A random variable confined to `[a, b]` has variance at most
    # `((b - a)/2)^2`, attained by the two-point law on the endpoints. Nothing about `mu` is used.
    var_bound = ((tmax - tmin) / 2.0) ** 2
    # DERIVED: the two is Wick's, from `rho_A(0) = 2 kappa^2 sum_w H_w(0)^2`; see `weight_sums`.
    rho0_min = 2.0 * qmin
    extra = var_bound / rho0_min
    print(f"  T = sum_w H_w(0) over the moduli space: [{tmin:.9f}, {tmax:.9f}]  "
          f"(trivial background {t_triv:.9f})")
    print(f"  inf_A rho_A(0)/kappa^2 = 2 sum_w H_w(0)^2: {rho0_min:.9f}  "
          f"(trivial background {2.0 * q_triv:.9f})")
    print(f"  Popoviciu bound on Var_mu(<phi>_A)/kappa^2 = ((Tmax-Tmin)/2)^2 = {var_bound:.6e}")
    print(f"  additive cost to the ratio, Var / inf_A rho_A(0) = {extra:.6e}")
    corrected = sup_r + extra
    print(f"  CORRECTED uniform bound on rho(2)/rho(0) = {sup_r:.12f} + {extra:.6e} = "
          f"{corrected:.12f}   ({100.0 * extra / sup_r:.2f}% above the per-background sup)")
    print(f"  margin against the threshold bracket {threshold}: x{threshold / corrected:.3f}")
    return corrected


def run_extent(n, lag, threshold, ceiling, tag, cfg, rng, t0) -> bool:
    """One lattice, end to end. Returns True if the substitution is REFUTED at this extent."""
    base = base_momenta(n)
    print("=" * 93)
    print(f"extent {n}, dimension {DIM}, plane {PLANE}, lag {lag} along {LAG_DIR}   [{tag}]")
    print(f"  clearance bracket (below the threshold, so it cannot manufacture a pass): {threshold}")
    print(f"  refutation bracket (above it, so it cannot manufacture a failure): {ceiling}")
    print("=" * 93)

    print("--- controls (each would fire if the instrument were broken) ---")
    trivial, closure = control_trivial_background(base, n, lag)
    control_defects_fire(base, n, lag)
    control_symmetries(base, n, lag)
    control_gauge_parameter(base, n, lag)
    control_lag_phase_rotation(base, n, lag)
    control_degenerate_locus(base, n, lag, trivial)

    per_axis = cfg["per_axis"]
    print(f"--- per-weight sup over the fundamental domain [0, 2pi/{n})^{DIM} ---")
    phis = grid_points(n, per_axis)
    allr, dropped, worst = sweep_points(phis, base, lag)
    j = int(np.argmax(allr))
    print(f"  grid {per_axis}^{DIM} = {phis.shape[0]} backgrounds:  max r = {allr[j]:.12f}"
          f"  at phi = {np.array2string(phis[j], precision=6)}")
    print(f"    zero-mode terms dropped over the whole grid: {dropped};  "
          f"max |term| seen = {worst:.9f}  (identity says <= 1)")

    rphis = rng.random((cfg["randoms"], DIM)) * (2.0 * np.pi / n)
    allrr = sweep_points(rphis, base, lag)[0]
    jr = int(np.argmax(allrr))
    print(f"  random {cfg['randoms']} backgrounds in the same domain: max r = {allrr[jr]:.12f}"
          f"  at phi = {np.array2string(rphis[jr], precision=6)}")

    # An independent draw over the FULL torus `[0, 2pi)^DIM`, not the fundamental domain. If the
    # periodicity reduction were wrong, this is where the sup would be larger.
    fphis = rng.random((cfg["randoms"], DIM)) * (2.0 * np.pi)
    allrf = sweep_points(fphis, base, lag)[0]
    print(f"  random {cfg['randoms']} backgrounds over the FULL torus [0,2pi)^{DIM}: "
          f"max r = {allrf.max():.12f}")

    order = np.argsort(allr)[::-1][:cfg["refine_top"]]
    step0 = (2.0 * np.pi / n) / per_axis / cfg["refine_step_div"]
    best, barg = -1.0, None
    for jj in order:
        v, p = refine(base, n, lag, phis[jj], step0, cfg["refine_shrink"], cfg["refine_rounds"])
        if v > best:
            best, barg = v, p
    for seed_pt in (rphis[jr], fphis[int(np.argmax(allrf))]):
        v, p = refine(base, n, lag, seed_pt, step0, cfg["refine_shrink"], cfg["refine_rounds"])
        if v > best:
            best, barg = v, p
    print(f"  pattern search from the best {cfg['refine_top']} grid points and the best random "
          f"points:")
    # The pattern search may walk ONTO the degenerate locus, where the value it reports is the
    # in-plane LIMIT rather than a background's value. Said so rather than left to be misread: the
    # test is whether the reported point is within a grid cell of `(2pi/n)Z^4`.
    cell = (2.0 * np.pi / n) / per_axis
    wrapped = np.abs((barg + np.pi / n) % (2.0 * np.pi / n) - np.pi / n)
    on_locus = bool((wrapped < cell).all())
    print(f"    SUP over non-degenerate backgrounds r = {best:.12f}  at "
          f"phi = {np.array2string(barg, precision=8)}"
          f"{'   [a LIMIT: this point sits on the degenerate locus]' if on_locus else ''}")
    _, bc0, bcl, bsl, _, _ = ratio(barg[None, :], base, lag)
    print(f"      there: C(0) = {bc0[0]:.10f}  C({lag}) = {bcl[0]:+.10f}  S({lag}) = "
          f"{bsl[0]:+.10f};  cosine-only ratio would read "
          f"{float(bcl[0] ** 2 / bc0[0] ** 2):.12f}")
    # THE SECOND INSTRUMENT. At extent six the half-period-in-plane shift is where the sweep lands;
    # it is evaluated here in exact `Q(sqrt 3)` arithmetic, which shares no code with the numpy
    # kernel. Reported whether or not it is the argmax, so a reader can see both the exact value and
    # how far the float sup sits from it.
    exact = exact_ratio_half_period_plane(n, lag)
    if exact is not None:
        er, ec0, ecl = exact
        half = np.full((1, DIM), 0.0)
        half[0, PLANE[0]] = half[0, PLANE[1]] = np.pi / n
        fr = float(ratio(half, base, lag)[0][0])
        print(f"  EXACT, in Q(sqrt 3), at phi = (pi/{n}, pi/{n}, 0, 0):")
        print(f"    C(0) = {ec0} = {float(ec0):.12f}")
        print(f"    C({lag}) = {ecl} = {float(ecl):.12f}   S({lag}) = 0 exactly")
        print(f"    r = {er} = {float(er):.15f}   (numpy kernel there: {fr:.15f})")
        assert abs(float(er) - fr) < AGREE, (float(er), fr)

    closure_sup = max(best, closure)
    print(f"    CLOSURE sup (including the limit ON the degenerate locus, exactly {closure:.12f}) "
          f"= {closure_sup:.12f}")
    print(f"    trivial background r = {trivial:.12f};  closure sup / trivial = "
          f"{closure_sup / trivial:.6f}")

    print("  how much of the domain sits above each level:")
    # DERIVED: the levels are the trivial-background value, the threshold itself, and their
    # geometric midpoint. They are read off the objects already in play; none is a chosen cut and
    # none decides the verdict, which is `sup vs threshold`.
    for lvl, name in ((trivial, "trivial value"),
                      (math.sqrt(trivial * threshold), "geometric midpoint"),
                      (threshold, "THRESHOLD")):
        print(f"    r > {lvl:.10f} ({name:18s}):  grid {float((allr > lvl).mean()):.9f}   "
              f"random {float((allrr > lvl).mean()):.9f}")

    print("--- approaching the degenerate locus (extra adjoint zero modes) ---")
    zero_mode_limit(base, n, lag, rng, cfg["dirs"])

    print("--- the moduli-space average rho_A(2)/rho_A(0) over the eight adjoint weights ---")
    mbest, marg = -1.0, None
    for i in range(0, cfg["moduli"], BATCH):
        m = min(BATCH, cfg["moduli"] - i)
        uv = rng.random((m, 2 * DIM)) * (2.0 * np.pi / n)
        mr = moduli_ratio(uv, base, lag)
        jm = int(np.argmax(mr))
        if mr[jm] > mbest:
            mbest, marg = float(mr[jm]), uv[jm].copy()
    # The two quadruples that put as many roots as possible AT the per-weight argmax. `u = v = barg`
    # sets two roots there and the third at `2 barg`; `u = -v = barg` sets two roots there (`|H|` is
    # even) and the third at zero, i.e. at the trivial value. No quadruple can put all three there,
    # because the roots satisfy `alpha_13 = alpha_12 + alpha_23`. That constraint is why the average
    # cannot reach the per-weight sup, and it is the reason the bound is conservative.
    print(f"  random {cfg['moduli']} toron quadruples:  max rho(2)/rho(0) = {mbest:.12f}")
    for label, uv1 in (("u = v = argmax   (roots argmax, argmax, 2*argmax)",
                        np.concatenate([barg, barg])[None, :]),
                       ("u = -v = argmax  (roots argmax, argmax, 0)",
                        np.concatenate([barg, -barg])[None, :])):
        print(f"  {label}:  {float(moduli_ratio(uv1, base, lag)[0]):.12f}")
    print(f"  per-weight closure sup (an UPPER bound on that average): {closure_sup:.12f}")

    print("--- the term the moduli INTEGRAL adds, which no per-background ratio can see ---")
    corrected = disconnected_variance(base, n, lag, cfg, rng, closure_sup, threshold)

    # The REFUTATION comparison uses the UPPER bracket and the CLEARANCE comparison the lower one,
    # so neither rounding can manufacture its own verdict. Between the two brackets the run says so
    # rather than choosing -- which matters because the tree proves an upper bracket only at extent
    # four.
    refuted = corrected >= ceiling
    verdict = ("REFUTED" if refuted else
               "not refuted" if corrected < threshold else
               "INDETERMINATE between the two brackets")
    print(f"*** extent {n}: corrected uniform bound {corrected:.12f}   clearance bracket "
          f"{threshold}   refutation bracket {ceiling}   "
          f"margin x{threshold / corrected:.3f}   -> {verdict}")
    print(f"    (elapsed {time.time() - t0:.1f}s)")
    return refuted


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--quick", action="store_true",
                    help="a cheap version of the same run: every control, a coarse sweep")
    ap.add_argument("--seed", type=int, default=None,
                    help="seed the random draws for a reproducible run; unseeded by default, so "
                         "two runs are two independent instruments")
    a = ap.parse_args()

    t0 = time.time()
    rng = np.random.default_rng(a.seed)
    # CHOSEN: the sweep effort. None of these enters a comparison -- they buy coverage and
    # resolution and nothing else -- and all are printed with the results so the reader can see how
    # much of the domain was visited. `per_axis` nodes per axis is `per_axis^4` backgrounds; the
    # random draws are independent instruments of the same order; `refine_*` is the pattern-search
    # schedule, which reaches about `cell / 2^(rounds + 2)` and so far inside the printed precision.
    full = dict(per_axis=40, randoms=1_000_000, refine_top=128, refine_step_div=4.0,
                refine_shrink=0.5, refine_rounds=14, dirs=64, moduli=200_000)
    quick = dict(per_axis=10, randoms=20_000, refine_top=8, refine_step_div=4.0,
                 refine_shrink=0.5, refine_rounds=8, dirs=16, moduli=20_000)
    cfg = quick if a.quick else full
    print(f"configuration: {'quick' if a.quick else 'full'}  {cfg}")
    print(f"seed: {a.seed if a.seed is not None else 'unseeded (fresh entropy)'}")

    refuted = False
    for n, threshold, ceiling, tag in (
            (EXTENT, THRESHOLD_SIX, CEILING_SIX, "THE OBLIGATION"),
            (EXTENT_ALT, THRESHOLD_FOUR, CEILING_FOUR, "corroborating lattice")):
        refuted |= run_extent(n, LAG, threshold, ceiling, tag, cfg, rng, t0)

    print("=" * 93)
    if refuted:
        print("VERDICT: the uniform-sup substitution is REFUTED. The free lag-two ratio reaches "
              "the threshold somewhere on the toron moduli space, so a sup over that space cannot "
              "replace the measure on it.")
    else:
        print("VERDICT: NOT REFUTED over the backgrounds visited. That is not support. No number "
              "above may enter a proof or be fitted to; the rigorous statement is a theorem about "
              "the function defined in this file, and it is not proved here.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
