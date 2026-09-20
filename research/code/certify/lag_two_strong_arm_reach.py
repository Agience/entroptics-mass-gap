"""HOW FAR THE STRONG-COUPLING SIDE OF B5 ACTUALLY REACHES, as a number.

`LagTwoBound.exists_cut_lag_two_ratio` proves `rho(2) <= K rho(0)` on a derived interval `[0, b]`
for EVERY `K > 0`, and names no numeral for `b`. This script evaluates `b`, from the Lean
DEFINITIONS rather than from their docstrings, and reports where the estimate's own hypothesis
`coreRate < 1` stops holding.

## The construction, read off the definitions (not the prose)

`MassGap/StrongCoupling.lean:3866,3876,3884`, verbatim, with `K` the touch degree:

    coreRate      K beta = (4 (K+1)^2) * (exp(2 beta) - 1) * exp(4 beta K)
    corePrefactor K beta = 8 * (4 (K+1)^2)^2 * exp(4 beta K)^2
    coreConst     K beta = corePrefactor K beta / (1 - coreRate K beta)

`corrClay_abs_le_coreConst_mul_rate_pow` (`StrongCoupling.lean:4727`) instantiates `K = 16*4 = 64`
and gives, under the hypothesis `coreRate 64 beta < 1`,

    |rho(d)| <= coreConst 64 beta * coreRate 64 beta ^ k      for k < circLag d

and `exists_cut_lag_two_ratio` uses it at `d = 2`, `k = 1` (`circLag 2 = 2`, `circLag_two`).

`ContactFloor.corrClay_zero_ge` (`ContactFloor.lean:1009`) gives the denominator:

    rho(0)|_beta >= exp(-128 beta) * rho(0)|_{beta = 0}        for beta >= 0

so the ratio bound the construction produces is

    RATIOBOUND(beta) = coreConst 64 beta * coreRate 64 beta * exp(128 beta) / D ,
    D = corrClay 4 0 0 .

Every factor is increasing on `beta >= 0`, so `RATIOBOUND` is increasing and the cut `b` is the
unique root of `RATIOBOUND(b) = threshold`.

WHAT THE LEAN PROOF DELIVERS IS SHORTER THAN THAT, THREE TIMES OVER. The pointwise crossing above
is an UPPER bound on any cut this construction can produce, not the cut itself. Three separate
losses sit between them, and all three are printed:

  1. THE FREEZE. The proof sets `A = coreConst 64 b0` at an interval endpoint and uses
     `A >= coreConst 64 beta` on `[0, b0]`. `coreConst` carries `1/(1 - coreRate)`, which diverges as
     `b0` approaches the rate-one point, so the frozen cut falls to ZERO there -- and `b0` comes from
     `StrongArm.exists_strong_arm_cut`, an existential with no numeral. `exists_strong_arm_cut`
     halves whatever `core_rate_lt_one_of_small`'s metric-ball radius is, so the Lean `b0` ranges
     over the whole interval `(0, rate-one/2]` and NO numeral is a lower bound for the frozen cut.
     One illustrative `b0` is printed.
  2. THE `eps/2`. `exists_cut_lag_two_ratio` returns `min b0 (eps/2)` (`LagTwoBound.lean:292`), with
     `eps` the radius of a ball on which the strict inequality holds. Even at the largest admissible
     `eps` -- the crossing itself -- the witness is HALF the crossing.
  3. THE CONSUMERS' `K`. All three call sites pass `lagTwoThreshold / 2`, not `lagTwoThreshold`
     (`LagTwoBound.lean:349`, `SpectralBound.lean:449`, `TailRatio.lean:295`). The bound is linear in
     the coupling in this regime, so the cut halves again.

So the number actually certified downstream is a quarter of the pointwise crossing. Both are given.

## D has no NUMERAL in the Lean tree, though the tree reduces it exactly

The tree gets further than a bare positivity statement, and the two lemmas that do it are the ones
that license the value used here. `ContactFloor.integral_hol_clay` (`ContactFloor.lean:858`) proves
the clay plaquette's holonomy pushes the product-Haar link measure forward to Haar on SU(3), and
`ContactFloor.corrClay_zero_at_zero_eq` (`:935`) concludes

    corrClay (m+2) 0 0 = haarSecond - haarMean ^ 2        for every m

with `haarMean`, `haarSecond` (`:918`, `:927`) the SU(3) Haar first and second moments of
`wilsonDensity` -- so `D` is extent-free and is exactly a Haar variance, IN LEAN.

What is missing is only the NUMBER. `PlaqVariance.corrClay_zero_pos` gives `0 < corrClay (N+1) 0 0`
non-constructively, `HaarVariance` shows only positivity, and `ContactFloor.exists_haar_floor`
carries it as an unnamed `min`. So no numeral for `D` exists anywhere and `b` is not evaluable
inside Lean at all. Evaluating those two Haar moments is what this file adds:

    D = Var_Haar(1 - Re tr U / 3) = (1/9) Var_Haar(Re tr U) = (1/9)(1/2) = 1/18 ,

since `E[chi] = 0`, `E[|chi|^2] = 1` and `E[chi^2] = 0` (3 (x) 3 = 6 (+) 3bar carries no singlet),
giving `E[(Re chi)^2] = (E[chi^2] + 2E[|chi|^2] + E[chibar^2])/4 = 1/2`. The Weyl-integration check
at the bottom of this file confirms `1/2` by deterministic quadrature on the maximal torus.
`b` is LINEAR in `D`, so this value decides no verdict: a `D` wrong by a factor 18 moves `b` by 18.

## Arithmetic, and which way it rounds

Exact rationals throughout (`fractions.Fraction`), with certified enclosures for `exp` (positive
series, partial sum below, geometric tail above) and for `sqrt` (integer square root, adjusted).
Every crossing is returned as a rational BRACKET `[b_lo, b_hi]` that the enclosures decide, never a
float root.

THE REPORTED REACH IS THE SHORT END, EVERYWHERE. Three separate roundings all go that way:

  * the headline cut is `b_lo`, at which the bound's UPPER enclosure is certified under the
    threshold's LOWER enclosure -- so `[0, b_lo]` is covered whatever the truncation did;
  * the threshold used as the target is `T_LO`, the low end of the Lean-proved bracket on
    `3^(-1/4)`, and a smaller threshold gives a smaller cut;
  * the rate-one point is reported as `d_lo`, the last argument at which the rate's upper
    enclosure is certified under one.

A truncation error can therefore only make the reported reach SHORTER than the true crossing, never
longer. The brackets printed are tight to about 25 significant figures, and every verdict below
turns on factors of 1e4 or more, so truncation is nowhere near deciding anything.

No fit, no sampling, no measured quantity enters any bound evaluated here. The measured peak is
quoted ONCE at the end, in a section that feeds nothing above it.

Deterministic. One core, seconds; no remote host and no GPU.
"""
import os

# DERIVED: one thread per library, from the shared-box rule. These are environment settings, not
# numbers that decide anything -- the arithmetic below is exact and thread count cannot move it.
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[_v] = "1"

import math
import sys
from fractions import Fraction as Q

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code
import console  # noqa: F401  -- UTF-8 stdout


# ---------------------------------------------------------------------------
# Certified rational enclosures
# ---------------------------------------------------------------------------
# DERIVED: the relative width the exp enclosure is grown until it meets. It is not a cut on any
# quantity: it only sets how many series terms are summed, and BOTH ends of the enclosure remain
# rigorous at any value, so the verdicts are decided by the bracket, not by this number. 1e-40 is
# fifteen orders tighter than the tightest comparison anything below makes.
EXP_REL_WIDTH = Q(1, 10 ** 40)


def exp_bounds(x: Q, rel: Q = EXP_REL_WIDTH):
    """exp(x) in [lo, hi] for x >= 0, exact rationals, truncation grown until hi/lo - 1 <= rel.

    All terms of sum_k x^k/k! are positive, so the partial sum through k = M-1 is a LOWER bound.
    Past k = M the successive ratio x/(k+1) is at most q = x/(M+1), so the tail is at most
    term_M/(1-q), an UPPER bound. Neither end is approximate; M only sets the width between them.
    """
    # DERIVED: 0 is a sign guard on the series argument, not a threshold -- every caller passes a
    # nonnegative coupling multiple and the geometric tail bound is stated for x >= 0.
    assert x >= 0
    # DERIVED: 1 is the k = 0 term x^0/0! and the empty-sum start; neither is chosen.
    S, t, k = Q(0), Q(1), 0
    while True:
        S += t
        t = t * x / (k + 1)
        k += 1
        q = x / (k + 1)
        # DERIVED: 1 is the geometric series' own radius of convergence; this is a guard on the
        # tail bound being valid at all, not a tolerance.
        if q < 1:
            tail = t / (1 - q)
            if tail <= rel * S:
                return S, S + tail


# DERIVED: the sqrt enclosure's width, 10^-SQRT_DIGITS. It enters ONE place (the extent-six
# threshold, through sqrt(9 - 8c^2) ~ 2.2), where the Lean-proved bracket on c = 3^(-1/4) is itself
# only 1e-6 wide -- so this is four orders finer than the input uncertainty it sits beside and
# cannot widen the threshold bracket it feeds.
SQRT_DIGITS = 40


def sqrt_bounds(x: Q, p: int = SQRT_DIGITS):
    """sqrt(x) in [lo, hi] for x >= 0, exact rationals, with hi - lo = 10^-p."""
    # DERIVED: 0 is a sign guard on the radicand, not a threshold.
    assert x >= 0
    scale = 10 ** p
    num, den = x.numerator * scale * scale, x.denominator
    k = math.isqrt(num // den)
    while (k + 1) * (k + 1) * den <= num:
        k += 1
    while k * k * den > num:
        k -= 1
    return Q(k, scale), Q(k + 1, scale)


# ---------------------------------------------------------------------------
# The Lean definitions, transcribed
# ---------------------------------------------------------------------------
# DERIVED: 16*4 is `StrongCoupling.touchDeg_bd_le` at dim = 4, the value every call site in
# `corrClay_abs_le_coreConst_mul_rate_pow` and `exists_cut_lag_two_ratio` passes.
KTOUCH = 16 * 4

# DERIVED: 128 = 2*16*4 is `ContactFloor.corrClay_zero_ge`'s exponent -- `wilsonDensity_le_two`
# against the same touch degree.
FLOOR_EXP = 2 * KTOUCH

# DERIVED: 1/18 is the SU(3) Haar variance of `wilsonDensity`, derived in the module docstring and
# checked by Weyl quadrature in `haar_variance_check` below. It IS corrClay 4 0 0, which the Lean
# tree carries only as a non-constructive positive number.
D_CONTACT = Q(1, 18)


def count_factor(K: int) -> Q:
    """`4 (K+1)^2` -- the count inside both `coreRate` and `corePrefactor`.

    DERIVED: 4 is the ordered split of a span into an activated pair (`card_corePairs_span_le`),
    +1 is the stay-put step of `stepSet`, and the square is the two-step detour. All three are read
    off the Lean definition; none is chosen here."""
    # DERIVED: 4, 1 and 2 are the definition's own, named in the docstring above.
    return Q(4 * (K + 1) ** 2)


def core_rate_bounds(K: int, beta: Q):
    """`coreRate K beta = (4(K+1)^2) (exp(2 beta) - 1) exp(4 beta K)`, enclosed."""
    A = count_factor(K)
    # DERIVED: 2 is `wilsonDensity`'s range [0,2]; 4 is that doubled by the two outside sums Z^2.
    # Both are the definition's literals, transcribed.
    e2lo, e2hi = exp_bounds(2 * beta)
    e4lo, e4hi = exp_bounds(4 * beta * K)
    # DERIVED: 1 is the definition's own subtraction, exp(2 beta) - 1.
    return A * (e2lo - 1) * e4lo, A * (e2hi - 1) * e4hi


def core_prefactor_bounds(K: int, beta: Q):
    """`corePrefactor K beta = 8 (4(K+1)^2)^2 (exp(4 beta K))^2`, enclosed.

    DERIVED: 8 is `pairTerm_abs_le`'s constant (4*1 + 2*2) and both squares are the definition's."""
    A = count_factor(K)
    # DERIVED: 4 is the hard-core exponent's, as in `core_rate_bounds`.
    e4lo, e4hi = exp_bounds(4 * beta * K)
    # DERIVED: 8 is `pairTerm_abs_le`'s constant, quoted from the definition.
    base = 8 * A * A
    return base * e4lo * e4lo, base * e4hi * e4hi


def core_const_bounds(K: int, beta: Q):
    """`coreConst K beta = corePrefactor / (1 - coreRate)`, enclosed. Needs the rate under one."""
    plo, phi = core_prefactor_bounds(K, beta)
    rlo, rhi = core_rate_bounds(K, beta)
    # DERIVED: 1 is the geometric sum's own denominator in the definition of `coreConst`, and the
    # hypothesis `coreRate K beta < 1` that `corrClay_abs_le_coreConst_mul_rate_pow` carries. This
    # is the estimate's own domain, not a cut imposed here.
    assert rhi < 1, "the estimate says nothing where its own hypothesis coreRate < 1 fails"
    return plo / (1 - rlo), phi / (1 - rhi)


def ratio_bound_L0(beta: Q):
    """AS PROVED: coreConst * coreRate * exp(128 beta) / D, pointwise in beta."""
    clo, chi = core_const_bounds(KTOUCH, beta)
    rlo, rhi = core_rate_bounds(KTOUCH, beta)
    flo, fhi = exp_bounds(FLOOR_EXP * beta)
    return clo * rlo * flo / D_CONTACT, chi * rhi * fhi / D_CONTACT


def ratio_bound_L0_frozen(beta: Q, b0: Q):
    """What the Lean proof literally uses: `A = coreConst 64 b0` frozen at the interval endpoint."""
    alo, ahi = core_const_bounds(KTOUCH, b0)
    rlo, rhi = core_rate_bounds(KTOUCH, beta)
    flo, fhi = exp_bounds(FLOOR_EXP * beta)
    return alo * rlo * flo / D_CONTACT, ahi * rhi * fhi / D_CONTACT


def ratio_bound_L1(beta: Q):
    """corePrefactor and 1/(1-r) set to one; the rate's own count kept."""
    rlo, rhi = core_rate_bounds(KTOUCH, beta)
    flo, fhi = exp_bounds(FLOOR_EXP * beta)
    return rlo * flo / D_CONTACT, rhi * fhi / D_CONTACT


def ratio_bound_L2(beta: Q):
    """Also the count 4(K+1)^2 set to one: only the exponential structure and the floor remain."""
    # DERIVED: 2, 4 and the subtracted 1 are `coreRate`'s own literals; only the COUNT is dropped.
    e2lo, e2hi = exp_bounds(2 * beta)
    ehlo, ehhi = exp_bounds(4 * beta * KTOUCH)
    flo, fhi = exp_bounds(FLOOR_EXP * beta)
    return (e2lo - 1) * ehlo * flo / D_CONTACT, (e2hi - 1) * ehhi * fhi / D_CONTACT


def ratio_bound_L3(beta: Q):
    """Also the floor's exp(128 beta) loss removed: the denominator taken at its beta = 0 value."""
    # DERIVED: as in `ratio_bound_L2`; only the floor's exponential is dropped.
    e2lo, e2hi = exp_bounds(2 * beta)
    ehlo, ehhi = exp_bounds(4 * beta * KTOUCH)
    return (e2lo - 1) * ehlo / D_CONTACT, (e2hi - 1) * ehhi / D_CONTACT


def ratio_bound_L4(beta: Q):
    """Also the hard core exp(4 beta K) removed: the per-plaquette activity over D and nothing else.

    This is the floor of the whole family. `(exp(2 beta) - 1)` is `pairTerm_abs_le`'s weight and
    `wilsonDensity`'s range [0, 2]; no sharpening of the COUNT can touch it."""
    # DERIVED: 2 is `wilsonDensity`'s range and 1 the definition's subtraction.
    e2lo, e2hi = exp_bounds(2 * beta)
    return (e2lo - 1) / D_CONTACT, (e2hi - 1) / D_CONTACT


def core_rate_countfree_bounds(beta: Q):
    """(exp(2 beta) - 1) exp(4 beta K) -- `coreRate` with its count factor set to one."""
    # DERIVED: 2, 4 and 1 are `coreRate`'s own literals.
    e2lo, e2hi = exp_bounds(2 * beta)
    ehlo, ehhi = exp_bounds(4 * beta * KTOUCH)
    return (e2lo - 1) * ehlo, (e2hi - 1) * ehhi


# ---------------------------------------------------------------------------
# The two derived thresholds, enclosed from the Lean-proved bracket on c = 3^(-1/4)
# ---------------------------------------------------------------------------
# DERIVED: `LagTwoBound.floor_bounds` PROVES 0.759835 < 3^(-1/4) < 0.759836. Both rationals report a
# derived quantity and are transcribed from the Lean statement; neither is chosen here.
C_LO, C_HI = Q(759835, 10 ** 6), Q(759836, 10 ** 6)


def threshold_four_bounds():
    """`lagTwoThreshold = ((1-c)/(1+c))^2`, decreasing in c, so c_hi gives the lower end."""
    # DERIVED: 1 and the square are `lagTwoThreshold`'s own -- the (1-c), (1+c) of the criterion's
    # quadratic and the squaring that carries the root in sqrt(rho(2)/rho(0)) to the ratio.
    lo = ((1 - C_HI) / (1 + C_HI)) ** 2
    hi = ((1 - C_LO) / (1 + C_LO)) ** 2
    return lo, hi


def _v_six(c: Q, which: str):
    """vSix at a fixed rational c, with the sqrt taken to the side `which` asks for."""
    # DERIVED: 9 and 8 are the extent-six discriminant (2c-1)^2 + 4(2+3c)(1-c) = 9 - 8c^2, a ring
    # identity in `LagTwoSix.vSix`; 2c-1, 2+3c and the outer 2 are that definition's coefficients.
    slo, shi = sqrt_bounds(9 - 8 * c * c)
    s = slo if which == "lo" else shi
    return (s - (2 * c - 1)) / (2 * (2 + 3 * c))


def threshold_six_bounds():
    """`lagTwoThresholdSix = vSix^2`. vSix's numerator falls with c (both terms do) and its
    denominator rises, so vSix falls with c; c_hi with the low sqrt gives the lower end."""
    # DERIVED: 2 is the squaring `lagTwoThresholdSix = vSix^2` performs.
    return _v_six(C_HI, "lo") ** 2, _v_six(C_LO, "hi") ** 2


# ---------------------------------------------------------------------------
# Crossings of an increasing enclosed function
# ---------------------------------------------------------------------------
# DERIVED: the significant figures the crossing bracket is refined to. It sets the bracket WIDTH
# only -- b_lo stays a certified point at which the bound is under the threshold whatever this is,
# so it decides nothing. 25 is far past the factor-1e4 margins every verdict here turns on.
CROSS_SIG = 25

# CHOSEN: the decade scan range. It is a SEARCH span, not a cut: the bracket it returns is verified
# by the enclosures before it is used, and a span too narrow raises rather than returning a wrong
# answer. -40 and 3 were picked to contain every crossing this file looks for, with room.
SCAN_LO_DECADE, SCAN_HI_DECADE = -40, 3


def crossing(f, target_lo: Q, target_hi: Q):
    """Bracket the root of an INCREASING enclosed f against a target enclosed in
    [target_lo, target_hi].

    Returns (b_lo, b_hi, hit_domain_edge).

    THE ONLY CERTIFIED END IS b_lo: `f_hi(b_lo) < target_lo`, so on [0, b_lo] the bound is under
    the threshold whatever the truncation did. `b_hi` is merely the first argument at which the
    upper enclosure FAILS to be under `target_lo`; nothing here tests it against `target_hi`, so
    `b_hi` does NOT certify that the bound is over the threshold there. It is a search endpoint and
    is printed only as a width.

    `hit_domain_edge` is True when the search was stopped by `coreRate >= 1` rather than by the
    target -- in which case the returned value is the estimate's own domain boundary wearing a
    crossing's clothes, and the caller must not read it as one.
    """
    lo = hi = None
    hit_edge = False
    for e in range(SCAN_LO_DECADE, SCAN_HI_DECADE):
        # DERIVED: 10 is the scan's base, a stride and not a magnitude.
        beta = Q(10) ** e
        try:
            flo, fhi = f(beta)
        except AssertionError:
            hi, hit_edge = beta, True
            break
        if fhi < target_lo:
            lo = beta
        elif flo > target_hi:
            hi = beta
            break
    assert lo is not None and hi is not None, "no bracket found in the scan range"
    # Binary search over integers at a FIXED power-of-ten denominator, so the rationals stay small.
    scale = Q(10) ** (CROSS_SIG - math.floor(math.log10(float(lo))))
    n_lo, n_hi = math.floor(lo * scale), math.ceil(hi * scale)
    # DERIVED: 1 is adjacency at the fixed denominator -- the loop stops when the two integer ends
    # are neighbours and no rational of this denominator lies between them. It is a termination
    # condition on the representation, not a tolerance on any quantity.
    while n_hi - n_lo > 1:
        # DERIVED: 2 is bisection's own halving.
        mid = (n_lo + n_hi) // 2
        beta = Q(mid) / scale
        try:
            flo, fhi = f(beta)
        except AssertionError:
            n_hi, hit_edge = mid, True
            continue
        if fhi < target_lo:
            n_lo = mid
        else:
            n_hi = mid
    return Q(n_lo) / scale, Q(n_hi) / scale, hit_edge


# CHOSEN: the default number of printed significant figures. It is display width only -- every
# value printed through it is already a certified bracket end, and callers that need more pass more.
def fmt(x: Q, sig: int = 6) -> str:
    return f"{float(x):.{sig}e}"


# ---------------------------------------------------------------------------
# Independent check on D, by Weyl integration -- deterministic, no RNG
# ---------------------------------------------------------------------------
# CHOSEN: the quadrature grid. A trigonometric-polynomial integrand on a torus is integrated EXACTLY
# by an equispaced grid once the grid beats the integrand's highest harmonic (here 4), so any n
# above about 16 returns the same value; 720 is comfort, and the printed normalisation and first
# moment are the positive controls that show the quadrature is doing what it claims.
WEYL_GRID = 720


def haar_variance_check(n: int = WEYL_GRID):
    """E_Haar[(Re tr U)^2] on SU(3) by the Weyl integration formula on the maximal torus.

    For a class function f: int_SU(3) f = (1/|W|) int_T f(t) |Delta(t)|^2 dt, |W| = 3! = 6, dt the
    normalised Haar measure of the 2-torus (theta_1, theta_2) with theta_3 = -theta_1-theta_2, and
    Delta the Vandermonde in the eigenvalues. The normalisation is self-checking: the same
    quadrature must return 1 for f = 1 and 0 for f = Re chi.
    """
    import numpy as np

    # DERIVED: 2 pi is the torus period; the angles are the maximal torus' coordinates.
    th = 2.0 * np.pi * np.arange(n) / n
    t1, t2 = np.meshgrid(th, th, indexing="ij")
    # DERIVED: the minus sign is det = 1 on SU(3), which fixes theta_3 from the other two.
    t3 = -(t1 + t2)
    z = [np.exp(1j * t) for t in (t1, t2, t3)]
    # DERIVED: 2 is the modulus squared in |Delta|^2, the Weyl formula's own.
    delta2 = np.abs((z[0] - z[1]) * (z[0] - z[2]) * (z[1] - z[2])) ** 2
    # DERIVED: 6 = 3! is the Weyl group order of SU(3), the formula's normalisation.
    w = delta2 / 6.0
    chi = (z[0] + z[1] + z[2]).real
    norm = w.mean()
    return norm, (w * chi * chi).mean() / norm, (w * chi).mean() / norm


def main():
    T4_LO, T4_HI = threshold_four_bounds()
    T6_LO, T6_HI = threshold_six_bounds()

    print("=" * 78)
    print("THE TWO DERIVED THRESHOLDS (from Lean's proved bracket on c = 3^(-1/4))")
    print("=" * 78)
    print(f"  lagTwoThreshold    in [{float(T4_LO):.9f}, {float(T4_HI):.9f}]   (extent four)")
    print(f"  lagTwoThresholdSix in [{float(T6_LO):.9f}, {float(T6_HI):.9f}]   (extent six)")
    print(f"  ratio six/four     >= {float(T6_LO / T4_HI):.4f}")

    print()
    print("=" * 78)
    print("THE CONTACT VALUE D = corrClay 4 0 0 (not a numeral anywhere in the Lean tree)")
    print("=" * 78)
    norm, m2, m1 = haar_variance_check()
    print(f"  exact (characters)            D = 1/18 = {float(D_CONTACT):.10f}")
    print(f"  Weyl quadrature normalisation (must be 1)  = {norm:.12f}")
    print(f"  E_Haar[Re tr U]               (must be 0)  = {m1:.3e}")
    print(f"  E_Haar[(Re tr U)^2]           (must be .5) = {m2:.12f}")
    print(f"  => Var(1 - Re tr U / 3)                    = {m2 / 9.0:.12f}")

    print()
    print("=" * 78)
    print("WHERE THE ESTIMATE'S OWN HYPOTHESIS coreRate 64 beta < 1 STOPS")
    print("=" * 78)
    one = (Q(1), Q(1))
    dlo, dhi, _ = crossing(lambda b: core_rate_bounds(KTOUCH, b), *one)
    print(f"  coreRate 64 beta = 1 at   beta_Lean in [{fmt(dlo, 12)}, {fmt(dhi, 12)}]")
    print(f"                            beta_std  >= {fmt(2 * dlo, 12)}")
    d1lo, _, _ = crossing(core_rate_countfree_bounds, *one)
    print(f"  count 4(K+1)^2 = 16900 set to 1:  beta_Lean >= {fmt(d1lo, 8)}"
          f"   (buys {float(d1lo / dlo):.1f}x)")
    print(f"  activity exp(2 beta) - 1 = 1 (count AND hard core gone): "
          f"beta_Lean = ln2/2 = {math.log(2) / 2:.8f}")
    print("    -- and that last one is the ceiling of ANY expansion in the Wilson activity.")

    print()
    print("=" * 78)
    print("THE CROSSING: largest beta with the CONSTRUCTED ratio bound below the threshold")
    print("  (b_lo reported; [0, b_lo] is certified under the threshold. This is an UPPER bound")
    print("   on the Lean cut, not the Lean cut -- see the ladder of three losses below.)")
    print("=" * 78)
    rungs = [
        ("L0  the construction's own ingredients", ratio_bound_L0),
        ("L1  corePrefactor and 1/(1-r) -> 1    ", ratio_bound_L1),
        ("L2  also count 4(K+1)^2 -> 1          ", ratio_bound_L2),
        ("L3  also floor loss exp(128b) -> 1    ", ratio_bound_L3),
        ("L4  also hard core exp(256b) -> 1     ", ratio_bound_L4),
    ]
    out = {}
    for name, f in rungs:
        b4lo, b4hi, edge4 = crossing(f, T4_LO, T4_HI)
        b6lo, _, edge6 = crossing(f, T6_LO, T6_HI)
        assert not (edge4 or edge6), "search stopped at the rate-one boundary, not at the target"
        out[name.split()[0]] = (b4lo, b6lo)
        print(f"  {name}")
        print(f"      K = lagTwoThreshold    : b_Lean = {fmt(b4lo, 8)}   "
              f"b_std = {fmt(2 * b4lo, 8)}   (search width {fmt(b4hi - b4lo, 2)})")
        print(f"      K = lagTwoThresholdSix : b_Lean = {fmt(b6lo, 8)}   "
              f"b_std = {fmt(2 * b6lo, 8)}")

    print()
    print("=" * 78)
    print("FROM THE CROSSING TO WHAT THE LEAN STATEMENT ACTUALLY DELIVERS (extent four)")
    print("=" * 78)
    cross = out["L0"][0]
    # DERIVED: 2 is `exists_cut_lag_two_ratio`'s own `eps/2` in its witness `min b0 (eps/2)`
    # (LagTwoBound.lean:292), taken at the largest admissible eps -- the crossing itself.
    eps_half = cross / 2
    # DERIVED: 2 is the `lagTwoThreshold / 2` every consumer passes -- LagTwoBound.lean:349,
    # SpectralBound.lean:449, TailRatio.lean:295. The bound is linear in beta in this regime, so a
    # halved target halves the crossing; the value is recomputed rather than assumed linear.
    half_cross, _, _ = crossing(ratio_bound_L0, T4_LO / 2, T4_HI / 2)
    print(f"  pointwise crossing at K = lagTwoThreshold        b_Lean = {fmt(cross, 8)}")
    print(f"  best the witness min b0 (eps/2) can deliver      b_Lean = {fmt(eps_half, 8)}")
    print(f"  crossing at the consumers' K = threshold/2       b_Lean = {fmt(half_cross, 8)}")
    print(f"  and the eps/2 on THAT -- what is certified       b_Lean = "
          f"{fmt(half_cross / 2, 8)}   b_std = {fmt(half_cross, 8)}")
    print(f"  total loss, crossing -> certified                {float(cross / (half_cross / 2)):.3f}x")
    print("  THE FREEZE is a further loss with no numeral: `exists_strong_arm_cut` halves an")
    print("  unnamed metric-ball radius, so the Lean b0 ranges over (0, rate-one/2] and the frozen")
    print("  cut falls to zero as b0 approaches the rate-one point. One illustrative b0:")
    # DERIVED: 2 is `exists_strong_arm_cut`'s own halving (StrongArm.lean:113-115); the certified
    # rate-one lower bracket halved is one admissible b0 among a continuum, not the canonical one.
    b0 = dlo / 2
    bflo, _, _ = crossing(lambda b: ratio_bound_L0_frozen(b, b0), T4_LO, T4_HI)
    rlo, rhi = core_rate_bounds(KTOUCH, b0)
    print(f"      b0 = {fmt(b0, 6)}  (coreRate there = {float(rhi):.6f}, so 1/(1-r) = "
          f"{float(1 / (1 - rlo)):.4f})")
    print(f"      frozen crossing b_Lean = {fmt(bflo, 8)}   "
          f"frozen/pointwise = {float(bflo / cross):.6f}")

    print()
    print("=" * 78)
    print("WHAT THE BOUND READS ACROSS ITS OWN DOMAIN (threshold ~ 0.0186 for scale)")
    print("=" * 78)
    # DERIVED: the sample points are fractions of the rate-one point dlo, the estimate's own domain
    # endpoint; the fractions are strides for a table and decide nothing.
    for num, den in ((1, 1000), (1, 100), (1, 10), (1, 2), (9, 10), (99, 100)):
        beta = dlo * Q(num, den)
        _, rhi = ratio_bound_L0(beta)
        print(f"  beta = {float(num) / den:>6.3f} * (rate-one point) = {fmt(beta, 4)} :"
              f"  bound <= {float(rhi):.4e}   ({float(rhi / T4_LO):.3e}x the threshold)")

    print()
    print("=" * 78)
    print("WHAT THE CONSTANTS ARE WORTH, at beta = 0 (the overshoot, sized)")
    print("=" * 78)
    plo, _ = core_prefactor_bounds(KTOUCH, Q(0))
    print(f"  count 4(K+1)^2 at K = 64                 = {int(count_factor(KTOUCH))}")
    print(f"  corePrefactor 64 0 = 8*(4*65^2)^2        = {float(plo):.6e}")
    # DERIVED: 128 is `le_corePrefactor`'s recorded lower bound (8 * 16 * 1), quoted to size the
    # gap between what the LEMMA states and what the DEFINITION evaluates to.
    print(f"  le_corePrefactor records only            >= 128  -- the lemma understates the"
          f" definition by {float(plo) / 128:.3e}x")
    # DERIVED: 16 is `circLag 2`^4 / ... -- the 1/circLag(d)^4 of `contact_relative_unconditional`
    # at circLag 2 = 2, i.e. 2^4; the bar is 16 * lagTwoThreshold, from
    # `contact_relative_constant_too_large`.
    print(f"  contact-relative bar 16*lagTwoThreshold  = {float(16 * T4_HI):.6f}")
    print(f"  coreConst 64 0 over that bar             = {float(plo / (16 * T4_HI)):.4e}x")

    print()
    print("=" * 78)
    print("MEASURED, QUOTED ONCE, FEEDING NOTHING ABOVE")
    print("=" * 78)
    # CHOSEN: transcribed from the lag-two probe's report so the uncovered window can be described.
    # No bound above reads them; this block is print-only and deliberately last.
    peak_beta_lean, peak_ratio, peak_err = 2.8, 0.00688, 0.00060
    print(f"  peak measured rho(2)/rho(0) = {peak_ratio} +/- {peak_err} "
          f"at beta_Lean = {peak_beta_lean}")
    print(f"  margin under lagTwoThreshold    = {float(T4_LO) / peak_ratio:.3f}x")
    print(f"  margin under lagTwoThresholdSix = {float(T6_LO) / peak_ratio:.3f}x")
    print(f"  peak / crossing (L0, extent four) = {peak_beta_lean / float(cross):.3e}")
    print(f"  peak / CERTIFIED cut              = {peak_beta_lean / float(half_cross / 2):.3e}")
    print(f"  peak / rate-one point             = {peak_beta_lean / float(dlo):.3e}")
    print(f"  peak / best-case crossing (L4)    = {peak_beta_lean / float(out['L4'][0]):.3e}")
    print(f"  peak / activity ceiling ln2/2   = {peak_beta_lean / (math.log(2) / 2):.3f}")


if __name__ == "__main__":
    main()
