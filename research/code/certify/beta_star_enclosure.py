"""The strong-coupling threshold beta_star of A1, certified to match the Lean.

`lean/MassGap/Apriori.lean`, `apriori_A1_strong`, proves: with `r` the leading
character ratio, `beta_c` defined by `2*beta_c*r = kappa_0`, and the character
bound `mu(beta) <= 2*beta*r` (Osterwalder-Seiler, T4, cited), every `beta <
beta_c` has `mu(beta) < kappa_0`. The Lean threshold is SYMBOLIC (`2*betac*r =
kappa_0`); it hardcodes no number. This script instantiates it with the actual
leading character ratio `r(beta) = I_2(beta)/I_1(beta)` (modified Bessel) and
`kappa_0 = (1/4) ln 3` (Floor.lean, `floor_pos`), and CERTIFIES the root

    2 * beta_star * r(beta_star) = kappa_0 ,   beta_star ~ 0.7497 .

Certification is by EXACT RATIONAL arithmetic (fractions.Fraction) with a proven
geometric tail bound on each positive power series, so every enclosure below is
rigorous, not floating point:

  * I_nu(beta) = sum_{m>=0} (beta/2)^(2m+nu)/(m!(m+nu)!): positive terms, so a
    partial sum is a lower bound; the successive-term ratio is <= q < 1 past the
    cutoff, so tail <= term_M/(1-q) is an upper bound.
  * ln 3 = sum_{k>=0} 1/((2k+1) 4^k) (from 2*artanh(1/2)): positive terms, ratio
    <= 1/4, tail <= term_M * 4/3.

From these, B(beta) = 2*beta*I_2/I_1 is enclosed in a rational interval, and the
bracket B(749/1000) < kappa_0 < B(750/1000) is checked with exact rationals, so
beta_star lies in (0.749, 0.750) by the intermediate value theorem.

beta_star ~ 0.75 is NOT the character-expansion convergence radius beta_KP ~ 0.97
(Kotecky-Preiss / Osterwalder-Seiler): the bound is VALID for beta < beta_KP, and
sub-floor only for beta < beta_star. At beta_KP the bound value 2 beta I2/I1 ~
0.45 is well above kappa_0 ~ 0.275. The two are different quantities.

The certified r and kappa_0 bounds printed below are the hypotheses of the Lean
`beta_star_enclosure` (Apriori.lean), which machine-checks the interval arithmetic
beta_star = kappa_0/(2 r) in [klo/(2 rhi), khi/(2 rlo)].

No Entroptics read here (this is the analytic threshold of a cited bound, not a
configuration read); it fixes the number the paper's Sec 8.2 cites.
"""
import math
from fractions import Fraction as Q

# ── certified rational enclosures ──────────────────────────────────────────────
def ln3_bounds(M: int = 40):
    """ln 3 = sum_{k>=0} 1/((2k+1) 4^k) in [lo, hi], exact rationals.
    Terms positive; ratio term_{k+1}/term_k = (2k+1)/((2k+3)*4) <= 1/4, so the
    tail from k=M is <= term_M/(1 - 1/4) = term_M * 4/3."""
    S = sum((Q(1, (2 * k + 1) * 4 ** k) for k in range(M)), Q(0))
    term_M = Q(1, (2 * M + 1) * 4 ** M)
    return S, S + term_M * Q(4, 3)          # ln 3 in [S, S + tail]


def kappa0_bounds(M: int = 40):
    lo, hi = ln3_bounds(M)
    return lo / 4, hi / 4                    # kappa_0 = (1/4) ln 3


def besselI_bounds(nu: int, beta: Q, M: int = 30):
    """I_nu(beta) = sum_{m>=0} (beta/2)^(2m+nu)/(m!(m+nu)!) in [lo, hi], exact.
    Positive terms, so the partial sum is a lower bound; past m=M the term ratio
    is <= q = (beta/2)^2/((M+1)(M+nu+1)) < 1, so tail <= term_M/(1-q)."""
    h = beta / 2
    t = h ** nu / Q(math.factorial(nu))      # m = 0 term
    S = Q(0)
    for m in range(M):
        S += t
        t = t * h * h / Q((m + 1) * (m + nu + 1))   # advance to term m+1
    q = (h * h) / Q((M + 1) * (M + nu + 1))          # bounds every later ratio
    assert q < 1
    return S, S + t / (1 - q)                 # I_nu in [S, S + tail], t = term_M


def ratio_bounds(beta: Q, M: int = 30):
    """r(beta) = I_2/I_1 in [rlo, rhi] (both positive)."""
    i1lo, i1hi = besselI_bounds(1, beta, M)
    i2lo, i2hi = besselI_bounds(2, beta, M)
    return i2lo / i1hi, i2hi / i1lo


def B_bounds(beta: Q, M: int = 30):
    """B(beta) = 2*beta*I_2/I_1 in [Blo, Bhi]."""
    rlo, rhi = ratio_bounds(beta, M)
    return 2 * beta * rlo, 2 * beta * rhi


def _f(x: Q) -> float:
    return float(x)


if __name__ == "__main__":
    klo, khi = kappa0_bounds()
    print(f"kappa_0 = (1/4) ln 3   certified in [{_f(klo):.12f}, {_f(khi):.12f}]")

    assert klo >= Q(2746, 10000) and khi <= Q(2747, 10000), "kappa_0 bracket not certified"
    print("CERTIFIED: kappa_0 in [0.2746, 0.2747]")
    print()
    print("NOTE: the strong-coupling threshold beta_star is no longer certified here. It is a")
    print("      THEOREM: Bessel.ratio_le_quarter gives I2/I1 <= x/4 termwise, so the character")
    print("      bound is beta^2/2 and sits below the floor exactly when beta^2 < (1/2) ln 3.")
    print("      This module remains the rational-enclosure toolkit its other callers use")
    print("      (kappa0_bounds, ln3_bounds, besselI_bounds, ratio_bounds, B_bounds).")
