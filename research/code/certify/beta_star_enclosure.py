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

    lo_beta, hi_beta = Q(749, 1000), Q(750, 1000)
    Blo_lo, Blo_hi = B_bounds(lo_beta)
    Bhi_lo, Bhi_hi = B_bounds(hi_beta)
    print(f"B(0.749) certified <= {_f(Blo_hi):.12f}   (kappa_0 lower {_f(klo):.12f})")
    print(f"B(0.750) certified >= {_f(Bhi_lo):.12f}   (kappa_0 upper {_f(khi):.12f})")

    assert Blo_hi < klo, "B(0.749) < kappa_0 not certified"
    assert Bhi_lo > khi, "B(0.750) > kappa_0 not certified"
    print("CERTIFIED: B(0.749) < kappa_0 < B(0.750)  =>  beta_star in (0.749, 0.750)")

    # certified r over the bracket (r increasing: r_lo at 0.749, r_hi at 0.750)
    rlo749, _ = ratio_bounds(lo_beta)
    _, rhi750 = ratio_bounds(hi_beta)
    print()
    print("Lean `beta_star_enclosure` hypotheses (certified rationals):")
    print(f"  r(beta_star)  in [{_f(rlo749):.6f}, {_f(rhi750):.6f}]  (use rlo=0.182, rhi=0.184)")
    print(f"  kappa_0       in [{_f(klo):.6f}, {_f(khi):.6f}]  (use klo=0.2746, khi=0.2747)")
    encl_lo = Q(2746, 10000) / (2 * Q(184, 1000))
    encl_hi = Q(2747, 10000) / (2 * Q(182, 1000))
    print(f"  => beta_star in [{_f(encl_lo):.6f}, {_f(encl_hi):.6f}]  (machine-checked in Lean)")
    assert Q(182, 1000) <= rlo749 and rhi750 <= Q(184, 1000)
    assert klo >= Q(2746, 10000) and khi <= Q(2747, 10000)
    print("CERTIFIED: the round rational hypotheses used in Lean bound the true values.")
