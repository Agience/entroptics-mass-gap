"""interval_enclosure.py -- the rigorous (exact-rational) character-bound curve for A1's strong-coupling
region, and the precise residual window the crossover interior leaves to the Monte-Carlo read.

Reuses the certified Bessel / kappa_0 enclosures of `beta_star_enclosure.py`. The Osterwalder-Seiler leading
character bound is a rigorous UPPER bound on the tension,

    mu(beta) <= B(beta) = 2*beta*I_2(beta)/I_1(beta),

VALID for beta < beta_KP ~ 0.97 (Kotecky-Preiss / character-expansion convergence radius). It certifies the
sub-floor confinement mu < kappa_0 exactly where B(beta) < kappa_0, i.e. beta < beta_star ~ 0.7497.

This tabulates B(beta) in exact rationals across a grid and reports the certified strong sub-floor region, the
value at beta_KP (the leading bound cannot reach kappa_0 inside its radius), and the residual crossover window
that no strong-coupling enclosure closes.

No Entroptics read: this is analytic interval arithmetic, not a configuration read.
"""
import os
import sys
from fractions import Fraction as Q

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import beta_star_enclosure as BSE

BETA_KP = Q(97, 100)   # ~0.97 character-expansion convergence radius (Kotecky-Preiss / Osterwalder-Seiler)


def main():
    klo, khi = BSE.kappa0_bounds()
    print(f"kappa_0 = (1/4) ln 3  certified in [{float(klo):.6f}, {float(khi):.6f}]")
    print("Osterwalder-Seiler leading bound  mu(beta) <= B(beta) = 2 beta I_2/I_1  "
          f"(valid beta < beta_KP = {float(BETA_KP):.2f})\n")

    print(f"{'beta':>6} | {'B_lo':>10} {'B_hi':>10} | mu < kappa_0 certified?")
    beta_star = None
    for bi in range(20, 96, 5):                         # 0.20 .. 0.95
        b = Q(bi, 100)
        Blo, Bhi = BSE.B_bounds(b)
        subfloor = Bhi < klo                            # rigorous: mu <= Bhi < kappa_0_lower
        if subfloor:
            beta_star = b
        print(f"{float(b):>6.2f} | {float(Blo):>10.6f} {float(Bhi):>10.6f} | {'YES' if subfloor else 'no'}")

    Bkp_lo, Bkp_hi = BSE.B_bounds(BETA_KP)
    print(f"\nB(beta_KP = {float(BETA_KP):.2f}) in [{float(Bkp_lo):.4f}, {float(Bkp_hi):.4f}]  "
          f">>  kappa_0 ~ {float(khi):.4f}")
    print("\n=> RIGOROUS strong sub-floor region:  [0, beta_star],  beta_star ~ 0.75 "
          f"(last certified grid point {float(beta_star):.2f}).")
    print("=> Character bound VALID only to beta_KP ~ 0.97; there B ~ 0.45 > kappa_0, so higher-order terms "
          "cannot reach the floor inside the radius.")
    print("=> RIGOROUS weak region: [beta_weak, inf)  (free-field plateau mu_inf < kappa_0 + asymptotic freedom, cited).")
    print("=> RESIDUAL (Monte-Carlo only): (beta_star ~ 0.75, beta_weak] -- the crossover interior, the open")
    print("   enclosure lemma. Attack: SU(2) small-volume rigorous spectral enclosure.")


if __name__ == "__main__":
    main()
