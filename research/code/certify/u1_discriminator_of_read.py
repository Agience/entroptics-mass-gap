"""The negative control: the SAME read applied to compact U(1) across its deconfinement transition.

WHY THIS IS THE TEST THAT MATTERS. `Complete.confinement_at_of_ratio` says `substrateRatio <= c`
implies `mu < kappa0`. Nothing in it knows which theory it is reading, and the Lean says so:

    "A channel whose lag moment stays under the ceiling for a GAPLESS theory makes the hypothesis
     satisfiable without a gap, and mu < kappa_0 then certifies nothing."

So the criterion is only worth anything if it SEPARATES. The paper's claim is that it does: for
SU(N) the tension stays sub-floor at every coupling, while for compact U(1) "the monopole action
a^2 mu ~ beta grows, crosses kappa_0 at a finite beta_c, and deconfines". That is a prediction about
this read, on a theory known independently to deconfine at beta_c ~ 1.011, and it had not been
measured with this functional -- the released U(1) evidence is a resolved-mode count, a different
quantity.

WHAT A PASS AND A FAIL LOOK LIKE. A pass is mu rising with beta and crossing kappa0 near the known
beta_c while the SU(N) reads stay below it. A fail -- mu staying sub-floor across the U(1) Coulomb
phase -- would mean the criterion does not discriminate confinement from its absence, and that is
worth knowing regardless of which way it comes out. The script reports the crossing it finds and
does not assume one exists.

DERIVED THROUGHOUT. `kappa0 = (1/4)log3` is proved in `Floor.lean`; the comparison value is that
floor, not a tolerance. The couplings are whatever the store holds, in order, with none selected.
The crossing is located as the first coupling whose tension exceeds the floor -- a comparison of two
measured quantities, not a fitted transition point.
"""
from __future__ import annotations

import csv
import glob
import math
import os
import re
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import store_path
import ym_confinement_of_cos_average as COS
import ym_crossover_confinement_of_grid as CG

KAPPA0 = 0.25 * math.log(3.0)
# DERIVED: the growth condition solved for c; the lag arity N+1 is the periodic extent L.
C_MAX = (1.0 - 3.0 ** -0.25) * 2 / (2 * math.pi) ** 2
BASE = store_path.store_root(required=False)


def ensembles(group):
    """Every (L, beta) the store holds for a group, with its shards."""
    out = {}
    if not BASE:
        return out
    for d in sorted(os.listdir(BASE)):
        p = os.path.join(BASE, d)
        # the raw-link collection shares these filenames at a different rank
        if not os.path.isdir(p) or "links" in d:
            continue
        for f in glob.glob(f"{p}/{group}_L*_b*.s*.npy"):
            m = re.match(rf"{group}_L(\d+)_b([\d.]+)\.s", os.path.basename(f))
            if m:
                out.setdefault((int(m.group(1)), float(m.group(2))), []).append(f)
    return out


# CHOSEN: ncap caps configurations per coupling. It costs read time, not validity -- the
# tension is an ensemble average, and a cap set too low surfaces as a noisier read rather than
# as a wrong one.
def read(files, ncap=256):
    arr = np.asarray(np.concatenate([np.load(f) for f in sorted(files)], 0)[:ncap],
                     dtype=np.float64)
    # DERIVED: two is where a sample variance exists at all.
    if arr.shape[0] < 2:
        return None
    P = CG.per_config_profiles(arr)
    c = COS.cos_avg(P)
    # DERIVED: the domain of the logarithm.
    return {
        "n": arr.shape[0],
        "cos_avg": c,
        # DERIVED: the domain of the logarithm, as in ym_confinement_of_cos_average.
        "mu": -math.log(c) if c > 0 else math.inf,
        "d2": CG.d2_from_profiles(P),
    }


def main() -> None:
    if not BASE:
        raise SystemExit("u1_discriminator_of_read: no ensemble store configured.\n"
                         + store_path.hint())
    u1 = ensembles("u1")
    if not u1:
        raise SystemExit("u1_discriminator_of_read: the store holds no compact U(1) ensembles, so "
                         "the discriminating test cannot be run. Refusing to report a separation "
                         "with only one theory measured.")

    print(f"kappa0 = (1/4)log3 = {KAPPA0:.6f}   (Floor.lean, derived)   c_max = {C_MAX:.6f}")
    print()
    rows = []
    for (L, b) in sorted(u1):
        r = read(u1[(L, b)])
        if r is None:
            continue
        r.update(group="u1", L=L, beta=b, ratio=r["d2"] / L ** 2)
        rows.append(r)

    print("COMPACT U(1) -- the theory that is known to deconfine")
    print(f"{'beta':>6} {'n':>5} {'<cos>':>10} {'mu':>11} {'mu/kappa0':>10} "
          f"{'ratio':>10} {'verdict':>14}")
    for r in rows:
        v = "sub-floor" if r["mu"] < KAPPA0 else "ABOVE FLOOR"
        print(f"{r['beta']:6.2f} {r['n']:5d} {r['cos_avg']:10.5f} {r['mu']:11.5f} "
              f"{r['mu'] / KAPPA0:10.3f} {r['ratio']:10.6f} {v:>14}")

    above = [r for r in rows if r["mu"] >= KAPPA0]
    print()
    if above:
        first = min(above, key=lambda r: r["beta"])
        below = [r for r in rows if r["beta"] < first["beta"] and r["mu"] < KAPPA0]
        print(f"  THE READ CROSSES THE FLOOR at beta = {first['beta']:.2f} "
              f"(mu = {first['mu']:.5f} >= kappa0 = {KAPPA0:.6f})")
        if below:
            last = max(below, key=lambda r: r["beta"])
            print(f"  last sub-floor coupling: beta = {last['beta']:.2f}, mu = {last['mu']:.5f}")
        print(f"  {len(above)} of {len(rows)} couplings are above the floor.")
    else:
        print("  THE READ NEVER CROSSES THE FLOOR on the U(1) ensembles the store holds.")
        print(f"  largest tension {max(r['mu'] for r in rows):.5f} against kappa0 = {KAPPA0:.6f}.")
        print("  The criterion does not separate compact U(1) from SU(N) on this evidence, which")
        print("  is a limitation of the discriminator and not a result about either theory.")

    out = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                       "data", "9_5_dat_u1_discriminator.csv")
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["group", "L", "beta", "nconfigs", "cos_avg", "mu", "d2_circle",
                    "substrate_ratio", "above_floor", "kappa0", "c_max"])
        for r in rows:
            w.writerow([r["group"], r["L"], f"{r['beta']:.2f}", r["n"], f"{r['cos_avg']:.6f}",
                        f"{r['mu']:.6f}", f"{r['d2']:.5f}", f"{r['ratio']:.6f}",
                        "yes" if r["mu"] >= KAPPA0 else "no",
                        f"{KAPPA0:.6f}", f"{C_MAX:.6f}"])
    print(f"\nwrote {os.path.relpath(out)}  ({len(rows)} couplings)")


if __name__ == "__main__":
    main()
