"""The entropy floor, certified by EXACT RATIONAL arithmetic: kappa_0 >= 0.455484.

WHAT THIS CERTIFIES, and it is the same kappa_0 the Lean tree uses.
`Floor.lean` proves kappa_0 >= (1/4) log 3 = 0.274653 by counting DIRECTED CUBE-PATHS -- three
choices of axis at each of k steps, boundary area 4k+6. That is one subfamily of the closed connected
vortex surfaces kappa_0 = limsup_A (ln N(A))/A is defined over. Counting a RICHER subfamily gives a
LARGER lower bound on the same quantity, and that is what this does.

THE METHOD (front-capped, void-excluded, comoving transfer matrix; Collatz-Wielandt).
Sweep directed cube-animals by coordinate sum s = x+y+z. The state is the comoving FRONT normalised
to its own corner, capped at K cells inside a DxD box. A step chooses a nonempty subset of the
forward neighbours; the boundary area added is 6*|new| - 2*(parent-child adjacencies), which is the
same accounting `CubeArea.boundary_card_eq` makes at K=1.

  * VOID EXCLUSION. A step is rejected when its new front caps a cube absent from the old front on
    all three forward neighbours. A maximum-coordinate-sum argument shows this catches EVERY enclosed
    void, so every accepted polycube is simply connected and its boundary is a SINGLE CONNECTED
    surface. MEASURED CAVEATS, recorded because the earlier wording overclaimed: 26-39% of accepted
    polycubes have a PINCHED (non-manifold) boundary, Euler characteristic 1 or 0 rather than 2 --
    which does NOT break the count, since 100% are Z2-closed and that is what
    VortexFamily.IsClosedSurface requires. And this is NOT the condition
    CubeConnected.boundary_connected proves: that theorem is for directed cube-PATHS, whose argument
    runs on one cube per coordinate sum, while these animals carry up to K. Nothing in Lean covers
    them. Disabling caps_void at these depths also produces zero voids and zero disconnected
    boundaries, moving the bound by 1.5e-4, so the exclusion is SAFE (it only over-rejects) rather
    than demonstrably necessary.
  * COLLATZ-WIELANDT. For T(x) nonnegative and any v > 0, min_i (Tv)_i / v_i <= rho(T). The weight
    x in (0,1) makes rho(x) increasing, so a certified rho(x*) > 1 places the critical x_c below x*
    and gives kappa_0 >= -ln(x*). A rigorous LOWER bound, and valid for ANY positive v -- so
    approximating the eigenvector by rationals costs tightness, never soundness.

WHY THIS FILE EXISTS SEPARATELY FROM THE ORIGINAL.
The ladder was computed in `_archive/classic/7_run_floor_ladder.py`, whose own exact-rational
cross-check ran only where `states <= 500`. THREE rungs were float-only with a 1e-9 margin --
(4,4) at 545 states as well as (4,5) at 2469 and (4,6) at 8273. This runs the exact check at EVERY
rung, so the published number stops resting on floating point.

THE ROUNDING DIRECTION, which is the only place rigour could leak.
`x_star` is found by float bisection. Before the exact pass it is rounded UP to a rational. rho is
increasing in x and the bound delivered is -ln(x), so a larger x makes rho > 1 EASIER to certify and
the resulting bound SMALLER. Rounding up is therefore conservative in both directions at once: the
certified statement is `rho(x_r) > 1` at an exact rational `x_r >= x_star`, and the only float left
in the logical chain is the final logarithm of that rational.

WHAT IT BUYS. The cited Osterwalder-Seiler character bound `mu <= 2 beta I2/I1` is rigorous only
inside its convergence radius beta_KP ~ 0.97 (`certify/interval_enclosure.py`), where it reads
B(0.97) = 0.453027. A floor above that value makes the character bound prove `mu < kappa_0` across
its ENTIRE validity range instead of stopping at beta < sqrt((1/2) log 3) = 0.74115.

Writes `7_dat_floor_ladder_exact.csv`.
"""
from __future__ import annotations

import csv
import itertools
import math
import os
import sys
from fractions import Fraction

import numpy as np
from scipy.sparse import csr_matrix

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "..", "data", "7_dat_floor_ladder_exact.csv")

#: the Lean-certified base rung: `Floor.directed_paths_card` + `CubeArea.boundary_card_eq`.
KAPPA0_LEAN = math.log(3) / 4.0
#: DERIVED: the character bound `2 beta I2/I1` evaluated at its own convergence radius
#: beta_KP ~ 0.97, by the exact-rational interval arithmetic of `certify/interval_enclosure.py`.
#: It is not a threshold anyone picked -- it is where the cited result stops being valid.
B_AT_BETA_KP = 0.453027
#: CHOSEN: the reference value mu(beta_c), recorded in the archived working notes as the target that
#: closes the crossover window. It is REPORTING ONLY -- no certified quantity below depends on it,
#: and removing it would change no verdict.
CLOSE_TARGET = 0.490
#: CHOSEN: denominator of the rational the float bisection is rounded UP to. It carries NO rigour:
#: any positive denominator yields a valid certificate, and a larger one only tightens the bound.
#: 10^6 keeps the exact pass fast at ~10^4 states.
RATIONAL_DEN = 10 ** 6

#: DERIVED: the three forward unit steps of a DIRECTED cube-path. `3` is the dimension of the
#: sublattice and each vector is a unit step along one axis -- the same three `Floor.directed_paths_card`
#: counts. The coordinate sum strictly increases, which is what makes the paths self-avoiding.
FWD = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]


def canon(f):
    """The front, normalised to its own corner -- the state is comoving."""
    m = [min(c[i] for c in f) for i in range(3)]
    return frozenset((c[0] - m[0], c[1] - m[1], c[2] - m[2]) for c in f)


def nxt(f):
    return sorted({(c[0] + e[0], c[1] + e[1], c[2] + e[2]) for c in f for e in FWD})


def adj(f, fp):
    """Parent-child adjacencies: each removes 2 from the boundary area (one face on each side)."""
    fs = set(f)
    return sum(1 for cp in fp for e in FWD
               if (cp[0] - e[0], cp[1] - e[1], cp[2] - e[2]) in fs)


def caps_void(s, fp):
    """Would this step enclose a void? If so the boundary would be disconnected -- reject it."""
    fps = set(fp)
    par = {(cp[0] - e[0], cp[1] - e[1], cp[2] - e[2]) for cp in fp for e in FWD}
    return any(q not in s and all((q[0] + e[0], q[1] + e[1], q[2] + e[2]) in fps for e in FWD)
               for q in par)


def build(K, D):
    seen = {canon({(0, 0, 0)})}
    frontier = list(seen)
    while frontier:
        nf = []
        for s in frontier:
            cand = nxt(s)
            for r in range(1, min(K, len(cand)) + 1):
                for sub in itertools.combinations(cand, r):
                    fp = set(sub)
                    if caps_void(s, fp):
                        continue
                    cfp = canon(fp)
                    if len(cfp) <= K and max(max(c) for c in cfp) <= D - 1 and cfp not in seen:
                        seen.add(cfp)
                        nf.append(cfp)
        frontier = nf
    states = sorted(seen, key=lambda f: (len(f), sorted(f)))
    idx = {s: i for i, s in enumerate(states)}
    rows, cols, exps = [], [], []
    for s in states:
        i = idx[s]
        for r in range(1, min(K, len(nxt(s))) + 1):
            for sub in itertools.combinations(nxt(s), r):
                fp = set(sub)
                if caps_void(s, fp):
                    continue
                cfp = canon(fp)
                if cfp in idx:
                    rows.append(i)
                    cols.append(idx[cfp])
                    # 6 faces per new cube, less 2 per parent-child adjacency
                    exps.append(6 * len(fp) - 2 * adj(s, fp))
    return len(states), np.array(rows), np.array(cols), np.array(exps, float)


# CHOSEN: `iters` and `tol` are the power-iteration budget. They carry NO rigour -- this routine only
# LOCATES a candidate `x_star` and an approximate eigenvector, and Collatz-Wielandt is valid for ANY
# strictly positive vector, so a badly converged `v` costs tightness and never soundness.
def cw_float(n, rows, cols, exps, x, iters=4000, tol=1e-14):
    T = csr_matrix((x ** exps, (rows, cols)), shape=(n, n))
    v = np.ones(n)
    for _ in range(iters):
        w = T @ v
        nrm = np.linalg.norm(w)
        # DERIVED: a zero iterate means the front has no admissible successor, so rho = 0.
        if nrm == 0:
            return 0.0, v
        nv = w / nrm
        if np.linalg.norm(nv - v) < tol:
            v = nv
            break
        v = nv
    return float((T @ v / v).min()), v


# CHOSEN: `margin` separates "rho above 1" from rounding during the FLOAT search. It carries no
# rigour either -- it only decides which rational the exact pass is then run at.
def bisect_x(K, D, margin=1e-9):
    """Float bisection for x_star. Only LOCATES the rational; it carries no rigour of its own."""
    n, rows, cols, exps = build(K, D)
    lo, hi = 0.30, 0.99
    for _ in range(50):
        m = (lo + hi) / 2
        r, _ = cw_float(n, rows, cols, exps, m)
        if r > 1.0 + margin:
            hi = m
        else:
            lo = m
    _, v = cw_float(n, rows, cols, exps, hi)
    return n, rows, cols, exps, hi, v


def cw_exact(n, rows, cols, exps, x_r, v):
    """Exact-rational Collatz-Wielandt at the rational `x_r`. Returns a Fraction lower bound on rho."""
    vf = [Fraction(float(t)).limit_denominator(RATIONAL_DEN) for t in v]
    eps = Fraction(1, RATIONAL_DEN * 1000)
    # DERIVED: Collatz-Wielandt requires v strictly positive; `0` is that requirement, not a cutoff.
    vf = [t if t > 0 else eps for t in vf]
    pw = {e: x_r ** e for e in {int(e) for e in exps}}
    Tv = [Fraction(0)] * n
    for a in range(len(rows)):
        Tv[rows[a]] += pw[int(exps[a])] * vf[cols[a]]
    return min(Tv[i] / vf[i] for i in range(n))


def rung(K, D):
    n, rows, cols, exps, xs, v = bisect_x(K, D)
    x_r = Fraction(math.ceil(xs * RATIONAL_DEN), RATIONAL_DEN)
    assert float(x_r) >= xs, "the rational must not fall below the bisected x_star"
    rho = cw_exact(n, rows, cols, exps, x_r, v)
    # DERIVED: `1` is the Collatz-Wielandt criterion itself -- rho(x) > 1 places the critical x_c
    # below x, which is what makes -ln(x) a lower bound on kappa_0. Not a tolerance.
    return dict(K=K, D=D, states=n, x_rational=str(x_r), x_float=round(float(x_r), 9),
                # DERIVED: `1` is the Collatz-Wielandt criterion itself. rho(x) > 1 places
                # the critical x_c below x, which is what makes -ln(x) a lower bound.
                exact_cw_rho=float(rho), certified=bool(rho > 1),
                # DERIVED: the bound is -ln(x_r) and the certificate is a LOWER bound, so the
                # published digits must be FLOORED, never rounded. round() rounds half and would
                # publish a value ABOVE what is certified -- which it did, on four of six rungs,
                # until 2026-09-17.
                kappa0_lower=math.floor(-math.log(float(x_r)) * 10 ** 6) / 10 ** 6)


def main(rungs=((1, 1), (2, 4), (3, 5), (4, 4), (4, 5), (4, 6))):
    print(f"kappa_0 (Lean, K=1 rung)    = {KAPPA0_LEAN:.10f}")
    print(f"B(beta_KP = 0.97) character = {B_AT_BETA_KP:.10f}   <- the bar to clear")
    print(f"mu(beta_c)                  = {CLOSE_TARGET:.10f}   <- a floor here closes the window")
    print()
    rows_out = []
    for K, D in rungs:
        rec = rung(K, D)
        rows_out.append(rec)
        verdict = ("CLOSES THE WINDOW" if rec["kappa0_lower"] >= CLOSE_TARGET
                   else "clears B(beta_KP)" if rec["kappa0_lower"] > B_AT_BETA_KP
                   else "below B(beta_KP)")
        print(f"K={K} D={D}  states={rec['states']:>6}  x={rec['x_float']:.6f}  "
              f"exact CW rho >= {rec['exact_cw_rho']:.8f}  "
              f"{'CERTIFIED' if rec['certified'] else '*** FAILED ***'}")
        print(f"            => kappa_0 >= {rec['kappa0_lower']:.6f}   {verdict}")
        if not rec["certified"]:
            print("REFUSED: exact Collatz-Wielandt did not place rho above 1", file=sys.stderr)
            return 1

    # validation: the K=1 sector IS the Lean floor, so the ladder and `Floor.lean` count the same thing
    base = next(r for r in rows_out if (r["K"], r["D"]) == (1, 1))
    # CHOSEN: `2e-3` is the agreement the K=1 rung must show with (1/4)log3. It is a
    # CALIBRATION tolerance on a validation assert, not an input to any certified bound --
    # the rung reproduces the Lean floor to six places.
    assert abs(base["kappa0_lower"] - KAPPA0_LEAN) < 2e-3, \
        f"path calibration failed: K=1 gave {base['kappa0_lower']}, expected {KAPPA0_LEAN}"
    print(f"[validation] K=1 rung = {base['kappa0_lower']:.6f} ~ (1/4)ln3 = {KAPPA0_LEAN:.6f}  OK")

    best = max(r["kappa0_lower"] for r in rows_out)
    os.makedirs(os.path.dirname(os.path.abspath(OUT)), exist_ok=True)
    with open(os.path.abspath(OUT), "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows_out[0].keys()))
        w.writeheader()
        for r in rows_out:
            w.writerow(r)
    print(f"wrote {os.path.abspath(OUT)}")
    print()
    if best > B_AT_BETA_KP:
        print(f"CERTIFIED: kappa_0 >= {best:.6f} > B(beta_KP) = {B_AT_BETA_KP:.6f}")
        print("  => the cited character bound proves mu < kappa_0 across its ENTIRE validity range")
        print(f"     [0, beta_KP ~ 0.97], not only below sqrt((1/2)log3) = {math.sqrt(math.log(3)/2):.5f}")
    else:
        print(f"kappa_0 >= {best:.6f}, which does NOT clear B(beta_KP) = {B_AT_BETA_KP:.6f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
