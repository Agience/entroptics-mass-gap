"""How large a gap the aperture criterion can certify -- a cap, derived from the floor alone.

WHAT IS BEING CERTIFIED. `ZeroMode.correlation_gap_of_tension` turns `mu < kappa_0` into an
exponential bound, so the criterion does yield a mass gap at finite aperture. This script answers the
next question: HOW BIG a gap can the criterion certify at aperture `n`? The answer is a ceiling that
shrinks like `1/n`, quantitative rather than a remark.

WHICH LIMIT THIS IS A NO-GO FOR, and it is not the one it was first written as. The ceiling shrinks
as the APERTURE widens. It says nothing about the box: `ScreenedGap.gap_bound_box_independent` carries
the box as a parameter and demonstrably never uses it, so `Delta_phys >= C / L_ap` is not a bound the
thermodynamic limit has to survive -- it is one the box never enters. Nor the continuum limit, where
the spacing cancels.

What the ceiling does forbid is `L_ap -> infinity`, and that is not a limit a finite observer
performs: the aperture's size is the observer's capacity, and an observer inside the substrate it
reads has a window strictly smaller than that substrate, however large the substrate becomes. The
substrate may be taken to infinity; the window cannot follow it.

THE OBJECT. The criterion reads a single transfer mode on the periodic lattice,

    rho(d) = lam ^ circLag(d),   circLag(d) = min(d, n - d),   theta(d) = 2 pi d / n,

and asks whether `<cos> = sum_d rho(d) cos(theta d) / sum_d rho(d)` clears `e^{-kappa_0} = 3^{-1/4}`.
Both sums are geometric, so `<cos>` is EXACT in closed form -- no large-`n` expansion, no fit. With
`m = n/2`, `k = 2 pi / n` and `(lam e^{ik})^m = -lam^m`:

    num = 2 (1 + lam^m) (1 - lam cos k) / (1 - 2 lam cos k + lam^2) - 1 - lam^m
    den = 2 (1 - lam^m) / (1 - lam) - 1 + lam^m

`_avg_direct` recomputes the same average by summing every lag, and the script REFUSES if the two
disagree beyond the working precision. That check is one reason to trust the closed form; the other is
that its load-bearing step is proved rather than checked. `ZeroMode.sum_geom_cos_eq_re` and
`ZeroMode.sum_geom_cos_closed` establish in Lean, on the three foundational axioms, that the real
cosine sum is the real part of a complex geometric series and hence equals `(z^m - 1)/(z - 1)` away
from `z = 1`; `ZeroMode.sum_range_antipodal_fold` and `ZeroMode.circLag_cos_sum_fold` prove the
antipodal fold, the second for this exact summand, giving

    sum_{d < 2m} lam^circLag(d) cos(2 pi d / 2m) = 1 - lam^m + 2 sum_{1<=d<m} lam^d cos(2 pi d / 2m).

The `- lam^m` there is the antipodal term the half-line constant has no counterpart for, so the step
that distinguishes `10.9887` from `11.1760` is proved and not merely computed. What remains here is
assembling the ratio, its monotonicity, and the solve for the critical `lam`.

THE CAP. `<cos>` is strictly increasing in `1 - lam` at fixed `n` (checked, not assumed), so there is
a unique critical `lam` at which the criterion is exactly saturated, and it is located by bisection
on that monotone function -- no scan, no grid, no tolerance. Reported as `n (1 - lam_crit)`, which is
`n` times the certified decay rate to first order. That product converges:

    n (1 - lam_crit)  ->  C = 2 pi a*,   a* the unique root of   a^2 coth(a pi / 2) = 3^{-1/4} (a^2+1)

`C` is derived from `kappa_0` and the circle geometry and nothing else. The limit is also computed
here from that transcendental equation and compared against the finite-`n` sequence; they agree to
eleven digits by `n = 2^40`.

WHY IT MATTERS, AND WHAT IT DOES NOT SAY. `Delta >~ C/n` is spacing-independent: it is a finite-
VOLUME statement, and at fixed physical box it does not improve as the continuum is approached. So
the aperture criterion cannot on its own establish a gap that survives `L -> infinity`, at ANY
aperture -- that needs an input bounding `lam` away from `1` uniformly in the volume, which the
tension is not. This does not weaken `correlation_gap_of_tension`, whose conclusion holds wherever
its hypothesis does; it measures that theorem's reach, and says where the remaining work is.

AND THE CAP IS NOT VACUOUS, WHICH IS THE OTHER HALF OF THE ANSWER. `C/n` could have been so small
that meeting the criterion said nothing about the physics -- for instance if it merely reproduced the
box. It does not. A free MASSLESS field in the same periodic box has lowest mode `2 pi / n`, which is
`a = 1` in the scaling variable, and `a* = 1.7489 > 1`: the massless mode reads `<cos> = 0.5452`
against a floor of `0.7598` and FAILS the criterion at every aperture. So where `mu < kappa_0` holds
for a spectral correlation it certifies a decay rate `a*` TIMES the massless finite-volume gap, and
`a*` is exactly that factor. The script refuses if that ordering ever reverses.

This is not in tension with the U(1) control (Sec 9), which found the MEASURED read failing to
separate a confining theory from a massless one. That control is about contact-scale correlations at
simulated apertures, where the criterion is met for resolution reasons and the lag distribution is
nothing like a transfer mode. The statement here is about the spectral object. Both are true, and
the distance between them is the distance between what the criterion means and what the current
measurement can deliver.

A NEIGHBOURING CONSTANT IS NOT THIS ONE. `2 pi sqrt(T/(1-T)) = 11.176` with `T = 3^{-1/4}` is the
ceiling for `rho(d) = lam^d` on the HALF-LINE. That is a different object: on the circle the antipodal
reflection contributes the `coth(a pi/2) > 1` factor, which lowers the requirement to `10.9887`. The
two are within `0.19` of each other, closer than any simulated aperture is to its own limit, so they
cannot be told apart from small `n`. Both are computed below and the difference reported. The periodic
read this program performs takes the circle constant; the half-line one belongs to an open chain.
"""
from __future__ import annotations

import csv
import math
import os
import sys

try:
    import mpmath as mp
except ImportError:                                     # pragma: no cover - environment guard
    print("REFUSED: mpmath is required; the cap is quoted to 11 digits and float64 cannot carry it.")
    raise SystemExit(2)

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(os.path.dirname(os.path.dirname(HERE)), "data", "9_10_dat_aperture_cap.csv")

#: DERIVED: the entropy floor proved in `Floor.lean`. Every constant below descends from this one.
mp.mp.dps = 50
KAPPA0 = mp.mpf(1) / 4 * mp.log(3)
TARGET = mp.e ** (-KAPPA0)                              # 3^(-1/4); mu < kappa_0  <=>  <cos> > TARGET

#: CITED, not derived here: the physical string tension that sets the lattice spacing, and the
#: conversion constant. `SQRT_SIGMA_GEV` is the only external number in this file and it enters ONLY
#: the physical restatement at the end -- the cap `C`, and every row above it, is independent of it.
#: Naming both here makes that dependence visible instead of burying it in a GeV.fm constant.
HBARC = mp.mpf("0.1973269804")          # GeV fm
SQRT_SIGMA_GEV = mp.mpf("0.44")         # GeV; the conventional value used throughout this paper

#: DERIVED: the apertures reported. Powers of two spanning the lattice sizes actually simulated
#: (n = 8..64) out to where the limit is resolved; the sequence's limit is computed analytically, so
#: no element of this list enters any conclusion -- they are evidence of convergence, not its basis.
APERTURES = (8, 16, 32, 64, 128, 256, 1024, 8192, 2 ** 20, 2 ** 30, 2 ** 40)


def _avg_closed(n: int, lam: mp.mpf) -> mp.mpf:
    """`<cos>` for `rho(d) = lam^circLag(d)` on `n` lags, in closed form. `n` even."""
    m = n // 2
    c = mp.cos(2 * mp.pi / n)
    lm = lam ** m
    num = 2 * (1 + lm) * (1 - lam * c) / (1 - 2 * lam * c + lam * lam) - 1 - lm
    den = 2 * (1 - lm) / (1 - lam) - 1 + lm
    return num / den


def _avg_direct(n: int, lam: mp.mpf) -> mp.mpf:
    """The same average by summing every lag. The closed form is checked against this, not trusted."""
    num = mp.mpf(0)
    den = mp.mpf(0)
    for d in range(n):
        w = lam ** min(d, n - d)
        num += w * mp.cos(2 * mp.pi * d / n)
        den += w
    return num / den


def _critical(n: int) -> mp.mpf:
    """The unique `1 - lam` at which the criterion is exactly saturated at aperture `n`.

    Bisection on a monotone function. Monotonicity is CHECKED by the caller rather than assumed;
    without it a bisection would be reporting a bracket rather than a root.
    """
    lo, hi = mp.mpf(0), mp.mpf(1)
    for _ in range(220):
        mid = (lo + hi) / 2
        if _avg_closed(n, 1 - mid) < TARGET:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def _limit_avg(a: mp.mpf) -> mp.mpf:
    """`<cos>` in the scaling limit `n -> inf` at fixed `a = n (1 - lam) / (2 pi)`.

    With `u = k d` filling `[0, pi]` and `lam^d -> e^{-a u}`, both sums become integrals:
    `a^2 (1 + e^{-a pi}) / [(a^2 + 1)(1 - e^{-a pi})]`, which is `a^2 coth(a pi/2)/(a^2+1)`.
    """
    e = mp.e ** (-a * mp.pi)
    return a * a * (1 + e) / ((a * a + 1) * (1 - e))


def main() -> int:
    rows = []

    # (1) the closed form must reproduce a direct sum over every lag, or nothing below is meaningful
    worst = mp.mpf(0)
    for n in (4, 8, 16, 64, 256, 1024):
        for ls in ("0.01", "0.3", "0.7", "0.9", "0.99", "0.999"):
            lam = mp.mpf(ls)
            worst = max(worst, abs(_avg_direct(n, lam) - _avg_closed(n, lam)))
    if worst > mp.mpf(10) ** (-30):
        print(f"REFUSED: closed form disagrees with the direct sum by {mp.nstr(worst, 6)}")
        return 1
    print(f"closed form vs direct sum over 36 (n, lam) pairs: max diff {mp.nstr(worst, 6)}")

    # (2) monotonicity in (1 - lam), which is what makes the critical point unique and bisectable
    for n in APERTURES[:8]:
        prev = None
        for j in range(1, 40):
            x = mp.mpf(j) / 40
            v = _avg_closed(n, 1 - x)
            if prev is not None and not v > prev:
                print(f"REFUSED: <cos> is not increasing in (1-lam) at n={n}, x={mp.nstr(x, 6)}")
                return 1
            prev = v
    print(f"<cos> increasing in (1-lam) at every aperture checked")

    # (3) the limit, from the transcendental equation alone
    a_star = mp.findroot(lambda a: _limit_avg(a) - TARGET, mp.mpf("1.5"))
    c_circle = 2 * mp.pi * a_star
    c_halfline = 2 * mp.pi * mp.sqrt(TARGET / (1 - TARGET))
    resid = _limit_avg(a_star) - TARGET
    if abs(resid) > mp.mpf(10) ** (-40):
        print(f"REFUSED: a* does not solve its own equation (residual {mp.nstr(resid, 6)})")
        return 1

    # (4) the finite-aperture sequence, and its approach to that limit.
    #
    # TWO forms, and the difference between them decides what may be quoted at a finite volume. The
    # criterion constrains `1 - lam`; a MASS is `Delta = -log lam`. Both products `n(1-lam)` and
    # `n*Delta` converge to the same `C`, but from opposite sides: `n(1-lam)` rises to it from below
    # while `n*Delta` also rises to it from below yet stays much closer (10.689 against 7.797 at
    # n = 16). So `C/n` is an upper bound on the certified MASS at every aperture -- which is what
    # is what the cap caps -- and the bound actually certified at aperture `n` is `n*Delta(n)/n`,
    # slightly less. Quoting `C/n` AT a finite volume overstates it; the physical section below uses
    # the aperture's own value, not `C`.
    print(f"\n{'aperture':>12} {'1-lam_crit':>18} {'n(1-lam)':>14} {'Delta_crit':>16} "
          f"{'n*Delta':>14} {'minus C':>12}")
    approach = []
    mass_at = {}
    for n in APERTURES:
        x = _critical(n)
        prod = n * x
        delta = -mp.log(1 - x)
        mass_prod = n * delta
        mass_at[n] = mass_prod
        approach.append(prod - c_circle)
        print(f"{n:>12} {mp.nstr(x, 10):>18} {mp.nstr(prod, 10):>14} {mp.nstr(delta, 10):>16} "
              f"{mp.nstr(mass_prod, 10):>14} {mp.nstr(mass_prod - c_circle, 4):>12}")
        if mass_prod > c_circle:
            print(f"REFUSED: at n={n} the certified mass product {mp.nstr(mass_prod, 10)} EXCEEDS "
                  f"the limit {mp.nstr(c_circle, 10)}; C would not be a ceiling")
            return 1
        rows.append({
            "quantity": "aperture_cap",
            "aperture": n,
            "one_minus_lambda_crit": mp.nstr(x, 12),
            "n_times_rate": mp.nstr(prod, 12),
            "deficit_from_limit": mp.nstr(prod - c_circle, 6),
        })
        rows.append({
            "quantity": "aperture_cap_mass",
            "aperture": n,
            "one_minus_lambda_crit": mp.nstr(delta, 12),
            "n_times_rate": mp.nstr(mass_prod, 12),
            "deficit_from_limit": mp.nstr(mass_prod - c_circle, 6),
        })

    # the sequence must actually converge, monotonically, to the analytic limit -- if it did not,
    # the limit would be a coincidence of the last row rather than the sequence's value
    #: DERIVED: zero is the analytic limit itself, so `prod - c_circle < 0` is the statement that the
    #: finite-aperture rate sits BELOW its limit. It is a sign, not a threshold: no magnitude is
    #: being tolerated, and the same line would fail for any sequence approaching from above.
    if not all(approach[i] < 0 for i in range(len(approach))):
        print("REFUSED: the finite-aperture rate does not approach the limit from below")
        return 1
    if not all(abs(approach[i + 1]) < abs(approach[i]) for i in range(len(approach) - 1)):
        print("REFUSED: the approach to the limit is not monotone")
        return 1
    if abs(approach[-1]) > mp.mpf(10) ** (-9):
        print(f"REFUSED: the sequence has not resolved the limit ({mp.nstr(approach[-1], 6)})")
        return 1

    rows.append({
        "quantity": "limit_circle",
        "aperture": "",
        "one_minus_lambda_crit": "",
        "n_times_rate": mp.nstr(c_circle, 12),
        "deficit_from_limit": "0",
    })
    rows.append({
        "quantity": "limit_halfline",
        "aperture": "",
        "one_minus_lambda_crit": "",
        "n_times_rate": mp.nstr(c_halfline, 12),
        "deficit_from_limit": mp.nstr(c_halfline - c_circle, 6),
    })
    rows.append({
        "quantity": "entropy_floor_exp_minus_kappa0",
        "aperture": "",
        "one_minus_lambda_crit": "",
        "n_times_rate": mp.nstr(TARGET, 10),
        "deficit_from_limit": "0",
    })
    rows.append({
        "quantity": "a_star",
        "aperture": "",
        "one_minus_lambda_crit": "",
        "n_times_rate": mp.nstr(a_star, 12),
        "deficit_from_limit": "",
    })

    print(f"\na*                     = {mp.nstr(a_star, 12)}   "
          f"(root of a^2 coth(a pi/2) = 3^(-1/4)(a^2+1))")
    print(f"C  (circle, circLag)   = {mp.nstr(c_circle, 12)}   <- the cap this criterion carries")
    print(f"C' (half-line, lam^d)  = {mp.nstr(c_halfline, 12)}   <- a DIFFERENT object; not this one")
    print(f"difference             = {mp.nstr(c_halfline - c_circle, 6)}")
    print(f"\nso mu < kappa_0 at aperture n certifies at most  Delta ~ {mp.nstr(c_circle, 6)} / n,")
    print("which vanishes as the aperture widens: a finite-volume gap, not a thermodynamic one.")

    # the measured spacings, needed by both (4c) and (5)
    _tension_path = os.path.join(os.path.dirname(OUT), "8_8_dat_string_tension.csv")
    if not os.path.exists(_tension_path):
        print(f"\nREFUSED: {os.path.basename(_tension_path)} absent; the physical statements below")
        print("would have to be hand-computed, and they are quoted in the paper.")
        return 1
    with open(_tension_path, newline="", encoding="utf-8") as fh:
        _all_t = [r for r in csv.DictReader(fh) if r.get("sqrt_sigma")]
    # EVERY (beta, L) the string tension was measured at, each carrying its OWN aperture. Naming one
    # extent here would be choosing which volume the discrimination is asked at, and the answer
    # depends on it -- so the aperture is read from each row instead, and every row is reported.
    _seen_bl = set()
    trows_for_discrimination = []
    for r in sorted(_all_t, key=lambda q: (float(q["beta"]), int(q["L"]))):
        key = (r["beta"], r["L"])
        if key in _seen_bl:
            continue
        _seen_bl.add(key)
        trows_for_discrimination.append(r)
    if not trows_for_discrimination:
        print("REFUSED: the string-tension artifact carries no rows to read a spacing from")
        return 1

    # (4b) WHAT THE CAP IS MEASURED AGAINST, which decides whether it is weak or strong. A free
    # MASSLESS field in the same periodic box is not gapless at finite volume: its lowest nonzero
    # mode is 2 pi / n, so it sits at a = 1 in the scaling variable. The criterion demands a >= a*,
    # and a* > 1, so a massless box mode FAILS it -- at every aperture, by a wide margin. The cap is
    # therefore not a restatement of the box size: satisfying `mu < kappa_0` certifies a decay rate
    # a* times the one a massless field would show in the same box, and a* is that factor exactly.
    #
    # This does NOT contradict the U(1) control, which found the measured read failing to separate a
    # confining theory from a massless one. That control concerns contact-scale correlations at the
    # apertures actually simulated, where the criterion is met for resolution reasons and the lag
    # distribution is nothing like a single transfer mode. The statement here is about the SPECTRAL
    # object: for a correlation that is a transfer mode, the criterion is strictly stronger than
    # masslessness-in-a-box. Both hold, and the gap between them is what the cap is worth.
    massless = _limit_avg(mp.mpf(1))
    if massless >= TARGET:
        print(f"REFUSED: a massless box mode clears the floor ({mp.nstr(massless, 8)} >= "
              f"{mp.nstr(TARGET, 8)}); the criterion would certify nothing beyond finite volume")
        return 1
    for n in (64, 256, 1024, 8192):
        v = _avg_closed(n, mp.e ** (-2 * mp.pi / n))
        if v >= TARGET:
            print(f"REFUSED: the massless box mode clears the floor at n={n}")
            return 1
    print(f"\nmassless box mode (a=1): <cos> = {mp.nstr(massless, 8)} < {mp.nstr(TARGET, 8)} "
          f"= 3^(-1/4), so it FAILS the criterion")
    print(f"the criterion therefore certifies a rate a* = {mp.nstr(a_star, 9)} times the massless "
          f"finite-volume gap 2pi/n")
    rows.append({
        "quantity": "massless_box_mode_cosavg",
        "aperture": "",
        "one_minus_lambda_crit": "",
        "n_times_rate": mp.nstr(massless, 9),
        "deficit_from_limit": mp.nstr(massless - TARGET, 6),
    })

    # (4c) DOES THE CRITERION DISCRIMINATE AT THE APERTURE ACTUALLY SIMULATED? The cap above is the
    # n -> infinity limit; at finite n the requirement is WEAKER (7.797 at n = 16, not 10.989), so
    # asking what the criterion decides at n = 16 must use the exact closed form and not the scaling
    # cap. It matters: at beta = 2.50 the scaling form would reject a physical glueball (8.59 < 10.99)
    # while the exact form accepts it (8.59 > 7.797). The asymptotic constant is the wrong tool here.
    #
    # The two hypotheses put to it are a physical 0++ glueball at 1.7 GeV, converted to lattice units
    # through the measured spacing, and a free massless field, whose lowest box mode is 2 pi / n. If
    # the criterion cannot separate those at the simulated aperture then it decides nothing there,
    # whatever it does asymptotically -- so this is the question, and the script refuses on either
    # failure. It is a statement about the SPECTRAL object: the measured reads are contact-scale and
    # clear the floor for resolution reasons, which is what the U(1) control (Sec 9) records.
    #: CITED, not derived here: the 0++ glueball mass. It enters only this comparison.
    GLUEBALL_GEV = mp.mpf("1.7")

    print(f"\nat each simulated aperture, against a {GLUEBALL_GEV} GeV glueball and a massless field:")
    print(f"{'beta':>6} {'n':>5} {'a [fm]':>10} {'m*a':>9} {'glue <cos>':>12} {'massless':>10} "
          f"{'verdict':>16}")
    for r in trows_for_discrimination:
        n = int(r["L"])                     # DERIVED: the row's OWN periodic extent
        if n % 2:                           # the closed form is stated for an even circle
            continue
        a_fm = mp.mpf(r["sqrt_sigma"]) * HBARC / SQRT_SIGMA_GEV
        ma = GLUEBALL_GEV * a_fm / HBARC
        v_glue = _avg_closed(n, mp.e ** (-ma))
        v_free = _avg_closed(n, mp.e ** (-2 * mp.pi / n))
        sep = v_glue > TARGET > v_free
        print(f"{r['beta']:>6} {n:>5} {mp.nstr(a_fm, 5):>10} {mp.nstr(ma, 5):>9} "
              f"{mp.nstr(v_glue, 6):>12} {mp.nstr(v_free, 6):>10} "
              f"{'separates' if sep else 'DOES NOT SEPARATE':>16}")
        if not sep:
            print(f"REFUSED: at beta={r['beta']}, n={n} the criterion does not put a physical "
                  "glueball above the floor and a massless field below it")
            return 1
        rows.append({
            "quantity": "glueball_vs_floor",
            "aperture": f"beta{r['beta']}_n{n}",
            "one_minus_lambda_crit": mp.nstr(1 - mp.e ** (-ma), 8),
            "n_times_rate": mp.nstr(v_glue, 8),
            "deficit_from_limit": mp.nstr(v_glue - TARGET, 6),
            # the inputs the comparison was made from, so the table in the paper is reproducible
            # from this file alone rather than by rerunning the conversion by hand
            "a_fm": mp.nstr(a_fm, 8),
            "m_times_a": mp.nstr(ma, 8),
            "lambda": mp.nstr(mp.e ** (-ma), 8),
        })
        rows.append({
            "quantity": "massless_vs_floor",
            "aperture": f"n{n}",
            "one_minus_lambda_crit": mp.nstr(1 - mp.e ** (-2 * mp.pi / n), 8),
            "n_times_rate": mp.nstr(v_free, 8),
            "deficit_from_limit": mp.nstr(v_free - TARGET, 6),
            "a_fm": "",
            "m_times_a": "0",
            "lambda": mp.nstr(mp.e ** (-2 * mp.pi / n), 8),
        })

    # (4d) THE EXCLUSION, as the Lean theorem consumes it. `Moment.Read.tension_ge_floor_of_substrate`
    # says a correlation whose circular second moment reaches (1 - 3^{-1/4})/8 has a tension at or
    # above the floor. The massless box mode's substrate ratio is computed here and compared against
    # that ceiling: if it did NOT exceed it, the diffraction-limit reading would have no arithmetic
    # behind it and this script would be reporting a mechanism that does not operate. It refuses.
    #
    # Reported at several apertures, not one, because the claim is that the exclusion holds at EVERY
    # screen size rather than at a convenient one.
    sub_ceiling = (1 - TARGET) / 8
    print(f"\nEXCLUSION: substrate ceiling forced by mu < kappa_0 = {mp.nstr(sub_ceiling, 8)}")
    print(f"{'aperture':>10} {'massless substrate':>20} {'ratio to ceiling':>18} {'verdict':>10}")
    worst_ratio = None
    for n in (16, 32, 64, 256, 1024, 8192):
        lam = mp.e ** (-2 * mp.pi / n)
        den = mp.mpf(0)
        m2 = mp.mpf(0)
        for d in range(n):
            c = min(d, n - d)
            w = lam ** c
            den += w
            m2 += w * c * c
        sub = (m2 / den) / n ** 2
        ratio = sub / sub_ceiling
        worst_ratio = ratio if worst_ratio is None else min(worst_ratio, ratio)
        print(f"{n:>10} {mp.nstr(sub, 8):>20} {mp.nstr(ratio, 6):>18} "
              f"{'EXCLUDED' if sub > sub_ceiling else 'ADMITTED':>10}")
        if sub <= sub_ceiling:
            print(f"REFUSED: at aperture {n} the massless mode does NOT exceed the substrate ceiling,")
            print("so the screen would admit it and the diffraction-limit exclusion would not hold.")
            return 1
        rows.append({
            "quantity": "massless_substrate",
            "aperture": n,
            "one_minus_lambda_crit": mp.nstr(sub, 10),
            "n_times_rate": mp.nstr(ratio, 8),
            "deficit_from_limit": mp.nstr(sub - sub_ceiling, 6),
        })
    rows.append({
        "quantity": "substrate_ceiling",
        "aperture": "",
        "one_minus_lambda_crit": mp.nstr(sub_ceiling, 10),
        "n_times_rate": "",
        "deficit_from_limit": "0",
    })
    print(f"  the massless mode exceeds the ceiling at every aperture, by at least "
          f"{mp.nstr(worst_ratio, 5)}x -- a band-limited screen cannot host it.")

    # (4e) THE RATE, DERIVED FROM THE TENSION -- the input `hrate` stops being an assumption.
    #
    # The exclusion of (4d) runs in the useful direction too. The substrate of a single mode
    # `rho(d) = lam^circLag(d)` DECREASES as the decay `1 - lam` grows (a faster-decaying correlation
    # is more concentrated), so a CEILING on the substrate is a FLOOR on the decay:
    #
    #     mu < kappa_0  =>  substrate < (1 - 3^{-1/4})/8  =>  n * Delta  >  kappa,  Delta = -log lam
    #
    # Two values of `kappa` are computed, and the difference between them is the price of wanting a
    # proof rather than a number:
    #
    #   BISECTION -- invert the exact substrate at each aperture. Sharper, but it is a root-find, and
    #     a root-find is not something a proof assistant checks.
    #   ELEMENTARY -- `substrate >= lam^{n/2}/12`, from three steps a proof assistant does check:
    #     every weight is at least `lam^{n/2}`, the normalisation is at most `n`, and the circular
    #     second moment of the UNIFORM distribution is `n^3/12`. Weaker, and formalisable.
    #
    # Both are reported. The elementary one is the one the Lean chain can consume.
    print("\n(4e) the decay rate FORCED by the tension, for a single mode")
    print(f"{'aperture':>10} {'x_crit=1-lam':>14} {'n*Delta':>12} {'elementary':>12}")

    def _substrate(n, lam):
        den = mp.mpf(0)
        m2 = mp.mpf(0)
        for d in range(n):
            c = min(d, n - d)
            w = lam ** c
            den += w
            m2 += w * c * c
        return (m2 / den) / n ** 2

    # DERIVED: the elementary constant solves lam^{n/2}/12 = ceiling, i.e. n*Delta = -2 log(12*ceiling).
    # No search: it is the closed-form inverse of the three-step bound above.
    kappa_elementary = -2 * mp.log(12 * sub_ceiling)
    worst_bisect = None
    for n in (4, 8, 16, 64, 256, 1024):
        lo, hi = mp.mpf(0), mp.mpf(1)
        for _ in range(90):
            mid = (lo + hi) / 2
            if _substrate(n, 1 - mid) > sub_ceiling:
                lo = mid
            else:
                hi = mid
        x = (lo + hi) / 2
        nd = n * -mp.log(1 - x)
        worst_bisect = nd if worst_bisect is None else min(worst_bisect, nd)
        print(f"{n:>10} {mp.nstr(x, 8):>14} {mp.nstr(nd, 7):>12} "
              f"{mp.nstr(kappa_elementary, 7):>12}")
        rows.append({
            "quantity": "rate_from_tension",
            "aperture": n,
            "one_minus_lambda_crit": mp.nstr(x, 10),
            "n_times_rate": mp.nstr(nd, 8),
            "deficit_from_limit": mp.nstr(nd - kappa_elementary, 6),
        })

    # the elementary constant must actually be a LOWER bound on the bisection one, or the
    # formalisable route would be claiming more than the exact computation supports
    if kappa_elementary >= worst_bisect:
        print(f"REFUSED: the elementary constant {mp.nstr(kappa_elementary, 7)} is not below the "
              f"exact {mp.nstr(worst_bisect, 7)}; the provable bound would exceed the true one")
        return 1
    # DERIVED: zero is where a rate stops being a rate. A non-positive constant certifies no gap
    # at all, so this is the definition of the claim failing, not a tolerance on it.
    if kappa_elementary <= 0:
        print("REFUSED: the elementary rate constant is not positive, so it certifies no gap")
        return 1
    rows.append({
        "quantity": "rate_constant_elementary",
        "aperture": "",
        "one_minus_lambda_crit": "",
        "n_times_rate": mp.nstr(kappa_elementary, 10),
        "deficit_from_limit": "",
    })
    print(f"\n  elementary (formalisable) kappa = {mp.nstr(kappa_elementary, 7)}")
    print(f"  exact (bisection), worst aperture = {mp.nstr(worst_bisect, 7)}")
    print(f"  sharp criterion C                 = {mp.nstr(c_circle, 7)}")
    print(f"  so mu < kappa_0 forces Delta > {mp.nstr(kappa_elementary, 6)}/n, and at a screen of")
    print(f"  fixed physical extent L that is Delta_phys > {mp.nstr(kappa_elementary, 6)}/L.")

    # (5) the same cap in physical units. Delta_phys = Delta_lat / a >= C/(L a) = C / L_phys, so the
    # bound depends on the physical box ALONE and not on the spacing -- which is exactly what makes
    # it a finite-VOLUME obstruction and not a continuum one. The spacing is taken from the measured
    # string tension in `8_8_dat_string_tension.csv` (a*sqrt(sigma), per beta), so no step here is
    # hand-arithmetic; the one external input is the physical scale sqrt(sigma), cited not derived.
    tension = os.path.join(os.path.dirname(OUT), "8_8_dat_string_tension.csv")
    if not os.path.exists(tension):
        print(f"\nREFUSED: {os.path.basename(tension)} absent, so the physical form would have to be")
        print("hand-computed. It is quoted in the paper, so it is emitted from the artifact or not at all.")
        return 1

    with open(tension, newline="", encoding="utf-8") as fh:
        trows = [r for r in csv.DictReader(fh) if r.get("sqrt_sigma")]
    if not trows:
        print("REFUSED: the string-tension artifact carries no sqrt_sigma column")
        return 1

    print(f"\n{'beta':>6} {'L':>4} {'a.sqrt(sigma)':>15} {'a [fm]':>10} "
          f"{'L_phys [fm]':>13} {'Delta >= [GeV]':>15}")
    seen = set()
    for r in sorted(trows, key=lambda q: (float(q["beta"]), int(q["L"]))):
        key = (r["beta"], r["L"])
        if key in seen:
            continue
        seen.add(key)
        asig = mp.mpf(r["sqrt_sigma"])
        a_fm = asig * HBARC / SQRT_SIGMA_GEV
        n_here = int(r["L"])
        lphys = n_here * a_fm
        # DERIVED: this aperture's own certified mass product, not the n -> infinity constant.
        # `C` is the ceiling; what is certified AT this volume is the finite-n value, and using
        # `C` here would claim a bound 2.8% stronger than the criterion supports at n = 16.
        kn = mass_at.get(n_here) or (n_here * -mp.log(1 - _critical(n_here)))
        dmin = kn * HBARC / lphys
        print(f"{r['beta']:>6} {r['L']:>4} {mp.nstr(asig, 6):>15} {mp.nstr(a_fm, 6):>10} "
              f"{mp.nstr(lphys, 6):>13} {mp.nstr(dmin, 6):>15}  (n*Delta={mp.nstr(kn, 8)})")
        rows.append({
            "quantity": "physical_bound",
            "aperture": f"beta{r['beta']}_L{r['L']}",
            "one_minus_lambda_crit": mp.nstr(lphys, 8),
            "n_times_rate": mp.nstr(dmin, 8),
            "deficit_from_limit": "",
        })
    rows.append({
        "quantity": "C_times_hbarc_GeV_fm",
        "aperture": "",
        "one_minus_lambda_crit": "",
        "n_times_rate": mp.nstr(c_circle * HBARC, 8),
        "deficit_from_limit": "",
    })
    n16 = mass_at.get(16) or (16 * -mp.log(1 - _critical(16)))
    rows.append({
        "quantity": "mass_product_times_hbarc_GeV_fm_n16",
        "aperture": "n16",
        "one_minus_lambda_crit": "",
        "n_times_rate": mp.nstr(n16 * HBARC, 8),
        "deficit_from_limit": "",
    })
    print(f"\nCEILING (n -> inf):  Delta <= certifiable at {mp.nstr(c_circle * HBARC, 8)} "
          f"GeV.fm / L_phys")
    print(f"CERTIFIED at n=16 :  Delta >= {mp.nstr(n16 * HBARC, 8)} GeV.fm / L_phys, "
          f"independent of the spacing.")

    # One header for every row. Collected as the UNION of the keys actually written rather than from
    # the first row, so a row carrying an extra input cannot silently drop it -- and DictWriter is
    # given a complete field list, so a missing key writes an empty cell instead of raising.
    fields = []
    for r in rows:
        for k in r:
            if k not in fields:
                fields.append(k)
    with open(OUT, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, restval="")
        w.writeheader()
        w.writerows(rows)
    print(f"\nwrote {OUT}  ({len(rows)} rows)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
