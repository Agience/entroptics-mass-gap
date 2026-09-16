"""Volume-independence and continuum scaling, read at FIXED SELECTION -- no cut anywhere.

WHY THIS EXISTS. Sec 8.7b's two volume/scaling claims are both stated through a variational MINIMUM
over an (operator, smearing, tau) basis, and taking a minimum forces a decision about which entries
are admissible. That decision was a literal `tol = 0.25`, and it is not inert: scanning it moves the
beta=2.30 bound by a factor 2.4, and at loose tolerances the rule selects the ACTION DENSITY -- the
operator the section turns on it never selecting. The repo currently holds TWO different derived
replacements for that number which disagree with each other (the tests' invariance plateau and the
figure's `e < v`), so the conflict is live rather than theoretical.

This file asks the same two physical questions WITHOUT taking a minimum at all. Hold the operator,
the smearing level and the lag FIXED, and compare that one observable across volumes, or across
couplings. No minimum is taken, so no admissibility rule is needed, so no tolerance exists to choose.
The conflict is dissolved rather than adjudicated.

WHAT THE TWO TESTS MEAN.

  VOLUME. For a gapped theory the finite-volume correction to a mass is EXPONENTIALLY small
  (Luscher): `Delta(L) - Delta_inf ~ e^{-m L}`. At beta=2.30 the measured `a*Delta ~ 1.2`, so past
  L=12 the correction is `e^{-14}`, seven decimal places down. A gapped theory must therefore show
  `m_eff` FLAT in volume -- not approximately flat over a chosen window, flat. Anything else is
  either gapless or an artifact of the instrument.

  SCALING. A physical mass holds `Delta/sqrt(sigma)` constant as the spacing changes; a cutoff
  artifact holds `a*Delta` constant instead, so its ratio rises as `1/(a sqrt sigma)`. Across
  beta = 2.30..2.50 the spacing moves by 1.78x, so the two predictions differ by 78% -- the whole
  effect. Both are ONE-parameter fits to the same three points, so they are compared by their chi2
  directly; neither is nested in the other and no significance is claimed beyond the likelihood
  ratio the chi2 difference gives.

WHAT THIS DOES NOT CLAIM. Three couplings spanning 1.78x is SCALING evidence, not a continuum limit.
Volume-independence at one spacing is finite-spacing confinement, not a mass gap. And the evidence is
not uniform across the basis: every action-density series prefers the cutoff reading, as does the
lightly-smeared plaquette. That is reported in full rather than filtered -- the table below carries
every series, and the reader sees which prefer which.

DERIVED THROUGHOUT. `sqrt(sigma)` per coupling is read from the string-tension artifact (Sec 8.8,
textbook Wilson loops, no Entroptics read in the extraction). Nothing is fitted but the two
one-parameter models being compared, and every series with enough points is reported.
"""
from __future__ import annotations

import csv
import math
import os
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(os.path.dirname(os.path.dirname(HERE)), "research", "data")
if not os.path.isdir(DATA):
    DATA = os.path.join(os.path.dirname(os.path.dirname(HERE)), "data")

#: DERIVED: the coupling whose volume tower the correlator artifact carries.
VOL_BETA = 2.30
#: DERIVED: the lattice size the coupling scan is measured at, fixed so the scan varies only beta.
SCAN_L = 16
#: DERIVED: a series needs at least three points for a one-parameter fit to have a residual at all.
MIN_PTS = 3


def _rows(name):
    with open(os.path.join(DATA, name), newline="") as fh:
        return list(csv.DictReader(fh))


def _f(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return float("nan")


def _chi2_const(vals, errs):
    """Weighted constant fit: the value and chi2 per degree of freedom."""
    w = [1.0 / e ** 2 for e in errs]
    c = sum(v * wi for v, wi in zip(vals, w)) / sum(w)
    chi = sum(((v - c) / e) ** 2 for v, e in zip(vals, errs))
    return c, chi / max(1, len(vals) - 1)


def _chi2_prop(vals, errs, basis):
    """Weighted fit to `k * basis` -- the cutoff alternative, also ONE parameter."""
    w = [1.0 / e ** 2 for e in errs]
    k = (sum(v * b * wi for v, b, wi in zip(vals, basis, w))
         / sum(b * b * wi for b, wi in zip(basis, w)))
    chi = sum(((v - k * b) / e) ** 2 for v, b, e in zip(vals, basis, errs))
    return k, chi / max(1, len(vals) - 1)


def series(rows):
    """Every (operator, smearing, lag) series, keyed so nothing is selected."""
    vol = defaultdict(dict)
    scan = defaultdict(dict)
    for r in rows:
        v, e = _f(r.get("m_eff")), _f(r.get("m_eff_err"))
        # DERIVED: a validity test, not a cut. NaN fails its own equality; a nonpositive value
        # or error is not a measurement at all. No quantity is being thresholded here.
        if v != v or e != e or v <= 0 or e <= 0:
            continue
        key = (r["operator"], r["nsmear"], int(r["tau"]))
        beta, L = round(_f(r["beta"]), 2), int(r["L"])
        # DERIVED: float identity for a table key, not a tolerance -- beta is written to two
        # decimals in both artifacts, so any epsilon far below that spacing selects the same rows.
        if abs(beta - VOL_BETA) < 1e-9:
            vol[key][L] = (v, e)
        if L == SCAN_L:
            scan[key][beta] = (v, e)
    return vol, scan


def _require_uniform_statistics(rows):
    """REFUSE if the configuration count varies across the volumes being compared.

    This is the confound that has produced a false result in this program twice. The lag moment and
    the effective mass are both inflated by noise, so fewer configurations at larger `L` manufactures
    a volume TREND out of nothing: a recomputation at 64/64/64/32/32 configurations gave a slope of
    `+0.354` where the uniform-statistics answer is `+0.094`, and a synthetic white-noise field --
    maximally gapped, zero correlation length -- read a slope of `+0.79` at low statistics,
    indistinguishable from a massless field.

    A volume comparison whose statistics vary with the volume is not a measurement of volume
    dependence. The correlator artifact happens to carry 256 configurations at every volume, so this
    check passes today; it is written because nothing else would notice if that changed.
    """
    counts = {}
    for r in rows:
        key = (r["operator"], r["nsmear"], int(r["tau"]), round(_f(r["beta"]), 2))
        n = r.get("ncfg")
        if n in (None, ""):
            return                      # the artifact does not record it; nothing to check
        counts.setdefault(key, set()).add(int(n))
    by_beta = {}
    for (op, ns, tau, beta), ns_set in counts.items():
        by_beta.setdefault(beta, set()).update(ns_set)
    # DERIVED: more than ONE distinct configuration count at a coupling is, by definition, a
    # count that varies across the volumes being compared. Not a tolerance -- the comparison
    # is either at uniform statistics or it is not.
    bad = {b: v for b, v in by_beta.items() if len(v) > 1}
    if bad:
        raise SystemExit(
            "fixed_selection_of_scaling: the configuration count VARIES across the volumes being "
            "compared (%s). Noise inflates both the lag moment and the effective mass, so a varying "
            "count manufactures a volume trend; this comparison cannot distinguish that from "
            "physics and refuses rather than reporting a slope it cannot support."
            % "; ".join("beta=%.2f: %s" % (b, sorted(v)) for b, v in sorted(bad.items())))


def main() -> int:
    gap = _rows("8_7_dat_gap_correlator.csv")
    _require_uniform_statistics(gap)
    sig = {round(_f(r["beta"]), 2): _f(r["sqrt_sigma"])
           for r in _rows("8_8_dat_string_tension.csv") if int(r["L"]) == SCAN_L}
    vol, scan = series(gap)

    out = []
    print(f"VOLUME-INDEPENDENCE at beta={VOL_BETA} (gapped => flat; corrections ~ e^-14 past L=12)")
    print(f"{'operator':<15}{'ns':<5}{'tau':<5}{'volumes':<26}{'const':>9}{'chi2/dof':>10}")
    for k in sorted(vol):
        d = vol[k]
        Ls = sorted(d)
        if len(Ls) < MIN_PTS:
            continue
        c, chi = _chi2_const([d[L][0] for L in Ls], [d[L][1] for L in Ls])
        print(f"{k[0][:14]:<15}{k[1]:<5}{k[2]:<5}"
              f"{' '.join('%d:%.2f' % (L, d[L][0]) for L in Ls):<26}{c:>9.3f}{chi:>10.2f}")
        out.append(dict(test="volume", operator=k[0], nsmear=k[1], tau=k[2],
                        points="|".join(str(L) for L in Ls),
                        fit_const="%.4f" % c, chi2_const="%.3f" % chi,
                        fit_alt="", chi2_alt=""))

    print()
    print(f"CONTINUUM SCALING at L={SCAN_L} (physical => Delta/sqrt(sigma) constant;")
    print("                                cutoff  => a*Delta constant, ratio ~ 1/(a sqrt sigma))")
    print(f"{'operator':<15}{'ns':<5}{'tau':<5}{'Delta/sqrt(sigma)':<24}{'chi2 phys':>10}{'chi2 cut':>10}{'prefers':>9}")
    for k in sorted(scan):
        d = scan[k]
        bs = sorted(b for b in d if b in sig)
        if len(bs) < MIN_PTS:
            continue
        r = [d[b][0] / sig[b] for b in bs]
        er = [d[b][1] / sig[b] for b in bs]
        _, chi_p = _chi2_const(r, er)
        _, chi_c = _chi2_prop(r, er, [1.0 / sig[b] for b in bs])
        pref = "physical" if chi_p < chi_c else "cutoff"
        print(f"{k[0][:14]:<15}{k[1]:<5}{k[2]:<5}"
              f"{' '.join('%.2f' % x for x in r):<24}{chi_p:>10.2f}{chi_c:>10.2f}{pref:>9}")
        out.append(dict(test="scaling", operator=k[0], nsmear=k[1], tau=k[2],
                        points="|".join("%.2f" % b for b in bs),
                        fit_const="%.4f" % (sum(r) / len(r)), chi2_const="%.3f" % chi_p,
                        fit_alt="", chi2_alt="%.3f" % chi_c))

    # ---- continuum scaling at FIXED PHYSICAL VOLUME ----------------------------------------
    # The 1/L_phys cap on what the tension can certify is a finite-VOLUME limit, not a
    # finite-spacing one: `Delta_phys >= C/(L a) = C/L_phys` carries no `a`. So the continuum
    # direction is the one that cap leaves open, and it is testable here -- but only at MATCHED
    # physical volume, otherwise the comparison mixes a change of spacing with a change of box.
    #
    # At fixed `L*a`, a PHYSICAL mass has `a*m` falling with the spacing (ratio `a'/a`), while a
    # cutoff artifact holds `a*m` fixed (ratio 1). Held at fixed (operator, smearing, tau), so no
    # minimum is taken and no tolerance enters -- the same discipline as the two tests above.
    pairs = [((12, 2.30), (16, 2.40)), ((8, 2.30), (16, 2.50))]
    bypair = defaultdict(dict)
    for r in gap:
        v, e = _f(r.get("m_eff")), _f(r.get("m_eff_err"))
        # DERIVED: validity, not a cut -- NaN fails its own equality and a nonpositive
        # value or error is not a measurement. Nothing is thresholded.
        if v != v or e != e or v <= 0 or e <= 0:
            continue
        bypair[(r["operator"], r["nsmear"], int(r["tau"]))][(int(r["L"]), round(_f(r["beta"]), 2))] = (v, e)
    print()
    print("CONTINUUM SCALING AT MATCHED PHYSICAL VOLUME (physical => ratio a'/a; cutoff => 1)")
    for A, B in pairs:
        if A[1] not in sig or B[1] not in sig:
            continue
        va, vb = A[0] * sig[A[1]], B[0] * sig[B[1]]
        pred = sig[B[1]] / sig[A[1]]
        print(f"  L={A[0]} b={A[1]:.2f}  vs  L={B[0]} b={B[1]:.2f}   "
              f"L*a*sqrt(sigma) {va:.3f} vs {vb:.3f} ({100*abs(va-vb)/va:.1f}% matched), "
              f"physical predicts {pred:.3f}")
        print(f"    {'operator':<15}{'ns':<5}{'tau':<5}{'ratio':>16}{'prefers':>10}")
        for k in sorted(bypair):
            d = bypair[k]
            if A not in d or B not in d:
                continue
            (x, ex), (y, ey) = d[A], d[B]
            ratio = y / x
            err = ratio * ((ex / x) ** 2 + (ey / y) ** 2) ** 0.5
            pref = "physical" if abs(ratio - pred) < abs(ratio - 1.0) else "cutoff"
            print(f"    {k[0][:14]:<15}{k[1]:<5}{k[2]:<5}{ratio:>10.3f}+/-{err:<5.3f}{pref:>10}")
            out.append(dict(test="matched_volume", operator=k[0], nsmear=k[1], tau=k[2],
                            points=f"{A[0]}@{A[1]:.2f}|{B[0]}@{B[1]:.2f}",
                            fit_const="%.4f" % ratio, chi2_const="%.4f" % err,
                            fit_alt="%.4f" % pred, chi2_alt=pref))

    # ---- the exclusion, stated without any rule at all -------------------------------------
    # `m_eff(tau) >= Delta` holds for EVERY operator and lag (reflection positivity: the correlator
    # is a positive-weight sum of exponentials, so its effective mass is monotone and never dips
    # below the gap). So `min_i (v_i + z e_i)` is an upper bound on Delta at EVERY z >= 0 -- larger
    # z is simply more conservative about how far a noisy entry may have fluctuated down. No
    # admissibility filter is needed, because a noise-dominated entry has a large error and loses
    # on its own.
    #
    # That turns Sec 8.7b's exclusion into a rule-free quantity: the largest z for which the
    # published Sec 8.6 value still exceeds the bound. It measures how much conservatism the
    # exclusion survives, which is more informative than a sigma at one chosen tolerance -- and it
    # is immune to the three-way disagreement over that tolerance.
    pub = {}
    try:
        for r in _rows("8_7_dat_mhi_multicoupling.csv"):
            if int(r["L"]) == SCAN_L:
                pub[round(_f(r["beta"]), 2)] = (_f(r["Delta"]), _f(r["Delta_err"]))
    except (OSError, KeyError, ValueError):
        pub = {}

    if pub:
        print()
        print("RULE-FREE EXCLUSION of the published Sec 8.6 read (no tolerance, no filter):")
        print(f"{'beta':<8}{'published':<22}{'bound z=0':<12}{'excluded for all z <':>22}")
        for beta in sorted(pub):
            cand = [(d[beta][0], d[beta][1]) for d in scan.values() if beta in d]
            if len(cand) < MIN_PTS:
                continue
            pv, pe = pub[beta]
            # DERIVED, in closed form -- no scan and no scan parameters. `min_i (v_i + z e_i) >= pv`
            # holds exactly when EVERY candidate satisfies `v_i + z e_i >= pv`, i.e. when
            # `z >= (pv - v_i)/e_i` for every i. So the critical z is the largest of those ratios,
            # and the exclusion holds for every z strictly below it. Searching for it would have
            # introduced a ceiling and a step; solving it introduces neither.
            zc = max((pv - v) / e for v, e in cand)
            at0 = min(v for v, _ in cand)
            shown = f"{zc:.2f}"
            print(f"{beta:<8.2f}{pv:.4f} +/- {pe:.4f}      {at0:<12.4f}{shown:>22}")
            out.append(dict(test="exclusion", operator="published_8_6", nsmear="", tau=0,
                            points="%.2f" % beta, fit_const="%.4f" % pv,
                            chi2_const="", fit_alt="%.4f" % at0,
                            chi2_alt=(shown if zc is None else "%.2f" % zc)))

    if not out:
        raise SystemExit("fixed_selection_of_scaling: no series had enough points; refusing to "
                         "write an empty artifact.")
    path = os.path.join(DATA, "9_8_dat_fixed_selection.csv")
    with open(path, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["test", "operator", "nsmear", "tau", "points",
                                           "fit_const", "chi2_const", "fit_alt", "chi2_alt"])
        w.writeheader()
        w.writerows(out)
    print(f"\nwrote {os.path.basename(path)} ({len(out)} series)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
