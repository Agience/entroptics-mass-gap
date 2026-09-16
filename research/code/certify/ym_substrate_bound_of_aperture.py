"""The one open hypothesis, measured: is the circle moment bounded INDEPENDENTLY OF APERTURE?

WHAT IS OPEN. Every theorem in the chain is proved. `ym_mass_gap_of_substrate` takes exactly one
input that is not:

    exists B, forall N beta.  d2At N beta <= B

-- the lag second moment ON THE CIRCLE, bounded uniformly over apertures. No number is supplied for
B anywhere; the hypothesis is that one EXISTS. Nothing had ever measured it, for a plain reason:
until the read was corrected to the circle distance, the measured quantity was not `d2At`, and the
raw-index quantity it did measure is bounded by NO B at all.

WHAT THIS MEASURES. The same functional at every aperture the store holds for one coupling, and the
three quantities that separate the hypothesis from its alternatives:

  1. `d2 circle`  -- the theorem's quantity. The hypothesis predicts it SATURATES with L.
  2. `d2 raw`     -- the retired quantity, the raw index over the FULL extent. This should GROW
                     without bound, roughly like L^2. That claim has been argued from a synthetic
                     exponential profile; here it is measured on the physical ensemble.
  3. `mu`         -- the tension. The aperture factorisation <theta^2> = (2pi/(N+1))^2 <d^2>
                     (`Moment.Read.thetaMoment_eq`) predicts that a saturating moment makes mu fall
                     like 1/L^2. That is `tension_tendsto_zero_of_bounded_circ_moment` in the data.

The three are not independent readings of one fact. (1) is the hypothesis, (2) is the reason the
hypothesis had to be restated before it could be true, and (3) is the consequence the gap uses. A
substrate that satisfies (1) must show (3) at the measured rate, so (3) is a falsifiable prediction
rather than a restatement.

DERIVED THROUGHOUT. The apertures are whatever the store holds -- no volume is selected, and the
scan reports every one it finds. The half-extent of each read comes from that ensemble's own spatial
axis. The 1/L^2 reference curve is anchored at the SMALLEST aperture measured, so it is a prediction
for the larger ones rather than a fit through them. No threshold, no window, no fitted scale.
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
BASE = store_path.store_root(required=False)


def volumes(group, beta):
    """Every aperture the store holds for this group and coupling, with its shards."""
    out = {}
    if not BASE:
        return out
    for d in sorted(os.listdir(BASE)):
        p = os.path.join(BASE, d)
        # The raw-link collection carries the SAME filenames at rank 7 -- (n,L,L,L,T,dir,group)
        # rather than the rank-5 density plane this reads. Concatenating those would read a
        # different data product without saying so, which is what `aperture_reads.load_su2`
        # refuses by rank; excluded here by collection so the refusal is never reached.
        if not os.path.isdir(p) or "links" in d:
            continue
        for f in glob.glob(f"{p}/{group}_L*_b{beta:.2f}.s*.npy"):
            m = re.match(rf"{group}_L(\d+)_b", os.path.basename(f))
            if m:
                out.setdefault(int(m.group(1)), []).append(f)
    return out


def d2_raw(P):
    """The RETIRED read: the RAW lag index over the FULL periodic extent.

        sum_{d=0}^{L-1} rho(d) d^2 / sum_{d=0}^{L-1} rho(d),   rho(d) = rho(min(d, L-d))

    OVER THE FULL EXTENT, not the half-window, and that distinction is the whole point. On the half
    window the raw index and the circle distance AGREE -- min(d, L-d) = d for d <= L/2 -- so a
    half-window version of this shows nothing and cannot support any claim about the raw index. The
    difference lives entirely in the far half, where a periodic correlation has rho(L-1) = rho(1),
    which is LARGE, and the raw index weights it by (L-1)^2.

    That is why the hypothesis had to be restated before it could be true: `exists B, forall N` is
    unsatisfiable for this quantity by any correlation, gapped or not. Computed here and nowhere
    else, to measure that on the physical ensemble rather than argue it from a synthetic profile.
    It feeds no certificate.
    """
    rho = P.mean(0)
    rho = rho / rho[0]
    p = np.clip(rho, 0, None)
    m = len(p) - 1
    L = 2 * m
    full = np.array([p[min(d, L - d)] for d in range(L)])
    s = full.sum()
    # DERIVED: a division guard, as in `d2_from_profiles`; zero total weight has no moment.
    return float(sum(full[d] * d * d for d in range(L)) / s) if s > 0 else 0.0


# CHOSEN: `ncap` caps configurations per aperture. It costs read time, not validity -- the moment
# is an ensemble average, and the bootstrap sigma reported beside it widens when the cap binds, so a
# cap set too low surfaces as a wider error bar rather than as a wrong number.
def scan(group, beta, ncap=256):
    rows = []
    for L, files in sorted(volumes(group, beta).items()):
        arr = np.asarray(np.concatenate([np.load(f) for f in sorted(files)], 0)[:ncap],
                         dtype=np.float64)
        # DERIVED: two is where a sample variance exists at all, so it is the arity of the
        # bootstrap below rather than a quality bar on the ensemble.
        if arr.shape[0] < 2:
            continue
        P = CG.per_config_profiles(arr)
        c = COS.cos_avg(P)
        n = arr.shape[0]
        # The reproducibility of the moment at THIS aperture, resampled over configurations. Without
        # it "growth 1.08x" and "growth 25x" are both uninterpretable -- a ratio of two numbers with
        # no scale attached. The spread across apertures is only evidence against the hypothesis if
        # it is larger than the spread within one.
        rng = np.random.default_rng(0)
        boot = np.array([CG.d2_from_profiles(P[rng.integers(0, n, n)]) for _ in range(200)])
        rows.append({
            "L": L, "n": n,
            "d2_circle": CG.d2_from_profiles(P),
            "d2_sigma": float(boot.std()),
            "d2_raw": d2_raw(P),
            # DERIVED: the domain of the logarithm, as in `ym_confinement_of_cos_average`.
            "mu": -math.log(c) if c > 0 else math.inf,
            "cos_avg": c,
            # the tightest confidence the companion certificate reports
            "mu_upper_1e-30": COS.mu_upper(P, 1e-30),
        })
    return rows


def report(group, beta, rows):
    # DERIVED: two is the arity of a comparison. One aperture cannot say whether a quantity
    # depends on the aperture, which is the only question here.
    if len(rows) < 2:
        print(f"{group} beta={beta:.2f}: only {len(rows)} aperture(s) -- no scan possible")
        return None
    print(f"\n=== {group.upper()} beta={beta:.2f} : {len(rows)} apertures ===")
    print(f"{'L':>4} {'n':>5} {'d2 circle':>19} {'d2 raw':>10} {'mu':>10} "
          f"{'mu*L^2':>9} {'signal':>7} {'confined':>9}")
    L0, mu0 = rows[0]["L"], rows[0]["mu"]
    for r in rows:
        conf = "yes" if r["mu_upper_1e-30"] < KAPPA0 else "NO"
        # DERIVED: a sign test, not a cut. mu <= 0 means <cos theta> >= 1, which no correlation with
        # a tension can produce -- the read is on noise and its moment is a ratio of two quantities
        # consistent with zero. Rows like that carry no information about the substrate either way.
        sig = "yes" if r["mu"] > 0 else "NOISE"
        print(f"{r['L']:>4} {r['n']:>5} {r['d2_circle']:>10.4f} +/-{r['d2_sigma']:<6.4f} "
              f"{r['d2_raw']:>10.4f} {r['mu']:>10.5f} {r['mu'] * r['L'] ** 2:>9.3f} "
              f"{sig:>7} {conf:>9}")

    # DERIVED: the same sign test as the per-row `signal` column -- zero tension, not a cut.
    sigrows = [r for r in rows if r["mu"] > 0]
    circ = [r["d2_circle"] for r in rows]
    raw = [r["d2_raw"] for r in rows]
    span = rows[-1]["L"] / rows[0]["L"]
    print(f"  aperture spans {rows[0]['L']} -> {rows[-1]['L']} ({span:.1f}x)")
    print(f"  d2 CIRCLE  {min(circ):.4f} -> {max(circ):.4f}   growth {max(circ) / min(circ):.2f}x"
          f"   (bounded hypothesis predicts ~1x)")
    print(f"  d2 RAW     {min(raw):.4f} -> {max(raw):.4f}   growth {max(raw) / min(raw):.2f}x"
          f"   (L^2 would be {span ** 2:.1f}x)")

    # Is the variation across apertures larger than the variation within one? Compared against the
    # constant each aperture would share if the moment were aperture-independent -- the
    # inverse-variance weighted mean, which is that constant's least-squares value. Rows with no
    # signal are excluded by the sign test above, not by a cut on their value.
    # DERIVED: two is the arity of the comparison, as above; the sigma sign test is the domain of
    # the inverse-variance weight, which does not exist for a point with no reproducibility.
    if len(sigrows) >= 2 and all(r["d2_sigma"] > 0 for r in sigrows):
        w = np.array([1.0 / r["d2_sigma"] ** 2 for r in sigrows])
        v = np.array([r["d2_circle"] for r in sigrows])
        Bhat = float((w * v).sum() / w.sum())
        chi2 = float((w * (v - Bhat) ** 2).sum())
        dof = len(sigrows) - 1
        print(f"  aperture-independent B would be {Bhat:.4f}; chi2/dof = {chi2 / dof:.2f} "
              f"over {len(sigrows)} apertures with signal"
              f"   (1 means the spread across apertures is its own reproducibility)")
        if len(sigrows) < len(rows):
            # DERIVED: the same zero-tension sign test as the `signal` column.
            drop = [r["L"] for r in rows if r["mu"] <= 0]
            print(f"    excluded as noise (mu <= 0, no tension to read): L={drop}")
        for r in rows:
            r["chi2_dof"] = chi2 / dof
            r["B_hat"] = Bhat
            r["n_apertures"] = len(sigrows)
    # 1/L^2 anchored at the SMALLEST aperture: a prediction for the rest, not a fit through them.
    # DERIVED: the 1/L^2 curve is anchored at this aperture, so it exists only where there is a
    # tension to anchor it to. Zero, again, not a cut.
    if mu0 > 0:
        print(f"  mu vs the 1/L^2 prediction anchored at L={L0}:")
        for r in rows[1:]:
            pred = mu0 * (L0 / r["L"]) ** 2
            print(f"    L={r['L']:>3}  predicted {pred:.5f}   measured {r['mu']:.5f}"
                  f"   ratio {r['mu'] / pred:.2f}")
    return rows


def main() -> None:
    if not BASE:
        raise SystemExit("ym_substrate_bound_of_aperture: no ensemble store configured.\n"
                         + store_path.hint())

    # DERIVED: every (group, coupling) the store holds at more than one aperture. Nothing is
    # selected -- the scan reports whatever is there, so it cannot be read as a chosen best case.
    targets = []
    for group in ("su2", "su3"):
        betas = set()
        for d in sorted(os.listdir(BASE)):
            p = os.path.join(BASE, d)
            if os.path.isdir(p):
                for f in glob.glob(f"{p}/{group}_L*_b*.s*.npy"):
                    m = re.search(r"_b([\d.]+)\.s", os.path.basename(f))
                    if m:
                        betas.add(float(m.group(1)))
        for b in sorted(betas):
            # DERIVED: one is the arity below which "does it depend on the aperture" has no meaning.
            if len(volumes(group, b)) > 1:
                targets.append((group, b))
    if not targets:
        raise SystemExit("ym_substrate_bound_of_aperture: no coupling is present at more than one "
                         "aperture, so the substrate hypothesis cannot be tested. Refusing to "
                         "report a scan with nothing behind it.")

    print(f"The open hypothesis: exists B, forall N beta.  d2At N beta <= B   (kappa0 = {KAPPA0:.6f})")
    print(f"{len(targets)} coupling(s) available at more than one aperture.")

    allrows = []
    for group, b in targets:
        rows = scan(group, b)
        if report(group, b, rows):
            for r in rows:
                allrows.append(dict(r, group=group, beta=b))

    out = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                       "data", "9_3_dat_substrate_of_aperture.csv")
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["group", "beta", "L", "nconfigs", "d2_circle", "d2_sigma", "d2_raw", "cos_avg", "mu",
                    "mu_upper_delta_1e-30", "confined_1e-30", "kappa0"])
        for r in allrows:
            w.writerow([r["group"], f"{r['beta']:.2f}", r["L"], r["n"], f"{r['d2_circle']:.5f}", f"{r['d2_sigma']:.5f}",
                        f"{r['d2_raw']:.5f}", f"{r['cos_avg']:.6f}", f"{r['mu']:.6f}",
                        f"{r['mu_upper_1e-30']:.6f}",
                        "yes" if r["mu_upper_1e-30"] < KAPPA0 else "NO", f"{KAPPA0:.6f}"])
    # ---- the hypothesis, over everything measured ----
    scored = sorted((r["chi2_dof"], r["group"], r["beta"], r["n_apertures"], r["B_hat"])
                    for r in {(r["group"], r["beta"]): r for r in allrows
                              if "chi2_dof" in r}.values())
    # DERIVED: the same zero-tension sign test as the `signal` column.
    sig = [r for r in allrows if r["mu"] > 0]
    print("\n" + "=" * 78)
    print("THE HYPOTHESIS:  exists B, forall N beta.  d2At N beta <= B")
    print("=" * 78)
    if scored:
        # The distribution is printed in full rather than reduced to a count against a cut: a
        # chi2/dof near 1 IS the statement that the across-aperture spread is the within-aperture
        # reproducibility, and naming every value leaves the outliers visible instead of binned.
        print(f"  chi2/dof of the circle moment against a CONSTANT B, {len(scored)} testable couplings:")
        for c, g, b, na, B in scored:
            print(f"    {g} beta={b:<5.2f}  chi2/dof = {c:>5.2f}   over {na} apertures   B_hat = {B:.4f}")
    if sig:
        Bmax = max(r["d2_circle"] for r in sig)
        at = [r for r in sig if r["d2_circle"] == Bmax][0]
        print(f"\n  largest circle moment anywhere with signal: {Bmax:.4f} "
              f"({at['group']} beta={at['beta']:.2f} L={at['L']})")
        print(f"  apertures measured: L = {sorted({r['L'] for r in sig})}")
        # The ceiling grows like L^2 while the moment does not, so the aperture condition gets
        # EASIER at larger N -- which is the structure `confinement_of_substrate_bound` uses.
        rhs = 1.0 - 3.0 ** -0.25
        for L in sorted({min(r["L"] for r in sig), max(r["L"] for r in sig)}):
            ceil = rhs * 2 * L ** 2 / (2 * math.pi) ** 2
            print(f"    at L={L:>3} the derived ceiling is {ceil:>7.3f} -- {ceil / Bmax:.1f}x that moment")

    # ---- the WEAKER hypothesis the proof actually takes ----
    #
    # `Complete.confinement_of_growth_bound` does not ask for a bounded moment. It asks for
    #
    #     d2At N b <= c * (N+1)^2     with     (2 pi)^2 c / 2 < 1 - 3^{-1/4}
    #
    # because the aperture condition's own ceiling grows like (N+1)^2. So the quantity to report is
    # the coefficient the DATA requires, c = d2 / (N+1)^2, against the ceiling's.
    #
    # DERIVED: c_max is that inequality solved for c. The lag arity N+1 is the periodic extent L.
    if sig:
        c_max = (1.0 - 3.0 ** -0.25) * 2 / (2 * math.pi) ** 2
        print(f"\n  THE WEAKER CONDITION: d2At <= c(N+1)^2 with c < c_max = {c_max:.6f}")
        by_L = {}
        for r in sig:
            c = r["d2_circle"] / r["L"] ** 2
            by_L[r["L"]] = max(by_L.get(r["L"], 0.0), c)
        for L in sorted(by_L):
            print(f"    L={L:>3}  worst c = {by_L[L]:.6f}   margin {c_max / by_L[L]:>6.1f}x")
        # A single `c` must cover EVERY aperture, so the binding constraint is the largest c --
        # which, because a flat moment makes c fall like 1/L^2, is the SMALLEST window measured.
        # Stating the max rather than the last row is what keeps this a bound and not a trend line.
        worst = max(sig, key=lambda r: r["d2_circle"] / r["L"] ** 2)
        cw = worst["d2_circle"] / worst["L"] ** 2
        print(f"    one c covering every aperture measured: {cw:.6f} "
              f"({worst['group']} beta={worst['beta']:.2f} L={worst['L']}, the smallest window) "
              f"-- {c_max / cw:.1f}x under the ceiling")

        # THE APERTURE DIVIDES OUT. `c = d2At/(N+1)^2` is `Complete.substrateRatio`: a squared
        # separation over a squared box, both in lattice units, so the lattice cancels. Its square
        # root is the RMS SEPARATION as a fraction of the extent -- NOT the correlation length.
        # For an exponential profile rms = sqrt(2) xi, and that factor is shape dependent while
        # the RMS is not, so naming xi here would import an assumption the theorem does not make.
        #
        # And it is a fraction OF THE APERTURE: widen the box and more correlation is permitted.
        # So this is a RESOLUTION condition -- is the window wide compared to the correlation? --
        # not a spectral one, which is why a contact-scale channel satisfies it trivially.
        print(f"\n  AS A FRACTION OF THE APERTURE (sqrt of the above):")
        print(f"    the condition says the RMS SEPARATION stays under "
              f"{100 * math.sqrt(c_max):.1f}% of the extent (for an exponential profile that is "
              f"xi < {100 * math.sqrt(c_max / 2):.1f}%, but the sqrt(2) is shape dependent)")
        for L in sorted(by_L):
            print(f"    L={L:>3}  measured {100 * math.sqrt(by_L[L]):>5.1f}%")
        print(f"    binding: {100 * math.sqrt(cw):.1f}% of the extent, against "
              f"{100 * math.sqrt(c_max):.1f}% -- a resolution condition, stated without a lattice")

    print(f"\nwrote {os.path.relpath(out)}  ({len(allrows)} rows)")


if __name__ == "__main__":
    main()
