"""REFUTATION PROBE for ApertureRoute.ConfinesAtAnAperture.

WHAT THIS CAN AND CANNOT DO. It can REFUTE. It cannot support. If the measured cosine average
falls at or below the floor at any coupling, the hypothesis is false at that aperture and we stop
walking that route. If it never does, NOTHING is established -- the data failed to refute, the
Lean obligation is untouched, and no number from here may enter a proof or be fitted to.

## The hypothesis, and why it is one measurable ratio

`MassGap/ApertureRoute.lean`:

    ConfinesAtAnAperture := exists a : EvenAp, forall beta, 3^(-1/4) < cosAvgEven a beta
    cosAvgEven a beta   := sum_d (readEven a beta).p d * cos ((readEven a beta).theta d)

`readEven` is `readA` applied to `wilsonCorrAt a.1 (max beta 0)`, so `p d = rho(d) / sum rho` and
`theta d = 2*pi*circLag(d)/(N+1)` with `circLag d = min d (N+1-d)`. Hence, with `T = N+1` the
temporal extent and `rho(d)` the connected lag correlation of the plaquette,

    cosAvgEven = sum_d rho(d) cos(2 pi d / T) / sum_d rho(d)

-- the cosine is even, so `circLag` and `d` give the same value and the wrap is automatic. That is
exactly `rhohat(1)/rhohat(0)`, the ratio of the first Matsubara mode of the plaquette power
spectrum to the zero mode. The floor is `3^(-1/4) = 0.7598357`, `exp(-kappa_0)` with
`kappa_0 = (1/4) log 3`.

## What rho is here

`wilsonCorrAt` is the connected correlation of the Wilson plaquette density at temporal lag d. We
form the timeslice-averaged plaquette `phi(t)` per configuration from the stored 4-d plaquette
field, and take

    rho(d) = < phi(t) phi(t+d) > - <phi>^2

averaged over every t (periodic) and every configuration. No fitting anywhere: rho is a sample mean
and cosAvg is a ratio of sample means. The uncertainty is estimated by BOOTSTRAP OVER
CONFIGURATIONS -- the reproducibility direction -- not from a within-sample formula.

## The read's own admissibility condition

`readA` takes a proof of `(forall d, 0 <= rho d) and 0 < sum rho`. A measured rho that goes
negative at some lag is NOT an instance of the object the Lean statement is about, so the probe
reports nonnegativity per point and never silently clips. A point with a negative lag is reported
as INADMISSIBLE, which is a statement about the sample, not about the hypothesis.

## Which part is the library's

`rho(d)` is: it is the library's periodic lag profile, `entroptics_adapter.decay(phi.T,
periodic=True, disconnected=<grand mean>)`, the same read `lattice_generator.connected_correlator`
takes. What stays here is `cosAvgEven` itself, a FIXED FUNCTIONAL written down in Lean: the distance
is the lattice lag, the normalisation is `sum_d rho(d)` (that is `readA`'s `p`), the window is the
whole period `T`, and there is no floor in it at all. Evaluating a named Lean definition on a
library-read profile leaves no method up for choice.
"""
import io
import json
import os
import sys

# CHOSEN: two threads. The workstation is shared with other live sessions and numpy has taken 18 of
# 22 cores here before; nothing in this file is compute-bound.
os.environ.setdefault("OMP_NUM_THREADS", "2")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "2")
os.environ.setdefault("MKL_NUM_THREADS", "2")

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import store_path                                        # noqa: E402  (needs the path above first)
import entroptics_adapter as W                           # noqa: E402  THE WRAPPER: the lag read

COLLECTION = "configs_paper83"
#: DERIVED: the entropy floor itself, `exp(-kappa_0)` with `kappa_0 = (1/4) log 3` -- the constant
#: `ApertureRoute.ConfinesAtAnAperture` compares against, assembled in Lean by
#: `VortexCount.kappa0_is_the_surface_entropy_density` from a directed-path count and a cube area.
FLOOR = 3.0 ** (-0.25)
#: CHOSEN: bootstrap resamples. The uncertainty is estimated by resampling CONFIGURATIONS -- the
#: reproducibility direction -- rather than from a within-sample formula. More would narrow the
#: reported interval and change no verdict below, since every interval is wide by a factor.
BOOT = 400
#: CHOSEN: a fixed seed, so the reported intervals are reproducible run to run.
RNG = np.random.default_rng(20260919)


def lag_correlation(phi):
    """rho(d) for d = 0..T-1 from phi of shape (n_cfg, T), connected and periodic.

    The mean subtracted is the GRAND mean over configurations and timeslices: phi(t) has no
    preferred origin on a periodic lattice, so a per-configuration mean would remove the zero mode
    the denominator of cosAvg is built from.

    The profile is the library's. `phi.T` because `decay` reads its FIRST axis as the ordered one,
    so the configurations are its exchangeable channels; `periodic=True` because the lattice IS
    periodic in t, so the wanted object is the CIRCULAR autocorrelation; `disconnected=` the grand
    mean, for the reason above; and `/ n` because `decay` SUMS its channels, where rho is their mean.
    """
    phi = np.asarray(phi, dtype=np.float64)
    n = int(phi.shape[0])
    prof = np.asarray(W.decay(phi.T, periodic=True, disconnected=float(phi.mean())))
    return prof / n


def cos_avg(rho):
    T = len(rho)
    d = np.arange(T)
    num = float((rho * np.cos(2.0 * np.pi * d / T)).sum())
    den = float(rho.sum())
    # DERIVED: `readA` consumes a proof of `0 < sum rho`, so a nonpositive total mass is not a
    # read at all and has no cosine average to report. Not a cut.
    return num / den if den > 0 else float("nan")


def timeslice_plaquette(path):
    """phi(t) per configuration: the stored field is (n_cfg, Lx, Ly, Lz, T)."""
    a = np.load(path, mmap_mode="r")
    # DERIVED: the stored plaquette field is (n_cfg, Lx, Ly, Lz, T) -- one configuration axis
    # and the four lattice directions. Counted from the manifest's own `shape` column.
    assert a.ndim == 5, "unexpected shape %r in %s" % (a.shape, path)
    return np.asarray(a, dtype=np.float64).mean(axis=(1, 2, 3))


def self_test():
    """Prove the probe DISCRIMINATES before it is allowed to report on real data.

    Two inputs with analytically known answers, at opposite ends of the verdict:

      * white noise in t  -- rho(d) = sigma^2 delta_{d0}, so cosAvg = 1 exactly. CLEARS the floor.
      * constant in t     -- rho(d) = sigma^2 for every d, so the numerator is
                             sigma^2 sum_d cos(2 pi d/T) = 0 and cosAvg = 0. REFUTES the floor.

    If only the clearing case were checked, a probe that returned 1 unconditionally would pass. The
    constant case is the one that can fail, so it is the one that matters.
    """
    rng = np.random.default_rng(11)
    T, n = 16, 4000

    white = rng.standard_normal((n, T))
    got = cos_avg(lag_correlation(white))
    # CHOSEN: a loose tolerance -- white noise at finite sample size does not give exactly 1,
    # and the assertion that carries weight is the next line, against the floor.
    assert abs(got - 1.0) < 0.05, "white noise should give cosAvg = 1, got %.4f" % got
    assert got > FLOOR, "white noise must CLEAR the floor"

    const = np.repeat(rng.standard_normal((n, 1)), T, axis=1)
    got_c = cos_avg(lag_correlation(const))
    # CHOSEN: floating-point zero. The t-constant answer is EXACTLY zero analytically, so this
    # is a representation tolerance and not a threshold on anything measured.
    assert abs(got_c) < 1e-9, "t-constant should give cosAvg = 0, got %.3e" % got_c
    assert got_c <= FLOOR, "t-constant must REFUTE the floor -- the probe cannot detect failure"

    # And a genuine intermediate: an exact circulant cosine profile, whose answer is exact.
    # rho(d) = 1 + r cos(2 pi d / T) has rhohat(1)/rhohat(0) = (r T / 2) / T = r/2.
    d = np.arange(T)
    for r in (0.5, 1.0, 1.9):
        rho = 1.0 + r * np.cos(2.0 * np.pi * d / T)
        # CHOSEN: floating-point zero again; the circulant identity is exact.
        assert abs(cos_avg(rho) - r / 2.0) < 1e-12, "cos_avg is not rhohat(1)/rhohat(0)"

    print("self-test: white noise cosAvg=%.4f (clears), t-constant cosAvg=%.2e (refutes), "
          "circulant exact\n" % (got, got_c))


def main():
    import csv
    self_test()
    store = store_path.store_root()
    rows = [r for r in csv.DictReader(
        io.open(os.path.join(store, "manifest.csv"), encoding="utf-8"))
            if r["collection"] == COLLECTION]
    assert rows, "collection not in the manifest"

    out = []
    for r in sorted(rows, key=lambda r: (r["group"], float(r["beta"]))):
        path = os.path.join(store, COLLECTION, r["filename"])
        if not os.path.exists(path):
            print("MISSING %s" % r["filename"])
            continue
        phi = timeslice_plaquette(path)
        n, T = phi.shape
        rho = lag_correlation(phi)
        val = cos_avg(rho)

        boot = W.bootstrap(phi, lambda s: cos_avg(lag_correlation(s)), draws=BOOT, rng=RNG)
        lo, hi = np.percentile(boot, [2.5, 97.5])

        # DERIVED: `readA` consumes `forall d, 0 <= rho d`; a negative lag makes the sample not
        # an instance of `readEven`. The true object is PROVED nonnegative
        # (`wilson_reflection_positive_at_even`), so a negative here is sampling noise.
        neg = int((rho < 0).sum())
        rec = dict(group=r["group"], L=int(r["L"]), T=T, beta=float(r["beta"]), n_cfg=n,
                   cos_avg=val, boot_lo=float(lo), boot_hi=float(hi),
                   # DERIVED (both): `readA`'s two admissibility clauses, verbatim.
                   negative_lags=neg, admissible=bool(neg == 0 and rho.sum() > 0),
                   # DERIVED: the contact value is positive on any admissible read, so a
                   # nonpositive one has no ratio to report. `readA`'s clause again.
                   rho2_over_rho0=float(rho[2] / rho[0]) if rho[0] > 0 else float("nan"))
        out.append(rec)
        verdict = "REFUTES" if hi < FLOOR else ("clears" if lo > FLOOR else "straddles")
        print("%-4s L%-2d T%-2d beta=%-5g n=%-4d cosAvg=%8.5f  [%8.5f,%8.5f]  neg_lags=%-2d %-9s %s"
              % (rec["group"], rec["L"], T, rec["beta"], n, val, lo, hi, neg,
                 "ADMISSIBLE" if rec["admissible"] else "INADMISS.", verdict))

    print("\nfloor 3^(-1/4) = %.7f" % FLOOR)
    ref = [r for r in out if r["admissible"] and r["boot_hi"] < FLOOR]
    if ref:
        print("REFUTED at %d admissible point(s):" % len(ref))
        for r in ref:
            print("  %s T=%d beta=%g : cosAvg=%.5f, 95%% upper %.5f < %.7f"
                  % (r["group"], r["T"], r["beta"], r["cos_avg"], r["boot_hi"], FLOOR))
        print("\nThat refutes confinement AT THESE APERTURES ONLY (T as measured). It does not")
        print("refute ConfinesAtAnAperture, which asks for SOME even extent -- but it does show the")
        print("extent cannot be chosen independently of the coupling if the trend continues.")
    else:
        print("NOT REFUTED at any admissible point. Nothing is thereby established.")

    dst = os.path.join(os.path.dirname(os.path.abspath(__file__)), "confines_refutation_probe.json")
    io.open(dst, "w", encoding="utf-8").write(json.dumps(
        dict(floor=FLOOR, collection=COLLECTION, bootstrap=BOOT, points=out), indent=2) + "\n")
    print("\nwrote %s" % dst)


if __name__ == "__main__":
    sys.exit(main())
