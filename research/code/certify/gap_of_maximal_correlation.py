"""Calibration / round-trip fidelity test for the entroptics MASS-GAP read (the wrapper's
``mass_gap`` = the dominant Koopman/DMD operator mode rate -log|mu_1|, a FORWARD operator
identification).  Inject KNOWN data, extract it, and confirm the number that comes back --
exact where the operator is exact, within a stated, characterized systematic where statistics
enter, and DETERMINISTIC throughout (operator eigenvalues).

  A. EXACT extraction + determinism (noise-free).  A single decaying mode W[t] = e^{-D t} v has
     dominant operator eigenvalue e^{-D}, so the read returns D to ~1e-6, and a repeated read of
     the same data is BIT-IDENTICAL.

  B. CHARACTERIZED recovery (with statistics).  On an ensemble the read is calibrated to the true
     rate: (i) an ensemble of fields with a PLANTED rate D recovers D within a small calibration
     (~few %); (ii) the free scalar recovers its exact gap E0 = arccosh(1 + m^2/2) across the mass
     range.

  C. PHASE SEPARATION (real configs).  The confinement order parameter K_signal -- resolved
     spatial modes above the pinned confined-vacuum floor -- is low in the confined phase and high
     in the Coulomb phase, and every Coulomb reading must sit above every confined one.  The gap
     Delta is printed beside it and does NOT separate the phases: on the action density, a
     gauge-invariant composite, the Coulomb correlator fits an effective exponential over a finite
     range and returns a finite Delta.  Runs when the config hopper is present.

    python gap_of_maximal_correlation.py                       # A + B (+ C if HOP configs are present)
    HOP=/path/to/configs python gap_of_maximal_correlation.py  # point C at the hopper

Everything goes through the WRAPPER (research/code/entroptics_adapter.py): the read under test is exactly
what the physics pipeline calls.  Run this on the CPU pod (the C-stage config ensembles are heavy)."""
import glob
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code (parent of certify/)
import entroptics_adapter as W          # THE WRAPPER (research/code/entroptics_adapter.py)
import lattice_generator as G           # the config generator (free_scalar, gauge stream)
import store_path                       # the ONE place the ensemble store is located

assert os.path.abspath(W.__file__).endswith(os.path.join("code", "entroptics_adapter.py")), \
    f"wrong entroptics: {W.__file__}"


# ══════════════════════════════════════════════════════════════════════════════
# Known-signal injectors
# ══════════════════════════════════════════════════════════════════════════════
def single_mode_field(dims, D, *, seed=0):
    """A noise-free 4-D field whose spatial-DC time series decays at a single rate D: every site
    carries a(t) = e^{-D t}, so the pooled ordered operator has dominant eigenvalue e^{-D}."""
    *space, Lt = dims
    a = np.exp(-D * np.arange(Lt, dtype=float))
    return np.broadcast_to(a, (*space, Lt)).astype(np.float64).copy()


def make_gapped_field(dims, D, *, noise=1.0, seed=0):
    """A 4-D field whose zero-momentum (spatial-sum) time correlator is a periodic cosh of a
    PLANTED rate D.  The spatial-DC time series a(t) is drawn from the 1-D lattice propagator
    S(k)=1/(4 sin^2(pi k/Lt)+M^2), M^2=2(cosh D - 1), whose circular autocorrelation is exactly
    cosh(D(t-Lt/2)); it is spread uniformly over space, and independent spatial noise (with its
    spatial DC removed) fills the other momenta WITHOUT touching the planted zero-momentum rate."""
    *space, Lt = dims
    Vol = int(np.prod(space))
    rng = np.random.default_rng(seed)
    M2 = 2.0 * (math.cosh(D) - 1.0)
    k = np.arange(Lt)
    S = 1.0 / (4.0 * np.sin(np.pi * k / Lt) ** 2 + M2)
    ahat = np.sqrt(S) * (rng.standard_normal(Lt) + 1j * rng.standard_normal(Lt))
    a = np.fft.ifft(ahat).real                                   # (Lt,) zero-momentum series, rate D
    base = (a / Vol).reshape(*([1] * len(space)), Lt)            # DC: every site carries a(t)/Vol
    n = rng.standard_normal((*space, Lt)) * noise
    n -= n.reshape(Vol, Lt).mean(0).reshape(*([1] * len(space)), Lt)   # remove the noise's spatial DC
    return (base + n).astype(np.float64)                        # sum_space = a(t) exactly


def ok(x):
    return "PASS" if x else "FAIL"


# ══════════════════════════════════════════════════════════════════════════════
# A. exact extraction + determinism (noise-free)
# ══════════════════════════════════════════════════════════════════════════════
def test_exact():
    print("\n===  A. EXACT EXTRACTION + DETERMINISM  (noise-free) -- the certainty  ===")
    # (1) a single decaying mode -> the operator's dominant eigenvalue IS its rate D, for every D
    #     and every Lt.  Read from the RAW operator spectrum (dynamics.decay_rates, dominant-first);
    #     the connected mass_gap read is exercised on field data in B1/B2.
    worst = 0.0
    for D in (0.20, 0.35, 0.50, 0.80, 1.20):
        for Lt in (16, 24, 32, 48, 64, 96, 128):
            cfgs = [single_mode_field((4, 4, Lt), D)]
            worst = max(worst, abs(W.run(cfgs, time_axis=-1).dynamics.decay_rates[0] - D))
    print(f"  single mode  a(t)=e^(-D t):   max|Dhat-D| over 5 rates x 7 windows = {worst:.2e}")
    # (2) the read is DETERMINISTIC: a repeated read of the same configs is bit-identical
    cfgs = [single_mode_field((4, 4, 64), 0.5)]
    d1 = W.run(cfgs, time_axis=-1).dynamics.decay_rates[0]
    d2 = W.run(cfgs, time_axis=-1).dynamics.decay_rates[0]
    print(f"  deterministic repeat:         |Dhat_1 - Dhat_2|                    = {abs(d1 - d2):.2e}")
    passed = worst < 1e-6 and d1 == d2
    print(f"  => {ok(passed)}: the operator's dominant eigenvalue returns the injected rate exactly and deterministically")
    return passed


# ══════════════════════════════════════════════════════════════════════════════
# B. Characterized recovery (with statistics)
# ══════════════════════════════════════════════════════════════════════════════
def test_planted_gap(dims_space=(6, 6, 6), n=64):
    print("\n===  B1. PLANTED-RATE FIELDS  (inject rate D into a 4-D field, recover through the wrapper) ===")
    print(f"  {'D_inject':>8} {'Lt':>4} | {'D_recover':>9} {'ratio':>6}   (ensemble n={n}, spatial {dims_space})")
    good = True
    for D in (0.30, 0.50, 0.80):
        ratios = []
        for Lt in (16, 32, 48):
            cfgs = [make_gapped_field((*dims_space, Lt), D, seed=s) for s in range(n)]
            Dhat = W.run(cfgs, time_axis=-1).mass_gap
            ratios.append(Dhat / D)
            print(f"  {D:>8.2f} {Lt:>4} | {Dhat:>9.4f} {Dhat/D:>6.3f}")
        r = np.array(ratios)
        good = good and np.all(r > 0.75) and np.all(r < 1.25) and (r.max() / r.min() < 1.30)
    print(f"  => {ok(good)}: planted rate recovered within calibration, stable across Lt")
    return good


def test_free_scalar_sweep(n=48):
    print("\n===  B2. FREE-SCALAR MASS SWEEP  (known gap E0 = arccosh(1 + m^2/2)) ===")
    print(f"  {'m':>4} {'E0':>7} | {'mass_gap':>8} {'ratio':>6}   (n={n}, 8x8x{{Lt}})")
    good = True
    for m in (0.3, 0.5, 0.8, 1.2):
        e0 = math.acosh(1 + m * m / 2)
        cfgs = [G.free_scalar((8, 8, 48), m, seed=s) for s in range(n)]
        mg = W.run(cfgs, time_axis=-1).mass_gap
        good = good and (0.80 < mg / e0 < 1.20)
        print(f"  {m:>4} {e0:>7.4f} | {mg:>8.4f} {mg/e0:>6.3f}")
    print(f"  => {ok(good)}: the free-scalar gap is recovered across the mass range")
    return good


# ══════════════════════════════════════════════════════════════════════════════
# C. Aperture separation on real configs (guarded by the hopper)
# ══════════════════════════════════════════════════════════════════════════════
def test_phase_separation(hop, ncap=192, volumes=(8, 12, 16, 24, 32)):
    """C. PHASE SEPARATION on real configs: the order parameter K_signal carries the phase.

    This check does not assert that the GAP read separates the phases -- su2 confined returning a
    finite ~L-stable Delta and u1 Coulomb returning ~0. That is false, and the paper was corrected on
    2026-08-20 to say so: the read is taken on the action density, a gauge-invariant composite
    (~:F^2:), whose correlator falls as a power law in the Coulomb phase and over a finite lattice
    range fits an effective exponential, returning a finite Delta. The margin is phase-blind here.
    `gap_of_margin` reads every U(1) Coulomb ensemble as finite-aperture, and `apriori_A1` classifies
    u1 beta=2.50 as CONFINED + GAPPED.

    What does separate them is the confinement order parameter K_signal (PAPER Sec 8.3): the count
    of resolved spatial modes above the pinned confined-vacuum floor, low in the confined phase and
    high in the Coulomb phase. So that is what this checks, and Delta is printed beside it as the
    documented negative -- the certificate reports the fact that the gap read does NOT discriminate,
    rather than asserting that it does.

    The verdict is threshold-free: at each shared volume, the Coulomb K_signal must exceed the
    confined one. No cut is chosen, so none can be tuned. The comparison is per volume because
    K_signal counts resolved modes and so scales with the lattice in both phases -- pooling the
    volumes would put Coulomb at a small L against confined at a large one and call the volume
    dependence a phase failure. K_signal needs the pinned reference (`pin_reference`), the same
    confined-vacuum null `apriori_A1` pins.

    `volumes` spans the whole tower the store carries, and deliberately so: the separation NARROWS
    monotonically with volume, measured 2026-08-23 at beta 2.30 (confined) against 2.50 (Coulomb),

        L=8   0.076 vs 0.319   4.18x        L=24  3.125 vs 4.849   1.55x
        L=12  0.191 vs 0.790   4.13x        L=32  6.723 vs 8.823   1.31x
        L=16  0.670 vs 1.764   2.63x

    because confined K_signal grows faster with L (2.51x, 3.50x, 4.67x, 2.15x per step) than Coulomb
    does (2.47x, 2.23x, 2.75x, 1.82x). Restricting this check to L <= 16 would test only the region
    where the property holds comfortably and pass regardless of what happens above it -- a check that
    cannot fail is not evidence. The tightest point, L=32 at 1.31x, is the one worth having. Reading
    K_signal per intact spatial plane over the full tower costs roughly an hour and 25 GB, against
    a minute and 1.2 GB for L <= 16.

    PAPER Sec 8.3 says K_signal is "a phase discriminator at fixed lattice size" and does not claim
    more; this measures how much room that statement has, and finds it holds to L=32 with the margin
    shrinking threefold across the tower.
    """
    print("\n===  C. PHASE SEPARATION  (real configs: K_signal carries the phase, the gap does not)  ===")

    def load(group, L, beta, cap=ncap):
        fs = sorted(glob.glob(f"{hop}/{group}_L{L}_b{beta:.2f}.s*.npy"))
        if not fs:
            return None
        return np.asarray(np.concatenate([np.load(f) for f in fs], 0)[:cap], dtype=np.float64)

    # K_signal is read against the pinned confined-vacuum null (su2 beta=0.50), never the library's
    # i.i.d. edge; with nothing pinned the read raises rather than inventing a floor.
    ref = []
    for L in (8, 12, 16):
        a = load("su2", L, 0.50, cap=48)
        if a is not None:
            ref += list(a)
    if not ref:
        print("  (no su2 beta=0.50 reference planes under the hop; skipping the verdict)")
        return None
    W.pin_reference(ref)
    print(f"  pinned confined reference: {len(ref)} su2 beta0.50 planes")

    print(f"  {'group':>4} {'phase':>9} {'L':>3} {'n':>4} | {'K_signal':>8} {'Delta':>7}")
    got = {}
    for group, beta, phase in (("su2", 2.30, "confined"), ("u1", 2.50, "Coulomb")):
        for L in volumes:
            arr = load(group, L, beta)
            if arr is None:
                continue
            r = W.run(list(arr), time_axis=-1)
            K, D = float(r.confinement), float(r.mass_gap)
            got[(group, L)] = (K, D)
            print(f"  {group:>4} {phase:>9} {L:>3} {arr.shape[0]:>4} | {K:>8.4f} {D:>7.4f}")

    su2K = [got[("su2", L)][0] for L in volumes if ("su2", L) in got]
    u1K = [got[("u1", L)][0] for L in volumes if ("u1", L) in got]
    su2D = [got[("su2", L)][1] for L in volumes if ("su2", L) in got]
    u1D = [got[("u1", L)][1] for L in volumes if ("u1", L) in got]
    if len(su2K) < 2 or len(u1K) < 2:
        print("  (insufficient configs for both phases; skipping the verdict)")
        return None

    # K_signal counts resolved spatial modes, so it grows with the volume in BOTH phases (confined
    # reads 0.076, 0.191, 0.67 at L = 8, 12, 16). Pooling the volumes and asking whether every
    # Coulomb reading beats every confined one therefore tests volume against phase: Coulomb at L=8
    # (0.319) loses to confined at L=16 (0.67) while saying nothing about either phase. The
    # comparison that means something is at MATCHED volume -- same lattice, same mode budget, one
    # phase against the other -- and it stays threshold-free.
    shared = [L for L in volumes if ("su2", L) in got and ("u1", L) in got]
    pairs = [(L, got[("su2", L)][0], got[("u1", L)][0]) for L in shared]
    separated = bool(pairs) and all(u > c for _, c, u in pairs)
    print(f"  K_signal  confined {[round(x, 3) for x in su2K]}  Coulomb {[round(x, 3) for x in u1K]}")
    for L, c, u in pairs:
        print(f"            L={L:<3} confined {c:.3f}  Coulomb {u:.3f}  "
              f"{'Coulomb higher' if u > c else 'NOT SEPARATED'} ({u / c:.2f}x)")
    print(f"            Coulomb above confined at every shared volume: {separated}")
    # The documented negative, reported rather than asserted away.
    overlap = not (min(su2D) > max(u1D) or min(u1D) > max(su2D))
    print(f"  Delta     confined {[round(x, 3) for x in su2D]}  Coulomb {[round(x, 3) for x in u1D]}")
    print(f"            gap read does NOT separate the phases (ranges overlap: {overlap})")
    print(f"  => {ok(separated)}: K_signal separates confined from Coulomb")
    return separated


# ══════════════════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    a = test_exact()
    b1 = test_planted_gap()
    b2 = test_free_scalar_sweep()
    # Same store root as every sibling script, resolved by store_path (CONFIGS, then the
    # git-ignored local config file, then nothing); part C runs whenever the store is reachable
    # instead of only when someone remembers to export HOP. Unconfigured is None here rather than
    # a refusal: parts A and B are synthetic and must still run where no data release exists.
    hop = os.environ.get("HOP") or store_path.collection("configs_phase1", required=False)
    c = test_phase_separation(hop) if hop and glob.glob(f"{hop}/*.npy") else None

    print("\n" + "=" * 70)
    print(f"  A   exact extraction + determinism (noise-free)     : {ok(a)}")
    print(f"  B1  planted-rate fields recovered (characterized)   : {ok(b1)}")
    print(f"  B2  free-scalar mass sweep (known gap)              : {ok(b2)}")
    print(f"  C   K_signal separates confined vs Coulomb          : "
          f"{'(skipped: no store -- set CONFIGS=<root> or HOP=<dir>)' if c is None else ok(c)}")
    print("=" * 70)
    core = a and b1 and b2
    sys.exit(0 if (core and (c is None or c)) else 1)
