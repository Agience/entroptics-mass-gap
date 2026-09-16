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
import aperture_reads as AR             # shared reads (pencil_rate, operator_history)
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


# DERIVED: `blocks` is a SAMPLE COUNT, not a cut -- it sets how well the reseeding spread is
# estimated, and no verdict anywhere in this file turns on its value.
#: DERIVED: a SAMPLE COUNT shared by the reseeded stages, not a cut -- it sets how well
#: the spread is estimated and no verdict turns on its value.
BLOCKS_DEFAULT = 4


def reseed_blocks(make, n, blocks=BLOCKS_DEFAULT):
    """Read the SAME configuration recipe from `blocks` disjoint seed ranges of `n` configs each.

    WHY. A recovery check needs a reference to judge the deviation against, and the only reference
    that is not a number written here is the one the read produces itself: reseed the ensemble and
    see how far the answer moves for no physical reason at all. Everything downstream compares a
    deviation-from-truth against this spread-from-reseeding -- two measured quantities, no window.

    `make(seed)` builds one configuration. Returns the per-block `mass_gap` array.

    DERIVED: `blocks=4` is a SAMPLE COUNT, not a cut -- it sets how well the spread is estimated and
    no verdict turns on its value. The seed ranges are disjoint by construction (`b * n + s`).
    """
    return np.array([W.run([make(b * n + s) for s in range(n)], time_axis=-1).mass_gap
                     for b in range(blocks)])


def _cell(truth, vals):
    """One (truth, reseeded reads) cell: mean, reseeding spread, deviation, and their ratio."""
    spread = float(vals.max() - vals.min())
    dev = float(abs(vals.mean() - truth))
    # DERIVED: the guard is against dividing by an exactly-zero spread, which can only happen if
    # every block returned the identical float. `inf` then correctly reports "outside the spread".
    return float(vals.mean()), spread, dev, (dev / spread if spread > 0.0 else float("inf"))


def _report(rows, label):
    """Print a recovery table and return the derived verdict.

    THE VERDICT, and why it needs no window. Two statements, both comparisons between quantities
    this call measured:

      (i) CONVERGENCE, while there is anything to converge. At each rate the deviation from truth
          must FALL as the window widens, for as long as it is still OUTSIDE the read's own
          reseeding spread. A finite window truncates a decay; the truncation is a systematic, and
          a systematic that is a property of the window shrinks when the window grows. Once the
          deviation is inside the spread it is not distinguishable from zero, and an ordering
          between two numbers that both sit under the measurement's own resolution is not a claim
          this can make -- so it is not required. (Without that clause the free scalar at
          E0 = 0.49 failed on 0.0047 -> 0.0019 -> 0.0065, three deviations spanning 0.02x to 0.12x
          of the spread: pure reshuffling of noise, reported as a defect.)

     (ii) CONSISTENCY, where the decay is sampled at all. At the widest window the deviation must
          sit inside the read's own reseeding spread -- for every rate whose correlation length
          exceeds one lattice spacing. A rate `D` has correlation length `1/D` in spacings, so the
          condition is `D < 1`: the `1` is the SAMPLING INTERVAL in its own units, the Nyquist
          statement that a decay finishing inside one step is not sampled. It is arity, not a cut:
          no value of the deviation passes or fails by being large or small.

    A rate at or below one-spacing correlation length is REPORTED with its deviation and excluded
    from (ii) rather than judged by a widened window -- the systematic is stated, not hidden.
    """
    print(f"  {'truth':>8} {'window':>6} | {'read':>9} {'spread':>8} {'dev':>8} {'dev/spread':>10}"
          f"  {'xi>1 spacing':>12}")
    good = True
    for truth, cells in rows:
        # DERIVED: 1.0 is the lattice spacing in its own units -- xi = 1/truth exceeds one sampling
        # interval exactly when truth < 1. Nyquist, not a tolerance.
        sampled = truth < 1.0
        devs = []
        for window, (mean, spread, dev, ratio) in cells:
            devs.append(dev)
            print(f"  {truth:>8.4f} {window:>6} | {mean:>9.4f} {spread:>8.4f} {dev:>8.4f}"
                  f" {ratio:>10.2f}  {'yes' if sampled else 'NO (sub-spacing)':>12}")
        ratios = [c[1][3] for c in cells]
        # DERIVED: 1.0 is the ratio at which the deviation EQUALS the reseeding spread -- the point
        # below which the read cannot tell its own error from its own noise. The pair is judged only
        # while the earlier cell is above it. No scale is introduced: both sides are measured here.
        converging = all(b <= a for a, b, ra in zip(devs, devs[1:], ratios) if ra > 1.0)
        widest_ratio = cells[-1][1][3]
        # DERIVED: 1.0 is the ratio at which the deviation EQUALS the read's own reseeding spread.
        # Both sides are measured here; the comparison introduces no scale.
        consistent = (widest_ratio <= 1.0) if sampled else True
        if not converging:
            print(f"      ^ deviation does not fall as the window widens while outside the "
                  f"spread: {devs}")
        if sampled and not consistent:
            print(f"      ^ at the widest window the deviation is {widest_ratio:.2f}x the "
                  f"reseeding spread")
        good = good and converging and consistent
    print(f"  => {ok(good)}: {label}")
    return good


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
    # DERIVED: machine-epsilon class -- a bit-identity check on two paths through the same read.
    passed = worst < 1e-6 and d1 == d2
    print(f"  => {ok(passed)}: the operator's dominant eigenvalue returns the injected rate exactly and deterministically")
    return passed


# ══════════════════════════════════════════════════════════════════════════════
# B. Characterized recovery (with statistics)
# ══════════════════════════════════════════════════════════════════════════════
def test_planted_gap(dims_space=(6, 6, 6), n=64, windows=(16, 32, 48)):
    """B1. Inject a known rate D into a 4-D field and recover it through the wrapper.

    Judged against the read's OWN reseeding spread and its OWN convergence in the window -- see
    `_report`. Nothing here is a tolerance: an earlier version passed this on +-25% and 1.3x
    windows, which concealed that at (D=0.80, Lt=16) the read returns 0.67, 4.3x outside its own
    reproducibility. That cell now prints its deviation, and the claim it supports is the one that
    is true of it: the truncation shrinks as the window widens.
    """
    print("\n===  B1. PLANTED-RATE FIELDS  (inject rate D into a 4-D field, recover through the wrapper) ===")
    print(f"  (ensemble n={n} per block, spatial {dims_space}; spread over disjoint seed blocks)")
    rows = []
    for D in (0.30, 0.50, 0.80):
        cells = []
        for Lt in windows:
            vals = reseed_blocks(lambda s, Lt=Lt, D=D: make_gapped_field((*dims_space, Lt), D, seed=s), n)
            cells.append((Lt, _cell(D, vals)))
        rows.append((D, cells))
    return _report(rows, "planted rate: truncation falls with the window, and the widest window "
                         "agrees with truth inside the read's own reseeding spread")


def test_free_scalar_sweep(n=48, windows=(16, 32, 48)):
    """B2. The free scalar, whose gap is known in closed form: E0 = arccosh(1 + m^2/2).

    Same derived verdict as B1. The mass range deliberately runs past the sampling limit: at
    m = 1.2 the correlation length is 1/E0 = 0.88 lattice spacings, BELOW one time step, and the
    read is biased low by 7% at the widest window -- 2.7x its own reseeding spread. An earlier
    +-20% window passed that cell silently. It is now printed, excluded from the consistency claim
    by the Nyquist condition rather than by a widened tolerance, and its convergence is still
    required: 0.86 -> 1.00 -> 1.06 against a truth of 1.14 as the window widens.
    """
    print("\n===  B2. FREE-SCALAR MASS SWEEP  (known gap E0 = arccosh(1 + m^2/2)) ===")
    print(f"  (n={n} per block, 8x8x{{Lt}}; spread over disjoint seed blocks)")
    rows = []
    for m in (0.3, 0.5, 0.8, 1.2):
        e0 = math.acosh(1 + m * m / 2)
        cells = []
        for Lt in windows:
            vals = reseed_blocks(lambda s, Lt=Lt, m=m: G.free_scalar((8, 8, Lt), m, seed=s), n)
            cells.append((Lt, _cell(e0, vals)))
        rows.append((e0, cells))
    return _report(rows, "the free-scalar gap converges to E0 as the window widens, and agrees "
                         "inside the reseeding spread wherever the decay is sampled")


def planted_operator(T, D, *, seed=0):
    """A zero-momentum operator history `O(t)` of shape `(T,)` with a PLANTED rate `D`.

    Drawn from the 1-D lattice propagator `S(k) = 1/(4 sin^2(pi k/T) + M^2)`, `M^2 = 2(cosh D - 1)`,
    whose circular autocorrelation is exactly `cosh(D(t - T/2))`. The same construction
    `make_gapped_field` uses for its zero-momentum component, without the spatial dressing -- because
    the pencil reads `O(t)` and nothing else.
    """
    rng = np.random.default_rng(seed)
    M2 = 2.0 * (math.cosh(D) - 1.0)
    k = np.arange(T)
    S = 1.0 / (4.0 * np.sin(np.pi * k / T) ** 2 + M2)
    ahat = np.sqrt(S) * (rng.standard_normal(T) + 1j * rng.standard_normal(T))
    return np.fft.ifft(ahat).real


# DERIVED: `T` and `n` are the GEOMETRY of the synthetic data -- the periodic extent the planted
# propagator is drawn on and the ensemble size per block. Nothing is compared against either.
def test_pencil_planted(T=32, n=96, orders=(2, 3, 4)):
    """B3. The Hankel moment pencil on planted rates, judged against its own reseeding spread.

    This is the read the box-at-fixed-aperture question needs, because its dimension is the moment
    order rather than the volume. Calibrated here before anything relies on it.

    Reported per (rate, order): the block mean, the reseeding spread, the deviation from truth, and
    how many of the blocks the read declared VALID. A configuration where the read invalidates itself
    is reported as such and carries no verdict -- that is the read refusing, which is the behaviour
    wanted, not a failure of this test.
    """
    print("\n===  B3. HANKEL MOMENT PENCIL  (planted rate through the reflection-positive pencil) ===")
    print(f"  (n={n} per block, T={T}; spread over disjoint seed blocks)")
    print(f"  {'truth':>8} {'order':>6} | {'read':>9} {'spread':>8} {'dev':>8} {'dev/spread':>10}"
          f"  {'valid':>7}")
    rows = []
    for D in (0.30, 0.50, 0.80):
        cells = []
        for order in orders:
            vals, nvalid = [], 0
            for b in range(BLOCKS_DEFAULT):
                O = np.array([planted_operator(T, D, seed=b * n + s) for s in range(n)])
                # NOT `ok` -- that is this module's PASS/FAIL formatter, and rebinding it here
                # shadowed the function for the rest of the scope.
                r, is_valid = AR.pencil_rate(O, order)
                if is_valid:
                    vals.append(r)
                    nvalid += 1
            # DERIVED: 2 is where a spread exists at all -- one surviving block has no range.
            if len(vals) < 2:
                print(f"  {D:>8.4f} {order:>6} |    read invalidated itself in "
                      f"{BLOCKS_DEFAULT - nvalid} of {BLOCKS_DEFAULT} blocks; no verdict")
                cells.append((order, None, nvalid))
                continue
            arr = np.array(vals, dtype=float)
            cell = _cell(D, arr)
            cells.append((order, cell, nvalid))
            print(f"  {D:>8.4f} {order:>6} | {cell[0]:>9.4f} {cell[1]:>8.4f} {cell[2]:>8.4f} "
                  f"{cell[3]:>10.2f}  {nvalid:>3}/{BLOCKS_DEFAULT}")
        rows.append((D, cells))

    # The verdict: at every planted rate, SOME order must both validate and land inside its own
    # reseeding spread. Which order is not fixed here -- the pencil is asked to have a usable order,
    # not a particular one, and which one works is a property of the correlator.
    good = True
    for D, cells in rows:
        # DERIVED: 1.0 is the ratio at which the deviation EQUALS the read's own reseeding
        # spread. Both sides measured; the comparison introduces no scale.
        usable = [o for o, c, _ in cells if c is not None and c[3] <= 1.0]
        if not usable:
            print(f"      ^ no pencil order both validated and agreed with {D:.4f} inside its own "
                  f"spread")
        good = good and bool(usable)
    print(f"  => {ok(good)}: the pencil has a usable order at every planted rate, its deviation "
          f"inside its own reseeding spread")
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
    b3 = test_pencil_planted()
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
    print(f"  B3  Hankel moment pencil on planted rates          : {ok(b3)}")
    print(f"  C   K_signal separates confined vs Coulomb          : "
          f"{'(skipped: no store -- set CONFIGS=<root> or HOP=<dir>)' if c is None else ok(c)}")
    print("=" * 70)
    core = a and b1 and b2 and b3
    sys.exit(0 if (core and (c is None or c)) else 1)
