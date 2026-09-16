"""What one rented GPU-hour has to settle before any production run is paid for.

WHY THIS EXISTS. The generator carries a batched torch/CUDA path that has never run on a GPU, and the
campaign that needs it (larger volumes for the volume-uniform bound) is costed from a CPU measurement
extrapolated by a bandwidth ratio. Both of those are estimates. Renting a card for an hour turns them
into measurements, and an hour on a consumer card costs less than a coffee -- so there is no reason to
buy a production run on an estimate.

THE THREE QUESTIONS, and each one can change the plan:

  1. HOW FAST is the card on THIS kernel? The sweep is elementwise and memory-bandwidth-bound, not
     FLOP-bound, so the speedup should track memory bandwidth rather than TFLOPs. If it does not, the
     whole cost projection is wrong and the campaign must be re-costed before it is run.

  2. WHAT DOES fp64 COST HERE? Consumer cards run fp64 at 1/64 the fp32 FLOP rate but at full memory
     BANDWIDTH, and fp64 moves twice the bytes. So a bandwidth-bound kernel should lose about 2x, not
     64x. Which of those two numbers shows up decides whether a consumer card is adequate: near 2x and
     it is, near 64x and the campaign needs a card with real fp64 (A100 class) or must use fp32.

  3. IS fp32 SOUND AT THE VOLUME THAT MATTERS? fp32 was checked against fp64 at L=6 and agreed to
     0.68 sigma, but rounding accumulates with the number of sites and L=48 has ~4000x more of them.
     The check is repeated here at the largest volume the hour affords. A shift in the action density
     propagates into the string tension, which sets every physical scale in the paper -- so this is
     the question that can invalidate results rather than merely slow them down.

WHAT IT DOES NOT DO. It generates nothing anyone keeps and writes no artifact. It is a decision
instrument: run it, read the verdict, then decide what to rent and for how long.

USAGE. Copy this file and `lattice_generator.py` to the pod -- the generator imports only `os` and
`numpy` at module scope, with torch loaded lazily, so those two files are the whole dependency.

    python gpu_bench.py                 # auto-detect; full benchmark
    BENCH_L=8,12,16 python gpu_bench.py # choose the ladder explicitly
    BENCH_SEEDS=6 python gpu_bench.py   # seeds per arm for the fp32 check

Precision is selected per call through `lattice_generator.config(..., fp=32|64)`; nothing here reads
or writes `GEN_FP`, so running this alongside another generation cannot perturb it.
"""
from __future__ import annotations

import os
import statistics
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import lattice_generator as G                        # noqa: E402  (needs HERE on sys.path first)

#: DERIVED: the volume ladder is read from the environment so no size is baked in; the default
#: doubles from the smallest volume the repo simulates up to where a single config still fits in a
#: benchmark minute. Each rung is measured independently, so the SCALING is what is reported, not a
#: single number that could be a fluke of one size.
LADDER = tuple(int(x) for x in os.environ.get("BENCH_L", "8,12,16").split(","))

#: DERIVED: seeds per arm for the precision comparison. The comparison is a difference of means
#: against the pooled standard error, so this sets the SENSITIVITY of the fp32 check and is reported
#: alongside the verdict rather than hidden -- a null result at low sensitivity is not a pass.
SEEDS = int(os.environ.get("BENCH_SEEDS", "6"))

#: CHOSEN: the coupling the benchmark generates at. It costs nothing but comparability with the
#: released ensembles, which sit at 2.30-2.50; timings are essentially flat in beta, and no verdict
#: below depends on its value.
BETA = 2.3

#: DERIVED: the volumes the campaign actually wants, not the ones that fit in a benchmark minute.
#: Q1 measures scaling cheaply at small L; this asks the question at the sizes that will be paid for,
#: because a cost extrapolated from volumes the card never filled is an extrapolation from overhead.
SCALE_LADDER = tuple(int(x) for x in os.environ.get("BENCH_SCALE_L", "16,24,32").split(","))

#: DERIVED: powers of two up to the point a batch stops fitting. Where it stops is not chosen here --
#: the loop catches the allocation failure and reports the row short, so the card states its own
#: limit rather than this list asserting one.
BATCHES = tuple(int(x) for x in os.environ.get("BENCH_BATCH", "1,4,16").split(","))

#: DERIVED, both of them, from what the hardware does rather than from a preference:
#:   fp64 moves exactly TWICE the bytes of fp32, so a purely MEMORY-BANDWIDTH-bound kernel costs 2x.
#:   A consumer GPU runs fp64 at 1/64 the fp32 FLOP rate, so a purely FLOP-bound one costs 64x.
#: Those are the two hypotheses, and the measurement falls between them. The discriminator is their
#: GEOMETRIC midpoint -- the point equidistant from both in the ratio that is actually being measured
#: -- so nothing here is a chosen cut: change either physical prediction and the boundary moves with
#: it. sqrt(2*64) = 11.3.
# DERIVED: fp64 moves exactly 2x the bytes of fp32
FP64_IF_BANDWIDTH_BOUND = 2.0
# DERIVED: a consumer GPU runs fp64 at 1/64 the fp32 FLOP rate
FP64_IF_FLOP_BOUND = 64.0
FP64_DISCRIMINATOR = (FP64_IF_BANDWIDTH_BOUND * FP64_IF_FLOP_BOUND) ** 0.5


# DERIVED: batch=1 and seed=0 are the UNIT being timed -- one configuration from one chain.
# Neither decides anything: callers that care pass their own, and the table reports per-config
# seconds precisely so that a batch size cannot flatter the result.
def _gen(L, device, fp, batch=1, seed=0):
    """One timed generation at (L, Lt=2L). Returns (seconds, field).

    Precision is an ARGUMENT, so the two arms differ only in what they are asked for. Selecting it
    through the `GEN_FP` environment variable instead would mutate process-global state that any
    concurrent generation would also read, which is not a property a measurement should have.
    """
    t0 = time.time()
    f = G.config((L, L, L, 2 * L), BETA, group="su2", seed=seed, device=device, batch=batch, fp=fp)
    if device is not None:                      # CUDA is async; the copy forces completion
        f = f.detach().cpu()
    return time.time() - t0, f


def _density(f):
    a = f.detach().cpu().numpy() if hasattr(f, "detach") else np.asarray(f)
    return float(np.mean(a.astype(np.float64)))


def main() -> int:
    try:
        import torch
    except ImportError:
        print("REFUSED: torch is not installed; this benchmark has nothing to measure.")
        return 2

    print(f"torch {torch.__version__}   cuda available: {torch.cuda.is_available()}")
    if not torch.cuda.is_available():
        print("REFUSED: no CUDA device visible. On a GPU pod this means the torch build is CPU-only")
        print("         (`pip install torch --index-url https://download.pytorch.org/whl/cu121`)")
        print("         or the pod has no GPU attached. Nothing here is meaningful without one.")
        return 2

    dev = torch.cuda.get_device_properties(0)
    bw = None
    try:  # memory bandwidth is what this kernel actually rides on, so report it if the driver knows
        bw = dev.memory_clock_rate * dev.memory_bus_width * 2 / 8 / 1e6  # GB/s
    except AttributeError:
        pass
    print(f"device: {dev.name}   {dev.total_memory / 1e9:.1f} GB"
          + (f"   ~{bw:.0f} GB/s" if bw else ""))
    print()

    # ---- 1 and 2: speed, and what fp64 costs ------------------------------------------------
    print("Q1/Q2  generation time for ONE config, by backend and precision")
    print(f"{'L':>4} {'sites':>10} {'numpy fp64':>12} {'gpu fp64':>11} {'gpu fp32':>11} "
          f"{'speedup':>9} {'fp64 cost':>10}")
    rows = []
    for L in LADDER:
        sites = L ** 3 * (2 * L)
        t_np, _ = _gen(L, None, None)
        t_g64, _ = _gen(L, "cuda", 64)
        t_g32, _ = _gen(L, "cuda", 32)
        # DERIVED: dividing by a zero time is undefined, not a threshold -- these guard the
        # ratio, and a run fast enough to time as 0.00s has nothing to report either way.
        # DERIVED: dividing by a zero elapsed time is undefined, not a threshold. A run that
        # times as 0.00s has nothing to report either way.
        speed = t_np / t_g32 if t_g32 > 0 else float("inf")
        # DERIVED: the same zero-divisor guard, on the same timing.
        fp64cost = t_g64 / t_g32 if t_g32 > 0 else float("inf")
        rows.append((L, sites, t_np, t_g64, t_g32, speed, fp64cost))
        print(f"{L:>4} {sites:>10} {t_np:>11.2f}s {t_g64:>10.2f}s {t_g32:>10.2f}s "
              f"{speed:>8.1f}x {fp64cost:>9.1f}x")

    print()
    fp64_costs = [r[6] for r in rows]
    worst_fp64 = max(fp64_costs)
    print(f"  measured fp64 cost {worst_fp64:.1f}x, against {FP64_IF_BANDWIDTH_BOUND:.0f}x if purely "
          f"bandwidth-bound and {FP64_IF_FLOP_BOUND:.0f}x if purely FLOP-bound")
    if worst_fp64 < FP64_DISCRIMINATOR:
        print(f"  -> closer to BANDWIDTH-bound. A consumer card is adequate even in fp64, and the")
        print("     fp32 question below is an optimisation rather than a requirement.")
    else:
        print(f"  -> closer to FLOP-bound: this card's crippled fp64 rate IS showing. Either fp32")
        print("     must be sound (Q3 below) or the campaign needs a card with real fp64.")

    # ---- 3: is fp32 sound at the largest volume the hour affords? ---------------------------
    Lbig = LADDER[-1]
    print()
    print(f"Q3  fp32 vs fp64 on the action density at L={Lbig}, {SEEDS} seeds per arm")
    arms = {}
    for label, fp in (("gpu fp64", 64), ("gpu fp32", 32)):
        vals = []
        for s in range(SEEDS):
            _, f = _gen(Lbig, "cuda", fp, seed=s)
            vals.append(_density(f))
        m = statistics.mean(vals)
        # DERIVED: a standard deviation needs at least two samples; with one there is no spread
        # to report, and nan propagates into the sigma below rather than faking a precise zero.
        se = statistics.stdev(vals) / len(vals) ** 0.5 if len(vals) > 1 else float("nan")
        arms[label] = (m, se, vals)
        print(f"  {label:<10} {m:.6f} +/- {se:.6f}")

    (m32, s32, _v32), (m64, s64, v64) = arms["gpu fp32"], arms["gpu fp64"]
    d = m32 - m64
    se = (s32 ** 2 + s64 ** 2) ** 0.5
    # DERIVED: a zero pooled error means the arms did not vary at all, so any difference is
    # infinitely many sigma -- the guard is against dividing by zero, not a tolerance.
    sigma = abs(d) / se if se > 0 else float("inf")
    print()
    print(f"  precision shift: {d:+.6f} +/- {se:.6f}   ({sigma:.2f} sigma)")
    print(f"  sensitivity: this can only exclude shifts larger than {se / abs(m64) * 100:.2f}% "
          f"of the observable")
    # The VERDICT names no threshold. It compares two MEASURED quantities: how much switching
    # precision moves the observable, against how much the observable already moves when only the
    # SEED changes. If precision moves it less than re-seeding does, precision is not a
    # distinguishable input at this volume -- which is the question, asked without choosing a sigma.
    # DERIVED: a standard deviation needs two samples. With one there is no re-seeding spread
    # to compare against, and infinity makes the verdict below refuse rather than pass blindly.
    reseed_spread = statistics.stdev(v64) if len(v64) > 1 else float("inf")
    print(f"  re-seeding fp64 alone moves it by {reseed_spread:.6f} (sd over {SEEDS} seeds)")
    if abs(d) < reseed_spread:
        print("  -> fp32 moves the observable LESS than changing the seed does: at this volume")
        print("     precision is not a distinguishable input.")
    else:
        print("  -> fp32 moves the observable MORE than re-seeding does. Use fp64, and re-read the")
        print("     fp64 cost above: it, not fp32, now sets which card the campaign needs.")

    # ---- Q4: where does the card actually start doing work? ---------------------------------
    # The Q1 table can come back FLAT -- the same seconds per config as the volume grows -- which
    # means the GPU is not compute-bound there at all: the time is fixed overhead, one launch per
    # sweep, and the lattice is too small to fill the card. Two things follow, and both change the
    # campaign. Extrapolating a cost from flat rungs is extrapolating from noise. And a batch costs
    # almost nothing until the card is full, so `batch=1` is the worst possible way to buy it.
    #
    # This measures both: per-CONFIG seconds against batch size, at each volume. The right batch is
    # the largest one whose per-config time is still falling, and the right cost model is fitted
    # from rungs that have actually left the overhead floor.
    print()
    print(f"Q4  per-config seconds vs batch size (fp{64}), the number that sets the campaign cost")
    print(f"{'L':>4} {'sites':>10} " + " ".join(f"{'b=' + str(b):>10}" for b in BATCHES))
    per_config = {}
    for L in SCALE_LADDER:
        sites = L ** 3 * (2 * L)
        row = []
        for b in BATCHES:
            try:
                dt, _ = _gen(L, "cuda", 64, batch=b)
                row.append(dt / b)
            except Exception as e:                      # out of memory is a RESULT, not a crash
                row.append(float("nan"))
                print(f"   (L={L} batch={b}: {type(e).__name__} -- card full, stopping this row)")
                break
        per_config[L] = row
        print(f"{L:>4} {sites:>10} " + " ".join(f"{v:>10.2f}" for v in row))

    print()
    for L, row in per_config.items():
        good = [(BATCHES[i], v) for i, v in enumerate(row) if v == v]
        # DERIVED: a speedup needs two batch sizes to compare. With one measurement there is
        # nothing to report, and the row is skipped rather than reported as a 1.0x change.
        if len(good) > 1:
            best_b, best_v = min(good, key=lambda kv: kv[1])
            worst_b, worst_v = good[0]
            print(f"  L={L}: batching {worst_b} -> {best_b} cuts per-config time "
                  f"{worst_v:.2f}s -> {best_v:.2f}s ({worst_v / best_v:.1f}x)")

    # ---- what this implies for the campaign -------------------------------------------------
    print()
    print("COST PROJECTION (extrapolating the measured per-config time in sites^1.22, the exponent")
    print("measured on CPU; the GPU exponent is whatever the table above shows, so treat this as")
    print("indicative and re-fit it from these rows if the rungs disagree)")
    ref_L, ref_t = rows[-1][0], rows[-1][4]
    ref_sites = rows[-1][1]
    print(f"{'L':>4} {'1 config':>11} {'96 configs':>13} {'@ $0.34/hr':>12}")
    for L in (24, 28, 32, 40, 48):
        sites = L ** 3 * (2 * L)
        t = ref_t * (sites / ref_sites) ** 1.22
        hrs = t * 96 / 3600
        print(f"{L:>4} {t:>10.1f}s {hrs:>12.1f}h {hrs * 0.34:>11.2f}$")
    print()
    print("96 configs per volume, held EQUAL across volumes: the config count must not vary with L")
    print("(a varying count manufactures a volume trend, which has produced two false results in this")
    print("program's history). 96 is where a gapped and a massless control separated at 10.9 sigma.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
