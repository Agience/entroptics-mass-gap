"""regen_all.py -- the one entry point that regenerates every committed artifact.

    python research/regen_all.py --list              # what exists, what owns it, what it costs
    python research/regen_all.py                     # regenerate everything runnable here
    python research/regen_all.py --phase data        # data | figures | certify
    python research/regen_all.py --only 8_7          # substring match on the owner script
    python research/regen_all.py --verify            # regenerate nothing; compare artifacts to git HEAD
    python research/regen_all.py --include-heavy     # also run the jobs flagged bigmem/gpu

Why this file exists
--------------------
Each committed ``*_dat_*.csv`` is produced by exactly ONE script (its OWNER). Several observables are
written by more than one script at different schemas, so running a NON-owner overwrites the artifact
with a different shape -- which is why the mapping matters, and why it lives here, in code, instead
of in prose that cannot be executed. ``OWNERS`` below IS the provenance table.

Resource classes
----------------
``cpu``     runs on a laptop, seconds to a few minutes.
``cpu2h``   CPU-bound but long (tens of minutes); fine unattended.
``long``    CPU-light and genuinely slow (hours). Separate from ``cpu2h`` so that hitting the budget
            reads as "needs more time" rather than as a fault.
``bigmem``  needs a large-memory host. The Koopman splice carries a dense F x F operator; at L=16,
            F = 13824, about 1.4 GiB per array with three live at once. Reducing the config count
            does NOT help -- F is fixed by the lattice size, not by how many configs are read.
``gpu``     wants CUDA to be practical. Runs on CPU, slowly.

Classes are set from MEASUREMENT, not from reading the code: every one of them has been corrected
at least once by a job being killed or timed out. When a job dies for want of a resource, move it
to the class that matches what it actually took, and say so in a comment beside it.

``--include-heavy`` is required for ``bigmem``/``gpu``, so a default run cannot silently skip them
without saying so, and cannot silently spend hours either. Skips are always reported.

Two facts about the artifacts that the table cannot carry
---------------------------------------------------------
* The ``*_regen_*`` owners read the frozen link store and take a deterministic first-``N``
  ``[:ncap]`` slice. That cap is REPORTED, in the per-row ``n``: it is the shard count available at
  freeze, not a post-hoc selection of "the configs that worked."
* ``mu`` is all-zero in ``8_3_dat_nobump.csv`` because the measured maximal-correlation tension is
  ``mu ~ 0`` in BOTH phases -- the order parameter is ``K_signal``, not ``mu``. That column is a
  genuine read of zero, not a missing one.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import os
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent            # research/data/
RESEARCH = HERE.parent                            # research/
REPO = RESEARCH.parent

# research/code holds `store_path`, the one module that knows where the (separate, multi-GB)
# lattice ensemble store lives. Every owner script resolves it for itself too; this driver
# resolves it once and hands the same answer to all of them (see `_env`).
sys.path.insert(0, str(RESEARCH / "code"))
import store_path                                 # noqa: E402  -- needs the path above
DATA, CERT = HERE, RESEARCH / "code" / "certify"

# artifact(s)                                    owner script                              dir   phase      cost
OWNERS = [
    (["8_3_dat_ksignal_planescale.csv"],         "8_3_run_ksignal_planescale.py",          DATA, "data",    "cpu"),
    (["8_3_dat_nobump.csv", "8_3_fig_nobump.png"],
                                                 "8_3_regen_from_store.py",                DATA, "data",    "cpu"),
    (["8_3_dat_su3_nobump.csv", "8_3_fig_su3_nobump.png"],
                                                 "8_3_regen_su3_from_store.py",            DATA, "data",    "cpu"),
    (["8_3_dat_confinement_order_parameter.csv"],
                                                 "8_3_run_confinement_order_parameter.py", DATA, "data",    "cpu"),
    (["8_4_dat_disorder_response.csv", "8_4_fig_disorder_response.png"],
                                                 "8_4_regen_from_store.py",                DATA, "data",    "cpu"),
    # `--mode full` is the configuration the committed table was measured at (six masses, 8x8x64,
    # n=40); the script's own default is the coarse `quick` run.  The reproduction recipe is part
    # of the provenance, so it is recorded here rather than left to whoever types the command.
    (["8_5_dat_gap_calibration.csv", "8_5_fig_gap_calibration.png"],
                                                 "8_5_run_gap_calibration.py --mode full",  DATA, "data",   "cpu"),
    (["8_6_dat_benchmark.csv", "8_6_fig_benchmark.png"],
                                                 "8_6_run_benchmark.py",                   DATA, "data",    "cpu"),
    (["8_6_dat_probe.csv"],                      "8_6_run_probe.py",                       DATA, "data",    "cpu"),
    # APE-smears 512 SU(2) link configurations through the generator backend (`_Backend(DEV)`),
    # four smearing levels deep. It was written for CUDA and its DEV default said so. On the
    # CPU it took 40 min to finish one of the four levels, and they get heavier: this is a gpu
    # job, and calling it cpu2h sent it to a host that could only crawl through it.
    (["8_7_dat_transfer_gap.csv", "8_7_dat_transfer_pencil.csv", "8_7_dat_meta.csv"],
                                                 "8_7_run_transfer_gap.py",                DATA, "data",    "gpu"),
    (["8_7_dat_mhi_lscan.csv"],                  "8_7_run_mhi_lscan.py",                   DATA, "data",    "long"),
    (["8_7_dat_mhi_multicoupling.csv"],          "8_7_run_mhi_multicoupling.py",           DATA, "data",    "cpu2h"),
    (["9_1_dat_d2_bound.csv", "9_1_fig_d2_bound.png"],
                                                 "9_1_run_d2_bound.py",                    DATA, "data",    "cpu2h"),
    (["9_1_dat_d2_certified.csv", "9_1_fig_d2_certified.png"],
                                                 "9_1_run_d2_certify.py",                  DATA, "data",    "cpu2h"),
    (["9_1_dat_d2_su3.csv", "9_1_fig_d2_su3.png"],
                                                 "9_1_run_d2_su3.py",                      DATA, "data",    "cpu2h"),

    # Figures drawn FROM the CSVs above, so they run after the data phase.
    (["8_6_fig_probe.png"],                      "8_6_fig_probe.py",                       DATA, "figures", "cpu"),
    (["8_7_fig_mhi_lscan.png"],                  "8_7_fig_mhi_lscan.py",                   DATA, "figures", "cpu"),
    (["8_7_fig_transfer_gap.png"],               "8_7_fig_transfer_gap.py",                DATA, "figures", "cpu"),

    # Certifications print a verdict; none of them writes a committed artifact. The string tension
    # did, so it moved to research/data as 8_8_run_string_tension.py -- a measurement that emits
    # tables belongs with the other 8_x producers, not among the verdict printers.
    ([],                                         "interval_enclosure.py",                  CERT, "certify", "cpu"),
    ([],                                         "small_volume_enclosure.py",              CERT, "certify", "cpu"),
    ([],                                         "beta_star_enclosure.py",                 CERT, "certify", "cpu"),
    # gap_of_margin and gap_of_maximal_correlation were SIGKILLed (rc=-9, cgroup oom_kill) at the
    # cpu2h envelope of 8 GB; they are Koopman-splice readers like the two below, so they are bigmem.
    # gap_of_margin.py now writes data/9_2_dat_margin_aperture.csv (the table it has always printed;
    # Sec 12 transcribes it by hand and nothing could check that). Add it to this row's artifact list
    # once the first regenerated copy is committed -- listing it before then breaks the invariant that
    # OWNERS never promises an artifact git does not carry (test_every_listed_artifact_is_actually_tracked).
    (["9_2_dat_margin_aperture.csv"],            "gap_of_margin.py",                       CERT, "certify", "bigmem"),    # lean_axiom_footprints.py runs `lake build` and writes data/13_dat_axiom_footprints.csv --
    # the footprint table Sec 13 states, captured from the build instead of left in its log. Add
    # the artifact to this row once the first generated copy is committed (listing it earlier
    # breaks test_every_listed_artifact_is_actually_tracked).
    (["13_dat_axiom_footprints.csv"],            "lean_axiom_footprints.py",               CERT, "certify", "build"),    ([],                                         "gap_of_maximal_correlation.py",          CERT, "certify", "bigmem"),
    # Writes data/9_3_dat_crossover_grid.csv (the dense-beta <d^2> grid and its 99.9% empirical-
    # Bernstein uppers). Add it to this row once the first generated copy is committed.
    (["9_3_dat_crossover_grid.csv"],             "ym_crossover_confinement_of_grid.py",    CERT, "certify", "cpu"),    # timed out at 7200s with work still to do -- it is a long job, not an 8 GB one.
    # Writes data/9_4_dat_interior_mixing_grid.csv (the dense-beta rho'(1) grid and its one-sided
    # 99.9% uppers). Add it to this row once the first generated copy is committed.
    (["9_4_dat_interior_mixing_grid.csv"],       "interior_mixing_of_analytic_grid.py",    CERT, "certify", "long"),    # Writes data/9_6_dat_gap_refinement.csv (Delta and a_delta per group/beta/L, with the
    # resolved|weak|gapless|unresolved tag). Add it once the first copy is committed.
    ([],                                         "gap_refinement_invariant.py",            CERT, "certify", "bigmem"),
    # Writes data/9_5_dat_apriori_a1.csv (the A1 conjunction table: Delta(L) per ensemble, and
    # mu / contrast / K_signal at L=16). Add it to this row once the first copy is committed.
    ([],                                         "apriori_A1.py",                          CERT, "certify", "bigmem"),
    # Writes data/9_7_dat_centre_dominance.csv (Inputs 3 and 4: rho'_coset(1) and sigma_Z/sigma
    # per beta). Add it to this row once the first generated copy is committed.
    (["9_7_dat_centre_dominance.csv"],           "string_tension_eq_centre.py",            CERT, "certify", "gpu"),    # Reads the archived L=16 SU(2) links (configs_links_su2, dataset [D]); it does not generate its
    # own L=8 ensemble. L=8 caps R at L/2=4, leaving three points for the three-parameter potential
    # fit V0 + sigma R - e/R -- an exactly-determined system whose slope carries no information, and
    # the script refuses it outright. Defaults ARE the committed configuration (source=links,
    # beta=2.30, NSMEAR=24), so a bare run reproduces both tables.
    # The raw correlator every Sec 8.6-8.7 gap number is extracted from, measured with no read on
    # top of it. Owned because the finding that it carries no plateau is a MEASUREMENT, and a
    # measurement that lives only in prose is not reproducible.
    (["8_7_dat_gap_correlator.csv"],             "8_7_run_gap_correlator.py",              DATA, "data",    "gpu"),
    (["8_7_fig_gap_correlator.png"],             "8_7_fig_gap_correlator.py",              DATA, "figures", "cpu"),
    (["8_8_dat_string_tension.csv", "8_8_dat_string_tension_curves.csv"],
                                                 "8_8_run_string_tension.py",              DATA, "data",    "gpu"),
    (["8_8_fig_string_tension.png"],             "8_8_fig_string_tension.py",              DATA, "figures", "cpu"),

    # Not a paper section: this one measures the DATA RELEASE. For every ensemble it differences
    # the mean action density the shards ship against an equilibrium measured here, so that
    # "these are equilibrium samples" is an executable claim rather than a statement in prose.
    # `therm` records the sweeps a campaign ran; the sweeps required grow with beta and volume, so
    # adequacy is established per ensemble by this measurement.
    (["store_dat_thermalisation.csv"],           "store_run_thermalisation.py",            DATA, "data",    "gpu"),
]

# `build` is a Lean/Mathlib compile, not a read: it needs the toolchain and a warm .lake, and it
# is gated like the other heavy classes so a plain regeneration never starts one by surprise.
HEAVY = {"bigmem", "gpu", "build"}
BUDGET = {"cpu": 1800, "cpu2h": 7200, "long": 28800, "bigmem": 28800, "gpu": 14400,
          "build": 28800}
PHASES = ("data", "figures", "certify")

# Peak resident memory a job in each class needs, in GB. Measured (VmHWM) rather than estimated:
# a value that is too low here takes the host down rather than failing a job.
# The Koopman splice carries a dense F x F operator, F = 13824 at L=16, with several live at once
# over the whole ensemble, and that is what makes `bigmem` what it is.
#
# Peaks observed on 2026-08-22, the first runs instrumented to record them, on a 108 GB host where
# every one of these jobs could reach the end of its work:
#
#     gap_of_margin              60.2 GB   exit 0
#     gap_of_maximal_correlation 62.2 GB   ran all four checks, exit 1 on the verdict
#     apriori_A1                 64.2 GB   read every ensemble, then refused a partial table
#
# The last two exit non-zero but did their whole computation first and refused at the write, so the
# figures are real measurements of what the job holds, not the ~1 GB a job shows when it refuses
# early (gap_refinement_invariant does exactly that, and its number must never be used for sizing).
#
# All three are above the 56.0 this class carried before, and the largest is above the 64.0 it
# carried for a few hours after the first correction. A host sized by 56 + 6 reserve = 62 GB would
# have admitted every one of them and been OOM-killed by two -- which is precisely what happened to
# apriori_A1 on a 57 GB pod. 72 sits above every observation with room; it is a ceiling to raise
# again the moment a run exceeds it, not a number to trust because it is written down.
#
# For scale: a workstation with ~18 GB free cannot run `bigmem`, and the refusal says so before the
# job starts rather than after the kernel intervenes.
NEED_GB = {"cpu": 2.0, "cpu2h": 8.0, "long": 8.0, "bigmem": 72.0, "gpu": 8.0, "build": 16.0}

# Per-job peaks, and ONLY ones this repo has watched a job reach. A job absent here falls back to
# its class and is refused more readily, not less, which is the safe direction.
#
# The figures that used to live in the comment above -- apriori_A1 25.0, gap_refinement_invariant
# 49.3 -- are not in this table, because instrumenting the runs disproved them. On 2026-08-22
# apriori_A1 was admitted to a 57 GB host on the strength of the 25.0 figure and was OOM-killed at
# 57.6 GB, and gap_of_margin, sized by the class at 56, peaked at 60.2. Both prose numbers were low,
# one of them by more than a factor of two. Sizing against an unverified number is how a preflight
# admits a job it should refuse, so the rule here is: measured by `_run_with_peak` on a run that
# COMPLETED, or absent.
#
NEED_GB_JOB = {"gap_of_margin.py": 60.2, "gap_of_maximal_correlation.py": 62.2,
               "apriori_A1.py": 64.2}

# Left for the operating system and everything else on the box. A regeneration that takes the
# machine down has not regenerated anything.
RESERVE_GB = 6.0


def _run_with_peak(cmd, cwd, env, stdout, timeout):
    """Run a job to completion; return (returncode, peak resident GB or None).

    The peak is read from the child's own `/proc/<pid>/status`. `VmHWM` is a high-water mark the
    kernel maintains, not an instantaneous sample, so polling cannot miss a spike between samples --
    only one reached after the last sample before the process exits. The interval backs off from 50
    ms to a second, because a job that finishes in under a second is otherwise never sampled at all
    and reports no peak, while an eight-hour job does not need a sample every 50 ms. Where /proc is
    absent the peak is None and the job still runs; a missing measurement is reported as missing
    rather than as zero.

    This is what keeps NEED_GB and NEED_GB_JOB honest: a class figure nobody has re-measured drifts
    away from what the jobs in it actually do, in whichever direction happens to be wrong.
    """
    proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=stdout,
                            stderr=subprocess.STDOUT, text=True)
    status = Path("/proc/%d/status" % proc.pid)
    peak, deadline, wait = None, time.time() + timeout, 0.05
    while True:
        try:
            rc = proc.wait(timeout=wait)
            break
        except subprocess.TimeoutExpired:
            wait = min(1.0, wait * 1.5)
        try:
            for line in status.read_text().splitlines():
                if line.startswith("VmHWM:"):
                    peak = max(peak or 0.0, int(line.split()[1]) / 1024 ** 2)
                    break
        except (OSError, ValueError, IndexError):
            pass
        if time.time() > deadline:
            proc.kill()
            proc.wait()
            raise subprocess.TimeoutExpired(cmd, timeout)
    return rc, peak


def _reclaimable(stat: "Path", key: str) -> int:
    """Page cache in this cgroup the kernel can evict on demand, in bytes; 0 when unreadable.

    A cgroup's usage counts page cache, which is not memory a job is denied: under pressure the
    kernel drops it. A pod holding 12 GB of cache under a 57 GB limit has 57 GB available, not 45,
    and sizing against the smaller figure refuses jobs that would run. Inactive file pages are the
    conservative part of that -- the same quantity /proc/meminfo's MemAvailable credits in full.
    """
    try:
        for line in stat.read_text().splitlines():
            name, _, value = line.partition(" ")
            if name == key:
                return int(value)
    except (OSError, ValueError):
        pass
    return 0


def _cgroup_available_gb() -> float | None:
    """Memory this CONTAINER may still use, in GB, or None when not containerised.

    Inside a container `/proc/meminfo` reports the host, so a pod advertising 251 GB may be limited
    to 57 GB by its cgroup. Sizing a job against the host figure gets it OOM-killed, so the cgroup
    limit is the one read here: v2 first, then v1. A limit at or above the host's total is not a
    limit, and is reported as not containerised."""
    for lim, use, stat, key in (
            (Path("/sys/fs/cgroup/memory.max"), Path("/sys/fs/cgroup/memory.current"),
             Path("/sys/fs/cgroup/memory.stat"), "inactive_file"),
            (Path("/sys/fs/cgroup/memory/memory.limit_in_bytes"),
             Path("/sys/fs/cgroup/memory/memory.usage_in_bytes"),
             Path("/sys/fs/cgroup/memory/memory.stat"), "total_inactive_file")):
        try:
            raw = lim.read_text().strip()
            if raw == "max":
                return None
            limit = int(raw)
            if limit >= 2 ** 62:                      # "no limit" spelled as a huge number
                return None
            used = int(use.read_text().strip())
            return max(0.0, (limit - used + _reclaimable(stat, key)) / 1024 ** 3)
        except (OSError, ValueError):
            continue
    return None


def _available_gb() -> float | None:
    """Memory a job may actually use here, in GB, or None where it cannot be read.

    No psutil dependency. The cgroup limit wins wherever there is one, because that is the number
    the kernel enforces. Returning None means 'unknown', and an unknown envelope is treated as a
    refusal for the heavy classes rather than as permission."""
    try:
        if sys.platform.startswith("linux"):
            cg = _cgroup_available_gb()
            if cg is not None:
                return cg
            for line in Path("/proc/meminfo").read_text().splitlines():
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) / 1024 ** 2
        elif sys.platform.startswith("win"):
            import ctypes

            class _MS(ctypes.Structure):
                _fields_ = [("dwLength", ctypes.c_ulong), ("dwMemoryLoad", ctypes.c_ulong),
                            ("ullTotalPhys", ctypes.c_ulonglong), ("ullAvailPhys", ctypes.c_ulonglong),
                            ("ullTotalPageFile", ctypes.c_ulonglong), ("ullAvailPageFile", ctypes.c_ulonglong),
                            ("ullTotalVirtual", ctypes.c_ulonglong), ("ullAvailVirtual", ctypes.c_ulonglong),
                            ("ullAvailExtendedVirtual", ctypes.c_ulonglong)]
            m = _MS()
            m.dwLength = ctypes.sizeof(_MS)
            if ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m)):
                return m.ullAvailPhys / 1024 ** 3
    except Exception:
        pass
    return None


def _usable_cpus() -> int:
    """Cores this container may actually use -- the cgroup CPU quota where there is one.

    `os.cpu_count()` reports the HOST: a pod showing 48 cores can be quota'd to 10. Sizing a BLAS
    pool from the host count oversubscribes by 5x and every thread then fights for the same slice."""
    for quota, period in ((Path("/sys/fs/cgroup/cpu.max"), None),
                          (Path("/sys/fs/cgroup/cpu/cpu.cfs_quota_us"),
                           Path("/sys/fs/cgroup/cpu/cpu.cfs_period_us"))):
        try:
            if period is None:                                  # cgroup v2: "<quota> <period>"
                q, p = quota.read_text().split()
                if q == "max":
                    break
                return max(1, int(float(q) / float(p)))
            q = int(quota.read_text().strip())
            if q > 0:
                return max(1, int(q / int(period.read_text().strip())))
        except (OSError, ValueError):
            continue
    # No quota. `os.cpu_count()` is still the wrong number: it counts every CPU on the machine,
    # ignoring the affinity mask this process is confined to -- a pod allocated 16 of 128 cores
    # reports 128, and a BLAS pool sized from it oversubscribes 8x. `sched_getaffinity` is what
    # `nproc` reads, and it is the count that is actually schedulable here.
    try:
        return max(1, len(os.sched_getaffinity(0)))
    except AttributeError:                                  # not Linux
        return os.cpu_count() or 4


def _env(threads: int) -> dict:
    """One store root drives the whole tree, UTF-8 output, and a bounded thread pool.

    The thread cap is the other half of the envelope. Every read here is BLAS-bound, and the BLAS
    default is one thread per core -- so several of these at full width, on top of the arrays they
    allocate, is how a regeneration takes a workstation down instead of finishing on it. All four
    common vendor variables are set, because which one is honoured depends on the wheel."""
    e = dict(os.environ)
    # The store root is resolved ONCE here, by store_path (CONFIGS, then the git-ignored local
    # config file, then nothing), and handed to every child so the whole regeneration reads one
    # store even where the child would have resolved it itself. Nothing is set when nothing is
    # configured: the child then refuses with the resolver's own message, which names the data
    # release and says it is a separate download -- better than this process guessing a path.
    _store = store_path.store_root(required=False)
    if _store:
        e.setdefault("CONFIGS", _store)
    e.setdefault("PYTHONIOENCODING", "utf-8")
    for var in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS",
                "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
        e[var] = str(threads)
    return e


def _key_columns(header, rows):
    """The shortest leading run of columns that identifies a row uniquely, or None.

    Rows are matched on this rather than on position, because comparing the Nth row of one file
    against the Nth of another turns a REORDER into a screenful of enormous bogus deltas -- which
    is exactly what a positional compare reported here once (a 12x "change" that was really 0.2)."""
    for k in range(1, len(header) + 1):
        keys = [tuple(r[:k]) for r in rows]
        if len(set(keys)) == len(keys):
            return k
    return None


def _cells_moved(head_bytes: bytes, live_bytes: bytes):
    """(cells changed, worst relative change) between two CSVs, compared BY VALUE.

    Line endings and float formatting are not results; a moved number is. A byte comparison reports
    every file whose writer disagrees about newlines, which buries the one row that actually moved --
    a failure this repo already hit."""
    A = list(csv.reader(head_bytes.decode("utf-8", "replace").splitlines()))
    B = list(csv.reader(live_bytes.decode("utf-8", "replace").splitlines()))
    if not A or not B:
        return None, "EMPTY file"
    head, ra, rb = A[0], A[1:], B[1:]
    if A[0] != B[0]:
        return None, f"HEADER {A[0]} -> {B[0]}"

    k = _key_columns(head, ra)
    if k is None or _key_columns(head, rb) is None:
        if len(ra) != len(rb):                       # no usable key and different lengths
            return None, f"SHAPE {len(ra)} -> {len(rb)} rows"
        pairs = zip(ra, rb)                          # fall back to position, as a last resort
        gone = added = []
    else:
        ma = {tuple(r[:k]): r for r in ra}
        mb = {tuple(r[:k]): r for r in rb}
        gone, added = sorted(set(ma) - set(mb)), sorted(set(mb) - set(ma))
        pairs = [(ma[key], mb[key]) for key in sorted(set(ma) & set(mb))]

    # Scale for the "is this cell actually zero" test: the largest magnitude anywhere in the file.
    # A relative comparison alone calls 1.15e-15 -> 1.87e-15 a 63% change, when both are numerically
    # zero and the difference is the last bit of a quantity the read returns as zero. Judging those
    # against the artifact's own scale is what separates a moved number from arithmetic noise.
    scale = 0.0
    for row in list(pairs) if isinstance(pairs, list) else []:
        for cell in row[0]:
            try:
                scale = max(scale, abs(float(cell)))
            except ValueError:
                pass
    atol = scale * 1e-12

    n, worst = 0, 0.0
    for x, y in pairs:
        for ca, cb in zip(x, y):
            if ca == cb:
                continue
            try:
                fa, fb = float(ca), float(cb)
            except ValueError:
                n += 1
                worst = float("inf")
                continue
            if abs(fa - fb) <= atol:        # both at the artifact's zero -- not a moved number
                continue
            n += 1
            worst = max(worst, abs(fa - fb) / max(abs(fa), atol, 1e-30))
    if gone or added:
        return None, (f"ROWS {len(ra)} -> {len(rb)}; {len(gone)} dropped, {len(added)} new"
                      + (f" (e.g. dropped {gone[0]})" if gone else "")
                      + (f" (e.g. new {added[0]})" if added else ""))
    return n, worst


def verify() -> int:
    """Compare every committed artifact against git HEAD. Regenerates nothing."""
    moved = same = 0
    # `d` is the owner's working directory, not its artifact root: every committed artifact lives
    # under research/data, while `d` is only where the owner runs. Keeping the two separate is what
    # allows a certification that lives in research/code/certify to write its table to the data
    # directory with the rest.
    for arts, _owner, _d, _phase, _cost in OWNERS:
        for a in arts:
            rel = (DATA / a).relative_to(REPO).as_posix()
            head = subprocess.run(["git", "show", "HEAD:" + rel], cwd=REPO, capture_output=True)
            if head.returncode != 0:
                print("  %-42s not tracked in HEAD" % a)
                continue
            if not (DATA / a).exists():
                print("  %-42s MISSING from the working tree" % a)
                moved += 1
                continue
            live = (DATA / a).read_bytes()
            if a.endswith(".png"):
                ok = hashlib.sha256(head.stdout).digest() == hashlib.sha256(live).digest()
                print("  %-42s %s" % (a, "identical" if ok else "DIFFERS (figure bytes)"))
                same, moved = same + ok, moved + (not ok)
                continue
            n, worst = _cells_moved(head.stdout, live)
            if n is None:
                print("  %-42s %s" % (a, worst))
                moved += 1
            else:
                print("  %-42s %s" % (a, "identical" if not n
                                      else "%d cell(s) moved, max rel %.2e" % (n, worst)))
                same, moved = same + (not n), moved + bool(n)
    print("\n%d unchanged, %d changed" % (same, moved))
    return 1 if moved else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--list", action="store_true", help="show the owner table and exit")
    ap.add_argument("--verify", action="store_true", help="compare artifacts to git HEAD; run nothing")
    ap.add_argument("--phase", choices=PHASES)
    ap.add_argument("--only", default="", help="substring match on the owner script name")
    ap.add_argument("--include-heavy", action="store_true", help="also run bigmem/gpu jobs")
    ap.add_argument("--reserve-gb", type=float, default=RESERVE_GB,
                    help="physical memory left for the host; a job needing more than what remains "
                         "is refused rather than started (default %(default)s)")
    ap.add_argument("--max-threads", type=int, default=None,
                    help="BLAS threads per job (default: cores - 2). Every read here is BLAS-bound, "
                         "so this is what keeps a regeneration from saturating the machine.")
    args = ap.parse_args()

    if args.list:
        # An empty artifact list means "nothing committed for this owner yet", which is not the
        # same as "writes nothing": gap_of_margin.py and lean_axiom_footprints.py both emit a
        # table whose first generated copy has not been committed, so it cannot be listed here
        # without breaking test_every_listed_artifact_is_actually_tracked.
        blank = {"certify": "(no committed artifact; prints its verdict)"}
        print("  %-40s %-8s %-7s %s" % ("owner", "phase", "cost", "artifacts"))
        for arts, owner, _d, phase, cost in OWNERS:
            print("  %-40s %-8s %-7s %s" % (owner, phase, cost,
                                            ", ".join(arts) or blank.get(phase, "")))
        return 0
    if args.verify:
        return verify()

    jobs = [j for j in OWNERS if (not args.phase or j[3] == args.phase) and args.only in j[1]]
    skipped = [(j, "class %s needs --include-heavy" % j[4])
               for j in jobs if j[4] in HEAVY and not args.include_heavy]
    jobs = [j for j in jobs if j not in [s[0] for s in skipped]]

    threads = args.max_threads or max(1, _usable_cpus() - 2)
    avail = _available_gb()
    print("envelope: %d BLAS thread(s)/job, %s free, keeping %.0f GB for the host"
          % (threads, "%.1f GB" % avail if avail else "free memory unknown", args.reserve_gb))

    failed, ran, t0 = [], 0, time.time()
    for job in jobs:
        _arts, owner, d, _phase, cost = job
        script, *extra = owner.split()  # an owner may carry the arguments it must be run with
        need = NEED_GB_JOB.get(script, NEED_GB[cost])
        avail = _available_gb()
        if avail is not None and avail < need + args.reserve_gb:
            # Refuse BEFORE starting. A job that exhausts the host does not fail cleanly -- it takes
            # the machine with it, and nothing that was running gets to report anything.
            skipped.append((job, "needs ~%.0f GB + %.0f GB reserve, only %.1f GB free"
                            % (need, args.reserve_gb, avail)))
            print("  %-40s SKIP  %.1f GB free < %.0f GB needed" % (owner, avail, need + args.reserve_gb),
                  flush=True)
            continue
        st = time.time()
        # Stream to a per-job file rather than capturing in memory. A job killed by the OOM killer
        # takes its buffered output with it, so `capture_output` leaves nothing to say WHERE it
        # died, and that is the run whose output matters most. `-u` for the same reason:
        # a job that dies mid-sweep should still have told you which row it reached.
        logdir = REPO / "logs"
        logdir.mkdir(exist_ok=True)
        logf = logdir / (script.replace(".py", "") + ".log")
        peak = None
        try:
            with open(logf, "w", encoding="utf-8", errors="replace") as fh:
                rc, peak = _run_with_peak([sys.executable, "-u", script, *extra], cwd=d,
                                          env=_env(threads), stdout=fh, timeout=BUDGET[cost])
        except subprocess.TimeoutExpired:
            rc = 124
        except MemoryError:
            rc = 137
        out = logf.read_text(encoding="utf-8", errors="replace") if logf.exists() else ""
        err = ("timed out after %ds (cost class %s)" % (BUDGET[cost], cost) if rc == 124 else
               "the host ran out of memory" if rc in (137, -9) else "")
        ran += 1
        tail = (out or err).strip().splitlines()
        # The measured peak is printed beside the result, and against what the job was sized for, so
        # a class figure that no longer matches its jobs is visible in the run that shows it. A job
        # that failed is marked: `gap_refinement_invariant` refuses a partial sweep in seconds and
        # peaks at ~1 GB doing it, which is not remotely what the job needs when it runs, and a
        # number like that must never be mistaken for a measurement worth sizing against.
        if peak is None:
            mark = "peak unknown"
        elif rc:
            mark = "peak %.1f GB (FAILED run)" % peak
        else:
            mark = "peak %.1f GB / %.0f sized" % (peak, need)
        print("  %-40s rc=%-3d %6.0fs  %-22s %s" % (owner, rc, time.time() - st, mark,
                                                    tail[-1][:60] if tail else ""), flush=True)
        if rc:
            failed.append(owner)
            print(out[-1200:], err[-1200:], sep="\n")

    print("\n%d ran, %d failed, %d skipped, %.0fs total"
          % (ran, len(failed), len(skipped), time.time() - t0))
    if skipped:
        # Skips are reported, so the summary distinguishes a job that ran from one that did not.
        print("\nSKIPPED (%d) -- run these on a host that fits:" % len(skipped))
        for job, why in skipped:
            print("  %-40s %s" % (job[1], why))
    if failed:
        print("\nFAILED: " + ", ".join(failed))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
