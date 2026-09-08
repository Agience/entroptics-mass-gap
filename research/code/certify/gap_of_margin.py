"""gap_of_margin.py -- the two deterministic runtime certificates behind A1, read on real
lattice configs through the WRAPPER (never the library; never the i.i.d.-Gaussian floor).

It answers two questions the paper's A1 rests on, with data:

  1. C-1 (soft, `ym_finite_corr_length`):  the whitened :F^2: tension `mu = log(contrast)` stays below the
     entropy floor `kappa0 = 1/4 ln 3`  <=>  contrast < 3^(1/4).  Measured `mu ~ 0` (contrast < 1, the
     leading feature mode sits below the pinned confined-vacuum floor) in BOTH the gapped and gapless
     phases -- so C-1 is a locality property of the dimension-4 operator, NOT the confinement discriminator.

  2. The LOAD-BEARING finite-aperture certificate:  the temporal forgetting margin `m_hi = e^{-Delta}` (the
     cosh `mass_gap` Delta) below `3^{-1/4}`.  This IS confinement, and it tracks the phase directly:

        "Why does U(1) fail?"  -- NOT a code/setup artifact.  The SAME U(1) reading pipeline reads a
        FINITE aperture in the confined phase (beta < beta_c ~ 1.01, m_hi ~ 0.14) and an INFINITE one in
        the Coulomb phase (m_hi ~ 1).  A setup artifact would read white in both phases; it does not.
        SU(N) is confining at every beta, so it reads finite aperture throughout.

Both certificates feed `lean/MassGap/Certify.lean` (`gap_of_margin_certified`) and, taken as the runtime
read `hconf`, discharge every Entroptics-specific axiom in `lean/MassGap/Complete.lean`
(`yang_mills_mass_gap_certified`: footprint = the three foundational + the cited `wilson_reflection_positive`).

Deterministic (no RNG in the reads).  Light: seconds on CPU -- these are reads, not Monte-Carlo generation.
Point the loader at the config store with  CONFIGS=/path/to/entroptics-lattice  python gap_of_margin.py,
or set CONFIGS once for the machine in the git-ignored local config file at the repository root.
"""
from __future__ import annotations

import csv
import glob
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code (parent of certify/)
import entroptics_adapter as W  # THE WRAPPER (research/code/entroptics_adapter.py); reads go through the front door
import store_path               # the ONE place the ensemble store is located

KAPPA0 = 0.25 * math.log(3.0)          # entropy floor, 1/4 ln 3
CRIT = 3.0 ** 0.25                     # contrast threshold e^{kappa0} = 3^(1/4) ~ 1.3161
THR_M = math.exp(-KAPPA0)              # aperture margin threshold 3^{-1/4} ~ 0.7598

# The measured table is persisted as well as printed. This is a bigmem read (it was OOM-killed at
# the 8 GB cpu2h envelope), so re-running it to re-check a number the paper quotes is not cheap;
# every value Sec 9 and Sec 12 source from this program reaches PAPER.md by hand from the stdout
# table, and without an artifact nothing can check the transcription.
OUT_CSV = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                       "data", "9_2_dat_margin_aperture.csv")

# The store root from ``store_path``: CONFIGS, then the git-ignored local config file, then a
# refusal -- never a path baked into this file. ``None``/``[]`` when nothing is configured rather
# than an exception, because the smoke tests import this module (and redirect HOPS) on machines
# with no store; the refusals below carry ``store_path.hint()``, which distinguishes "no store
# configured" from "configured, but it does not hold this".
ROOT = store_path.store_root(required=False)
HOPS = store_path.collections("configs_phase1", "configs_betasweep", "configs_links_su2_density",
                              "configs_paper83")


def load(group: str, L: int, beta: float, ncap: int = 128):
    """Every shard for one (group, L, beta) across ALL hops, capped at ncap; None if absent.

    This pools across every hop. A first-hop read would
    return at the first hop that matched, so a coupling's ensemble depended on the order of `HOPS`
    rather than on what the store holds. `aperture_reads.load_su2`, `9_1_run_d2_certify` and
    `gap_refinement_invariant` all pool, and this was the last §9 reader that did not.

    For the eight ensembles this script actually reads the two agree exactly -- checked shard by
    shard, first-hop and pooled give the same config counts at all eight -- so the change is inert
    on today's store and `9_2_dat_margin_aperture.csv` is unaffected. It is made so that the readers
    cannot drift apart again when a hop or an ensemble is added.
    """
    fs = []
    for h in HOPS:
        fs += sorted(glob.glob(f"{h}/{group}_L{L}_b{beta:.2f}.s*.npy"))
    if not fs:
        return None

    # Read only as far as `ncap`, straight into the array that is returned. Reading every shard and
    # concatenating before slicing costs the whole ensemble twice over in float32 on top of the
    # result -- at L=32 that is 4.2 GB of churn to keep 48 configurations -- and the shards past the
    # cap are never looked at. `mmap_mode` opens a shard without reading it, so the only pass over
    # the bytes is the assignment below, which converts to float64 as it copies.
    #
    # The shard order and the configurations taken are exactly those the slice-after-concatenate
    # form selected: the same `fs` in the same order, the same leading `ncap`.
    parts, total = [], 0
    for f in fs:
        if total >= ncap:
            break
        a = np.load(f, mmap_mode="r")
        take = min(a.shape[0], ncap - total)
        parts.append((a, take))
        total += take

    out = np.empty((total,) + parts[0][0].shape[1:], dtype=np.float64)
    at = 0
    for a, take in parts:
        out[at:at + take] = a[:take]
        at += take
    return out


def pin_confined_vacuum():
    """Pin the caller-supplied null to the deep-confinement su2 beta=0.50 vacuum (the disorder floor).
    The wrapper never falls back to the library's i.i.d.-Gaussian 'mp' floor for a physics read."""
    ref = []
    for L in (8, 12, 16):
        a = load("su2", L, 0.50, ncap=48)
        if a is not None:
            ref += list(a)
    if not ref:
        raise SystemExit(f"no su2 b0.50 reference under {ROOT or '<no store configured>'} -- cannot pin the confined-vacuum null"
                         f"\n{store_path.hint()}")
    W.pin_reference(ref)
    return len(ref)


# (group, beta, L, phase label) -- includes U(1) on both sides of its deconfinement transition.
# The U(1) rows are read at L=8, which is the volume the released U(1) ensembles are held at and the
# one Sec 8.3's K_signal transition is measured on, so the two U(1) statements the paper makes rest
# on the same configurations. `configs_paper83` is in HOPS for them; it carries no su2 or su3
# ensemble this table names, so the five SU(N) rows read exactly what they read without it.
#
# The largest SU(2) volume this read reaches is L=24. The read's peak resident set is set by the
# lattice volume rather than by the number of configurations: at L=32 it holds ~22.5 GB for 12
# configurations (a 0.19 GB array) and ~22.7 GB for 48, so reading fewer does not bring it down and
# there is no configuration count at which L=32 fits in 23 GB. The L=32 transfer magnitude is
# reported in Sec 8.7, where the connected-DMD tower reads it directly; that reader and this one
# agree to six figures at L=16 (0.31353) and L=24 (0.341559), which is what ties the two together.
ENSEMBLES = [
    ("su2", 0.50, 16, "confined (strong)"),
    ("su2", 2.30, 16, "confined (scaling)"),
    ("su2", 2.30, 24, "confined (scaling)"),
    ("su3", 6.00, 12, "confined"),
    ("u1", 0.90, 8, "U(1) CONFINED  b<bc"),
    ("u1", 1.70, 8, "U(1) Coulomb   b>bc"),
    ("u1", 2.50, 8, "U(1) Coulomb   b>bc"),
]


def main():
    nref = pin_confined_vacuum()
    print(f"pinned confined-vacuum null: {nref} su2 b0.50 planes")
    print(f"kappa0 = 1/4 ln3 = {KAPPA0:.4f}    C-1: mu<kappa0  <=>  contrast < 3^(1/4) = {CRIT:.4f}")
    print(f"finite-aperture margin threshold  m_hi = e^-Delta < 3^(-1/4) = {THR_M:.4f}\n")
    print(f"{'group':>4} {'beta':>5} {'L':>3} {'n':>4} {'phase':>20} | "
          f"{'mu(C-1)':>8} {'contr':>6} {'mu<k0':>6} | {'Delta':>6} {'m_hi':>6} {'aperture':>9}")
    rows = []          # the measured table -- the verdict below is derived from THIS
    for group, beta, L, phase in ENSEMBLES:
        arr = load(group, L, beta)
        if arr is None:
            print(f"  {group} b{beta} L{L}: (absent)")
            continue
        r = W.run(list(arr), time_axis=-1)
        mu = float(r.attenuation)          # feature-side tension mu = log(contrast) (C-1)
        contrast = float(r.contrast)       # leading feature-mode coherence vs the pinned floor
        delta = float(r.mass_gap)          # the gap Delta = dominant operator mode rate -log|mu_1|
        m_hi = math.exp(-delta) if delta > 0 else 1.0
        c1 = "PASS" if mu < KAPPA0 else "FAIL"
        aperture = "finite" if m_hi < THR_M else "INFINITE"
        print(f"{group:>4} {beta:>5.2f} {L:>3} {arr.shape[0]:>4} {phase:>20} | "
              f"{mu:>8.4f} {contrast:>6.3f} {c1:>6} | {delta:>6.3f} {m_hi:>6.3f} {aperture:>9}")
        rows.append(dict(group=group, beta=beta, L=L, ncfg=int(arr.shape[0]), phase=phase,
                         mu=mu, contrast=contrast, c1=c1, delta=delta, m_hi=m_hi,
                         aperture=aperture))
    # The verdict is derived from the rows above, so it reports what this run measured rather than
    # what the read is expected to show.
    n_pass = sum(1 for r in rows if r['c1'] == 'PASS')
    conf = [r for r in rows if 'Coulomb' not in r['phase']]
    coul = [r for r in rows if 'Coulomb' in r['phase']]
    fin = lambda rs: sum(1 for r in rs if r['aperture'] == 'finite')
    print()
    print('C-1 (mu<kappa0): %d/%d rows PASS -- soft :F^2: locality.%s'
          % (n_pass, len(rows), '' if n_pass == len(rows) else '  NOT universal.'))
    print('finite-aperture margin (m_hi < %.4f): confined %d/%d finite, Coulomb %d/%d finite.'
          % (THR_M, fin(conf), len(conf), fin(coul), len(coul)))
    if coul and fin(coul) == 0 and fin(conf) == len(conf):
        print('-> the margin DISCRIMINATES: finite where confined, infinite in the Coulomb phase.')
    elif coul and fin(coul) == len(coul):
        print('-> the margin does NOT discriminate on this data: every Coulomb row reads finite too')
        print('   (m_hi = %s). Here the deconfinement transition is carried by K_signal'
              % ', '.join('%.3f' % r['m_hi'] for r in coul))
        print('   (PAPER Sec 8.3), not by the finite-aperture margin.')
    else:
        print('-> partial: %d of %d Coulomb rows finite.' % (fin(coul), len(coul)))

    if len(rows) != len(ENSEMBLES):
        raise SystemExit("read %d of %d ensembles: refusing to write a partial aperture table\n%s"
                         % (len(rows), len(ENSEMBLES), store_path.hint()))
    with open(OUT_CSV, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)
    print("\nwrote %s (%d ensembles)" % (OUT_CSV, len(rows)))


if __name__ == "__main__":
    main()
