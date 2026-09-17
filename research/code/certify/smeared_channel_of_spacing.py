"""Is there a channel whose correlation length is PHYSICAL rather than UV?

THE QUESTION. Three independent reads now say the :F^2: action-density channel is soft: `mu < kappa0`
holds in both U(1) phases, the contrast sits near 1.04 in both, and the lag moment is contact-scale
-- rms separation 0.38-0.41 SITES, falling with the lattice spacing rather than holding. So the
substrate hypothesis is satisfied for a UV reason, not a gap reason.

The Lean is explicit that this is the caller's problem, not the theorem's: "Which correlation
`wilsonCorrAt` reads is part of supplying the hypothesis, and nothing in this file chooses it." So
the question is whether a DIFFERENT channel on the same configurations carries a length that tracks
physics.

THE TEST. APE-smeared spatial plaquettes -- the 0++ operator Sec 8.7 uses, which carries a decade of
signal where the action density falls into noise by tau ~ 2. Measured at two points of MATCHED
PHYSICAL VOLUME with the spacing 1.34x finer:

    (beta=2.30, L=12)  ->  (beta=2.40, L=16)     L a sqrt(sigma):  4.241 -> 4.213

A length that is PHYSICAL is a fixed number of fermis, so in LATTICE units it grows as the spacing
shrinks: <d^2> should rise by (16/12)^2 = 1.78. A length that is UV sits at a fixed number of SITES
and <d^2> stays flat. The two predictions differ by the whole effect, so the measurement decides it.

These are the only two link ensembles at matched physical volume the store holds, so the comparison
is the one the data allows rather than one selected for its answer.

DERIVED THROUGHOUT. SU(2) links are unit quaternions, so the SU(2) projection APE smearing needs is
exactly quaternion normalisation -- no approximation and no fitted constant. The staple construction
is `lattice_generator`'s, restricted to SPATIAL neighbours because the operator is a spatial
plaquette. The lag moment is the same circle-distance functional the Lean consumes.
"""
from __future__ import annotations

import csv
import glob
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))

import store_path
import aperture_ceiling            # the ceiling, derived in ONE place
import ym_crossover_confinement_of_grid as CG
import lattice_generator as _lg  # the ONE quaternion algebra in the tree
import entroptics_adapter as W   # the wrapper: resampling is the library's, not a local copy

BASE = store_path.store_root(required=False)
LINKS = os.path.join(BASE, "configs_links_su2") if BASE else None

#: CHOSEN: the APE smearing weight, the standard value for SU(2) spatial smearing. It sets how fast
#: the UV is suppressed per sweep, not whether a length is physical -- the test is the RATIO of two
#: points measured at the same weight, so a different weight moves both together.
ALPHA = 0.5

#: CHOSEN: smearing sweeps AT THE COARSE POINT. Reported at several so the answer is not read off
#: one, and so a reader can see the UV being removed rather than being told it was.
SWEEPS = (0, 2, 4, 8)

#: DERIVED from the string tension: a*sqrt(sigma) is 0.3534 at beta=2.30 and 0.2633 at beta=2.40, so
#: the fine lattice is 1.342x finer. A smearing sweep reaches a fixed number of SITES, so holding the
#: reach fixed in PHYSICAL units needs (a_coarse/a_fine)^2 more sweeps on the fine lattice.
#:
#: This is not a detail. Comparing at equal sweep count under-smears the fine point and pushed the
#: ratio from 1.47 to 0.90 -- across the whole gap between the two hypotheses the test distinguishes.
RADIUS_FACTOR = (0.3534 / 0.2633) ** 2

#: DERIVED: a*sqrt(sigma) per coupling, read from the string tension (Sec 8.8). The lattice spacing
#: is what the prediction is written in, so it is carried explicitly rather than inferred from L.
SIG = {2.30: 0.3534, 2.40: 0.2633, 2.50: 0.1991}

#: DERIVED: the matched pairs the LINK ensembles support, coarse first, ordered by how well their
#: physical volumes agree. The first is matched to 0.7%; the second to 11.9%, at a longer lever arm
#: (spacing 1.78x finer rather than 1.34x). Not selected for their answer -- these are the pairs
#: that exist.
PAIRS = (((12, 2.30), (16, 2.40)),
         ((8, 2.30), (16, 2.50)))

#: The first pair, kept as the primary comparison the paper tabulates.
POINTS = PAIRS[0]


# The quaternion algebra is IMPORTED, not restated. Two copies of a multiplication table is two
# chances for a sign convention to drift, and a sign convention is exactly what went wrong once here
# already -- the staple orientation, which made smearing ROUGHEN the field until it was checked.
# `lattice_generator` builds these against a backend, so its numpy backend is used.
_B = _lg._Backend(None)


def _qmul(a, c):
    return _lg._qmul(_B, a, c)


def _qconj(a):
    return _lg._qconj(_B, a)


# DERIVED: `nd` is the spacetime dimension count -- four, the rank of the lattice the links
# live on. It converts a direction index into the array axis that direction occupies,
# counting from the right past the (direction, quaternion) pair. Not a magnitude.
def _spatial_staple(q, mu, nd=4):
    """The staple sum for direction `mu`, over SPATIAL neighbours only.

    `lattice_generator._su2_staple` sums over every nu != mu, including time. The operator here is a
    SPATIAL plaquette, so the smearing that defines it must stay in the spatial hyperplane --
    including the time staples would mix the channel this is trying to isolate.
    """
    A = np.zeros(q.shape[:-2] + (4,), dtype=q.dtype)
    qmu = q[..., mu, :]
    for nu in range(3):                       # spatial directions only
        if nu == mu:
            continue
        ax = nu - nd - 1                      # the axis `nu` occupies, counting from the right
        axmu = mu - nd - 1
        qnu = q[..., nu, :]
        qnu_pmu = np.roll(qnu, -1, axis=axmu)
        A = A + _qmul(_qmul(qnu_pmu, _qconj(np.roll(qmu, -1, axis=ax))), _qconj(qnu))
        A = A + _qmul(_qmul(_qconj(np.roll(qnu_pmu, 1, axis=ax)),
                            _qconj(np.roll(qmu, 1, axis=ax))), np.roll(qnu, 1, axis=ax))
    return A


def ape(q, sweeps):
    """`sweeps` of spatial APE smearing. SU(2) projection IS quaternion normalisation."""
    q = q.copy()
    for _ in range(sweeps):
        out = q.copy()
        for mu in range(3):
            # DERIVED: the standard APE combination. The 6 is the number of staples a link has in
            # four dimensions; here only the spatial ones are summed, which the normalisation below
            # absorbs -- the projection makes any positive overall scale irrelevant.
            # The staple is built in the orientation the ACTION uses, where Re tr(U A) is
            # the plaquette -- so A carries the conjugate orientation to U and the APE
            # combination needs A-dagger. Verified rather than reasoned: with A as built,
            # smearing RAISED the plaquette density 0.398 -> 1.446, which is the field
            # getting rougher; with the conjugate it falls 0.398 -> 0.036, which is
            # smearing.
            cand = ((1.0 - ALPHA) * q[..., mu, :]
                    + (ALPHA / 6.0) * _qconj(_spatial_staple(q, mu)))
            n = np.linalg.norm(cand, axis=-1, keepdims=True)
            # DERIVED: a division guard. A candidate of zero norm has no SU(2) element to project
            # to; the original link is kept, which is what "no smearing applied here" means.
            out[..., mu, :] = np.where(n > 0, cand / np.maximum(n, 1e-30), q[..., mu, :])
        q = out
    return q


# DERIVED: `nd` is the spacetime dimension count -- four, the rank of the lattice the links
# live on. It converts a direction index into the array axis that direction occupies,
# counting from the right past the (direction, quaternion) pair. Not a magnitude.
def plaquette_density(q, nd=4):
    """The spatial-plaquette action density per site: 1 - (1/3) sum_{i<j} Re tr U_ij / 2.

    For unit quaternions, Re tr U / 2 is the real component of the product.
    """
    tot = np.zeros(q.shape[:-2], dtype=np.float64)
    npl = 0
    for mu in range(3):
        for nu in range(mu + 1, 3):
            axmu, axnu = mu - nd - 1, nu - nd - 1
            qmu, qnu = q[..., mu, :], q[..., nu, :]
            P = _qmul(_qmul(qmu, np.roll(qnu, -1, axis=axmu)),
                      _qmul(_qconj(np.roll(qmu, -1, axis=axnu)), _qconj(qnu)))
            tot += P[..., 0].astype(np.float64)
            npl += 1
    return 1.0 - tot / npl


def load_links(L, beta, ncap):
    fs = sorted(glob.glob(os.path.join(LINKS, "su2_L%d_b%.2f.s*.npy" % (L, beta))))
    if not fs:
        return None
    out, got = [], 0
    for f in fs:
        a = np.load(f)
        out.append(a[: max(0, ncap - got)])
        got += out[-1].shape[0]
        if got >= ncap:
            break
    return np.concatenate(out, 0).astype(np.float64)


def main() -> None:
    if not BASE or not os.path.isdir(LINKS or ""):
        raise SystemExit("smeared_channel_of_spacing: the raw-link collection is not present, so "
                         "no smeared operator can be built.\n" + store_path.hint())

    # CHOSEN: configurations per point. Links are large; this costs the width of the read, not its
    # direction, and the comparison is a ratio measured the same way at both points. Raised from
    # 12 once the incremental smearing and the profile-level jackknife removed the repeated work.
    ncap = 48
    print("Is the smeared channel PHYSICAL or UV?  matched physical volume, spacing 1.34x finer")
    print("  physical: <d^2> rises by (16/12)^2 = %.2f     UV: <d^2> stays flat" % ((16 / 12) ** 2))
    print()
    print("%11s %20s %20s %16s %9s %9s"
          % ("sweeps c/f", "d2 beta=2.30 L=12", "d2 beta=2.40 L=16", "ratio",
             "margin c", "margin f"))

    fields = {}
    for L, beta in POINTS:
        q = load_links(L, beta, ncap)
        if q is None:
            raise SystemExit(f"smeared_channel_of_spacing: no links for L={L} beta={beta:.2f}; the "
                             f"matched pair is the only one the store holds, so the test cannot run.")
        fields[(L, beta)] = q

    # DERIVED in `aperture_ceiling`, the same ceiling the aperture scan uses, and SHARP.
    c_max = aperture_ceiling.C_MAX
    # DERIVED, and in the right variable. A length fixed in FERMIS is 1/a sites, so the moment
    # scales as (a_coarse/a_fine)^2. The volume ratio (L_fine/L_coarse)^2 equals that only when the
    # volumes match exactly: 1.80 vs 1.78 on the matched pair, but 3.15 vs 4.00 on the second, where
    # using the volume ratio would test against a prediction 27% wrong.
    physical = (SIG[POINTS[0][1]] / SIG[POINTS[1][1]]) ** 2

    def profiles_at(q, wanted):
        """Lag profiles at each sweep count in `wanted`, smearing ONCE through the largest.

        Sweep 4 is sweep 2 smeared twice more, so re-smearing from scratch per row does roughly
        twice the work for no change in the result. The field is smeared once and snapshotted.
        """
        out, cur, done = {}, q, 0
        for target in sorted(wanted):
            if target > done:
                cur = ape(cur, target - done)
                done = target
            out[target] = CG.per_config_profiles(plaquette_density(cur))
        return out

    def d2_jack(Pm):
        """The moment and its jackknife error, from a profile matrix.

        The resampling is the LIBRARY's `jackknife`, not a local copy: how the groups are formed,
        whether samples or bins are deleted, and what the (G-1)/G factor applies to are the
        library's decisions, and a hand-rolled version silently re-decides all three.

        Deleting a configuration only changes which ROWS of the matrix are averaged, so passing the
        profile matrix -- rather than the field -- means no re-smearing and no re-profiling.
        """
        est, se = W.jackknife(Pm, CG.d2_from_profiles)
        return float(est), float(se)

    # MATCHED RADIUS, not matched sweep count -- see RADIUS_FACTOR.
    coarse_sweeps = sorted(SWEEPS)
    fine_sweeps = sorted({int(round(s * RADIUS_FACTOR)) for s in SWEEPS})
    Pa = profiles_at(fields[POINTS[0]], coarse_sweeps)
    Pb = profiles_at(fields[POINTS[1]], fine_sweeps)

    rows = []
    for s in SWEEPS:
        s_fine = int(round(s * RADIUS_FACTOR))
        (La, ba), (Lb, bb) = POINTS
        a, sa = d2_jack(Pa[s])
        b, sb = d2_jack(Pb[s_fine])
        # DERIVED: the domain of the division; a zero moment has no ratio to report.
        r = b / a if a > 0 else float("nan")
        # DERIVED: the domain of the relative-error propagation; a zero moment has no relative
        # error, so the ratio has no band to report.
        sr = r * math.sqrt((sa / a) ** 2 + (sb / b) ** 2) if a > 0 and b > 0 else float("nan")
        ma, mb = c_max / (a / La ** 2), c_max / (b / Lb ** 2)
        rows.append((s, s_fine, a, sa, b, sb, r, sr, ma, mb))
        print("%6d/%-4d %12.4f+/-%.4f %12.4f+/-%.4f %8.2f+/-%.2f %8.1fx %8.1fx"
              % (s, s_fine, a, sa, b, sb, r, sr, ma, mb))

    print()
    print("  physical would give %.2f at every row; UV would give ~1.00" % physical)
    print("  the margin columns are the cost: the hypothesis clears easily on the UV channel")
    print("  (no smearing) and marginally on the physical one.")

    out = os.path.join(os.path.dirname(os.path.dirname(HERE)), "data",
                       "9_7_dat_smeared_channel.csv")
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["sweeps_coarse", "sweeps_fine", "d2_coarse", "d2_coarse_err",
                    "d2_fine", "d2_fine_err", "ratio", "ratio_err",
                    "margin_coarse", "margin_fine", "physical_prediction", "c_max"])
        for s, sf, a, sa, b, sb, r, sr, ma, mb in rows:
            w.writerow([s, sf, f"{a:.6f}", f"{sa:.6f}", f"{b:.6f}", f"{sb:.6f}",
                        f"{r:.4f}", f"{sr:.4f}", f"{ma:.2f}", f"{mb:.2f}",
                        f"{physical:.4f}", f"{c_max:.6f}"])
    print(f"\nwrote {os.path.relpath(out)}")


if __name__ == "__main__":
    main()
