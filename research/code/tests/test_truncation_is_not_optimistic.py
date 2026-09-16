"""The truncated certificate must not certify more gap than the cell has.

THE RISK IS REAL AND ONE-SIDED. The backward pivot recurrence is `p_i = d_i - mu - lam^2/p_{i+1}`.
Truncating at `n` sets `p_{n-1} = d_{n-1} - mu`, DROPPING the `- lam^2/p_n` term, and dropping a
subtraction makes every pivot below it too large. So a truncated certificate errs in the one direction
that overstates -- `MassGap.CellTail` is the Lean side of exactly this, and
`cell_pivot_certificate.tail_lifts` checks, AT THE SHIFT EACH ROUTE ACTUALLY CERTIFIES AT, that the
tail-inclusive sequence still carries at most one negative. That question is owned by
`test_emitted_jmax_lifts_to_the_cell.py`, not by this file.

Inertia is not the whole question. This asks the other half: by HOW MUCH does the truncation overstate
the gap, and is that smaller than the margin the certificate claims over the floor?

THE COMPARISON IS PER COUPLING, which is the part that is easy to get wrong. The absolute route
certifies `mu = 2747/10000`, a margin of 4.7e-5 over `kappa_0`; the relative route certifies the gap
itself, which reaches 4.87. Comparing a relative-route overstatement against the absolute route's
margin is a category error and reports a false alarm -- it did, the first time this was run.
"""
from __future__ import annotations

import sys
from fractions import Fraction as Q
from pathlib import Path

import numpy as np
import pytest

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO / "research" / "code" / "certify"))

#: CHOSEN: the truncation treated as converged. Not a tolerance on the answer -- the measurement below
#: shows the gap is identical from jmax = 8 upward to float precision, so any order past that names
#: the same number; 128 is simply far enough to make that visible.
CONVERGED = 128


@pytest.fixture(scope="module")
def cert():
    import cell_pivot_certificate
    return cell_pivot_certificate


def _emitted_jmax() -> int:
    """The truncation the generated Lean file actually uses, read from the file.

    Not a constant here: the emitter's `--lean-jmax` is what the theorems are about, and a test that
    hard-coded a different one would check a truncation nobody transcribed.
    """
    import re
    text = (REPO / "research" / "lean" / "MassGap" / "CellPivot.lean").read_text(encoding="utf-8")
    m = re.search(r"at `jmax = (\d+)`", text)
    assert m, "CellPivot.lean does not state the jmax it was generated at"
    return int(m.group(1))


def _gap(dim_n: int, lam: float) -> float:
    A = np.zeros((dim_n, dim_n))
    for i in range(dim_n):
        A[i, i] = i * (i + 2) / 4.0
    for i in range(dim_n - 1):
        A[i, i + 1] = A[i + 1, i] = -lam
    w = np.linalg.eigvalsh(A)
    return float(w[1] - w[0])


def test_the_gap_has_converged_by_the_orders_the_artifact_reports(cert):
    """The artifact's jmax spread is a convergence, not a coincidence of the orders tried."""
    for lam in (0.16, 1.0, 3.0, 6.76):
        a = _gap(cert.dim(8), lam)
        b = _gap(cert.dim(CONVERGED), lam)
        assert a == pytest.approx(b, abs=1e-9), (
            f"lam={lam}: the gap still moves between jmax=8 ({a}) and jmax={CONVERGED} ({b}); the "
            f"artifact's truncation-spread column would then be reporting the orders it happened to "
            f"try rather than a converged value")


def test_the_transcribed_truncation_does_not_overstate_the_true_gap(cert):
    """Whatever `jmax` the Lean emitter uses, its certificates must not claim more than the cell has.

    This is not the same question as the margin test below, and the difference caught a real defect.
    The margin test asks whether the overstatement is smaller than the certificate's own margin over
    the floor; it is, comfortably, at every truncation. But a RELATIVE-route certificate claims the
    GAP itself, not a shift just above the floor, and at `jmax = 2` the claim at `lam = 6.00` was
    4.625 against a true gap of 4.568 -- a theorem true of `HcellR 2 6` and false of the cell it
    truncates, in a file whose header says "the physical single-cell gap".

    So the emitter's own truncation is read out of the generated file and checked directly.
    """
    jmax = _emitted_jmax()
    khi_q = cert.check_mu_above_floor(cert.MU_DEFAULT)[1]
    khi = float(khi_q)
    checked, over = 0, []
    for lamf in (0.16, 1.0, 1.92, 2.5, 3.0, 4.0, 5.0, 6.0, 6.76):
        lam = Q(str(lamf))
        ok, _, _, _, _ = cert.certify(jmax, lam, cert.MU_DEFAULT)
        if ok:
            claimed = float(cert.MU_DEFAULT)
        else:
            t, _, _ = cert.simple_sturm_shift(jmax, lam, khi_q)
            if t is None:
                continue
            v, g, _ = cert.simple_trial(jmax, lam, t, khi_q)
            if v is None:
                continue
            claimed = float(g)
        true_gap = _gap(cert.dim(CONVERGED), lamf)
        checked += 1
        if claimed > true_gap + 1e-9:
            over.append((lamf, claimed, true_gap))
    assert not over, (
        f"at jmax={jmax} the certificate claims more gap than the untruncated cell has: "
        + "; ".join(f"lam={l}: claims {c:.6f}, true {tg:.6f}" for l, c, tg in over)
        + ". The transcribed theorems are then true of the truncation and false of the cell.")
    # DERIVED: 6 couplings spans both routes -- fewer would leave one of them unexercised.
    assert checked >= 6, f"only {checked} couplings were checked at jmax={jmax}"


def test_truncation_overstates_by_less_than_the_certified_margin(cert):
    """At every coupling, `gap(jmax=4) - gap(converged)` is under THAT coupling's margin.

    The margin is the certificate's own claim at that coupling: `mu - kappa_0` where the absolute
    route applies, and `gap - kappa_0` where the relative one does.
    """
    jmax = 4
    khi_q = cert.check_mu_above_floor(cert.MU_DEFAULT)[1]
    khi = float(khi_q)
    checked = 0
    for lamf in (0.16, 0.5, 1.0, 1.5, 1.92, 3.0, 5.0, 6.76):
        lam = Q(str(lamf))
        ok, _, _, _, _ = cert.certify(jmax, lam, cert.MU_DEFAULT)
        if ok:
            certified = float(cert.MU_DEFAULT)
        else:
            rok, _, _, g, _ = cert.certify_relative(jmax, lam, khi_q)
            if not rok:
                continue
            certified = float(g)
        over = _gap(cert.dim(jmax), lamf) - _gap(cert.dim(CONVERGED), lamf)
        margin = certified - khi
        checked += 1
        assert over < margin, (
            f"lam={lamf}: truncation at jmax={jmax} overstates the gap by {over:.3e}, which is not "
            f"under the certified margin {margin:.3e} over the floor. The transcribed theorems at "
            f"this truncation would then claim a gap the cell does not have.")
    # DERIVED: 4 is the arity of "covers both routes" -- the absolute route holds below lam ~ 2 and
    # the relative one above, so fewer than a couple of couplings each would leave one unchecked.
    assert checked >= 4, f"only {checked} couplings were checked; both routes must be represented"
