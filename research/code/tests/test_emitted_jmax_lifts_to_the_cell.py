"""The transcribed theorems must be statements about the CELL, not about `HcellR jmax`.

WHAT WENT WRONG, so the shape is on record. `CellPivot.lean` was generated at `jmax = 4` and its
header describes "the physical single-cell gap". Both halves were checked, and neither check was this
one:

  * `test_truncation_is_not_optimistic` asks whether the certified GAP VALUE exceeds the untruncated
    cell's. At `jmax = 4` it does not, so that test was green.
  * the cover's walk asked `tail_is_safe(jmax, lam, MU_DEFAULT)` -- whether including the tail changes
    the pivot SIGNS, at `MU_DEFAULT`.

The second is wrong twice over. A certificate is an inertia claim AT A SHIFT, and neither route uses
`MU_DEFAULT`: the absolute walk certifies at the bisected `M` (which runs to ~0.84) and the relative
route certifies at its own Sturm shift (which runs to about -5). And sign AGREEMENT is not the
question -- `pivots_with_tail` is a LOWER BOUND on the cell's pivots, so what the theorem needs is
"at most one negative in the bound", which gives "at most one eigenvalue below the shift" for the
cell. The old predicate returned "safe" where both sequences carried three negatives, which is
agreement about a certificate that does not exist.

Asked correctly, `jmax = 4` lifts 17 of 61 couplings -- every absolute one and no relative one. The
44 relative theorems were true of `HcellR 4` and were not statements about the cell.

THIS TEST asks the emitted truncation the question the theorems need, at the shift each route
actually uses, and reads the truncation out of the GENERATED FILE so it cannot drift from what was
transcribed.
"""
from __future__ import annotations

import re
import sys
from fractions import Fraction as Q
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO / "research" / "code" / "certify"))

LEAN = REPO / "research" / "lean" / "MassGap" / "CellPivot.lean"


@pytest.fixture(scope="module")
def cert():
    import cell_pivot_certificate
    return cell_pivot_certificate


def _emitted_jmax() -> int:
    """The truncation the generated file was written at, read from the file itself."""
    m = re.search(r"at `jmax = (\d+)`", LEAN.read_text(encoding="utf-8"))
    assert m, "CellPivot.lean does not state the jmax it was generated at"
    return int(m.group(1))


def _emitted_couplings(cert) -> list[Q]:
    """The couplings the generated file actually states theorems about.

    From the FILE, not from the default grid: a theorem that is not in the file needs no tail, and a
    coupling in the file that the grid no longer contains would otherwise go unchecked.
    """
    text = LEAN.read_text(encoding="utf-8")
    # The coupling is in the declaration NAME (`cell_gap_4_25` is lam = 4/25) and again in the
    # STATEMENT (`HcellR_isHermitian 8 (4 / 25)`). Both are parsed and required to agree: a name is
    # what a reader indexes by and a statement is what the kernel checked, and a generator bug that
    # desynchronised them would otherwise let this test check couplings nobody proved anything about.
    by_name = {Q(int(n), int(d))
               for n, d in re.findall(r"^theorem (?:rel_)?cell_gap_(\d+)_(\d+)\b", text, re.M)}
    # `(5)` as well as `(511 / 100)`: an integral coupling is emitted without a denominator, and a
    # regex that demanded one silently dropped lam = 5 from the set it checked.
    by_stmt = {Q(int(n), int(d or 1))
               for n, d in re.findall(
                   r"HcellR_isHermitian\s+\d+\s+\((-?\d+)(?:\s*/\s*(\d+))?\)", text)}
    assert by_name == by_stmt, (
        f"the generated file's theorem NAMES and STATEMENTS disagree about which couplings it "
        f"covers: only in names {sorted(by_name - by_stmt)[:4]}, only in statements "
        f"{sorted(by_stmt - by_name)[:4]}")
    return sorted(by_name)


def test_every_transcribed_coupling_lifts_to_the_cell(cert):
    """At the emitted `jmax`, the tail bound must lift every theorem in the file to the cell."""
    jmax = _emitted_jmax()
    lams = _emitted_couplings(cert)
    # DERIVED: the generated file states 61 theorems; fewer parsed means the extraction missed some
    # and the test would pass by checking a subset of what was transcribed.
    n_thms = len(re.findall(r"^theorem ", LEAN.read_text(encoding="utf-8"), re.M))
    assert len(lams) == n_thms, (
        f"parsed {len(lams)} couplings out of {n_thms} theorems in CellPivot.lean; the extraction is "
        f"not seeing everything the file states, so this test would check a subset")

    khi = cert.check_mu_above_floor(cert.MU_DEFAULT)[1]
    unlifted = []
    for lam in lams:
        shift, route = cert.certifying_shift(jmax, lam, cert.MU_DEFAULT, khi)
        assert shift is not None, f"lam={lam} is in the file but certifies by neither route at jmax={jmax}"
        lifts, _, neg, note = cert.tail_lifts(jmax, lam, shift)
        if not lifts:
            unlifted.append((lam, route, note or f"{len(neg)} negatives with the tail"))
    assert not unlifted, (
        f"at jmax={jmax} the tail bound does not lift {len(unlifted)} of {len(lams)} transcribed "
        f"coupling(s), so those theorems are true of `HcellR {jmax}` and are NOT statements about "
        f"the cell its header claims: "
        + "; ".join(f"lam={l} ({r}): {w}" for l, r, w in unlifted[:5]))


def test_the_check_is_shift_aware_and_would_fail_at_a_shallower_truncation(cert):
    """The guard must be able to fail, and must fail for the reason it names.

    Two negatives, because a guard that cannot fail is not a guard, and a guard that fails for the
    wrong reason is worse. At `jmax = 4` the relative route provably does not lift -- that is the
    defect this file exists to prevent recurring -- and asking at `MU_DEFAULT` instead of at the
    route's own shift provably hides it.
    """
    khi = cert.check_mu_above_floor(cert.MU_DEFAULT)[1]
    lam = Q(3)  # a relative-route coupling, comfortably inside the range

    shift, route = cert.certifying_shift(4, lam, cert.MU_DEFAULT, khi)
    assert route == "relative", f"lam={lam} is not on the relative route at jmax=4; pick another"
    # DERIVED: the SIGN, not a threshold. The whole point is that the relative route's shift is on
    # the opposite side of zero from `MU_DEFAULT`, so checking the tail at `MU_DEFAULT` asks about a
    # different operator; zero is where "opposite side" is defined.
    assert shift < 0, f"the relative shift at lam={lam} is {shift}, not negative -- the premise moved"

    lifts_at_4, _, _, _ = cert.tail_lifts(4, lam, shift)
    assert not lifts_at_4, (
        "jmax=4 now lifts the relative route at lam=3. If that is a real improvement the emitter's "
        "minimum can drop, but this test encodes why it was raised and must be revisited first.")

    # THE SHIFT IS PER-TRUNCATION. `largest_sturm_shift` bisects against `HcellR jmax`, so the
    # shift at jmax=8 is not the shift at jmax=4 and feeding one to the other asks a question about
    # neither certificate. (It failed exactly that way the first time this test was written.)
    shift8, route8 = cert.certifying_shift(8, lam, cert.MU_DEFAULT, khi)
    assert route8 == "relative", f"lam={lam} is not on the relative route at jmax=8"
    lifts_at_8, _, _, _ = cert.tail_lifts(8, lam, shift8)
    assert lifts_at_8, "jmax=8 must lift the relative route; it is the emitter's stated minimum"

    # AND THE OLD QUESTION WOULD HAVE SAID YES. Reconstructed here rather than described, because a
    # defect that is only described in a docstring is a defect nobody can re-run: the retired
    # predicate compared the SIGN PATTERNS of the truncated and tail-inclusive sequences at
    # `MU_DEFAULT` and called them "safe" when they matched. At lam = 3, jmax = 4 they match -- with
    # TWO negatives each. So it reported safe for a coupling where no certificate at that shift
    # exists at all, while the certificate that does exist (at the Sturm shift) does not lift.
    pv, _, pok, _ = cert.pivots(4, lam, cert.MU_DEFAULT)
    tv, _ = cert.pivots_with_tail(4, lam, cert.MU_DEFAULT, lam)
    assert pok and tv is not None, "the reconstruction of the old predicate did not run"
    old_says_safe = cert.negatives(pv) == cert.negatives(tv)
    assert old_says_safe and not lifts_at_4, (
        f"the old sign-agreement check at MU_DEFAULT no longer reproduces the defect: it says "
        f"safe={old_says_safe} where the correct check says lifts={lifts_at_4}. If the code has "
        f"moved on, this test's account of what went wrong needs rewriting, not deleting.")
    # DERIVED: more than one negative is what makes the agreement vacuous -- two sequences can only
    # agree about a certificate that exists if at most one pivot is negative.
    assert len(cert.negatives(pv)) > 1, (
        "the truncated pivots at MU_DEFAULT carry at most one negative, so the old check's agreement "
        "was not vacuous here and this coupling no longer illustrates the defect")


def test_the_emitter_refuses_a_truncation_that_does_not_lift(cert, tmp_path):
    """The generator must refuse, not warn. A warning in a build log is not a guard."""
    import subprocess
    out = tmp_path / "probe.lean"
    r = subprocess.run(
        [sys.executable, "cell_pivot_certificate.py", "--emit-lean", str(out), "--lean-jmax", "4"],
        cwd=str(REPO / "research" / "code" / "certify"),
        capture_output=True, text=True, timeout=1800)
    # DERIVED: zero is the POSIX convention for success, not a threshold -- the emitter must exit
    # non-zero, because a generator that warns and writes the file anyway is not a guard.
    assert r.returncode != 0, (
        "the emitter accepted jmax=4, at which 44 of 61 theorems do not lift to the cell")
    assert "REFUSING to emit" in (r.stdout + r.stderr), (
        f"the emitter failed at jmax=4 but not with its own refusal:\n{(r.stdout + r.stderr)[-600:]}")
    assert not out.exists(), "the emitter refused but still wrote a file"
