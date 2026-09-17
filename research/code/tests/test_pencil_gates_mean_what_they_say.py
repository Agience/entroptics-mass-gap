"""The moment pencil's two gates decide every box verdict, so their semantics are tested.

`aperture_reads.pencil_rate` returns `(rate, valid)` and the whole fixed-aperture box question is
read through it. `valid` is the conjunction of two claims:

  * `rate` is not NaN -- the leading transfer eigenvalue lies in `(0,1)`, since a transfer operator
    cannot grow a correlation;
  * `isolation` is infinite -- the pencil separates a single mode, so the leading eigenvalue is that
    mode and not a mixture.

Both are documented and neither was tested. `certify/gap_of_maximal_correlation.test_pencil_planted`
calibrates them, but it is a function inside a script: it runs when someone runs that script, not when
the suite runs. So "the read invalidated itself" -- the sentence the entire beta=2.4 campaign came
down to -- rested on a docstring.

Planted here, where the answer is known: a single decaying exponential must be RECOVERED and declared
valid, and a two-mode mixture must be REFUSED by the isolation gate specifically. A gate that accepts
everything and a gate that accepts nothing both look like a working gate from one side only.

Structureless data is NOT the pencil's job, and finding that out is half of what this file records --
see the Nyquist test below.
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO / "research" / "code"))

#: DERIVED: the pencil of order `m` consumes lags `c_0 .. c_{2m+1}`, so `T` must exceed that. 32 is
#: the aperture the campaigns actually use, which is the geometry worth testing at.
T = 32
#: DERIVED: the block size the box read uses -- `n=384` split into four blocks of 96. Planting at the
#: size the read sees is the point; a gate calibrated at a larger n says nothing about the one used.
N = 96


@pytest.fixture(scope="module")
def ar():
    import aperture_reads
    return aperture_reads


# CHOSEN: a default seed, so a caller that does not vary it still gets a reproducible plant. Every
# call below passes its own; this only fixes what happens when one does not.
def _planted(rate: float, n: int = N, t: int = T, seed: int = 11) -> np.ndarray:
    """`n` histories whose connected correlator decays at exactly `rate`.

    An AR(1) process with coefficient `exp(-rate)`: its autocorrelation is `exp(-rate * tau)` by
    construction, so the pencil has a single mode to find and its value is known in advance.
    """
    rng = np.random.default_rng(seed)
    a = float(np.exp(-rate))
    x = np.zeros((n, t))
    x[:, 0] = rng.standard_normal(n)
    for k in range(1, t):
        x[:, k] = a * x[:, k - 1] + np.sqrt(1 - a * a) * rng.standard_normal(n)
    return x


def test_a_planted_single_mode_is_recovered_and_declared_valid(ar):
    """The gates accept a signal they should, and the rate is the planted one."""
    recovered = []
    for rate in (0.30, 0.50, 0.80):
        got = [ar.pencil_rate(_planted(rate, seed=s), order=2) for s in (11, 12, 13, 14)]
        valid = [r for r, ok in got if ok]
        assert valid, (
            f"planted rate {rate}: the pencil declared itself invalid in all four blocks. A gate that "
            f"never accepts a single planted mode cannot distinguish a crowded spectrum from a clean "
            f"one, and every 'invalidated itself' in the box reads would be uninformative")
        mean = float(np.mean(valid))
        recovered.append((rate, mean, len(valid)))
        # DERIVED: half the planted rate is the width inside which "recovered" means recovered. The
        # pencil is an estimator on 96 samples, so it is not exact; a bound proportional to the
        # planted value asks the same question at every rate rather than a fixed absolute one.
        assert abs(mean - rate) < 0.5 * rate, (
            f"planted rate {rate}: the pencil recovered {mean:.4f} from {len(valid)} valid blocks, "
            f"which is not that rate. The reads that consume it would then be reporting a number "
            f"unrelated to the decay they are measuring")
    # DERIVED: 3 is the number of rates planted above -- the loop must have run to completion rather
    # than skipped a rate, which `continue`-free code makes true but nothing else states.
    assert len(recovered) == 3


def test_noise_is_rejected_by_the_NYQUIST_gate_not_the_pencils(ar):
    """Which gate rejects noise, and it is not the pencil's.

    The first version of this test asserted that `pencil_rate` declines white noise. It does not, and
    it should not: white noise DOES decay -- essentially instantly -- and the pencil reports that
    correctly. Measured, it returns rates of 1.4 to 3.5, i.e. correlation lengths of 0.29 to 0.70
    lattice spacings. The pencil's gates are about whether a single mode is isolated, not about
    whether the mode is physically meaningful.

    What rejects noise is the composite read's NYQUIST condition, `xi/a > 1`: a correlation length
    below one sampling interval is past the read's own limit whatever the pencil says. Asserting a
    property against the wrong gate is how a test passes while checking nothing, so the division of
    labour is written down here rather than assumed.
    """
    rng = np.random.default_rng(99)
    subnyquist = 0
    trials = 6
    for _ in range(trials):
        rate, ok = ar.pencil_rate(rng.standard_normal((N, T)), order=2)
        if rate != rate:                       # the pencil declined outright
            subnyquist += 1
            continue
        # DERIVED: 1.0 is the lattice spacing in its own units -- xi = 1/rate exceeds one sampling
        # interval exactly when rate < 1. Nyquist, not a tolerance.
        if rate > 1.0:
            subnyquist += 1
    assert subnyquist == trials, (
        f"white noise cleared the Nyquist condition in {trials - subnyquist} of {trials} trials, "
        f"meaning it produced a correlation length above one lattice spacing. Then neither the "
        f"pencil's gates nor Nyquist rejects structureless data, and a box read could report noise "
        f"as a gap")


def test_the_two_gates_are_not_the_same_gate(ar):
    """`rate` finite and `isolation` infinite are distinct conditions, so at least one configuration
    should separate them -- otherwise one of the two is doing nothing and the docstring describes a
    conjunction that is really a single test."""
    seen_finite_rate_only = False
    rng = np.random.default_rng(7)
    for s in range(12):
        # a two-mode mixture: a slow and a fast decay superposed, which is what "the modes crowd"
        # means in the box reads
        slow, fast = _planted(0.25, seed=100 + s), _planted(1.20, seed=200 + s)
        mix = slow + fast
        rate, ok = ar.pencil_rate(mix, order=2)
        if (rate == rate) and not ok:
            seen_finite_rate_only = True
            break
    assert seen_finite_rate_only, (
        "no mixture produced a finite rate that the isolation gate nonetheless refused. The two gates "
        "may then be equivalent in practice, and 'the modes crowd' would not be a distinct finding "
        "from 'the rate is out of range'")
