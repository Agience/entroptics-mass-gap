"""The pinned reference null is calibrated per plane shape (research/code/entroptics_adapter.py).

WHY. The library's ``reference_null`` is an absolute top-singular-value level with no record of the
(N, F) it was calibrated at, and under the 0.2.5 whitening a screen's energy is fixed at N*F, so the
level a signal-free plane reaches is set by the plane's shape. One floor calibrated on 8x8 planes and
applied to 6x6 and 16x16 planes read the shape, not the field: SU(3) 6x6 read 0.0000 at every
coupling, SU(2) 16x16 read 3.59, and both read the same with each plane's values shuffled.

WHAT IS PINNED HERE, at each plane shape the Sec 8.3 producers read (6x6, 8x8, 16x16):

  * the pin REFUSES a plane shape it holds no calibration for, and a caller-supplied null that
    records its shape refuses another shape;
  * a planted rank-1 structure (one mode shared by every channel) is detected above the false-alarm
    level measured at the same shape through the same pin (positive control);
  * the same planes with their values permuted within each plane -- same marginal, no arrangement --
    read at that false-alarm level (negative control);
  * and the instrument can fail: a floor calibrated at 8x8 and applied to 16x16 noise reads far
    above the 16x16 false-alarm level, and applied to the 6x6 rank-1 planes misses them. Those are
    the two defects the per-shape pin removes, run here so the controls above are seen to fail on the defects they target.

The reference is synthetic i.i.d. Gaussian planes: signal-free by construction, which is the property
the pin needs, and cheap enough to calibrate three shapes in the light suite.
"""
from __future__ import annotations

import math

import numpy as np
import pytest

import entroptics_adapter as W

# CHOSEN: the three plane shapes the Sec 8.3 producers read -- SU(3) 6^3 (6x6), the L=8 ensembles
# (8x8) and SU(2) 16^3 (16x16). Other shapes behave the same way; these are the ones that matter.
SHAPES = ((6, 6), (8, 8), (16, 16))
# CHOSEN: 600 reference planes per shape. Enough that the floor's mean and std of the top singular
# value are settled to a few percent; the test compares reads against a false-alarm level measured
# through the same floor, so the floor's own sampling error does not enter any comparison.
N_REF = 600
# CHOSEN: 24 configurations of 30 planes per read. The per-configuration mean is the sample the
# errors are taken over, so 24 of them give a standard error with a stable scale.
N_CFG, N_PLANES = 24, 30
# CHOSEN: rank-1 amplitude a = 1, a pairwise channel correlation rho = a^2/(1+a^2) = 0.5, the
# structure the regression hand-off used at 8x8 (mean K 0.84 there under 0.2.5).
AMP = 1.0
# CHOSEN: four standard errors. A band at four sigma leaves a flake probability far below one in
# ten thousand per comparison, and every contrast it has to see is several times wider than that.
Z = 4.0


# DERIVED: amplitude 0 is the signal-free plane -- no planted mode at all.
def _planes(rng, shape, n, amp=0.0):
    """``n`` planes of ``shape`` (rows = samples, columns = channels): i.i.d. standard normal, plus
    ``amp`` times one standard-normal offset per row shared by every channel (the rank-1 mode)."""
    rows, cols = shape
    x = rng.standard_normal((n, rows, cols))
    if amp:
        x = x + amp * rng.standard_normal((n, rows, 1))
    return x


# DERIVED: amplitude 0 is the signal-free plane -- no planted mode at all.
def _configs(rng, shape, amp=0.0):
    """``N_CFG`` raw configurations, each ``N_PLANES`` planes stacked on the last (time) axis, so the
    wrapper's slabs cut exactly these planes back out."""
    return [np.moveaxis(_planes(rng, shape, N_PLANES, amp), 0, -1) for _ in range(N_CFG)]


def _k(configs, **kw):
    """Per-configuration plane-mean K_signal through the wrapper."""
    return np.array([W.confinement(c, -1, **kw) for c in configs], dtype=float)


def _se(values):
    return float(np.std(values, ddof=1) / math.sqrt(len(values)))


@pytest.fixture(scope="module")
def pinned():
    rng = np.random.default_rng(20260929)
    refs = [p for shape in SHAPES for p in _planes(rng, shape, N_REF)]
    W.pin_reference(realisations=refs)
    yield rng
    W.unpin_reference()


def test_the_pin_holds_one_calibration_per_shape(pinned):
    assert W.pinned_shapes() == tuple(sorted(SHAPES))
    held = W.pinned_reference()
    for shape in SHAPES:
        assert len(held[shape]) == N_REF, f"{shape}: {len(held[shape])} reference planes"


def test_the_pin_refuses_an_uncalibrated_shape(pinned):
    rng = pinned
    # (10, 10) is not among SHAPES: the pin has no planes of it, so the read must refuse.
    with pytest.raises(W.UncalibratedShape):
        W.confinement(np.moveaxis(_planes(rng, (10, 10), 3), 0, -1), -1)
    with pytest.raises(W.UncalibratedShape):
        W.run([np.moveaxis(_planes(rng, (10, 10), 3), 0, -1)]).contrast
    # a null that records its calibration shape refuses another shape, and floors its own
    svs = W.confined_top_singular_values([np.moveaxis(_planes(rng, (8, 8), 50), 0, -1)])
    own = W.confined_reference_null(svs, plane_shape=(8, 8))
    with pytest.raises(W.UncalibratedShape):
        W.confinement(np.moveaxis(_planes(rng, (6, 6), 3), 0, -1), -1, null=own)
    assert np.isfinite(W.confinement(np.moveaxis(_planes(rng, (8, 8), 3), 0, -1), -1, null=own))
    # and with nothing pinned every floor read raises
    saved = (W._PINNED_REFERENCE, W._PINNED_PROVIDER)
    W.unpin_reference()
    try:
        with pytest.raises(RuntimeError):
            W.confinement(np.moveaxis(_planes(rng, (8, 8), 3), 0, -1), -1)
    finally:
        W._PINNED_REFERENCE, W._PINNED_PROVIDER = saved


@pytest.mark.parametrize("shape", SHAPES, ids=lambda s: f"{s[0]}x{s[1]}")
def test_rank1_is_detected_and_the_shuffle_reads_at_the_false_alarm_level(pinned, shape):
    rng = pinned
    noise = _k(_configs(rng, shape))                        # the false-alarm level at this shape
    planted = _configs(rng, shape, AMP)
    real = _k(planted)
    shuf = _k(planted, shuffle=1)                           # same planes, values permuted per plane
    fa, fa_se = float(noise.mean()), _se(noise)

    # positive control: the planted mode stands above the false-alarm level
    d, d_se = float(real.mean()) - fa, math.hypot(_se(real), fa_se)
    assert d > Z * d_se, (f"{shape}: rank-1 reads {real.mean():.4f}, false-alarm level {fa:.4f} "
                          f"+/- {fa_se:.4f}; not detected")
    # negative control: the same marginal without the arrangement reads at the false-alarm level
    s, s_se = float(shuf.mean()) - fa, math.hypot(_se(shuf), fa_se)
    assert abs(s) <= Z * s_se, (f"{shape}: shuffled rank-1 reads {shuf.mean():.4f} against the "
                                f"false-alarm level {fa:.4f}; {s / s_se:+.1f} se")
    # and the paired difference the producers report is the planted structure
    paired = real - shuf
    assert paired.mean() > Z * _se(paired)


def test_another_shapes_floor_reads_the_shape(pinned):
    """The two defects the per-shape pin removes, run so the controls above are seen to fail on the defects they target. The
    floor is the library's shape-blind ``reference_null`` calibrated on 8x8 planes -- what one pin
    applied to every shape amounted to."""
    rng = pinned
    svs8 = W.confined_top_singular_values([np.moveaxis(_planes(rng, (8, 8), N_REF), 0, -1)])
    blind = W.reference_null(svs8)                          # records no shape: nothing refuses it

    # 16x16 noise against the 8x8 floor: far above the 16x16 false-alarm level
    noise16 = _configs(rng, (16, 16))
    own, other = _k(noise16), _k(noise16, null=blind)
    gap = float(other.mean() - own.mean())
    assert gap > Z * math.hypot(_se(own), _se(other)), (
        f"16x16 noise: 8x8 floor {other.mean():.4f} vs own floor {own.mean():.4f}")

    # 6x6 rank-1 against the 8x8 floor: missed, where its own floor detects it
    planted6 = _configs(rng, (6, 6), AMP)
    own6, other6 = _k(planted6), _k(planted6, null=blind)
    assert float(own6.mean() - other6.mean()) > Z * math.hypot(_se(own6), _se(other6)), (
        f"6x6 rank-1: own floor {own6.mean():.4f} vs 8x8 floor {other6.mean():.4f}")
