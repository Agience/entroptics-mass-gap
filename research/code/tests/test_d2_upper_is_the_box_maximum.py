"""`d2_upper` returns the EXACT maximum of the read over the box its per-lag bounds license.

The read is f(p) = sum w_d d^2 p_d / (1 + sum w_d p_d) on 0 <= p_d <= pmax_d. Its partial derivative
in p_d has the sign of d^2 - f, so the all-upper corner is the maximum only while its value is at
most min d^2; above that a vertex with the short lags at 0 is higher, so the corner value is not a
bound there, and inf in its place would discard a finite one. `ratio_box_max` evaluates every
threshold vertex, and its docstring proves one of them attains f*.

These tests hold that to an independent check: over random boxes, the returned value must be at
least every sampled point of the box (every vertex, and random interior points) and must be attained
by one of them. The same check run on the corner plug-in must FAIL, or it is not a check.
"""
from __future__ import annotations

import importlib.util
import itertools
import math
import sys
from pathlib import Path

import numpy as np
import pytest

CODE = Path(__file__).resolve().parents[1]                     # research/code
CERT = CODE / "certify"


def _load_cg():
    """Import the certificate module by path, leaving `sys.path` as found (see test_certify_smoke).

    Both directories go on the path: the module imports `aperture_reads` from research/code and
    `aperture_ceiling` from its own directory, which a script run supplies as its first entry."""
    mine = [str(CODE), str(CERT)]
    for p in mine:
        sys.path.insert(0, p)
    try:
        spec = importlib.util.spec_from_file_location(
            "d2_box_cg", CERT / "ym_crossover_confinement_of_grid.py")
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod
    finally:
        for p in mine:
            try:
                sys.path.remove(p)
            except ValueError:                                  # pragma: no cover - already gone
                pass


CG = _load_cg()

# CHOSEN: relative float tolerance for "attained" -- every value here is a ratio of sums of at most
# nine O(1..100) products, so rounding is ~1e-15 relative; 1e-12 leaves three decades of room and is
# far below the smallest gap the negative control opens (0.5 in the two-lag case).
RTOL = 1e-12


def f(p, w, d2):
    p, w, d2 = (np.asarray(x, dtype=float) for x in (p, w, d2))
    return float((w * d2 * p).sum() / (1.0 + (w * p).sum()))


def corner(pmax, w, d2):
    """The all-upper corner plug-in: the value returned as a bound before the exact rule."""
    return f(pmax, w, d2)


def sampled_points(pmax, rng, n_interior):
    """Every vertex of the box, then `n_interior` uniform points inside it."""
    pmax = np.asarray(pmax, dtype=float)
    for bits in itertools.product((0.0, 1.0), repeat=len(pmax)):
        yield pmax * np.array(bits)
    for _ in range(n_interior):
        yield pmax * rng.random(len(pmax))


# CHOSEN: 200 interior points per box on top of every vertex. The vertices alone decide the
# verdict (the maximum is a vertex); the interior points guard against a bound that is right at the
# vertices by construction and wrong inside, and more of them only costs time.
def check_bound(bound_fn, pmax, w, d2, rng, n_interior=200):
    """(exceeded, attained): does some sampled point exceed the bound, and does one reach it?"""
    b = bound_fn(pmax, w, d2)
    vals = [f(p, w, d2) for p in sampled_points(pmax, rng, n_interior)]
    tol = RTOL * max(1.0, abs(b))
    return max(vals) > b + tol, abs(max(vals) - b) <= tol


def random_box(rng):
    # CHOSEN: 1..8 lags (the L=16 read has 8), weights in (0.5, 2.5], d^2 drawn from small squares
    # WITH repeats so the threshold scan meets ties, and a quarter of the pmax entries pinned to 0 so
    # the degenerate faces are exercised. None of these decides a verdict; they span the inputs.
    m = int(rng.integers(1, 9))
    w = 0.5 + 2.0 * rng.random(m)
    d2 = rng.integers(1, 6, size=m).astype(float) ** 2
    pmax = rng.random(m) * rng.choice([0.2, 1.0, 5.0])
    # CHOSEN: a quarter of the entries at 0, as the note above says.
    pmax[rng.random(m) < 0.25] = 0.0
    return pmax, w, d2


def test_the_two_lag_counterexample():
    """w = (2, 1), d^2 = (1, 4), pmax = (1, 1): the corner reads 6/4 = 1.5, the box maximum is 2,
    attained at p = (0, 1) -- lowering the lag-1 weight RAISES the read, because 1 < 1.5."""
    w, d2, pmax = (2.0, 1.0), (1.0, 4.0), (1.0, 1.0)
    # DERIVED: (2*1*1 + 1*4*1) / (1 + 2 + 1) = 6/4, exact in binary.
    assert corner(pmax, w, d2) == 1.5
    # DERIVED: the vertex p = (0, 1) gives (1*4*1) / (1 + 1) = 2, exact in binary.
    assert CG.ratio_box_max(pmax, w, d2) == 2.0
    # DERIVED: the same vertex evaluated directly.
    assert f((0.0, 1.0), w, d2) == 2.0
    exceeded, attained = check_bound(CG.ratio_box_max, pmax, w, d2, np.random.default_rng(0))
    assert not exceeded and attained


def test_the_corner_plug_in_fails_the_same_check():
    """NEGATIVE CONTROL. The check above must reject the corner value on the counterexample and on
    every random box where the corner exceeds min d^2 with a positive pmax at that minimum --
    otherwise the check cannot tell a bound from a non-bound."""
    rng = np.random.default_rng(1)
    w, d2, pmax = (2.0, 1.0), (1.0, 4.0), (1.0, 1.0)
    exceeded, _ = check_bound(corner, pmax, w, d2, rng)
    assert exceeded, "the check accepted the corner plug-in on the two-lag counterexample"
    failed = seen = 0
    for _ in range(300):
        pmax, w, d2 = random_box(rng)
        lowest = d2 == d2.min()
        # DERIVED: the corner is beaten exactly when some lag below its value has room to drop
        # (pmax > 0), which the sign argument in `ratio_box_max` makes the whole condition.
        if corner(pmax, w, d2) > d2.min() and (pmax[lowest] > 0).any():
            seen += 1
            failed += check_bound(corner, pmax, w, d2, rng, n_interior=0)[0]
    # DERIVED: a control that never met the case it controls would pass vacuously.
    assert seen > 0, "no random box put the corner above min d^2; the control exercised nothing"
    assert failed == seen, f"the check let the corner through on {seen - failed} of {seen} boxes"


def test_the_exact_maximum_bounds_and_attains_on_random_boxes():
    rng = np.random.default_rng(2)
    above = 0
    for _ in range(300):
        pmax, w, d2 = random_box(rng)
        exceeded, attained = check_bound(CG.ratio_box_max, pmax, w, d2, rng)
        assert not exceeded, (pmax, w, d2)
        assert attained, (pmax, w, d2)
        # the characterisation in the docstring: g(f*) = sum w (d2 - f*)^+ pmax - f* = 0
        fs = CG.ratio_box_max(pmax, w, d2)
        g = float((w * np.clip(d2 - fs, 0, None) * pmax).sum() - fs)
        assert abs(g) <= RTOL * max(1.0, float((w * d2 * pmax).sum())), g
        # DERIVED: count the boxes where the exact rule departs from the corner, so the sweep is
        # seen to reach the regime the fix is about.
        above += fs > corner(pmax, w, d2) * (1 + RTOL)
    # DERIVED: the sweep must include boxes past the corner regime, or it tested only the easy case.
    assert above > 0


def _profiles(rng, n, lag0, lags, noise):
    P = np.empty((n, 1 + len(lags)))
    P[:, 0] = lag0 + noise * rng.standard_normal(n)
    for j, v in enumerate(lags, start=1):
        P[:, j] = v + noise * rng.standard_normal(n)
    return P


def _box(P, delta):
    """pmax, w, d^2 exactly as d2_upper builds them (the union over K one-sided events)."""
    K = P.shape[1]; dp = delta / K; m = K - 1
    lo0 = CG.eb(P[:, 0], dp, -1)
    pmax = [max(0.0, CG.eb(P[:, d], dp, +1) / lo0) for d in range(1, K)]
    # DERIVED: the circle-distance mirroring multiplicities, interior lags twice, the endpoint once.
    w = [2.0] * (m - 1) + [1.0]
    return pmax, w, [float(d * d) for d in range(1, m + 1)], lo0


def test_d2_upper_below_one_is_the_corner_bit_for_bit():
    """Where the corner value is at most 1 it is the maximum, and d2_upper must return it exactly as
    the corner formula computes it -- the committed columns below 1 do not move."""
    rng = np.random.default_rng(3)
    # CHOSEN: an L=16-shaped profile (9 lags) with short-range correlation, 96 configurations as at
    # the grid's smallest ensemble; the values only need to put the corner under 1.
    P = _profiles(rng, 96, 1.0, [0.05, 0.01, 0.002, 0.0005, 0.0, 0.0, 0.0, 0.0], 0.0003)
    for delta in (1e-2, 1e-3, 1e-6):
        pmax, w, d2, _ = _box(P, delta)
        m = len(pmax)
        num = 2.0 * sum(pmax[d - 1] * d * d for d in range(1, m)) + pmax[m - 1] * m * m
        den = 1.0 + 2.0 * sum(pmax[d - 1] for d in range(1, m)) + pmax[m - 1]
        t = num / den
        # DERIVED: 1 = min d^2, the edge of the corner regime this test is about.
        assert t <= 1.0, t
        assert CG.d2_upper(P, delta) == t


def test_d2_upper_above_one_is_the_box_maximum():
    """Where the corner value exceeds 1, d2_upper returns the box maximum, strictly above the corner,
    and a brute force over all 2^8 vertices agrees with it."""
    rng = np.random.default_rng(4)
    # CHOSEN: long-range correlation so the corner lands well above 1.
    P = _profiles(rng, 96, 1.0, [0.9, 0.8, 0.7, 0.6, 0.5, 0.4, 0.3, 0.2], 0.01)
    for delta in (1e-6, 1e-30):
        pmax, w, d2, _ = _box(P, delta)
        t = corner(pmax, w, d2)
        # DERIVED: the case under test is the corner past min d^2 = 1.
        assert t > 1.0, t
        u = CG.d2_upper(P, delta)
        brute = max(f(np.asarray(pmax) * np.array(bits), w, d2)
                    for bits in itertools.product((0.0, 1.0), repeat=len(pmax)))
        assert u > t
        assert abs(u - brute) <= RTOL * brute, (u, brute)
        assert math.isfinite(u)


def test_d2_upper_just_above_one_is_the_box_maximum():
    """The regime the real grid reaches (a corner of 1.3684 at beta=0.50, delta=1e-6): corner value
    between 1 and 2. A threshold written anywhere in [1, 2) in place of 1 would return the corner
    here, and this test rejects it."""
    rng = np.random.default_rng(6)
    base = np.array([0.9, 0.8, 0.7, 0.6, 0.5, 0.4, 0.3, 0.2])
    # CHOSEN: noise and ensemble size as the grid's smallest ensemble; the scale is searched below.
    noise = rng.standard_normal((96, 9))
    found = False
    for s in np.geomspace(1e-3, 1.0, 400):
        P = np.column_stack([np.ones(96), np.tile(base * s, (96, 1))]) + 0.001 * noise
        pmax, w, d2, _ = _box(P, 1e-6)
        t = corner(pmax, w, d2)
        # DERIVED: 1 = min d^2 is where the corner stops being the maximum; 2 bounds the band a
        # wrong threshold in [1, 2) would still cover.
        if 1.0 < t < 2.0:
            found = True
            u = CG.d2_upper(P, 1e-6)
            brute = max(f(np.asarray(pmax) * np.array(bits), w, d2)
                        for bits in itertools.product((0.0, 1.0), repeat=len(pmax)))
            assert u > t, (s, t, u)
            assert abs(u - brute) <= RTOL * brute, (s, u, brute)
    assert found, "no scale put the corner between 1 and 2; the test exercised nothing"


def test_d2_upper_is_inf_without_a_positive_rho0_bound():
    rng = np.random.default_rng(5)
    # CHOSEN: a lag-0 mean at 0 with unit noise, so its lower bound is negative and no box exists.
    P = _profiles(rng, 20, 0.0, [0.1] * 8, 1.0)
    assert CG.d2_upper(P, 1e-3) == math.inf


@pytest.mark.filterwarnings("ignore:Degrees of freedom:RuntimeWarning")    # the n=1 case, on purpose
def test_d2_upper_is_inf_not_zero_on_undefined_bounds():
    """A NaN sample, or a single configuration (sample variance undefined), gives no enclosure.
    Compared as `lo0 <= 0` a NaN falls through, and max(0.0, nan) turns every lag into 0 -- a bound
    of 0.0, the most optimistic value there is."""
    rng = np.random.default_rng(7)
    P = _profiles(rng, 50, 1.0, [0.05] * 8, 0.01)
    P0 = P.copy(); P0[3, 0] = np.nan
    Pd = P.copy(); Pd[3, 4] = np.nan
    assert CG.d2_upper(P0, 1e-3) == math.inf
    assert CG.d2_upper(Pd, 1e-3) == math.inf
    assert CG.d2_upper(P[:1], 1e-3) == math.inf


def test_ratio_box_max_refuses_inputs_outside_its_proof():
    with pytest.raises(ValueError):
        CG.ratio_box_max((-1.0,), (1.0,), (1.0,))
    with pytest.raises(ValueError):
        CG.ratio_box_max((1.0,), (0.0,), (1.0,))
    with pytest.raises(ValueError):
        CG.ratio_box_max((float("nan"),), (1.0,), (1.0,))
    with pytest.raises(ValueError):
        CG.d2_upper(np.ones((10, 1)), 1e-3)


@pytest.mark.parametrize("pmax, w, d2", [((), (), ()), ((0.0,), (1.0,), (4.0,))])
def test_degenerate_boxes(pmax, w, d2):
    """No lags, or a box collapsed to p = 0: the read is 0 there and nothing exceeds it."""
    # DERIVED: f(0) = 0 / 1.
    assert CG.ratio_box_max(pmax, w, d2) == 0.0
