"""The wrapper read layer (research/code/entroptics_adapter.py): the typed reads and the certified
confinement intervals, all via the public ``run()`` surface. The instrument is anchored on the free
scalar (a known gap); the gauge reads check shape, finiteness, and the certificate invariants."""
import math

import numpy as np
import pytest

import entroptics_adapter as entroptics
import lattice_generator as generator


# ── the read entry point ──────────────────────────────────────────────────────

def test_run_requires_at_least_one_config():
    with pytest.raises(ValueError):
        entroptics.run([])


def test_mass_gap_recovers_free_scalar_gap(free_configs):
    """The forward operator read (dominant Koopman/DMD mode rate -log|mu_1|) recovers the exact
    free-scalar gap E0 = arccosh(1 + m^2/2)."""
    mg = entroptics.run(free_configs).mass_gap
    e0 = math.acosh(1 + 0.6 ** 2 / 2)
    assert mg == pytest.approx(e0, rel=0.15)


def test_mass_gap_recovers_gap_across_Lt_and_is_deterministic():
    """The forward operator gap read recovers E0 within ensemble statistics at every time extent
    Lt, and is DETERMINISTIC in the operator eigenvalues: a repeated read of the same configs is
    bit-identical."""
    e0 = math.acosh(1 + 0.5 ** 2 / 2)
    gaps = []
    for Lt in (16, 32, 64):
        cfgs = [generator.free_scalar((8, 8, Lt), 0.5, seed=s) for s in range(48)]
        g = entroptics.run(cfgs).mass_gap
        assert entroptics.run(cfgs).mass_gap == g          # deterministic (bit-identical repeat)
        gaps.append(g)
    gaps = np.array(gaps)
    assert np.all(np.abs(gaps / e0 - 1.0) < 0.20)          # every Lt within statistics of the true gap


def test_a_delta_tracks_mass_on_free_scalar():
    """The connected diffraction limit rises with the mass (heavier gap -> more concentrated)."""
    light = entroptics.run([generator.free_scalar((8, 8, 49), 0.3, seed=s) for s in range(8)]).a_delta
    heavy = entroptics.run([generator.free_scalar((8, 8, 49), 1.0, seed=s) for s in range(8)]).a_delta
    assert heavy > light


# ── gauge reads: shape and finiteness ─────────────────────────────────────────

def test_ordered_and_spatial_reads_finite(su2_configs, pin_su2):
    r = entroptics.run(su2_configs)
    assert np.isfinite(r.mass_gap)
    assert np.isfinite(r.a_delta)
    assert np.isfinite(r.contrast)          # floor read -> needs a pinned reference (pin_su2)
    assert r.confinement >= 0.0             # floor read -> needs a pinned reference (pin_su2)
    assert np.isfinite(r.coherence)


def test_spectral_reads_finite_and_bounded(su2_configs, pin_su2):
    """The correlation-spectrum reads exposed off the same batched spectral pass as contrast
    (resolved_modes / attenuation / top_share / dispersion) read finite and in range."""
    r = entroptics.run(su2_configs)
    assert np.isfinite(r.resolved_modes) and r.resolved_modes >= 0.0
    assert np.isfinite(r.attenuation) and r.attenuation >= 0.0
    assert np.isfinite(r.top_share) and 0.0 <= r.top_share <= 1.0
    assert np.isfinite(r.dispersion) and r.dispersion >= 0.0


def test_temporal_interval_ordered(su2_configs):
    t = entroptics.run(su2_configs).temporal
    assert t.attenuation_lo <= t.attenuation_hi
    assert np.isfinite(t.attenuation)
    assert 0.0 <= t.certified <= 1.0


def test_optics_schema_reads_finite(free_configs, pin_free):
    o = entroptics.run(free_configs).optics          # optics includes the spectral floor read -> needs a pin
    assert np.isfinite(o.a_delta) and o.a_delta >= 0.0
    assert np.isfinite(o.correlation_length)
    assert np.isfinite(o.strehl)


def test_time_axis_selects_axis(su2_configs):
    """Reading across a spatial axis is a different aperture than across time."""
    r_t = entroptics.run(su2_configs, time_axis=-1).a_delta
    r_x = entroptics.run(su2_configs, time_axis=0).a_delta
    assert np.isfinite(r_t) and np.isfinite(r_x)


# ── the certified confinement reads ───────────────────────────────────────────

def test_confinement_certificate_invariants(su2_configs, pin_su2):
    c = entroptics.run(su2_configs).confinement_certificate
    assert c.attenuation_lo <= c.attenuation <= c.attenuation_hi
    assert c.resolved_lo <= c.resolved_modes <= c.resolved_hi
    assert c.band > 0.0
    assert c.n_samples > 0 and c.n_features >= 2


def test_confinement_certificate_band_tightens_with_ensemble(pin_su2):
    """More configs -> more pooled samples -> a tighter certified band."""
    small = entroptics.run(list(generator.stream((5, 5, 5, 16), 2.0, group="su2",
                                                  n=2, therm=20))).confinement_certificate
    large = entroptics.run(list(generator.stream((5, 5, 5, 16), 2.0, group="su2",
                                                  n=6, therm=20))).confinement_certificate
    assert large.n_samples > small.n_samples
    assert large.band < small.band


def test_k_signal_certificate_interval(su2_configs, pin_su2):
    c = entroptics.run(su2_configs).k_signal_certificate(delta=0.05)
    assert c.n == len(su2_configs)
    assert c.lo <= c.mean <= c.hi
    assert c.std >= 0.0
    assert 0.0 < c.delta < 1.0


def test_k_signal_certificate_single_config_degenerate(pin_free):
    c = entroptics.run([generator.free_scalar((8, 8, 49), 0.6, seed=0)]).k_signal_certificate()
    assert c.n == 1 and c.lo == c.mean == c.hi
