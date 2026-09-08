"""The config generator: shapes, finiteness, non-negativity of the action density, and the
group dispatch. Tiny lattices and short thermalisation (validity, not physics)."""
import numpy as np
import pytest

import lattice_generator as generator


@pytest.mark.parametrize("group", ["u1", "su2", "su3"])
def test_action_density_nonneg_and_finite(group):
    phi = generator.config((4, 4, 4, 8), beta=1.0, group=group, therm=5)
    assert phi.shape == (4, 4, 4, 8)
    assert np.all(np.isfinite(phi))
    assert float(phi.min()) >= -1e-9          # phi = sum (1 - Re tr U_p / N) >= 0


def test_free_scalar_shape_and_finite():
    f = generator.free_scalar((8, 8, 32), m=0.5, seed=0)
    assert f.shape == (8, 8, 32)
    assert np.all(np.isfinite(f))


def test_free_scalar_is_deterministic():
    a = generator.free_scalar((8, 8, 32), m=0.5, seed=3)
    b = generator.free_scalar((8, 8, 32), m=0.5, seed=3)
    assert np.array_equal(a, b)


def test_stream_yields_n_decorrelated_fields():
    cfgs = list(generator.stream((4, 4, 4, 8), 1.0, group="u1", n=3, therm=3, gap=2))
    assert len(cfgs) == 3
    assert all(c.shape == (4, 4, 4, 8) for c in cfgs)
    assert all(np.all(np.isfinite(c)) for c in cfgs)


def test_gauge_field_then_action_density_matches_config_path():
    link = generator.gauge_field((4, 4, 4, 8), beta=1.0, group="su2", seed=0, therm=4)
    phi = generator.action_density(link, group="su2")
    assert phi.shape == (4, 4, 4, 8)
    assert np.all(np.isfinite(phi)) and float(phi.min()) >= -1e-9


def test_sun_dispatch_accepts_n_ge_3():
    phi = generator.config((4, 4, 4, 6), beta=2.0, group="su4", therm=3)
    assert phi.shape == (4, 4, 4, 6) and np.all(np.isfinite(phi))


def test_unknown_group_raises():
    with pytest.raises(ValueError):
        generator.config((4, 4, 4, 8), group="bogus")


def test_su1_rejected():
    with pytest.raises(ValueError):
        generator.config((4, 4, 4, 8), group="su1")


# ── method= threading (heatbath vs metropolis) ───────────────────────────────────────────
# Regression guard: `config_batch`/`gauge_field`/`stream` must PASS `method=` down to `config`/`_ops`.
# The batched fast path once accepted `method=` but silently dropped it, so `method="heatbath"` ran
# Metropolis for SU(2)/SU(N).  Heatbath and Metropolis are DIFFERENT updates, so for the same seed and
# init they produce DIFFERENT configs -- if `method` were dropped, both would be Metropolis and IDENTICAL.

@pytest.mark.parametrize("group", ["su2", "su3"])
def test_config_batch_threads_method(group):
    hb = np.asarray(generator.config_batch((4, 4, 4, 8), beta=2.0, group=group, n=2, therm=4,
                                           seed=0, method="heatbath"))
    mc = np.asarray(generator.config_batch((4, 4, 4, 8), beta=2.0, group=group, n=2, therm=4,
                                           seed=0, method="metropolis"))
    assert hb.shape == (2, 4, 4, 4, 8) and np.all(np.isfinite(hb)) and float(hb.min()) >= -1e-9
    assert not np.array_equal(hb, mc), \
        f"{group}: config_batch ignored method= (heatbath == metropolis -- method dropped)"


@pytest.mark.parametrize("group", ["su2", "su3"])
def test_gauge_field_threads_method(group):
    hb = generator.action_density(
        generator.gauge_field((4, 4, 4, 8), beta=2.0, group=group, seed=0, therm=4, method="heatbath"),
        group=group)
    mc = generator.action_density(
        generator.gauge_field((4, 4, 4, 8), beta=2.0, group=group, seed=0, therm=4, method="metropolis"),
        group=group)
    assert not np.array_equal(np.asarray(hb), np.asarray(mc)), \
        f"{group}: gauge_field ignored method= (heatbath == metropolis -- method dropped)"


def test_stream_threads_method():
    hb = list(generator.stream((4, 4, 4, 8), 2.0, group="su2", n=1, therm=4, gap=1, method="heatbath"))[0]
    mc = list(generator.stream((4, 4, 4, 8), 2.0, group="su2", n=1, therm=4, gap=1, method="metropolis"))[0]
    assert not np.array_equal(np.asarray(hb), np.asarray(mc)), \
        "stream ignored method= (heatbath == metropolis -- method dropped)"


def test_su3_overrelax_is_microcanonical():
    """The SU(N) Cabibbo-Marinari over-relaxation must PRESERVE the plaquette action exactly
    (micro-canonical), so heat-bath + over-relaxation samples the SAME equilibrium as heat-bath
    alone -- just faster to thermalise. If the reflection formula were wrong, the action would drift."""
    b = generator._Backend(None).seed(0)
    dims, N = (4, 4, 4, 6), 3
    link = generator._sun_init(b, dims, (2,), N)
    for _ in range(8):                                   # thermalise a bit (heat-bath + OR)
        generator._sun_hb_sweep(b, link, dims, N, 6.0, None, n_or=2)
    phi0 = float(generator._sun_action(b, link, N).mean())
    for _ in range(10):                                  # OR-ONLY passes must not change the action
        generator._sun_cm_pass(b, link, dims, N, 6.0, overrelax=True)
    phi1 = float(generator._sun_action(b, link, N).mean())
    assert abs(phi1 - phi0) < 1e-8, \
        f"su3 over-relaxation is not micro-canonical: action drifted {phi0} -> {phi1}"
