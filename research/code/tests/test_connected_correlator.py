"""`lattice_generator.connected_correlator` is the object every gap in this program is read from.

Sec 8.7's `C(tau)/C(0)` table, its `m_eff`, the transfer pencil of Table 1 and every `pencil_rate`
and `lag_budget` in the certificates all descend from this one function, and until these tests it
had no direct coverage at all -- it was exercised only through `aperture_reads.pencil_rate`, which
reports `nan` for a broad class of inputs and so cannot distinguish a wrong profile from a
correlator that decayed into noise.

WHAT IS PINNED, and why each one is a thing that has been gettable wrong:

  * THE VALUES. The profile is compared against the arithmetic it states -- the periodic lag
    average about the ENSEMBLE mean, written out here directly. That reference is a definition, not
    a golden file: it is what the docstring says the quantity IS, so a rewrite of the body is
    measured against the claim rather than against the last run's numbers.
  * THE LEVEL. `reads.decay`'s default subtracts each channel's OWN mean. This function subtracts
    the ensemble mean, and `c / c[0]` does not put the difference back -- the two profiles differ by
    a constant at every lag, which the normalisation does not cancel. That is asserted with its own
    algebra, because it is the single change that would leave every number plausible and every
    number wrong.
  * THE RING. `C(tau) == C(T - tau)` exactly, and `nlag` past `T - 1` aliases rather than running
    off the end.
  * THE REFUSALS. Empty, complex and non-finite records raise. `T = 0` in particular would
    otherwise return an all-ones profile: perfect correlation at every lag, read off no data.
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import lattice_generator as G                                          # noqa: E402


def reference(O, nlag):
    """`C(tau)/C(0)` written out: the periodic lag average of the ensemble-connected record.

    Deliberately the slow, literal form -- one explicit sum per lag about one explicit level. It is
    the definition the docstring states, so it is what the implementation owes its values to.
    """
    O = np.asarray(O, dtype=float)
    n, T = O.shape
    d = O - O.mean()
    c = np.array([sum(float(d[k, t] * d[k, (t + tau) % T]) for k in range(n) for t in range(T))
                  / (n * T) for tau in range(nlag + 1)])
    return c / c[0]


# CHOSEN: the fixture's shape and its AR(1) parameters. Nothing here decides a verdict -- every
# assertion below compares the read against the arithmetic it claims on whatever record it is given,
# so these only have to produce a record with a decay along time, a level well away from zero (so a
# level convention has something to get wrong) and per-configuration offsets when asked. The
# parametrised cases override all of them.
def ensemble(rng, n=48, T=12, rho=0.7, offset=0.0, level=5.0):
    """An `(nconf, T)` operator history with a real decay along time and per-configuration offsets.

    `offset` is what separates the two level conventions: with every configuration sitting at the
    same height the two agree, and the test that matters is the one where they do not.
    """
    x = rng.standard_normal((n, T))
    for t in range(1, T):
        x[:, t] = rho * x[:, t - 1] + np.sqrt(1.0 - rho ** 2) * x[:, t]
    return x + offset * rng.standard_normal((n, 1)) + level


@pytest.mark.parametrize("n,T,nlag,offset", [
    (48, 12, 6, 0.0),
    (48, 12, 6, 3.0),          # per-configuration offsets: where the level convention shows
    (64, 16, 13, 2.0),         # nlag past T - 1: the profile aliases
    (96, 8, 13, 0.0),
    (2, 16, 6, 1.0),           # the smallest ensemble a connected correlator exists on
    (1, 16, 6, 0.0),           # one configuration: every channel mean IS the ensemble mean
    (32, 3, 4, 2.0),           # short records, where the two levels disagree in sign
    (32, 2, 4, 2.0),
])
def test_profile_is_the_periodic_lag_average_about_the_ensemble_mean(n, T, nlag, offset):
    """The values, against the arithmetic the docstring states."""
    O = ensemble(np.random.default_rng(n * 1000 + T * 10 + nlag), n=n, T=T, offset=offset)
    got, want = G.connected_correlator(O, nlag), reference(O, nlag)
    assert got.shape == want.shape == (nlag + 1,)
    # DERIVED: the arithmetic's own resolution. The reference accumulates n*T products in Python
    # order and the read accumulates the same products through a Gram; the two orders differ, so
    # they agree to the backward error of a sum of that many terms, not exactly.
    tol = 64 * n * T * np.finfo(float).eps
    assert np.max(np.abs(got - want)) <= tol, f"max |delta| = {np.max(np.abs(got - want)):.3e}"


def test_lag_zero_is_one():
    O = ensemble(np.random.default_rng(0), offset=2.0)
    # DERIVED: the normalisation is `c / c[0]`, so lag 0 is a quantity divided by itself. Exactly
    # one, not one to within a tolerance -- a tolerance here would hide a profile that was not
    # normalised at all.
    assert G.connected_correlator(O, 5)[0] == 1.0


def test_the_ring_closes():
    """`C(tau) == C(T - tau)` exactly -- the property `periodic=True` is taken for."""
    T = 12
    c = G.connected_correlator(ensemble(np.random.default_rng(1), T=T, offset=2.0), T - 1)
    for tau in range(1, T):
        assert c[tau] == c[T - tau], f"lag {tau} and lag {T - tau} differ"


def test_lags_past_the_time_extent_alias_rather_than_run_off_the_end():
    T, nlag = 8, 19
    c = G.connected_correlator(ensemble(np.random.default_rng(2), T=T, offset=1.0), nlag)
    assert c.shape == (nlag + 1,)
    for tau in range(nlag + 1):
        assert c[tau] == c[tau % T]


def test_the_level_is_the_ensemble_mean_and_the_normalisation_does_not_restore_the_choice():
    """The per-channel level gives a DIFFERENT profile, offset by a constant the ratio keeps.

    With `u` the record with each channel's own mean removed, the ensemble-level profile is
    `C_per_channel(tau) + K` with `K = var_f(mean_t O)` -- the same constant at every lag, lag 0
    included -- so `(C + K)/(C(0) + K)` is not `C/C(0)`. This asserts the identity and then asserts
    that the two normalised profiles are far apart, which is the part that matters.
    """
    from entroptics_adapter import decay

    O = ensemble(np.random.default_rng(3), n=64, T=16, offset=3.0)
    n, T = O.shape
    per_channel = np.asarray(decay(O.T, periodic=True)) / n            # the library's DEFAULT level
    ensemble_lvl = np.asarray(decay(O.T, periodic=True, disconnected=float(O.mean()))) / n

    K = float(np.mean((O.mean(axis=1) - O.mean()) ** 2))
    # DERIVED: `K` is a variance, so zero is where the configurations share one mean exactly and the
    # two conventions coincide. A positive-control on the FIXTURE, not a threshold on the result:
    # without offsets this test would pass by having nothing to detect.
    assert K > 0, "the fixture must carry per-configuration offsets or there is nothing to test"
    tol = 64 * n * T * np.finfo(float).eps * max(1.0, abs(ensemble_lvl[0]))
    assert np.max(np.abs(ensemble_lvl - (per_channel + K))) <= tol

    got = G.connected_correlator(O, 4)
    other = (per_channel / per_channel[0])[:5]
    # DERIVED: the same round-off tolerance the identity above is checked to. If the level choice
    # made no difference to the normalised profile -- the thing `c / c[0]` is sometimes assumed to
    # arrange -- the two would agree to exactly this. They do not, and the gap is the finding. No
    # separation is chosen here; the measured one is reported when it fails.
    sep = float(np.max(np.abs(got - other)))
    assert sep > tol, (
        f"the two level conventions agree to {sep:.3e}, within the {tol:.3e} round-off of the "
        f"identity above: either the fixture lost its offsets or this function stopped passing "
        f"the ensemble level")


def test_a_constant_history_is_not_a_decay():
    """No deviation from the level means no profile -- `nan`, not the round-off divided by itself."""
    c = G.connected_correlator(np.full((16, 8), 3.25), 5)
    assert np.isnan(c).all()


def test_a_history_flat_in_time_is_perfectly_correlated():
    """Configurations that differ from each other but not across time: every lag carries the same
    deviation, so the profile is 1 at every lag. The complement of the constant case."""
    O = np.repeat(np.random.default_rng(4).standard_normal((16, 1)), 8, axis=1)
    assert np.allclose(G.connected_correlator(O, 5), 1.0)


@pytest.mark.parametrize("bad,why", [
    (np.zeros((8, 0)), "empty time axis"),
    (np.zeros((0, 16)), "empty ensemble"),
    (np.zeros(16), "one-dimensional"),
    (np.zeros((4, 8, 3)), "three-dimensional"),
    (np.zeros((8, 6), dtype=complex), "complex"),
])
def test_an_input_that_is_not_an_ensemble_raises(bad, why):
    with pytest.raises(ValueError):
        G.connected_correlator(bad, 3)


@pytest.mark.parametrize("cell", [np.nan, np.inf, -np.inf])
def test_a_non_finite_record_raises(cell):
    """It must not return an all-`nan` profile: downstream that reads as a correlator in noise."""
    O = ensemble(np.random.default_rng(5))
    O[3, 2] = cell
    with pytest.raises(ValueError):
        G.connected_correlator(O, 3)


def test_an_empty_time_axis_does_not_read_as_perfect_correlation():
    """The specific shape of the refusal above, stated on its own because the alternative is the
    worst kind of wrong answer: `(n, 0)` has no lags, and the profile it would otherwise return is
    all ones -- the strongest claim the read can make, from no data."""
    with pytest.raises(ValueError, match="empty ensemble"):
        G.connected_correlator(np.zeros((8, 0)), 3)
