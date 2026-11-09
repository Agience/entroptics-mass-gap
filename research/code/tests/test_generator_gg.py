"""The Georgi-Glashow generator (SU(2) links with a unit adjoint Higgs): the checks that make it a valid
control before any phase is read from it. Tiny lattices; exact identities where one exists, and the
heat bath against its own closed-form law."""
import math

import numpy as np
import pytest

import lattice_generator as G


# DERIVED: 0 is only the default stream; each test names its own seed where it matters.
def _b(seed=0):
    return G._Backend(None).seed(seed)


def _random_gauge(b, dims):
    g = b.randn((*dims, 4))
    return g / b.norm(g, -1, True)


def _transform(b, q, phi, g):
    """U_mu(x) -> g(x) U_mu(x) g(x+mu)*, phi(x) -> R(g(x)) phi(x)."""
    q2 = b.clone(q)
    for mu in range(G.D):
        g_f = b.roll(g, -1, G._sax(mu, 1))
        q2[..., mu, :] = G._qmul(b, G._qmul(b, g, q[..., mu, :]), G._qconj(b, g_f))
    return q2, G._qrot(b, g, phi)


def test_qrot_is_a_rotation_and_a_homomorphism():
    b = _b(1)
    q1, q2 = _random_gauge(b, (50,)), _random_gauge(b, (50,))
    v = b.randn((50, 3))
    r = G._qrot(b, q1, v)
    assert np.allclose(np.linalg.norm(r, axis=-1), np.linalg.norm(v, axis=-1))
    assert np.allclose(G._qrot(b, G._qmul(b, q1, q2), v), G._qrot(b, q1, G._qrot(b, q2, v)))


def test_action_is_gauge_invariant():
    b = _b(2)
    dims = (4, 4, 4, 4)
    q, phi = G.gg_init(b, dims, ())
    q2, phi2 = _transform(b, q, phi, _random_gauge(b, dims))
    beta, kappa = 2.3, 0.7
    assert math.isclose(float(G.gg_action(b, q, phi, beta, kappa)),
                        float(G.gg_action(b, q2, phi2, beta, kappa)), rel_tol=1e-12)


def test_link_sweep_at_zero_kappa_is_the_pure_su2_sweep():
    dims = (4, 4, 4, 4)
    b0 = _b(3)
    q, phi = G.gg_init(b0, dims, ())
    qa, qb = b0.clone(q), b0.clone(q)
    G._su2_sweep(_b(9), qa, dims, 2.3, 0.35)
    G._gg_link_sweep(_b(9), qb, phi, dims, 2.3, 0.0, 0.35)
    assert np.array_equal(qa, qb)


def test_link_sweep_reads_the_hopping_term():
    dims = (4, 4, 4, 4)
    b0 = _b(4)
    q, phi = G.gg_init(b0, dims, ())
    qa, qb = b0.clone(q), b0.clone(q)
    G._gg_link_sweep(_b(9), qa, phi, dims, 2.3, 0.0, 0.35)
    G._gg_link_sweep(_b(9), qb, phi, dims, 2.3, 2.0, 0.35)
    assert not np.array_equal(qa, qb)


@pytest.mark.parametrize("k", [0.0, 0.3, 2.0, 25.0])
def test_vmf_cosine_matches_its_closed_form_mean(k):
    b = _b(5)
    n = 200_000
    w = G.vmf_cos(b, np.full(n, k), b.rand(n))
    # DERIVED: the von Mises-Fisher mean cosine on S^2 is coth(k) - 1/k, and 0 at k = 0 (uniform).
    mean = 0.0 if k == 0 else 1.0 / math.tanh(k) - 1.0 / k
    se = float(np.std(w)) / math.sqrt(n)
    # DERIVED: 5 standard errors, a two-sided level of 6e-7 per case.
    assert abs(float(np.mean(w)) - mean) < 5 * se
    assert float(w.min()) >= -1.0 - 1e-12 and float(w.max()) <= 1.0 + 1e-12


def test_heatbath_samples_the_conditional_law():
    """The first colour of the heat bath (even sites) is drawn against the untouched odd sites, so the
    new cosine to h(x) at an even site is von Mises-Fisher at k = kappa |h(x)|, whatever the second
    colour does afterwards. Checked on the mean over sites and repetitions."""
    dims = (4, 4, 4, 4)
    b = _b(6)
    q, phi = G.gg_init(b, dims, ())
    kappa = 0.8
    even = b.parity(dims)[0]
    n, _e1, _e2, hn = G._gg_frame(b, G._gg_higgs_field(b, q, phi))
    k = kappa * hn[even]
    want = float(np.mean(1.0 / np.tanh(k) - 1.0 / k))
    got = []
    for rep in range(300):
        p = b.clone(phi)
        G._gg_higgs_heatbath(_b(100 + rep), q, p, dims, kappa)
        assert np.allclose(np.linalg.norm(p, axis=-1), 1.0)
        got.append(float((p * n).sum(-1)[even].mean()))
    # DERIVED: 5 standard errors of the repetition mean.
    assert abs(np.mean(got) - want) < 5 * np.std(got) / math.sqrt(len(got))


def test_overrelaxation_is_microcanonical():
    dims = (4, 4, 4, 4)
    b = _b(7)
    q, phi = G.gg_init(b, dims, ())
    s0 = float(G.gg_action(b, q, phi, 2.3, 1.1))
    G._gg_higgs_overrelax(b, q, phi, dims)
    assert math.isclose(float(G.gg_action(b, q, phi, 2.3, 1.1)), s0, rel_tol=1e-12)
    assert np.allclose(np.linalg.norm(phi, axis=-1), 1.0)


def test_large_kappa_deficit_obeys_equipartition():
    """At large kappa the Higgs and the four links' transverse directions are harmonic with stiffness
    of order kappa: 2 + 4 * 2 modes per site, less the 2 gauge rotations that turn the Higgs, so 8
    physical modes carrying 1/2 each. The hopping term's share of that is at most all of it, so
    kappa * (1 - hopping per link) rises toward 1 from below as kappa grows past beta.

    Cold start: a hot start at kappa = 128 is not thermalised in this many sweeps (it reads above the
    bound), which is the reason the campaign brackets its thermalisation from both starts."""
    b = _b()
    got = {}
    for kappa in (32.0, 128.0):
        vals = []
        for seed in range(3):
            q, phi = G.gg_field((4, 4, 4, 4), 2.5, kappa, seed=seed, therm=150, start="cold")
            vals.append(kappa * (1.0 - float(G.gg_hopping(b, q, phi).mean()) / G.D))
        got[kappa] = (np.mean(vals), np.std(vals) / math.sqrt(len(vals)))
    for kappa, (m, se) in got.items():
        # DERIVED: 1 is the equipartition ceiling above; 5 standard errors of the seed mean.
        assert m <= 1.0 + 5 * se, (kappa, m, se)
    # DERIVED: the plaquette's share of the stiffness shrinks as kappa grows, so the value rises.
    assert got[128.0][0] > got[32.0][0] - 5 * math.hypot(got[128.0][1], got[32.0][1])
    # CHOSEN: 0.5 excludes a Higgs that does not align at all (which reads near kappa) and anything
    # far below the ceiling; the measured values sit at 0.90 and 0.93.
    assert got[32.0][0] > 0.5


def test_zero_kappa_higgs_decouples():
    """At kappa = 0 the Higgs is uniform on S^2 whatever the links: its mean hopping is zero."""
    q, phi = G.gg_field((4, 4, 4, 4), 2.5, 0.0, seed=1, therm=10)
    hop = G.gg_hopping(_b(), q, phi) / G.D
    se = float(hop.std()) / math.sqrt(hop.size)
    assert abs(float(hop.mean())) < 5 * se
