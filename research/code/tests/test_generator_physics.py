"""Physics certification of the lattice-gauge Monte-Carlo generator (``lattice_generator``).

Every check below compares a MEASURED observable against a value KNOWN from analytic lattice gauge
theory (cited inline), with a tolerance taken from Monte-Carlo statistics (a stated number of standard
errors) plus, where relevant, an explicit truncation/systematic allowance.  Nothing here is fit to the
generator's own output: the reference numbers are external.  Small CPU lattices, fixed seeds, short but
sufficient thermalisation.

Conventions (Wilson action)
---------------------------
The generator samples the Wilson weight exp(+beta * sum_p (1/N) Re tr U_p) (equivalently exp(-S),
S = beta * sum_p [1 - (1/N) Re tr U_p]); larger beta favours ordered plaquettes.  ``config``/
``config_batch`` return the action-density field phi(x) = sum_{mu<nu} [1 - (1/N) Re tr U_p(x)].  On a
D=4 lattice there are NP = D(D-1)/2 = 6 planes, so the mean plaquette is

    <P> := < (1/N) Re tr U_p >  =  1 - mean(phi)/NP        (SU(N))
    <cos theta_p>               =  1 - mean(phi)/NP        (U(1))

References
----------
* M. Creutz, "Monte Carlo study of quantized SU(2) gauge theory", Phys. Rev. D 21 (1980) 2308
  -- SU(2): strong coupling <P> -> beta/4; weak coupling <P> -> 1 - 3/(4 beta).
* M. Creutz, "Quarks, Gluons and Lattices" (CUP 1983), ch. on strong/weak coupling expansions.
* I. Montvay & G. Munster, "Quantum Fields on a Lattice" (CUP 1994), sec. 5 -- SU(N) character
  expansion: <P> -> beta/(2 N^2) leading (N>=3); U(1): <cos theta_p> = I1(beta)/I0(beta) -> beta/2.
* Standard quenched SU(3) Wilson plaquette values (large-volume): <P>(5.7) ~ 0.5498, <P>(6.0) ~ 0.5937
  (e.g. tabulated in the scale-setting / string-tension literature; the plaquette is UV-dominated and
  varies by <~0.5% between a 6^4 box and the infinite-volume limit).
"""
import math

import numpy as np
import pytest
from scipy import stats

import lattice_generator as generator
import ensemble_cache

D = generator.D                      # 4
NP = D * (D - 1) // 2                 # 6 planes on a 4D lattice


# ── helpers ───────────────────────────────────────────────────────────────────

def plaquette_per_config(dims, beta, *, group, n, therm, seed, method="heatbath"):
    """Return the length-``n`` array of per-config mean plaquettes <P>_i from ``n`` INDEPENDENT chains
    (``config_batch`` runs independent batched chains, each its own RNG stream), giving an honest i.i.d.
    error bar.  <P>_i = 1 - mean_x phi_i(x)/NP.

    Cached on disk (``ensemble_cache``): the generator is seeded, so these numbers are the same on
    every run and cost a full 6^4 thermalisation to reproduce.  The cache key includes a fingerprint
    of ``lattice_generator.py``, so editing the generator regenerates instead of re-serving.
    """
    def produce():
        phi = np.asarray(generator.config_batch(dims, beta, group=group, n=n, therm=therm,
                                                seed=seed, method=method))
        return 1.0 - phi.reshape(phi.shape[0], -1).mean(axis=1) / NP

    return ensemble_cache.cached(
        "plaquette", dict(dims=tuple(dims), beta=beta, group=group, n=n, therm=therm,
                          seed=seed, method=method, NP=NP), produce)


def mean_se(per):
    """(mean, standard error of the mean) of a per-config sample."""
    per = np.asarray(per, dtype=float)
    return float(per.mean()), float(per.std(ddof=1) / math.sqrt(len(per)))


# ══════════════════════════════════════════════════════════════════════════════
# 1. Group membership / unitarity: generated links are genuinely in the group.
# ══════════════════════════════════════════════════════════════════════════════

def test_su2_links_are_unit_quaternions_and_unitary():
    q = np.asarray(generator.gauge_field((4, 4, 4, 4), 2.0, group="su2", seed=1, therm=6,
                                         method="heatbath"))
    assert np.abs(np.linalg.norm(q, axis=-1) - 1.0).max() < 1e-12          # |q| = 1  <=>  SU(2)
    U = np.asarray(generator._su2_matrix(generator._Backend(None), q))      # (...,2,2)
    UUd = np.einsum("...ij,...kj->...ik", U, U.conj())
    assert np.abs(UUd - np.eye(2)).max() < 1e-12                            # U U^dag = 1
    assert np.abs(np.linalg.det(U) - 1.0).max() < 1e-12                     # det = 1


def test_su3_links_are_special_unitary():
    U = np.asarray(generator.gauge_field((4, 4, 4, 4), 5.5, group="su3", seed=1, therm=6,
                                         method="heatbath"))
    UUd = np.einsum("...ij,...kj->...ik", U, U.conj())
    assert np.abs(UUd - np.eye(3)).max() < 1e-10                            # U U^dag = 1
    assert np.abs(np.linalg.det(U) - 1.0).max() < 1e-10                     # det = 1


def test_u1_links_are_unit_modulus():
    th = np.asarray(generator.gauge_field((4, 4, 4, 4), 1.0, group="u1", seed=1, therm=6))
    assert np.isrealobj(th)
    assert np.abs(np.abs(np.exp(1j * th)) - 1.0).max() < 1e-12              # |z| = 1


# ══════════════════════════════════════════════════════════════════════════════
# 2. Strong-coupling limit (beta -> 0): leading character-expansion plaquette.
#    For a plaquette of independent-Haar links, <((1/N)Re tr U_p)^2>_Haar = 1/(2N^2) (N>=3) or 1/4
#    (SU(2), pseudoreal fundamental), and to O(beta) <P> = beta * <P^2>_Haar.  Hence:
#        U(1):  <cos theta_p> -> beta/2         (= I1/I0 leading; Montvay-Munster 5)
#        SU(2): <P>           -> beta/4         (Creutz 1980)
#        SU(3): <P>           -> beta/(2N^2)=beta/18   (Montvay-Munster 5.2)
#    Tested at beta=0.2, where the next (O(beta^3)) term is <~0.5% of the leading value, i.e. far below
#    the Monte-Carlo error, so the assertion is 4 sigma statistical.
# ══════════════════════════════════════════════════════════════════════════════

@pytest.mark.parametrize("group,ref", [
    ("u1",  0.2 / 2.0),          # <cos theta_p> -> beta/2
    ("su2", 0.2 / 4.0),          # <P>           -> beta/4
    ("su3", 0.2 / 18.0),         # <P>           -> beta/(2N^2)
])
def test_strong_coupling_leading_plaquette(group, ref):
    beta = 0.2
    method = "metropolis" if group == "u1" else "heatbath"
    per = plaquette_per_config((6, 6, 6, 6), beta, group=group, n=24, therm=40, seed=11, method=method)
    m, se = mean_se(per)
    trunc = 0.01 * ref                                   # >= the O(beta^3) truncation at beta=0.2
    assert abs(m - ref) < 4.0 * se + trunc, \
        f"{group} strong coupling: measured <P>={m:.5f}+-{se:.5f}, leading ref={ref:.5f}"


# ══════════════════════════════════════════════════════════════════════════════
# 3. Weak-coupling limit (beta -> infinity): 1-loop plaquette slope.
#    Free (Gaussian) lattice gauge theory gives, in D=4,
#        <1 - (1/N)Re tr U_p> = (N^2-1)/(4 beta) + O(1/beta^2),   i.e.  beta*<1-P> -> (N^2-1)/4.
#    Equivalently, with g^2 = 2N/beta,  <1-P> = (N^2-1)/(8N) * g^2 + ...  (coefficient 3/16 for SU(2),
#    1/3 for SU(3)).  In the uniform C/beta form C = (N^2-1)/4:  SU(2) C=3/4 (Creutz 1980), SU(3) C=2.
#    (The "1/3" sometimes quoted for SU(3) is the g^2 coefficient (N^2-1)/(8N), not the 1/beta one.)
#    The series approaches from ABOVE (positive higher-order terms), so beta*<1-P> DECREASES toward C.
# ══════════════════════════════════════════════════════════════════════════════

def test_weak_coupling_su2_slope_three_quarters():
    C = 3.0 / 4.0                                        # (N^2-1)/4 for N=2  (Creutz 1980)
    betas = (6.0, 10.0)
    slope = {}
    for beta in betas:
        per = plaquette_per_config((6, 6, 6, 6), beta, group="su2", n=16, therm=90, seed=21)
        m, se = mean_se(1.0 - per)
        slope[beta] = (beta * m, beta * se)
    hi_b = betas[-1]
    val, err = slope[hi_b]
    # approaches C from above and is within statistics + the residual O(1/beta) tail at beta=10 (<~10%)
    assert slope[betas[0]][0] > val, f"beta*<1-P> not decreasing toward C: {slope}"
    assert abs(val - C) < 4.0 * err + 0.10 * C, \
        f"SU(2) weak-coupling slope beta*<1-P>={val:.4f}+-{err:.4f} at beta={hi_b}, C=(N^2-1)/4={C}"


def test_weak_coupling_su3_coefficient_is_two():
    C = 2.0                                              # (N^2-1)/4 for N=3
    beta = 12.0                                          # SU(3) perturbation theory converges slowly
    # EVEN lattice required: the checkerboard heat-bath disorders on odd extents (guarded in the generator).
    per = plaquette_per_config((6, 6, 6, 6), beta, group="su3", n=8, therm=90, seed=22)
    m, se = mean_se(1.0 - per)
    val, err = beta * m, beta * se
    assert abs(val - C) < 4.0 * err + 0.15 * C, \
        f"SU(3) weak-coupling slope beta*<1-P>={val:.4f}+-{err:.4f} at beta={beta}, C=(N^2-1)/4={C}"


# ══════════════════════════════════════════════════════════════════════════════
# 4. Textbook SU(3) plaquette values (quenched Wilson, large volume).
#    <P> = <(1/3)Re tr U_p>:  beta=5.7 -> ~0.5498,  beta=6.0 -> ~0.5937.  The plaquette is UV-dominated,
#    so a 6^4 box sits within <~0.5% of these infinite-volume numbers; tolerance 4 sigma + 0.5%.
# ══════════════════════════════════════════════════════════════════════════════

@pytest.mark.parametrize("beta,ref", [(5.7, 0.5498), (6.0, 0.5937)])
def test_su3_textbook_plaquette(beta, ref):
    per = plaquette_per_config((6, 6, 6, 6), beta, group="su3", n=10, therm=80, seed=31)
    m, se = mean_se(per)
    assert abs(m - ref) < 4.0 * se + 0.005 * ref, \
        f"SU(3) <P>(beta={beta})={m:.5f}+-{se:.5f}, textbook ref={ref}"


# ══════════════════════════════════════════════════════════════════════════════
# 5. Haar measure at beta=0: a single SU(2) link samples the group Haar measure, so t = (1/2)tr U = q0
#    is distributed with the Vandermonde/semicircle density p(t) = (2/pi) sqrt(1-t^2) on [-1,1].
#    Moments: <t>=0, <t^2>=1/4, <t^4>=1/8.  CDF F(t) = (t sqrt(1-t^2) + arcsin t + pi/2)/pi.
# ══════════════════════════════════════════════════════════════════════════════

def _haar_su2_cdf(t):
    t = np.clip(t, -1.0, 1.0)
    return (t * np.sqrt(1.0 - t * t) + np.arcsin(t) + np.pi / 2.0) / np.pi


def test_su2_beta0_samples_haar_measure():
    # Metropolis at beta=0 always accepts and multiplies each link by a random rotation, a
    # Haar-preserving random walk (Haar is invariant under group multiplication), so it stays exactly
    # Haar-distributed.  The beta=0 heat bath is pinned separately below, where the sampler is
    # checked against its density directly at betak=0.
    q = np.asarray(generator.gauge_field((8, 8, 8, 8), 0.0, group="su2", seed=7, therm=5,
                                         method="metropolis"))
    t = q[..., 0].ravel()                                # t = q0 = (1/2) tr U, one i.i.d. draw per link
    n = t.size
    # moments (all links independent at beta=0): compare to Haar within 4 sigma
    assert abs(t.mean() - 0.0) < 4.0 / math.sqrt(n)                       # <t> = 0
    se2 = np.std(t ** 2, ddof=1) / math.sqrt(n)
    se4 = np.std(t ** 4, ddof=1) / math.sqrt(n)
    assert abs((t ** 2).mean() - 0.25) < 4.0 * se2                        # <t^2> = 1/4
    assert abs((t ** 4).mean() - 0.125) < 4.0 * se4                       # <t^4> = 1/8
    # KS goodness-of-fit on a 5000-link subsample (D well below the 1%/2.5-sigma critical band)
    sub = np.random.default_rng(0).choice(t, size=5000, replace=False)
    Dks, _ = stats.kstest(sub, _haar_su2_cdf)
    assert Dks < 0.04, f"SU(2) beta=0 q0 KS statistic {Dks:.4f} vs Haar (crit@1% ~ 0.023)"


# ══════════════════════════════════════════════════════════════════════════════
# 5b. The a0 heat-bath sampler draws from its density at every coupling.
#     Acceptance is lowest near betak ~ 0.465, where Kennedy-Pendleton takes ~8% of trials, so this
#     is where a bounded rejection loop would run out and leave a site unsampled. The test covers
#     that point and both extremes, and checks the draw against the exact density rather than a
#     summary statistic.
# ══════════════════════════════════════════════════════════════════════════════

@pytest.mark.parametrize('betak', [0.0, 0.2, 0.465, 1.0, 2.0, 6.0, 40.0])
def test_a0_sampler_matches_its_density_and_never_substitutes(betak):
    """``_su2_a0`` samples p(a) ~ sqrt(1-a^2) exp(betak*a) at every betak, with every site drawn
    from the density. a0 = 0 is the value a bounded loop would leave behind, and a genuine draw
    hits it with probability zero, so its absence is checked directly."""
    b = generator._Backend(None); b.seed(4242)
    a0 = np.asarray(b.to_numpy(generator._su2_a0(b, np.full(60_000, betak))), dtype=float)
    assert a0.shape == (60_000,)
    assert np.all(np.isfinite(a0)) and np.all(np.abs(a0) <= 1.0)
    # a = sin(th) removes the sqrt cusp, so the reference CDF is accurate rather than the error term
    th = np.linspace(-np.pi / 2, np.pi / 2, 200_001)
    dens = np.cos(th) ** 2 * np.exp(betak * (np.sin(th) - 1.0))
    cum = np.concatenate([[0.0], np.cumsum((dens[1:] + dens[:-1]) * 0.5 * np.diff(th))])
    cum /= cum[-1]
    D, pv = stats.kstest(a0, lambda x: np.interp(x, np.sin(th), cum))
    assert pv > 1e-4, f'betak={betak}: KS D={D:.5f} p={pv:.2e} vs the exact heat-bath density'
    # a genuine draw hits exactly 0.0 with probability zero
    assert (a0 == 0.0).sum() == 0, f'betak={betak}: {(a0 == 0.0).sum()} sites carry the a0=0 stand-in'


def test_beta0_heatbath_samples_haar_not_the_equator():
    """The beta=0 heat bath is the case the capped sampler could not do at all: betak = 0, no site
    ever accepts, every link comes back perpendicular to its staple.  It must be Haar."""
    q = np.asarray(generator.gauge_field((8, 8, 8, 8), 0.0, group='su2', seed=7, therm=5,
                                         method='heatbath'))
    t = q[..., 0].ravel()
    assert (t == 0.0).sum() == 0                                  # no forced-equator links
    n = t.size
    assert abs(t.mean()) < 4.0 / math.sqrt(n)                     # <t> = 0
    assert abs((t ** 2).mean() - 0.25) < 4.0 * np.std(t ** 2, ddof=1) / math.sqrt(n)
    assert abs((t ** 4).mean() - 0.125) < 4.0 * np.std(t ** 4, ddof=1) / math.sqrt(n)
    sub = np.random.default_rng(0).choice(t, size=5000, replace=False)
    Dks, _ = stats.kstest(sub, _haar_su2_cdf)
    assert Dks < 0.04, f'beta=0 heat-bath q0 KS {Dks:.4f} vs Haar'

# ══════════════════════════════════════════════════════════════════════════════
# 6. Heat-bath and Metropolis are different updates that must sample the same equilibrium:
#    <P> from method="heatbath" and method="metropolis" agree within combined error.
# ══════════════════════════════════════════════════════════════════════════════

@pytest.mark.parametrize("beta", [2.0, 2.3])
def test_heatbath_metropolis_agree_su2(beta):
    hb = plaquette_per_config((6, 6, 6, 6), beta, group="su2", n=16, therm=50, seed=41, method="heatbath")
    mc = plaquette_per_config((6, 6, 6, 6), beta, group="su2", n=16, therm=220, seed=42, method="metropolis")
    mh, sh = mean_se(hb)
    mm, sm = mean_se(mc)
    comb = math.sqrt(sh * sh + sm * sm)
    assert abs(mh - mm) < 4.0 * comb, \
        f"SU(2) beta={beta}: heatbath <P>={mh:.5f}+-{sh:.5f} vs metropolis <P>={mm:.5f}+-{sm:.5f}"


# ══════════════════════════════════════════════════════════════════════════════
# 7. Determinism / reproducibility (fixed seed -> bit-identical).
# ══════════════════════════════════════════════════════════════════════════════

def test_config_is_bit_reproducible():
    a = generator.config((4, 4, 4, 8), 1.0, group="u1", seed=5, therm=8)
    b = generator.config((4, 4, 4, 8), 1.0, group="u1", seed=5, therm=8)
    assert np.array_equal(np.asarray(a), np.asarray(b))


@pytest.mark.parametrize("group", ["su2", "su3"])
def test_config_matches_gauge_field_then_action_density(group):
    """config(...) must equal action_density(gauge_field(...)) bit-for-bit: same seed, same sweeps,
    the only difference is whether the action reduction is applied inside or after."""
    kw = dict(group=group, seed=5, therm=6, method="heatbath")
    a = np.asarray(generator.config((4, 4, 4, 6), 2.0, **kw))
    link = generator.gauge_field((4, 4, 4, 6), 2.0, **kw)
    b = np.asarray(generator.action_density(link, group=group))
    assert np.array_equal(a, b)


def test_stream_first_yield_matches_config():
    """stream(therm=T, gap=G, n=1) does T+G sweeps of the same unbatched chain as config(therm=T+G)."""
    s = list(generator.stream((4, 4, 4, 6), 2.0, group="su2", seed=5, therm=6, gap=3, n=1,
                              method="heatbath"))[0]
    c = generator.config((4, 4, 4, 6), 2.0, group="su2", seed=5, therm=9, method="heatbath")
    assert np.array_equal(np.asarray(s), np.asarray(c))


def test_config_batch_matches_config_with_batch_and_is_reproducible():
    cb = np.asarray(generator.config_batch((4, 4, 4, 6), 1.0, group="u1", seed=3, therm=5, n=3))
    cc = np.asarray(generator.config((4, 4, 4, 6), 1.0, group="u1", seed=3, therm=5, batch=3))
    assert np.array_equal(cb, cc)                                         # wrapper == config(batch=n)
    cb2 = np.asarray(generator.config_batch((4, 4, 4, 6), 1.0, group="u1", seed=3, therm=5, n=3))
    assert np.array_equal(cb, cb2)                                        # reproducible
    assert cb.shape == (3, 4, 4, 4, 6)
