"""The per-field peel of `MassGap.NearOwnAttack.PeelOwnAlong` at the free field.

`PeelOwnAlong` asks, for a point of one field at height `x0 >= d` below a configuration `Q` at height
`>= x0 + 2d`, that the reflected reading of the combined configuration be at most `C(d)` times a field's own
reference reading times the reading of `Q` lowered by `x0 + d`. At the free field every reflected point reading
is a hafnian of the propagator over the `2n` points `(theta x_i, x_i)`; the cell powers `a^8` cancel between the
two sides, and the reference reading enters as a constant at fixed `s0`. So the clause at the free field is: the
ratio `Haf(x, Q) / Haf(Q lowered)` is bounded over all such configurations, at fixed `d`.

Two checks, and a third that shows the check can fail:

* the lowered ratio stays bounded over random and adversarial configurations (heights to `10^3 d`, spatial
  spread to `10^3 d`, lists up to four points);
* the sandwich operator norm of one oscillator mode, `||T^u phi T^v||^2`, is bounded by a constant times its
  vacuum reading `<phi T^{2u} phi>` at `u, v >= d` (the operator form the peel reads on monomials);
* without the lowering, `Haf(x, Q) / Haf(Q)` is unbounded: with `x` at height `X` and `Q` one point at the gap
  just above it, `Haf(Q) ~ G(2X)` decays while the cross pairing `G(2d)^2` stays, so the ratio grows like `X^2`.
  The lowering in the clause is load-bearing.

Massless continuum propagator `G(r) = 1 / |r|^2` (the `4 pi^2` drops out of the ratios). Runs in well under 10 s.
"""
import itertools

import numpy as np

# CHOSEN: the margin d = 1; the clause is scale-free at the massless field, so the value sets the unit only.
D = 1.0  # CHOSEN: the margin; the clause is scale-free at the massless field, so its value is a unit


def G(x, y):
    r2 = float(np.sum((np.asarray(x) - np.asarray(y)) ** 2))
    return 1.0 / r2


def hafnian(pts):
    if not pts:
        return 1.0
    first, rest = pts[0], pts[1:]
    total = 0.0
    for j in range(len(rest)):
        total += G(first, rest[j]) * hafnian(rest[:j] + rest[j + 1:])
    return total


def refl(x):
    y = list(x)
    y[0] = -y[0]
    return y


def reading(conf):
    pts = []
    for x in conf:
        pts.append(refl(x))
        pts.append(list(x))
    return hafnian(pts)


def lowered(conf, c):
    return [[x[0] - c] + list(x[1:]) for x in conf]


def peel_ratio(x, Q, lower=True):
    num = reading([x] + Q)
    den = reading(lowered(Q, x[0] + D) if lower else Q)
    return num / den


def configurations(rng, count):
    for _ in range(count):
        n = int(rng.integers(0, 4))
        x0 = D * 10 ** rng.uniform(0, 3)
        x = [x0] + list(rng.uniform(-1, 1, 3) * 10 ** rng.uniform(-1, 3))
        Q = []
        for _ in range(n):
            q0 = x0 + 2 * D + D * 10 ** rng.uniform(-2, 3)
            Q.append([q0] + list(rng.uniform(-1, 1, 3) * 10 ** rng.uniform(-1, 3)))
        yield x, Q


def adversarial():
    # The point and the configuration touching the constraints: x at the margin or far up, Q at the gap.
    for x0 in (D, 10 * D, 1000 * D):
        for gap in (2 * D, 3 * D, 100 * D):
            for s in (0.0, D, 100 * D):
                x = [x0, 0.0, 0.0, 0.0]
                for n in (1, 2, 3):
                    Q = [[x0 + gap + 2 * D * i, s * i, 0.0, 0.0] for i in range(n)]
                    yield x, Q


def test_lowered_peel_is_bounded_at_the_free_field():
    rng = np.random.default_rng(0)
    worst = max(peel_ratio(x, Q) for x, Q in itertools.chain(configurations(rng, 3000), adversarial()))
    # Bound: G(2 x0) <= G(2d) for the vacuum pairing of x, and the cross pairings of x with Q are at most
    # G(2d)-sized against the lowered Q (heights >= d). The empirical sup is a few times G(2d) = 1/4.
    # CHOSEN: 10 as the finite cap that stands in for "bounded" over the sample; the sampled sup is 0.31, so the cut is loose by a factor 30.
    assert worst < 10.0, worst


def test_the_unlowered_peel_is_unbounded():
    # x high above the plane, Q at the gap just above x: Haf(Q) ~ G(2 X) decays, the cross pairing G(2d)^2 stays.
    ratios = [peel_ratio([X, 0, 0, 0], [[X + 2 * D, 0, 0, 0]], lower=False) for X in (D, 10 * D, 100 * D)]
    assert ratios[0] < ratios[1] < ratios[2]
    assert ratios[2] > 500 * ratios[0]  # grows like X^2
    # The same configurations lowered stay bounded.
    # CHOSEN: the same cap of 10 as the bounded test; the lowered ratios read at most 0.29 while the unlowered ones grow past 500 times their start.
    assert max(peel_ratio([X, 0, 0, 0], [[X + 2 * D, 0, 0, 0]]) for X in (D, 10 * D, 100 * D)) < 10.0


def test_sandwich_operator_norm_against_its_vacuum_reading():
    # One oscillator mode of frequency w: T = exp(-w N), phi = (a + a^dagger) / sqrt(2 w), truncated Fock space.
    # The comparison reading is at the smaller margin min(u, v): the annihilation part of phi returns an excited
    # vector to the vacuum, where T^u no longer damps, so the norm is set by the nearer side. Against the reading
    # at u itself the ratio is exp(2 w (u - v)), unbounded in u (asserted below).
    M = 300  # CHOSEN: the truncation; level m is damped by exp(-w m min(u, v)), below 1e-12 at the cut here
    a = np.diag(np.sqrt(np.arange(1, M)), 1)
    worst = {}
    against_u = 0.0
    for w in (0.1, 0.3, 1.0, 3.0):
        phi = (a + a.T) / np.sqrt(2 * w)
        for u in (D, 2 * D, 5 * D):
            for v in (D, 2 * D, 5 * D):
                Tu = np.diag(np.exp(-w * u * np.arange(M)))
                Tv = np.diag(np.exp(-w * v * np.arange(M)))
                norm2 = np.linalg.norm(Tu @ phi @ Tv, 2) ** 2
                m = min(u, v)
                ratio = norm2 / (np.exp(-2 * w * m) / (2 * w))
                worst[w] = max(worst.get(w, 0.0), ratio)
                against_u = max(against_u, norm2 / (np.exp(-2 * w * u) / (2 * w)))
    # Bounded at each frequency; the bound grows like 1 / (w min(u, v)) for a soft mode (sup_m m exp(-2 w m v)),
    # so the constant of the clause depends on the gap at the scale d, not on the step.
    for w, r in worst.items():
        assert r < 3.0 + 1.0 / (w * D), (w, r)
    # CHOSEN: 1e9 as "unbounded in u"; the largest exp(2 w (u - v)) on the grid is exp(24) = 2.6e10 (w = 3, u - v = 4), and the read sits there, a factor 26 above the cut.
    assert against_u > 1e9
