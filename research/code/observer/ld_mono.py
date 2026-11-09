"""Does one observer step (ApeLattice.apeConf = BlockSU2.blockLink on every link at once) raise the
Wilson action?  Global S = sum_p (1 - 1/2 tr P) and local sums over sub-boxes.

    python ld_mono.py mode L c seeds [extra]

mode: haar | near EPS | wave AMP | frust EPS | climbG ITERS | climbL ITERS (hill-climb the global ratio
S(VU)/S(U) or the worst local ratio). Per seed it prints the global ratio, the largest site ratio, and the
largest ratio of smoothed box energy to raw energy of the same box and of the box enlarged by 1 and 2 sites.

Self-contained numpy: unit quaternions (a0, a1, a2, a3), 1/2 tr U = a0, multiplied with the Hamilton
product. lattice_generator._qmul (used by observer_step) is the opposite product; the two groups are
isomorphic by q -> conj(q), which maps the step to itself and keeps every trace, so the statistics agree,
while a given seed reads the conjugate configuration. The algebra is kept here so the recorded per-seed
outputs reproduce.
"""
import json
import sys

import numpy as np

# DERIVED: four spacetime dimensions
D = 4


def qmul(p, q):
    a0, a1, a2, a3 = p[..., 0], p[..., 1], p[..., 2], p[..., 3]
    b0, b1, b2, b3 = q[..., 0], q[..., 1], q[..., 2], q[..., 3]
    return np.stack([a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3,
                     a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2,
                     a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1,
                     a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0], axis=-1)


def qconj(p):
    return p * np.array([1.0, -1.0, -1.0, -1.0])


def roll(a, s, mu):
    return np.roll(a, s, axis=mu)


def step(q, c):
    out = np.empty_like(q)
    for mu in range(D):
        U = q[..., mu, :]
        V = U.copy()
        for nu in range(D):  # NOT A READ: the six staples
            if nu == mu:
                continue
            Un = q[..., nu, :]
            up = qmul(qmul(Un, roll(U, -1, nu)), qconj(roll(Un, -1, mu)))
            Unm = roll(Un, 1, nu)
            dn = qmul(qmul(qconj(Unm), roll(U, 1, nu)), roll(Unm, -1, mu))
            V = V + c * (up + dn)
        out[..., mu, :] = V / np.linalg.norm(V, axis=-1, keepdims=True)
    return out


def plaq(q):
    """(6, L, L, L, L) array of 1 - 1/2 tr P, plaquette based at x in plane (mu, nu)."""
    vals = []
    for mu in range(D):
        for nu in range(mu + 1, D):  # NOT A READ: the six planes
            P = qmul(qmul(qmul(q[..., mu, :], roll(q[..., nu, :], -1, mu)),
                          qconj(roll(q[..., mu, :], -1, nu))), qconj(q[..., nu, :]))
            vals.append(1.0 - P[..., 0])
    return np.stack(vals)


def site_energy(q):
    return plaq(q).sum(axis=0)


def box_sum(e, x0, w):
    """sum of the site field e over the periodic box [x0, x0 + w)^4."""
    L = e.shape[0]
    idx = [(np.arange(w) + x0[i]) % L for i in range(D)]
    return e[np.ix_(*idx)].sum()


def haar(rng, L):
    q = rng.standard_normal((L, L, L, L, D, 4))
    return q / np.linalg.norm(q, axis=-1, keepdims=True)


def near(rng, L, eps):
    v = eps * rng.standard_normal((L, L, L, L, D, 3))
    th = np.linalg.norm(v, axis=-1, keepdims=True)
    n = v / np.maximum(th, 1e-300)
    return np.concatenate([np.cos(th), np.sin(th) * n], axis=-1)


def wave(rng, L, amp):
    """abelian (sigma_3) embedded random superposition of a few lattice plane waves, large amplitude."""
    x = np.indices((L, L, L, L)).astype(float)
    th = np.zeros((L, L, L, L, D))
    for _ in range(3):
        k = rng.integers(0, L, size=D)
        ph = rng.uniform(0, 2 * np.pi)
        mu = rng.integers(0, D)
        th[..., mu] += amp * np.cos(2 * np.pi * np.tensordot(k, x, axes=1) / L + ph)
    q = np.zeros((L, L, L, L, D, 4))
    q[..., 0] = np.cos(th)
    q[..., 3] = np.sin(th)
    return q


def frust(rng, L, eps):
    """pi flux through every plaquette (U_mu = (-1)^(x_0 + ... + x_{mu-1})), times near-identity noise."""
    x = np.indices((L, L, L, L))
    q = np.zeros((L, L, L, L, D, 4))
    for mu in range(D):
        # DERIVED: the exponent x_0 + ... + x_{mu-1} is the empty sum for mu = 0
        q[..., mu, 0] = (-1.0) ** (x[:mu].sum(axis=0) if mu > 0 else 0)
    return qmul(near(rng, L, eps), q)


# CHOSEN: w = 2, the box side in sites; the enlarged boxes w + 2 and w + 4 fit on L = 4 and L = 6
def report(q, c, L, tag, w=2):
    e0 = site_energy(q)
    q1 = step(q, c)
    e1 = site_energy(q1)
    S0, S1 = e0.sum(), e1.sum()
    # local: smoothed energy in box [x0, x0+w) against raw energy in the box enlarged by r on each side
    rng = np.random.default_rng(7)
    loc_same, loc_r1, loc_r2 = [], [], []
    for _ in range(64):
        x0 = rng.integers(0, L, size=D)
        a = box_sum(e1, x0, w)
        b0 = box_sum(e0, x0, w)
        b1 = box_sum(e0, x0 - 1, w + 2) if w + 2 <= L else S0
        b2 = box_sum(e0, x0 - 2, w + 4) if w + 4 <= L else S0
        loc_same.append(a / max(b0, 1e-300))
        loc_r1.append(a / max(b1, 1e-300))
        loc_r2.append(a / max(b2, 1e-300))
    return {"tag": tag, "L": L, "c": c, "S0": float(S0), "S1": float(S1), "ratio": float(S1 / S0),
            "site_max_ratio": float((e1 / np.maximum(e0, 1e-300)).max()),
            "box_same_max": float(max(loc_same)), "box_r1_max": float(max(loc_r1)),
            "box_r2_max": float(max(loc_r2))}


def climb(rng, L, c, iters, target, start):
    """random-perturbation hill climb maximising S(VU)/S(U) (target=global) or the worst local ratio."""
    q = start

    def score(q):
        e0 = site_energy(q)
        e1 = site_energy(step(q, c))
        if target == "global":
            return e1.sum() / e0.sum()
        # worst site: smoothed site energy over raw energy of the box x + {-1..2}^4 it reads
        best = 0.0
        acc = np.zeros_like(e0)
        for s in np.ndindex(4, 4, 4, 4):
            sh = tuple(si - 1 for si in s)
            acc += np.roll(e0, sh, axis=(0, 1, 2, 3))
        return float((e1 / np.maximum(acc, 1e-300)).max())

    f = score(q)
    scale = 0.3
    for it in range(iters):
        pert = near(rng, L, scale)
        # CHOSEN: each proposal perturbs about a tenth of the links
        mask = rng.random((L, L, L, L, D, 1)) < 0.1
        cand = np.where(mask, qmul(pert, q), q)
        g = score(cand)
        if g > f:
            q, f = cand, g
        # CHOSEN: the proposal scale shrinks by 0.8 every 200 iterations, down to 0.01
        if it % 200 == 199:
            scale = max(scale * 0.8, 0.01)
    return f, q


if __name__ == "__main__":
    mode, L, c, seeds = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
    # CHOSEN: the mode parameter is optional; haar reads none
    extra = float(sys.argv[5]) if len(sys.argv) > 5 else 0.0
    for s in range(seeds):
        rng = np.random.default_rng(100 + s)
        if mode == "haar":
            print(json.dumps(report(haar(rng, L), c, L, "haar")), flush=True)
        elif mode == "near":
            print(json.dumps(report(near(rng, L, extra), c, L, f"near{extra}")), flush=True)
        elif mode == "wave":
            print(json.dumps(report(wave(rng, L, extra), c, L, f"wave{extra}")), flush=True)
        elif mode == "frust":
            print(json.dumps(report(frust(rng, L, extra), c, L, f"frust{extra}")), flush=True)
        elif mode in ("climbG", "climbL"):
            st = [near(rng, L, 0.5), haar(rng, L), frust(rng, L, 0.3)][s % 3]
            f, q = climb(rng, L, c, int(extra), "global" if mode == "climbG" else "local", st)
            out = report(q, c, L, mode)
            out["climb_score"] = f
            print(json.dumps(out), flush=True)
