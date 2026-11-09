"""Is the topological charge frozen along a campaign? The clover charge Q after the observer step, per shard.

The Lean-step energy-density correlator keeps a residual decline at the finest spacing that the slow modes of one
heat-bath chain would produce. Frozen topology is the slowest such mode. This applies the observer step
(observer_step.step: blockLink, all four directions, c, n steps) and reads the clover charge
    Q = (1/(2 pi^2)) sum_x (v01.v23 - v02.v13 + v03.v12),
v_{mu nu}(x) the vector part of the average of the four clover leaves in the (mu, nu) plane (an SU(2) element
a0 + i a.sigma has vector part a; tr(F F) contracts the vector parts). After smearing Q sits near integers when
the read is right. Per shard and chain it writes Q in Markov order, so its autocorrelation along the chain is read
directly: a frozen chain keeps Q fixed across shards.

    python topo_read_gpu.py CAMPAIGN_DIR c nsteps > out.json
"""
import json
import math
import os
import sys

import numpy as np

from lattice_generator import _Backend, _qmul, _qconj, _sax

camp, cw, nst = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
bg = _Backend("cuda", fp="32")
# DERIVED: the spacetime dimension of the four-dimensional lattice
D4 = 4


def step(q):
    outq = q.clone()
    for mu in range(D4):
        U = q[..., mu, :]
        V = U.clone()
        for nu in range(D4):  # NOT A READ: the six staples
            if nu == mu:
                continue
            Un = q[..., nu, :]
            up = _qmul(bg, _qmul(bg, Un, bg.roll(U, -1, _sax(nu, 1))), _qconj(bg, bg.roll(Un, -1, _sax(mu, 1))))
            Unm = bg.roll(Un, 1, _sax(nu, 1))
            dn = _qmul(bg, _qmul(bg, _qconj(bg, Unm), bg.roll(U, 1, _sax(nu, 1))), bg.roll(Unm, -1, _sax(mu, 1)))
            V = V + cw * (up + dn)
        outq[..., mu, :] = V / V.norm(dim=-1, keepdim=True)
    return outq


def sh(a, s, d):
    return bg.roll(a, s, _sax(d, 1))


def clover_vec(q, mu, nu):
    Um, Un = q[..., mu, :], q[..., nu, :]
    m = lambda *xs: _reduce(xs)
    c = _qconj
    L1 = m(Um, sh(Un, -1, mu), c(bg, sh(Um, -1, nu)), c(bg, Un))
    L2 = m(Un, c(bg, sh(sh(Um, 1, mu), -1, nu)), c(bg, sh(Un, 1, mu)), sh(Um, 1, mu))
    L3 = m(c(bg, sh(Um, 1, mu)), c(bg, sh(sh(Un, 1, mu), 1, nu)), sh(sh(Um, 1, mu), 1, nu), sh(Un, 1, nu))
    L4 = m(c(bg, sh(Un, 1, nu)), sh(Um, 1, nu), sh(sh(Un, -1, mu), 1, nu), c(bg, Um))
    return (L1 + L2 + L3 + L4)[..., 1:] / 4.0


def _reduce(xs):
    out = xs[0]
    for x in xs[1:]:  # NOT A READ: the product along the leaf
        out = _qmul(bg, out, x)
    return out


def charge(q):
    v = {(m, n): clover_vec(q, m, n) for m in range(D4) for n in range(m + 1, D4)}
    dot = lambda a, b: (a * b).sum(-1).double()
    dens = dot(v[0, 1], v[2, 3]) - dot(v[0, 2], v[1, 3]) + dot(v[0, 3], v[1, 2])
    return (dens.sum(dim=(1, 2, 3, 4)) / (2 * math.pi ** 2)).cpu().numpy()  # (chain,)


lst = os.path.join(camp, "verified.list")
names = ([l.strip() for l in open(lst) if l.strip()] if os.path.exists(lst)
         else [l.split()[1] for l in open(os.path.join(camp, "SHA256SUMS")) if l.strip()])
rows = []
for name in sorted(set(names)):
    links = np.load(os.path.join(camp, name), mmap_mode="r")
    qs = []
    for ch in range(links.shape[0]):  # NOT A READ: one chain at a time bounds the memory
        q = bg.t.as_tensor(np.array(links[ch:ch + 1], dtype=np.float32), dtype=bg.f, device=bg.dev)
        for _ in range(nst):
            q = step(q)
        qs.append(float(charge(q)[0]))
        del q
    rows.append({"shard": name, "Q": qs})
    print(name, " ".join(f"{x:+.3f}" for x in qs), file=sys.stderr, flush=True)
print(json.dumps({"campaign": camp, "c": cw, "nsteps": nst, "rows": rows}))
