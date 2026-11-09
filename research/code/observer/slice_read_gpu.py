"""Read the observer's slice from raw links: block the configurations, then read the coarse theory.

The aperture is the factor-2 block step observer_step.block2 applied k times (s = 2^k):
    V_mu(x) = Proj[ U_mu(x) U_mu(x+mu) + c * sum_{nu != mu, +-} U_{+-nu}(x) U_mu(x+-nu) U_mu(x+-nu+mu) U_{+-nu}(x+2mu)^dag ]
with Proj the normalisation back to SU(2) and the coarse lattice the even sites. c = 0 is raw decimation
(a product of two links, local, spacing-dependent through the perimeter); c > 0 averages within the block.
For c < 1/6 the block step is continuous (|UU| = 1 and the six staples sum to at most 6c < 1, so the
normalised link never divides by zero): the observer is then a continuous configuration map.

Reads on the coarse configurations, per shard (one shard = one measurement of every chain):
  * u = <(1/2) tr P> over coarse plaquettes, and rho_adj = corr(q_P(x), q_P(x + mu)) for in-plane neighbours;
  * the single-link conditional read. With A the staple sum of a coarse link U (lattice_generator._su2_staple)
    and c_l = sdot(U, A)/|A|, a coarse theory that is Wilson at one beta_eff has E[c_l | A] = I2(beta|A|)/I1(beta|A|)
    for every |A|. Links are binned by |A| (8 bins, fixed quantile edges from the first shard); in each bin beta
    is solved exactly from the bin's mean of c_l (bisection on the monotone map beta -> mean_i R(beta |A_i|)).
    A flat beta_eff(|A|) is Wilson; its variation is the single-link residual of the coarse action. No
    parameter is fitted.
Uncertainty: the spread of the per-shard reads (reproducibility over independent measurements), not a formula.
The block steps run on CUDA (fp32), the coarse reads on the CPU.

    python slice_read_gpu.py CAMPAIGN_DIR k c [maxshards] > out.json
Reads only shards listed in verified.list or SHA256SUMS.
"""
import json
import os
import sys

import numpy as np
from scipy.special import ive

import observer_step as O
import lattice_generator as G

# CHOSEN: eight |A| bins, quantile edges from the first shard
NB = 8


def plaq_stats(b, q):
    trs, adj = [], []
    for mu in range(O.D):
        for nu in range(mu + 1, O.D):  # NOT A READ: the six plaquette planes
            t = O.halftr(b, q, mu, nu).astype(np.float64)
            trs.append(t)
            for d in (mu, nu):  # NOT A READ: the two in-plane neighbour directions
                adj.append((t, np.roll(t, -1, axis=d - O.D)))
    allt = np.stack(trs)
    u = allt.mean()
    var = allt.var()
    cov = np.mean([((x - u) * (y - u)).mean() for x, y in adj])
    return u, cov / var


def link_read(b, q):
    Ks, Cs = [], []
    for mu in range(O.D):
        A = G._su2_staple(b, q, mu).astype(np.float64)
        a = np.linalg.norm(A, axis=-1)
        cl = G._sdot(q[..., mu, :].astype(np.float64), A) / a
        Ks.append(a.ravel())
        Cs.append(cl.ravel())
    return np.concatenate(Ks), np.concatenate(Cs)


def R(x):
    return ive(2, x) / ive(1, x)


def solve_beta(a, cmean):
    lo, hi = 1e-6, 50.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if R(mid * a).mean() < cmean:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


if __name__ == "__main__":
    camp, k, cw = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    maxsh = O.opt(4, 10 ** 9)
    b = G._Backend(None, fp="32")
    bg = G._Backend("cuda", fp="32")
    names = O.shards(camp, maxsh)
    edges = None
    per = []
    for name in names:
        q = bg.t.as_tensor(np.load(os.path.join(camp, name)).astype(np.float32), dtype=bg.f, device=bg.dev)
        for _ in range(k):
            q = O.block2(bg, q, cw)
        q = q.cpu().numpy()
        u, rho = plaq_stats(b, q)
        a, cl = link_read(b, q)
        if edges is None:
            edges = np.quantile(a, np.linspace(0, 1, NB + 1))
            edges[0], edges[-1] = -np.inf, np.inf
        idx = np.digitize(a, edges[1:-1])
        betas, amean = [], []
        for j in range(NB):  # NOT A READ: one exact inversion per |A| bin
            m = idx == j
            betas.append(solve_beta(a[m], cl[m].mean()))
            amean.append(a[m].mean())
        per.append({"shard": name, "u": u, "rho_adj": rho, "beta_bins": betas, "A_bins": amean})
        print(f"{name} u={u:.5f} rho={rho:+.5f} beta(|A|)=" + " ".join(f"{x:.4f}" for x in betas),
              file=sys.stderr, flush=True)

    arr = lambda key: np.array([p[key] for p in per])
    res = {
        "campaign": camp, "params": json.load(open(os.path.join(camp, "params.json"))),
        "k": k, "s": 2 ** k, "c": cw, "nshards": len(per),
        "coarse_L": int(per and np.load(os.path.join(camp, names[0]), mmap_mode="r").shape[1] // 2 ** k),
        "u": [arr("u").mean(), arr("u").std(ddof=1) / np.sqrt(len(per))],
        "rho_adj": [arr("rho_adj").mean(), arr("rho_adj").std(ddof=1) / np.sqrt(len(per))],
        "A_bins": arr("A_bins").mean(0).tolist(),
        "beta_bins": arr("beta_bins").mean(0).tolist(),
        "beta_bins_err": (arr("beta_bins").std(0, ddof=1) / np.sqrt(len(per))).tolist(),
        "per_shard": per,
    }
    print(json.dumps(res, indent=1, default=float))
