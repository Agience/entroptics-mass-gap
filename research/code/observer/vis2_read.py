"""Visibility at one physical scale: does the smeared observer see a slower decay than the block observer?

M for the continuum observer is (the coarse view lies in N) + visibility: no vector of the smeared observer's
space orthogonal to the block observer's decays more slowly than the block observer's slowest,
at the coarse time step. Read here variationally, on CUDA:

  operators on the coarse time grid (block size b = 2^k fine steps):
    B(t): zero-momentum spatial plaquette sum, sum of (1/2) tr P, of the block configuration
          (observer_step.block2 at c, k times) on coarse slice t;
    M(t): the same sum on the APE-smeared configuration (lattice_generator.ape_smear, n sweeps), summed over
          the b fine slices of coarse slice t;
  C(D) = <dO_i(t) dO_j(t + D)>, symmetrised, vacuum-subtracted;
  block-only decay ratio  r_B(D) = C_BB(D+1) / C_BB(D);
  span decay ratio        r_*(D) = lambda_max(D+1) / lambda_max(D), lambda from C(D) v = lambda C(0) v;
  leakage rows on this basis: the residual is the smeared operator minus its
  projection on the block operator in the C(0) metric; rho_c^2(D) = C_BB(D)/C_BB(0), rho_r^2(D) = C_rr(D)/C_rr(0),
  eta(D) = C_Br(D)/sqrt(C_BB(0) C_rr(0)), margin(D) = (1 - rho_c^2)(1 - rho_r^2) - eta^2.

Visibility holds at this scale when r_* = r_B within errors: the span's slowest decay is already the block
observer's. No parameter is fitted (the generalised eigenvalue is exact linear algebra on the measured
matrix); the uncertainty is a jackknife over shards.

    python vis2_read.py CAMPAIGN_DIR k c nsmear [maxshards] > out.json
Reads only shards listed in verified.list or SHA256SUMS.
"""
import json
import os
import sys
import time

import numpy as np
import scipy.linalg as sla

import observer_step as O
import lattice_generator as G
from lattice_generator import _Backend


def slices(bg, q):
    tot = 0.0
    for mu in range(3):
        for nu in range(mu + 1, 3):  # NOT A READ: the three spatial planes
            tot = tot + O.halftr(bg, q, mu, nu).double()
    return tot.sum(dim=(1, 2, 3)).cpu().numpy()  # (chain, T)


def reads(Xs, nop, nc, Tc, Dmax):
    d = Xs - Xs.mean(axis=(0, 2, 3), keepdims=True)
    C = np.zeros((Dmax + 1, nop, nop))
    for Dt in range(Dmax + 1):  # NOT A READ: the time separations
        M = np.einsum("sict,sjct->ij", d, np.roll(d, -Dt, axis=3)) / (d.shape[0] * nc * Tc)
        C[Dt] = 0.5 * (M + M.T)
    rB = C[1:, 0, 0] / C[:-1, 0, 0]
    lam = np.array([sla.eigh(C[Dt], C[0], eigvals_only=True).max() for Dt in range(Dmax + 1)])
    rS = lam[1:] / lam[:-1]
    lamb = C[0, 1, 0] / C[0, 0, 0]
    Crr = C[:, 1, 1] - 2 * lamb * C[:, 0, 1] + lamb ** 2 * C[:, 0, 0]
    CBr = C[:, 0, 1] - lamb * C[:, 0, 0]
    rc2 = C[:, 0, 0] / C[0, 0, 0]
    rr2 = Crr / Crr[0]
    eta = CBr / np.sqrt(C[0, 0, 0] * Crr[0])
    margin = (1 - rc2) * (1 - rr2) - eta ** 2
    return rB, rS, C, np.stack([rc2, rr2, eta, margin])


if __name__ == "__main__":
    camp, k, cw, nsm = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
    maxsh = O.opt(5, 10 ** 9)
    bg = _Backend("cuda", fp="32")
    per, t0 = [], time.time()
    for name in O.shards(camp, maxsh):
        q0 = bg.t.as_tensor(np.load(os.path.join(camp, name)).astype(np.float32), dtype=bg.f, device=bg.dev)
        q = q0
        for _ in range(k):
            q = O.block2(bg, q, cw)
        B = slices(bg, q)                                    # (chain, Tc)
        del q
        qs = G.ape_smear(q0, nsm, alpha=0.5, device="cuda")
        Mf = slices(bg, qs)                                  # (chain, T)
        del qs, q0
        Mc = Mf.reshape(Mf.shape[0], -1, 2 ** k).sum(axis=2)  # (chain, Tc)
        per.append(np.stack([B, Mc]))                        # (2, chain, Tc)
        print(f"{name} ({time.time() - t0:.0f}s)", file=sys.stderr, flush=True)

    X = np.stack(per)                                        # (shard, op, chain, Tc)
    ns, nop, nc, Tc = X.shape
    Dmax = Tc // 2
    rB, rS, C, LK = reads(X, nop, nc, Tc, Dmax)
    jk = [reads(np.delete(X, i, axis=0), nop, nc, Tc, Dmax) for i in range(ns)]  # NOT A READ: jackknife over shards
    jerr = lambda arrs, full: np.sqrt((ns - 1) / ns * ((np.stack(arrs) - full) ** 2).sum(0))
    print(json.dumps({"campaign": camp, "params": json.load(open(os.path.join(camp, "params.json"))),
                      "k": k, "b": 2 ** k, "c": cw, "nsmear": nsm, "nshards": ns, "coarse_T": Tc,
                      "r_block": rB.tolist(), "r_block_err": jerr([j[0] for j in jk], rB).tolist(),
                      "r_span": rS.tolist(), "r_span_err": jerr([j[1] for j in jk], rS).tolist(),
                      "leak": LK.tolist(), "leak_err": jerr([j[3] for j in jk], LK).tolist(),
                      "leak_rows": ["rho_c^2(D)", "rho_r^2(D)", "eta(D)", "margin(D)"],
                      "C": C.tolist()}, indent=1))
