"""The Sommer scale r0/a from raw links, without a fit.

Planar Wilson loops W(R,T) on spatial-x-temporal planes, spatial links APE-smeared (temporal links
untouched, so the transfer matrix is unchanged):
    V_eff(R,T) = log[W(R,T) / W(R,T+1)]                 -> V(R) as T grows
    F(R - 1/2, T) = V_eff(R,T) - V_eff(R-1,T)             the force between adjacent separations
    r0: where r^2 F(r) crosses 1.65, linearly between the two adjacent midpoints that bracket it.
No functional form is fitted to the potential. r0/a is printed at every T so the plateau in T is read,
not assumed. Uncertainty: delete-one-block jackknife over observer_step.chain_blocks (an SU(2) shard is its
own block; the SU(N) shards `links_c{k}_m{j}.npy` of one chain form one block).

SU(2) quaternion shards and SU(N) matrix shards (complex) are both read; the SU(N) loops are Re tr W / N and
the SU(N) smearing is observer_step.ape_sun (the generator's spatial APE with the SU(N) projection), the same
normalisation and the same kernel as the SU(2) path at N = 2.

The ratio r0/a between two couplings is the spacing ratio a(beta_1)/a(beta_2), which the observer's
matched comparisons need; it is read here independently of the observer.

`wilson_matrix` is carried here so that this read needs neither the Entroptics wrapper nor the store
locator.

    python r0_read.py CAMPAIGN_DIR rmax tmax nsmear [maxshards] [device] > out.json
Reads only shards listed in verified.list or SHA256SUMS.
"""
import json
import os
import sys
import time

import numpy as np

import observer_step as O
import lattice_generator as G
from lattice_generator import _Backend, _qmul, _qconj, _sax

# CHOSEN: APE weight 0.5, the standard APE weight
ALPHA = 0.5
# CHOSEN: the Sommer convention r0^2 F(r0) = 1.65
TARGET = 1.65


def wilson_matrix(b, q, rmax, tmax):
    """W[R-1, T-1] = <(1/2) Re tr U(R x T)> over spatial-x-temporal planes."""
    tax = G.D - 1
    tline, P, sh = {}, q[..., tax, :], q[..., tax, :]
    tline[1] = P
    for T in range(2, tmax + 2):  # NOT A READ: the temporal Wilson line of length T (one extra, for W(R,T+1))
        sh = b.roll(sh, -1, _sax(tax, 1))
        P = _qmul(b, P, sh)
        tline[T] = P
    W = np.zeros((rmax, tmax + 1))
    for mu in range(G.D - 1):  # NOT A READ: spatial directions; the rolls build the spatial line and close the loop
        S = q[..., mu, :]
        shs = S
        sline = {1: S}
        for R in range(2, rmax + 1):
            shs = b.roll(shs, -1, _sax(mu, 1))
            S = _qmul(b, S, shs)
            sline[R] = S
        for R in range(1, rmax + 1):
            bottom = sline[R]
            for T in range(1, tmax + 2):
                left = tline[T]
                right = b.roll(left, -R, _sax(mu, 1))
                top = b.roll(bottom, -T, _sax(tax, 1))
                loop = _qmul(b, _qmul(b, _qmul(b, bottom, right), _qconj(b, top)), _qconj(b, left))
                W[R - 1, T - 1] += float(loop[..., 0].mean())
        del sline, S, shs
    return W / (G.D - 1)


def wilson_matrix_sun(b, U, rmax, tmax):
    """W[R-1, T-1] = <Re tr U(R x T) / N> over spatial-x-temporal planes, SU(N) matrices."""
    tax = G.D - 1
    N = U.shape[-1]

    def dag(M):
        return b.conj(b.swap(M))

    tline, P, sh = {}, U[..., tax, :, :], U[..., tax, :, :]
    tline[1] = P
    for T in range(2, tmax + 2):  # NOT A READ: the temporal Wilson line of length T (one extra, for W(R,T+1))
        sh = b.roll(sh, -1, _sax(tax, 2))
        P = P @ sh
        tline[T] = P
    W = np.zeros((rmax, tmax + 1))
    for mu in range(G.D - 1):  # NOT A READ: spatial directions; the rolls build the spatial line and close the loop
        S = U[..., mu, :, :]
        shs = S
        sline = {1: S}
        for R in range(2, rmax + 1):
            shs = b.roll(shs, -1, _sax(mu, 2))
            S = S @ shs
            sline[R] = S
        for R in range(1, rmax + 1):
            bottom = sline[R]
            for T in range(1, tmax + 2):
                left = tline[T]
                right = b.roll(left, -R, _sax(mu, 2))
                top = b.roll(bottom, -T, _sax(tax, 2))
                loop = bottom @ right @ dag(top) @ dag(left)
                W[R - 1, T - 1] += float(b.real(b.trace(loop)).mean()) / N
        del sline, S, shs
    return W / (G.D - 1)


def r0_at(W, T, rmax):
    """r0/a from the mean Wilson matrix at time T; NaN when no adjacent pair brackets the condition."""
    with np.errstate(invalid="ignore", divide="ignore"):
        V = np.log(W[:, T - 1] / W[:, T])                 # V_eff(R,T), R = 1..rmax
    r = np.arange(2, rmax + 1) - 0.5                       # midpoints of the force
    y = r ** 2 * (V[1:] - V[:-1])
    for i in range(len(y) - 1):  # NOT A READ: the first bracketing pair of adjacent midpoints
        if np.isfinite(y[i]) and np.isfinite(y[i + 1]) and y[i] < TARGET <= y[i + 1]:
            return float(r[i] + (TARGET - y[i]) * (r[i + 1] - r[i]) / (y[i + 1] - y[i]))
    return float("nan")


if __name__ == "__main__":
    camp = sys.argv[1]
    rmax, tmax, nsmear = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    maxsh = O.opt(5, 10 ** 9)
    device = O.opt(6, None, str)
    b = _Backend(device)
    Ws, t0 = [], time.time()
    names = O.shards(camp, maxsh)
    for name in names:
        raw = np.load(os.path.join(camp, name))
        if np.iscomplexobj(raw):
            Ws.append(wilson_matrix_sun(b, O.ape_sun(b, O.tensor(b, raw), nsmear, ALPHA), rmax, tmax))
            del raw
            print(f"{name}  ({time.time() - t0:.0f}s)", file=sys.stderr, flush=True)
            continue
        arr = raw.astype(np.float32)
        q = b.t.as_tensor(arr, dtype=b.f, device=b.dev) if b.torch else arr
        q = G.ape_smear(q, nsmear, alpha=ALPHA, device=device)
        Ws.append(wilson_matrix(b, q, rmax, tmax))
        del q
        print(f"{name}  ({time.time() - t0:.0f}s)", file=sys.stderr, flush=True)
    Ws = np.array(Ws)
    Wm = Ws.mean(0)
    pos = {nm: i for i, nm in enumerate(names)}
    blocks = [[pos[nm] for nm in bl] for bl in O.chain_blocks(names)]
    n = len(blocks)
    out = {"campaign": camp, "params": json.load(open(os.path.join(camp, "params.json"))),
           "nshards": len(Ws), "nblocks": n, "rmax": rmax, "tmax": tmax, "nsmear": nsmear, "alpha": ALPHA,
           "W": Wm.tolist(), "W_shards": Ws.tolist(), "r0": {}}
    for T in range(1, tmax + 1):  # NOT A READ: r0/a at every T, the plateau shown rather than assumed
        full = r0_at(Wm, T, rmax)
        jk = np.array([r0_at(np.delete(Ws, bl, axis=0).mean(0), T, rmax) for bl in blocks])
        err = float(np.sqrt((n - 1) / n * np.sum((jk - jk.mean()) ** 2))) if np.all(np.isfinite(jk)) else float("nan")
        out["r0"][T] = [full, err]
        print(f"T={T}  r0/a = {full:.4f} +- {err:.4f}", file=sys.stderr, flush=True)
    print(json.dumps(out, indent=1))
