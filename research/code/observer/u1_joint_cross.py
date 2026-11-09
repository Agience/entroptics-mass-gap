"""The cross blocks of the joint view's near row on compact U(1): how the cell energies move the coarse links'
conditional law, and how the coarse links move the cell energies' conditional law. numpy only.

The joint view's sites are the coarse links (TV cost) and the cell energies (W1 cost). Its near row splits into four
blocks: a (links on links, TV; u1_coarse_read.py), d (energies on energies, W1; cellview_w1.py), and the two read here:

  b  links from energies, TV per unit energy. For a coarse link l, the regression of cos k phi_l and sin k phi_l
     (k <= K) on the energies of the 8 cells whose edge l is, with |S_l| as a control, gives d<cos k phi>/dE_j; the
     density derivative is (1/2pi) sum_k 2 (b^c_kj cos k x + b^s_kj sin k x), and its half-L1 norm is the TV per unit
     energy of cell j. b = sum over the 8 cells.
  c  energies from links, energy per unit TV. For a cell, the indicator 1{E <= t} (NT thresholds) is regressed on
     the energies of its 8 nearest cells and on cos of the 54 coarse plaquettes based at the cell and those 8 cells.
     Changing one coarse link changes cos of its 6 plaquettes by at most 2 each, so its influence is at most
     2 sum_{p containing it} int |beta_p| dt, and summing over links counts each plaquette 4 times:
     c = 8 sum_p int |beta_p| dt (an upper reading over links).

|beta| is read by the cross-fit (sign on one half of the groups, value on the other), as cellview_w1.py does.

The joint near row's condition is that some rescaling of the energy cost makes every row below 1, i.e. the Perron
root of [[a, b], [c, d]] below 1: rho = ((a + d) + sqrt((a - d)^2 + 4 b c))/2.

    python u1_joint_cross.py OUT.json b file1.npz ...      (files of u1_cell_read.py with SAVE_LINKS=1)
"""
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from u1_coarse_read import coarse_links, phi_r  # noqa: E402

# CHOSEN: harmonics k <= 4 of phi regressed (block b); a basis-size budget
K = 4
# CHOSEN: energy thresholds for the t-integral of block c; a quadrature grid
NT = 40
# CHOSEN: cross-fit splits (a compute budget against split noise)
NSPLIT = 8


def plaq_cos(Th):
    """cos of the 6 coarse plaquettes based at every coarse site: (n, m, m, m, m, 6)."""
    sh = lambda a, mu: np.roll(a, -1, axis=1 + mu)
    out = []
    for mu in range(4):
        for nu in range(mu + 1, 4):
            P = Th[..., mu] + sh(Th[..., nu], mu) - sh(Th[..., mu], nu) - Th[..., nu]
            out.append(np.cos(P))
    return np.stack(out, -1)


def wls_beta(X, Y, idx):
    Xs = np.concatenate([np.ones((len(idx), 1)), X[idx]], 1)
    A = Xs.T @ Xs
    return np.linalg.solve(A, Xs.T @ Y[idx])[1:]


def xfit(X, Y, grp, rng):
    G = np.unique(grp)
    out = []
    for _ in range(NSPLIT):  # NOT A READ: cross-fit halves
        A = rng.permutation(G)[: len(G) // 2]
        ia, ib = np.isin(grp, A), ~np.isin(grp, A)
        Ba, Bb = wls_beta(X, Y, np.where(ia)[0]), wls_beta(X, Y, np.where(ib)[0])
        out.append(0.5 * (np.sign(Ba) * Bb + np.sign(Bb) * Ba))
    return np.mean(out, 0), np.std(out, 0)


if __name__ == "__main__":
    out, b, files = sys.argv[1], int(sys.argv[2]), sys.argv[3:]
    rng = np.random.default_rng(20261005)
    dirs = sorted({os.path.dirname(os.path.abspath(f)) for f in files})
    Es, Ths, grp = [], [], []
    for f in files:
        z = np.load(f)
        E = z[f"b{b}"].astype(np.float64)
        Th = coarse_links(z["theta_s"].astype(np.float64), b)
        Es.append(E)
        Ths.append(Th)
        grp.append(np.arange(E.shape[0]) + 1000 * dirs.index(os.path.dirname(os.path.abspath(f))))
    E = np.concatenate(Es)
    Th = np.concatenate(Ths)
    g = np.concatenate(grp)
    E = E - E.mean()
    n, m = E.shape[0], E.shape[1]
    roll = lambda a, d: np.roll(a, tuple(-v for v in d), axis=(1, 2, 3, 4))
    unit = lambda mu, s: tuple(s if i == mu else 0 for i in range(4))
    nn = [unit(mu, s) for mu in range(4) for s in (1, -1)]

    # c: energies from links
    pc = plaq_cos(Th)
    regs = [roll(E, d) for d in nn] + [roll(pc, d)[..., q] for d in [(0, 0, 0, 0)] + nn for q in range(6)]
    X = np.stack([r.ravel() for r in regs], 1)
    gc = np.repeat(g, m ** 4)
    y = E.ravel()
    tj = np.quantile(y, np.linspace(0.01, 0.99, NT))
    dt = np.gradient(tj)
    Yt = (y[:, None] <= tj[None]).astype(float)
    bt, bsd = xfit(X, Yt, gc, rng)   # (regressors, NT)
    c_energy_row = float((bt[:8] @ dt).sum())
    c_plaq = float((bt[8:] @ dt).sum())
    c_val = 8 * c_plaq

    # b: links from energies
    phi, rr = phi_r(Th)
    bcols = []
    for mu in range(4):
        others = [nu for nu in range(4) if nu != mu]
        cells = []
        for mask in range(8):  # NOT A READ: the 8 cells having the edge (X, mu)
            d = [0, 0, 0, 0]
            for t, nu in enumerate(others):
                if mask >> t & 1:
                    d[nu] = -1
            cells.append(roll(E, tuple(d)))
        bcols.append(np.stack(cells + [rr[..., mu]], -1))
    Xb = np.stack(bcols, -2).reshape(-1, 9)
    gb = np.repeat(g, m ** 4 * 4)
    ph = phi.reshape(-1)
    Yb = np.stack([np.cos(k * ph) for k in range(1, K + 1)] + [np.sin(k * ph) for k in range(1, K + 1)], 1)
    bb, bbsd = xfit(Xb, Yb, gb, rng)
    grid = np.linspace(-np.pi, np.pi, 512, endpoint=False)
    basis = np.stack([2 * np.cos(k * grid) for k in range(1, K + 1)] + [2 * np.sin(k * grid) for k in range(1, K + 1)])
    tvs = []
    for j in range(8):  # NOT A READ: TV per unit energy of each of the 8 cells
        dens = (bb[j] @ basis) / (2 * np.pi)
        tvs.append(0.5 * np.abs(dens).sum() * (2 * np.pi / len(grid)))
    b_val = float(sum(tvs))
    rep = {"files": files, "b": b, "m": m, "centres": int(n * m ** 4), "links": int(phi.size),
           "c_energy_from_links": c_val, "c_plaq_sum": c_plaq, "energy_nn_row_in_this_fit": c_energy_row,
           "b_links_from_energy": b_val, "b_per_cell": tvs, "sd_E": float(E.std())}
    print(json.dumps({k: v for k, v in rep.items() if k != "files"}), flush=True)
    with open(out, "w") as f:
        json.dump(rep, f, indent=1)
