"""Unit checks for `MassGap.UniformAperture`: (B) from cells of one fixed physical length.

`UniformAperture.contr_of_gram` bounds the slab rate by the cell rate and the Gram row sum of the
coupling between cells: if every mean-zero g is a sum of pairwise orthogonal pieces v_i (one per cell)
with ||K v_i||^2 <= rho_c^2 ||v_i||^2 and <K v_i, K v_j>^2 <= c_ij^2 ||v_i||^2 ||v_j||^2, then
rho^2 <= rho_c^2 + eta, eta = max_i sum_{j != i} c_ij. (B) asks that rho_c and eta stay bounded with
rho_c^2 + eta < 1 as the aperture L grows at fixed cell side ell. This script reads those numbers.

1. Lattice Gaussian fields, spacing a = 1, periodic spatial box of side L (L^d sites per slice), slab
   of tau lattice steps, cells of side ell (d = 3: the 4D field; d = 1: the 2D field, which reaches
   large L). Gaussian, so the maximal correlation is the largest canonical correlation (Lancaster;
   cited, not proved) and is attained on linear functionals. In the state's norm a linear functional
   a.phi(0) has ||.||^2 = a^T C0 a; whitened, b = C0^{1/2} a, and the slab kernel acts as
   T = C0^{-1/2} C_tau C0^{-1/2}, diagonal in momentum with entries e^{-eps_p tau},
   cosh eps_p = 1 + (m^2 + p_hat^2)/2. The pieces are the martingale differences along the
   lexicographic order of the cells: QR of the columns of C0^{1/2} taken cell by cell, Q_i the block of
   cell i. Then rho_c^2 = max_i ||Q_i^T T^2 Q_i||, c_ij = ||Q_i^T T^2 Q_j||. All of this is on the
   first chaos (linear functionals): Lancaster gives rho there, not rho_c or eta over all of L^2. The
   asserted bound rho^2 <= rho_c^2 + eta checks the implementation of the Schur bound, not a property
   of the field. The ||offdiag|| column (operator norm of the off-diagonal Gram part, the additive
   form) is skipped (nan) above 1024 sites.
   Massive (m = 1, the gapped control) and massless with the spatial zero mode removed (a massless
   scalar with the photon's dispersion, one polarisation; not gauge-invariant photon observables).
2. 2D U(1) and SU(2) heat kernel on the periodic box: at fixed time the gauge-invariant states are
   class functions of the one holonomy around the box, so the slab transfer acts on the holonomy
   alone and the cell bound is not exercised. The holonomy slab kernel (heat time t = kappa L tau,
   Haar class measure, discretised) has maximal correlation e^{-kappa L tau} (U(1), charge 1,
   Casimir n^2) and e^{-3 kappa L tau} (SU(2), Casimir n^2 - 1 in the dimension n = 2, the
   normalisation of `FixedAperture.su2_control`), both falling as L grows: (B) holds. The level is a
   flux (torelon) energy growing with L, which fails `VolumeLink` (`FixedAperture.su2_not_volumeLink`).

Total run time under 10 seconds (asserted). No Monte Carlo.
"""
import math
import time

import numpy as np
from entroptics_adapter import matrix_pencil

T_START = time.time()

# CHOSEN: units a = 1; slab thickness and cell side in lattice units; the massive control's mass.
TAU, ELL, MASS = 2, 2, 1.0
# CHOSEN: the aperture sides read (multiples of ELL); 4D up to 12^3 = 1728 sites per slice.
L4 = (4, 6, 8, 10, 12)
# CHOSEN: the 2D aperture sides, doubling from 8 to 256 (4 to 128 cells); 256 is where the massless 2D cell bound has crossed 1, and larger L costs dense QR time.
L2 =(8, 16, 32, 64, 128, 256)


def phat2_grid(L, d):
    """Lattice momentum squared on the periodic L^d box, as a d-dimensional array."""
    s = 4.0 * np.sin(np.pi * np.arange(L) / L) ** 2
    p2 = np.zeros((L,) * d)
    for ax in range(d):
        shape = [1] * d
        shape[ax] = L
        p2 = p2 + s.reshape(shape)
    return p2


def circulant(kernel_fourier, L, d):
    """The real symmetric translation-invariant matrix with the given Fourier multiplier."""
    k = np.real(np.fft.ifftn(kernel_fourier))
    idx = np.indices((L,) * d).reshape(d, -1).T            # site coordinates, lexicographic
    diff = (idx[:, None, :] - idx[None, :, :]) % L
    return k[tuple(diff[..., ax] for ax in range(d))]


def cell_order(L, d, ell):
    """Site indices grouped by cell (cells in lexicographic order), and the cell sizes."""
    idx = np.indices((L,) * d).reshape(d, -1).T
    cell = idx // ell
    ncell = L // ell
    key = np.zeros(len(idx), dtype=int)
    for ax in range(d):
        key = key * ncell + cell[:, ax]
    order = np.argsort(key, kind="stable")
    return order, ncell ** d, ell ** d


def gram_read(L, d, ell, tau, m2, massless):
    """rho, rho_c^2, eta, the additive defect of the block-diagonal part, the block norms c_ij.

    Q = C0^{1/2} P R^{-1} with C0_P = R^T R (Cholesky in cell order: the nested spans of the cells),
    so G = Q^T T^2 Q = R^{-T} C_{2 tau, P} R^{-1}, C_{2 tau} = C0^{1/2} T^2 C0^{1/2} the equal-position
    covariance at time separation 2 tau. Massless: the zero mode is removed from both multipliers and
    the last site of the last cell is dropped (on the zero-mode-free field e_last is minus the sum of
    the others, so every span is unchanged and C0 restricted to the rest is positive definite).
    """
    p2 = phat2_grid(L, d) + m2
    with np.errstate(divide="ignore", invalid="ignore"):
        eps = np.arccosh(1.0 + 0.5 * p2)
        c0 = 1.0 / (2.0 * np.sinh(eps))
    t2 = np.exp(-2.0 * eps * tau)
    if massless:                                            # remove the spatial zero mode
        c0.flat[0] = 0.0
        t2.flat[0] = 0.0
    rho = math.sqrt(t2.max())
    order, nc, cs = cell_order(L, d, ell)
    C0 = circulant(c0, L, d)[np.ix_(order, order)]
    C2 = circulant(c0 * t2, L, d)[np.ix_(order, order)]
    keep = np.arange(len(order) - 1) if massless else np.arange(len(order))
    Rt = np.linalg.cholesky(C0[np.ix_(keep, keep)])         # C0 = Rt Rt^T, Rt lower
    X = np.linalg.solve(Rt, C2[np.ix_(keep, keep)])
    Gk = np.linalg.solve(Rt, X.T).T                         # Rt^{-1} C2 Rt^{-T}
    G = np.zeros((nc * cs, nc * cs))
    G[np.ix_(keep, keep)] = Gk                              # zero row/column at a dropped site
    B = G.reshape(nc, cs, nc, cs).transpose(0, 2, 1, 3)     # B[i, j] = Q_i^T T^2 Q_j
    # NOT A READ: operator norms of the cell blocks of the defined free-field matrix Rt^-1 C2 Rt^-T, the inputs of the Lean cell bound; no measured field enters and the spectrum is read below by matrix_pencil
    c = np.linalg.svd(B, compute_uv=False)[..., 0]         # spectral norms of the blocks
    diag = np.diag(c).copy()
    np.fill_diagonal(c, 0.0)
    eta = c.sum(axis=1).max()
    rc2 = diag.max()
    # the bound the Lean theorem proves, on the first chaos
    assert rho ** 2 <= rc2 + eta + 1e-10, (L, rho ** 2, rc2, eta)
    # additive form: operator norm of the off-diagonal part (GapL2 CellInput reads this as eps)
    off = G.copy()
    for i in range(nc):
        off[i * cs:(i + 1) * cs, i * cs:(i + 1) * cs] = 0.0
    # NOT A READ: the operator norm of the off-diagonal part of the same defined matrix, the eps that GapL2 CellInput consumes; no measured field enters
    # CHOSEN: the dense eigensolve runs only up to 1024 sites (the docstring's cut) to stay inside the 10 s budget; above it the column is nan.
    add = np.abs(np.linalg.eigvalsh(off)).max() if len(off) <= 1024 else float("nan")
    # decay of the cross term with cell distance (from the first cell)
    return rho, rc2, eta, add, c


def section1():
    t0 = time.time()
    print("1. Lattice Gaussian slab, tau = %d, cells of side ell = %d (a = 1)" % (TAU, ELL))
    out = {}
    last = {}
    for d, Ls in ((3, L4), (1, L2)):
        for name, m2, ml in (("massive m=1", MASS ** 2, False), ("massless scalar, photon dispersion", 0.0, True)):
            print("   %dD field (d = %d spatial), %s" % (d + 1, d, name))
            print("     L   cells   rho      rho^2    rho_c^2  eta      rho_c^2+eta  ||offdiag||")
            rows = []
            for L in Ls:
                rho, rc2, eta, add, cmat = gram_read(L, d, ELL, TAU, m2, ml)
                last[(d, ml)] = cmat
                rows.append((L, rho, rc2, eta, add))
                print("    %3d  %5d   %.5f  %.5f  %.5f  %.5f  %.5f      %.5f"
                      % (L, (L // ELL) ** d, rho, rho ** 2, rc2, eta, rc2 + eta, add))
            out[(d, ml)] = rows
    # verdicts
    for d in (3, 1):
        mass = out[(d, False)]
        etas = [r[3] for r in mass]
        sums = [r[2] + r[3] for r in mass]
        # DERIVED: (B) asks rho_c^2 + eta < 1 (module docstring, contr_of_gram); the massive sums read at most 0.035.
        assert max(sums) < 1.0,("massive cell bound must stay below 1", d, sums)
        inc = np.diff(etas)
        # the increments of eta shrink as L grows (a convergent shell sum), unlike the massless line
        assert np.all(inc[1:] <= inc[:-1] + 1e-12), ("massive eta increments shrink", d, etas)
        ml = out[(d, True)]
        rhos = [r[1] for r in ml]
        assert all(b > a for a, b in zip(rhos, rhos[1:])), "massless rho grows with L"
        etas_ml = [r[3] for r in ml]
        assert etas_ml[-1] > etas_ml[0], ("massless eta grows with L", d, etas_ml)
    ml1 = out[(1, True)]
    # DERIVED: the same threshold 1 of (B), here asserted crossed; the massless 2D sum reads 3.06 at L = 256.
    assert ml1[-1][2] + ml1[-1][3] > 1.0,"massless 2D cell bound crosses 1 at the largest aperture"
    # decay profile at the largest 4D aperture: cross term vs cell distance (l_inf), cell 0
    print("   cross term c_ij vs l_inf cell distance from the row i that sets eta, 4D field, L = %d"
          " (the largest distance is the periodic antipode)" % L4[-1])
    for name, ml in (("massive", False), ("massless", True)):
        c = last[(3, ml)]
        n = L4[-1] // ELL
        idx = np.indices((n,) * 3).reshape(3, -1).T
        row = c.sum(axis=1).argmax()                        # the row that sets eta
        dr = np.minimum((idx - idx[row]) % n, (idx[row] - idx) % n).max(axis=1)
        prof = [c[row, dr == k].max() for k in range(1, dr.max() + 1)]
        shell = [c[row, dr == k].sum() for k in range(1, dr.max() + 1)]
        print("     %-9s row i = %3d: max c_ij by l_inf distance 1..%d = %s; shell sums = %s"
              % (name, row, dr.max(), " ".join("%.2e" % x for x in prof),
                 " ".join("%.2e" % x for x in shell)))
    dt = time.time() - t0
    print("   section 1: %.1f s" % dt)


# CHOSEN: 200 midpoint nodes on [0, pi]; enough for the 1e-6 match against e^{-3 t} that section 2 asserts, and small for the dense eigensolve.
def heat_su2(t, n=200):
    """Max correlation of the SU(2) class heat kernel at time t, discretised on [0, pi]."""
    th = (np.arange(n) + 0.5) * np.pi / n
    w = (2.0 / np.pi) * np.sin(th) ** 2 * (np.pi / n)       # Haar class measure
    k = np.arange(1, 60)
    chi = np.sin(np.outer(k, th)) / np.sin(th)[None, :]
    K = (chi.T * np.exp(-t * (k * k - 1))[None, :]) @ chi
    M = np.sqrt(w)[:, None] * K * np.sqrt(w)[None, :]
    # the one-step kernel in the L^2(Haar)-orthonormal basis: zero-lag Gram identity, one-step M
    ev = np.sort(np.abs(matrix_pencil(np.eye(n), M).evals))[::-1]
    return ev[1] / ev[0]


# CHOSEN: 200 nodes on the circle, as in heat_su2; enough for the 1e-6 match against e^{-t}.
def heat_u1(t, n=200):
    """Max correlation of the U(1) heat kernel at time t, discretised on the circle."""
    th = (np.arange(n) + 0.5) * 2 * np.pi / n
    k = np.arange(1, 60)
    cs = np.cos(np.outer(k, th))
    sn = np.sin(np.outer(k, th))
    wgt = 2 * np.exp(-t * k * k)[None, :]
    K = 1.0 + (cs.T * wgt) @ cs + (sn.T * wgt) @ sn
    M = K / n
    # the one-step kernel in the L^2(d theta / 2 pi)-orthonormal basis: zero-lag Gram identity
    ev = np.sort(np.abs(matrix_pencil(np.eye(n), M).evals))[::-1]
    return ev[1] / ev[0]


def section2():
    t0 = time.time()
    kappa, tau = 0.05, 1.0
    print("2. 2D heat kernel, holonomy slab, kappa = %.2f, tau = %.1f: rho vs L" % (kappa, tau))
    print("     L     U(1) rho   e^{-k L tau}   SU(2) rho  e^{-3 k L tau}")
    prev = (1.0, 1.0)
    for L in (1, 2, 4, 8, 16):
        t = kappa * L * tau
        ru, rs = heat_u1(t), heat_su2(t)
        eu, es = math.exp(-t), math.exp(-3 * t)
        # CHOSEN: 1e-6, a discretisation tolerance against the exact e^{-t} and e^{-3 t}; the read agrees in all six printed digits.
        assert abs(ru - eu) < 1e-6 and abs(rs - es) < 1e-6, (L, ru, eu, rs, es)
        assert ru < prev[0] and rs < prev[1]
        prev = (ru, rs)
        print("    %3d   %.6f   %.6f       %.6f   %.6f" % (L, ru, eu, rs, es))
    print("   both fall with L at fixed tau: (B) holds for the 2D theories, U(1) included; the level is a"
          " torelon (fails VolumeLink)")
    print("   section 2: %.1f s" % (time.time() - t0))


if __name__ == "__main__":
    section1()
    section2()
    total = time.time() - T_START
    print("total %.1f s" % total)
    # CHOSEN: the 10 s run-time budget the module docstring states; close to its read, the run takes 8 to 9 s on the shared box.
    assert total < 10.0, total
