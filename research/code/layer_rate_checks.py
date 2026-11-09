"""Unit checks for `MassGap.LayerRate`: the approximate layer split and the rate of the new modes.

`LayerRate.refine_step_sq` bounds one refinement step of the slab's maximal correlation by
    rho_{k+1}^2 <= max(rho_k^2, r_W^2) + eta (2 + eta) + delta,
and `LayerRate.contr_of_approxSplit` gives, for the fine slab alone,
    rho_{k+1}^2 <= max(r_old^2, r_W^2) + delta.
The objects, all measured in L^2 of the fine state:
    delta  = the operator norm of the off-diagonal block of (f, g) -> <K' f, K' g> between the old
             readings and the new layer W (the L^2 orthogonal complement of the old readings), with unit
             input norms: the relative cross term;
    eta    = the intertwining defect, sup over coarse mean-zero u of ||K' e(u) - e(K u)|| / ||u||;
    r_old  = the rate of the fine slab on the old readings, sup ||K' e(u)|| / ||e(u)||;
    r_W    = the rate of the fine slab on W.
This script computes them where they are computable exactly.

1. 4D free fields, Gaussian (Lancaster: the maximal correlation of a Gaussian pair is the largest
   canonical correlation; cited, not proved). Spatial periodic box M^3, side L, spacing a = L/M, slab of
   physical thickness tau, n = tau/a steps. Old readings at zoom N = M/2: the linear functionals of the
   averages over 2x2x2 spatial blocks. Per fine momentum k the whitened slab kernel is e^{-n eps_k},
   cosh eps_k = 1 + (p_hat^2 + m^2 a^2)/2, equal-time variance 1/(2 sinh eps_k). The block average of
   the coarse mode q lives on the 8 aliases k = q + N s, s in {0,1}^3, with Fourier weight
   prod_i cos^2(pi k_i / M); everything is block-diagonal over these fibres, so each quantity is a max
   over fibres of an 8-dimensional computation. The embedding e sends the coarse whitened mode q to the
   normalised block-average vector o_q (an isometry by construction). Linear functionals only: on the
   n-th Wiener chaos the kernel is the n-th tensor power, and a telescoping over the n factors bounds
   the cross term there by n rho^{2(n-1)} delta (sketched here, not proved), so the first chaos sets the
   scale. (a) the 4D free photon with each transverse polarisation treated as a massless scalar (the
   k-dependent transverse projector, which mixes polarisations across the aliases, is not included),
   spatial zero mode removed, tau = L; (b) the free massive scalar, m L = 1, tau = L. Read: delta_k, its ratios along
   the doubling line and its partial sum; r_W for the block layer and for the Fourier layer (momenta new
   at 2N), the latter against e^{-c tau / a}; and both inequalities above on the computed numbers.
2. 2D gauge, heat kernel. (a) Z_G (the discretised U(1)) on a spatial circle of two fine links against
   one coarse link, gauge-projected: old readings = functions of the holonomy theta_1 + theta_2; the
   gauge-variant functions are the rest and the projected kernel kills them, so delta = eta = r_W = 0 to
   rounding. (b) SU(2) class functions: the class heat kernel at heat time t equals the square of the one
   at t/2 (the fine slab is the coarse one exactly), read as an operator difference in L^2 of the
   discretised Haar class measure.
3. 4D U(1) in its Gaussian (Coulomb-phase, spin-wave) form at growing aperture L, fixed tau = 1: delta,
   eta, r_W stay small and summable at every L, while rho -> e^{-2 pi tau / L} -> 1. What fails is (B),
   uniformity in the aperture, not the approximate split or the layer rate. Monopoles are not in the
   Gaussian; the compact theory's Coulomb phase is cited (Guth 1980, Froehlich-Spencer 1982).

Each section runs in under 10 seconds; the script asserts it. No Monte Carlo.
"""
import itertools
import math
import os
import sys
import time

import numpy as np
from entroptics_adapter import matrix_pencil

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import relative_gap_checks as rg  # noqa: E402

# CHOSEN: the coarse zooms read; each step is N -> 2N (the doubling line of FixedAperture).
NS = (4, 8, 16, 32, 64)
# CHOSEN: units L = 1 and slab tau = L, the slab of relative_gap_checks section 1.
L = 1.0
# The 8 aliases of a coarse momentum on the doubled lattice.
SHIFTS = np.array(list(itertools.product((0, 1), repeat=3)))


def fibre_split(N, mass, tau, Lb=L):
    """The approximate-split quantities of one refinement N -> M = 2N, from the 8-alias fibres.

    Returns a dict: rho_c (coarse slab rho at N), r_old, eta, delta, rW_block, rW_fourier, rho_fine
    (the exact slab rho at M), and n_fine (slab steps at M).
    """
    M = 2 * N
    a_f, a_c = Lb / M, Lb / N
    n_f, n_c = int(round(tau / a_f)), int(round(tau / a_c))
    # CHOSEN: float64 slack checking that tau is a whole number of steps at both spacings.
    assert abs(n_f * a_f - tau) < 1e-12 and abs(n_c * a_c - tau) < 1e-12
    q = np.array(list(itertools.product(range(N), repeat=3)))            # (Q, 3)
    k = q[:, None, :] + N * SHIFTS[None, :, :]                            # (Q, 8, 3)
    p2 = (4.0 * np.sin(np.pi * k / M) ** 2).sum(-1)
    eps_f = np.arccosh(1.0 + 0.5 * (p2 + (mass * a_f) ** 2))
    pc = (4.0 * np.sin(np.pi * q / N) ** 2).sum(-1)
    eps_c = np.arccosh(1.0 + 0.5 * (pc + (mass * a_c) ** 2))
    f2 = np.prod(np.cos(np.pi * k / M) ** 2, axis=-1)                     # block-average weight
    # DERIVED: p2 == 0 exactly at k = 0 (sin 0 = 0) and mass == 0 selects the massless line; selectors, not magnitudes.
    zero = (p2 == 0) & (mass == 0)                                        # k = 0, massless only
    live = ~zero
    C = np.where(live, 1.0 / (2.0 * np.sinh(np.where(live, eps_f, 1.0))), 0.0)
    x = np.where(live, np.exp(-n_f * np.where(live, eps_f, 0.0)), 0.0)  # whitened slab kernel
    x2 = x ** 2
    # the old reading of the coarse mode q (q = 0 is the removed zero mode when massless)
    # DERIVED: mass == 0 selects the massless line, the only one with a removed zero mode; not a magnitude.
    has_old = ~(zero.any(axis=1)) if mass == 0 else np.ones(len(q), bool)
    w = np.where(live, f2 * C, 0.0)
    o = np.sqrt(w / w.sum(axis=1, keepdims=True))
    o[~has_old] = 0.0
    xc = np.exp(-n_c * eps_c)
    old2 = (o ** 2 * x2).sum(1)                                           # ||K' o||^2
    delta_q = np.sqrt((o ** 2 * (x2 - old2[:, None]) ** 2).sum(1))       # ||P_perp K'^2 o||
    eta_q = np.sqrt((o ** 2 * (x - xc[:, None]) ** 2).sum(1))            # ||K' o - x_q o||
    # r_W: the largest eigenvalue of P D P on o-perp in each fibre (D = diag x2). It is at most the
    # fibre's max x2, so only the fibres whose max x2 exceeds the best value found need the eigenproblem.
    def rW2_of(sel):
        D = np.einsum('qi,ij->qij', x2[sel], np.eye(8))
        P = np.eye(8)[None] - o[sel][:, :, None] * o[sel][:, None, :]
        # per fibre, the pair (Gram of o-perp = P, two-step = P D P): the pencil drops the o direction
        # at P's own null eigenvalue and returns the spectrum on o-perp
        return np.array([matrix_pencil(Pi, Pi @ Di @ Pi).evals[0] for Pi, Di in zip(P, D)])
    ub = x2.max(1)
    order = np.argsort(-ub)
    # CHOSEN: the first batch size; it changes the run time, never the value.
    first = order[:2048]
    best = float(rW2_of(first).max())
    rest = order[2048:][ub[order[2048:]] > best]
    if len(rest):
        best = max(best, float(rW2_of(rest).max()))
    rW2_q = np.array([best])
    hq = has_old
    # the Fourier layer: momenta new at M (some |k_i| index >= N/2)
    kk = np.minimum(k, M - k)
    newF = live & (kk.max(-1) > N / 2)                    # index N/2 is the coarse Nyquist momentum
    return dict(
        rho_c=float(xc[hq].max()),
        r_old=float(math.sqrt(old2[hq].max())),
        eta=float(eta_q[hq].max()),
        delta=float(delta_q[hq].max()),
        rW_block=float(math.sqrt(max(rW2_q.max(), 0.0))),
        rW_fourier=float(x[newF].max()),
        rho_fine=float(x[live].max()),
        n_fine=n_f,
    )


def run_line(name, mass, tau, Lb=L, ns=NS, verbose=True):
    rows = []
    for N in ns:
        r = fibre_split(N, mass, tau, Lb)
        rows.append((N, r))
        # contr_of_approxSplit on the computed numbers, and refine_step_sq
        lhs = r['rho_fine'] ** 2
        rhs1 = max(r['r_old'], r['rW_block']) ** 2 + r['delta']
        rhs2 = max(r['rho_c'], r['rW_block']) ** 2 + r['eta'] * (2 + r['eta']) + r['delta']
        assert lhs <= rhs1 * (1 + 1e-12) + 1e-300, (N, lhs, rhs1)
        assert lhs <= rhs2 * (1 + 1e-12) + 1e-300, (N, lhs, rhs2)
        # the Fourier layer rate is e^{-c n} with c the smallest per-step energy of a new momentum
        c_eff = -math.log(r['rW_fourier']) / r['n_fine']
        if verbose:
            print(f"   {N:3d}->{2 * N:3d}: rho_k = {r['rho_c']:.6f}, r_old = {r['r_old']:.6f},"
                  f" eta = {r['eta']:.2e}, delta = {r['delta']:.2e}, r_W(block) = {r['rW_block']:.2e},"
                  f" r_W(Fourier) = {r['rW_fourier']:.2e} = e^(-{c_eff:.3f} tau/a);"
                  f" rho(2N) = {r['rho_fine']:.6f}")
    return rows


def section1():
    t0 = time.time()
    tau = L
    for label, mass in (("(a) 4D free photon (per polarisation, zero mode removed)", 0.0),
                        ("(b) 4D free massive scalar, m L = 1", 1.0)):
        print(f"1{label}, tau = L: block-average split on N -> 2N")
        rows = run_line(label, mass, tau)
        ds = [r['delta'] for _, r in rows]
        es = [r['eta'] for _, r in rows]
        ws = [r['rW_block'] for _, r in rows]
        ratios = [ds[i + 1] / ds[i] for i in range(len(ds) - 1)]
        eratios = [es[i + 1] / es[i] for i in range(len(es) - 1)]
        print(f"     delta ratios along the line: {', '.join(f'{x:.3f}' for x in ratios)};"
              f" partial sum of delta = {sum(ds):.3e}")
        print(f"     eta ratios: {', '.join(f'{x:.3f}' for x in eratios)};"
              f" partial sum of eta(2+eta)+delta = {sum(e * (2 + e) + d for e, d in zip(es, ds)):.3e}")
        print(f"     r_W(block) ratios: {', '.join(f'{ws[i + 1] / ws[i]:.3f}' for i in range(len(ws) - 1))}"
              f"  (beside 2^(-3/2) = {2 ** -1.5:.3f}: the block average leaks into the aliases of q along"
              f" the directions where q is nonzero, weight ~ (a/L)^2 times the variance ratio ~ a/L)")
        # the cross term and the defect fall along the doubling line, the layer rate goes to 0
        # DERIVED: a step ratio below 1 is "falls along the line", the claim itself, not a magnitude.
        assert all(x < 1 for x in ratios) and all(x < 1 for x in eratios)
        assert all(ws[i + 1] < ws[i] for i in range(len(ws) - 1))
        # CHOSEN: 1e-30 as the floor below which r_W(Fourier) counts as zero; every row here passes on
        # the first clause (the smallest read is 1.7e-75, still under r_W(block)).
        assert all(r['rW_fourier'] < r['rW_block'] or r['rW_fourier'] < 1e-30 for _, r in rows)
    dt = time.time() - t0
    print(f"   ({dt:.2f} s)")
    # CHOSEN: the 10 s run-time budget per section stated in the module docstring; it sees no number.
    assert dt < 10


def heat_zg(G, s):
    """The heat kernel e^{s Delta} on Z_G as a G x G stochastic matrix."""
    I = np.eye(G)
    lap = np.roll(I, 1, axis=1) + np.roll(I, -1, axis=1) - 2 * I
    # NOT A READ: diagonalises the defined Z_G Laplacian only to exponentiate it into the heat kernel e^{s Delta}; it builds the kernel, it does not read one
    w, U = np.linalg.eigh(lap)
    return (U * np.exp(s * w)) @ U.T


def section2():
    t0 = time.time()
    print("2. 2D gauge, heat kernel: the fine slab against the coarse one")
    # CHOSEN: G = 12 points of Z_G and heat time t = 1 (kappa L tau = 1); any values read the same.
    G, t = 12, 1.0
    h = heat_zg(G, t / 2)                                  # fine: two links, heat time t/2 each
    hc = heat_zg(G, t)                                     # coarse: one link, heat time t
    n = G * G
    idx = np.arange(n).reshape(G, G)
    Pg = np.zeros((n, n))                                  # gauge average over (th1 + d, th2 - d)
    # NOT A READ: the loop is over the G gauge shifts d; the rolls move the index grid by (+d, -d) to write down the gauge-averaging projector, not a lag profile
    for d in range(G):
        Pg[idx.ravel(), np.roll(np.roll(idx, -d, axis=0), d, axis=1).ravel()] += 1.0 / G
    Kf = Pg @ np.kron(h, h) @ Pg
    E = np.zeros((n, G))                                   # e(u)(th1, th2) = u(th1 + th2)
    for a in range(G):
        for b in range(G):
            E[idx[a, b], (a + b) % G] = 1.0
    Qo = E / math.sqrt(G)                                  # orthonormal old readings (uniform state)
    PW = np.eye(n) - Qo @ Qo.T
    eta = np.linalg.norm(Kf @ E - E @ hc, 2) / math.sqrt(G)
    delta = np.linalg.norm(Qo.T @ Kf.T @ Kf @ PW, 2)
    rW = np.linalg.norm(Kf @ PW, 2)
    ev = rg.transfer_evals(hc)                             # the coarse kernel against the uniform state
    print(f"   (a) Z_{G}: eta = {eta:.1e}, delta = {delta:.1e}, r_W = {rW:.1e};"
          f" coarse rho = {ev[1]:.6f} = e^(-{-math.log(ev[1]):.4f})")
    # CHOSEN: rounding slack; all three are 0 in exact arithmetic (they read 3e-16 to 2e-15).
    assert eta < 1e-12 and delta < 1e-12 and rW < 1e-12
    _, M1 = rg.l2_eigs_su2(t / 2)
    _, M2 = rg.l2_eigs_su2(t)
    diff = np.linalg.norm(M1 @ M1 - M2, 2)
    print(f"   (b) SU(2) class functions: ||K_(t/2)^2 - K_t|| = {diff:.1e} in L^2 of the discretised"
          f" class measure (G = {rg.fa.G})")
    # CHOSEN: 1e-4 slack for the discretised class measure; the difference reads 1e-16.
    assert diff < 1e-4
    dt = time.time() - t0
    print(f"   ({dt:.2f} s)")
    # CHOSEN: the 10 s run-time budget per section stated in the module docstring; it sees no number.
    assert dt < 10


def section3():
    t0 = time.time()
    print("3. 4D U(1), Gaussian (Coulomb phase), fixed tau = 1, growing aperture L")
    tau = 1.0
    for Lb, ns in ((1.0, (4, 8, 16)), (2.0, (4, 8, 16)), (4.0, (4, 8, 16)), (8.0, (8, 16, 32))):
        print(f"   L = {Lb:g}  (a = L/N)")
        rows = run_line("U(1)", 0.0, tau, Lb, ns)
        for key in ('delta', 'eta', 'rW_block'):
            v = [r[key] for _, r in rows]
            assert all(v[i + 1] < v[i] for i in range(len(v) - 1)), (Lb, key, v)
        print(f"     rho at the finest zoom = {rows[-1][1]['rho_fine']:.4f};"
              f" e^(-2 pi tau / L) = {math.exp(-2 * math.pi * tau / Lb):.4f}")
    dt = time.time() - t0
    print(f"   ({dt:.2f} s)")
    # CHOSEN: the 10 s run-time budget per section stated in the module docstring; it sees no number.
    assert dt < 10


if __name__ == "__main__":
    section1()
    section2()
    section3()
