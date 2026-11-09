"""Unit checks for `MassGap.RelativeGap`: the box gap at fixed aperture, read in L^2 of the state.

`FixedAperture` section 4 shows that the sup-based tools (Birkhoff cross ratio, projective diameter)
lose the fixed-aperture gap as the zoom refines: in 4D the cross ratio of the fixed physical slab grows
like (L/a)^2. `RelativeGap` states the floor in the relative form: the maximal correlation rho of the
slab kernel in L^2 of the box state (`GapL2.maxCorr`), gap = -log(rho) / tau per unit physical time.
This script reads that quantity in the two exactly solvable models.

1. 4D free photon (Gaussian, periodic box of N^3 sites per slice, side L, spacing a = L/N, spatial zero
   mode removed). For a Gaussian pair the maximal correlation equals the largest canonical correlation
   (Lancaster; cited, not proved). Per Fourier mode the slab of n = tau N / L steps has canonical
   correlation e^{-n eps_p}, cosh(eps_p) = 1 + p_hat^2 / 2, p_hat^2 = sum 4 sin^2(pi n_i / N). So
   rho_slab = e^{-n eps_min}. Read beside the cross ratio of `fixed_aperture_checks.py` section 3 (same
   formula, same slab tau = L). (a) A direct matrix computation at N = 3, 4 confirms the mode formula.
   (b) The layer split of `RelativeGap.refine_step`: on N -> 2N the modes new at 2N have a slab
   correlation far below the old ones, so rho(2N) = max(rho_old, rho_new) = rho_old; the old modes'
   rho changes by a lattice-dispersion correction (the embedding is not exact), geometric along the
   doubling line read here (ratios near 1/4).
2. 2D U(1) and SU(2) heat kernel, gauge-projected (the slice state is the holonomy class): the L^2
   second eigenvalue of the fixed-slab kernel (heat time t = kappa L tau), from the discretised kernel
   in L^2 of the Haar class measure, and the same read off the N-th power of the one-step kernel. Beside
   it the one-step-composed sup bound tanh(D_1/2)^N of `fixed_aperture_checks.py` section 1.
3. Aperture growth at fixed physical slab thickness tau = 1: photon rho = e^{-2 pi tau / L} -> 1 (fails
   (B)); 2D SU(2) rho = e^{-3 kappa L tau} -> 0.

Each section runs in under 10 seconds; the script asserts it. No Monte Carlo.
"""
import math
import os
import sys
import time

import numpy as np
from entroptics_adapter import matrix_pencil

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fixed_aperture_checks as fa  # noqa: E402

# CHOSEN: the zooms read, N = L / a lattice sites per side (the doubling line of FixedAperture).
NS = (4, 8, 16, 32, 64)
# CHOSEN: units kappa = 1, L = 1, slab tau = L (the slab of fixed_aperture_checks section 3).
KAPPA, L = 1.0, 1.0


def eps(phat2):
    """Lattice energy per step of a mode with lattice momentum squared phat2: cosh eps = 1 + phat2/2."""
    return np.arccosh(1.0 + 0.5 * phat2)


def phat2_modes(N):
    """All nonzero lattice momenta squared on the periodic N^3 box."""
    s = 4.0 * np.sin(np.pi * np.arange(N) / N) ** 2
    p2 = s[:, None, None] + s[None, :, None] + s[None, None, :]
    return p2.ravel()[1:]                                   # drop the zero mode (index 0)


def section1():
    t0 = time.time()
    print("1. 4D free photon: L^2 maximal correlation of the fixed slab tau = L vs the cross ratio")
    tau = L
    prev_rho = None
    for N in NS:
        n = int(round(tau * N / L))
        e_min = float(eps(4.0 * math.sin(math.pi / N) ** 2))
        rho1 = math.exp(-e_min)                              # one lattice step
        rho = math.exp(-n * e_min)                           # the slab, = rho1^n (lossless stacking)
        gapL = -math.log(rho) * L / tau
        cr = math.pi ** 2 * (N ** 3 / 2) * math.sinh(e_min) / math.sinh(N * e_min)   # FA section 3
        print(f"   N={N:3d}: one-step rho_1 = {rho1:.5f} (1 - rho_1 = {1 - rho1:.4f}),"
              f" slab rho = {rho:.6f}, gap*L = {gapL:.4f};  log cross ratio = {cr:9.2f}")
        # CHOSEN: float64 slack on the exact stacking identity rho = rho_1^n.
        assert abs(rho - rho1 ** n) < 1e-12
        # The lattice dispersion sits below the continuum one, so rho falls toward e^{-2 pi} as N grows:
        # the line is not an exact embedding (`RelativeGap.maxCorr_le_of_embed` does not apply), and
        # its rho stays below the coarsest one.
        if prev_rho is not None:
            assert rho <= prev_rho
        prev_rho = rho
    lim = math.exp(-2 * math.pi)
    print(f"   slab rho -> e^(-2 pi) = {lim:.6f}; gap*L -> 2 pi; cross ratio grows like N^2")
    assert abs(prev_rho - lim) < 0.01 * lim + 1e-4

    # (a) direct matrix check of the mode formula: canonical correlations between slice 0 and slice n
    # of the periodic lattice field, spatial zero mode removed, T slices in time.
    print("   (a) direct Gaussian canonical correlations vs mode formula (periodic time T):")
    # NOT A READ: the loop is over two box sizes; its rolls are the neighbour shifts that write down the lattice Laplacian, and the correlation itself is read by matrix_pencil
    for N, T, n in ((3, 24, 2), (4, 20, 3)):
        V = N ** 3
        idx = np.arange(V).reshape(N, N, N)
        lap = np.zeros((V, V))
        # NOT A READ: the loop is over the three axes; the roll is the neighbour shift of the Laplacian stencil
        for ax in range(3):
            # NOT A READ: the forward and backward neighbour of the same Laplacian stencil
            for sh in (1, -1):
                nb = np.roll(idx, sh, axis=ax).ravel()
                lap[idx.ravel(), nb] -= 1.0
            lap[idx.ravel(), idx.ravel()] += 2.0
        Q = np.linalg.qr(np.hstack([np.ones((V, 1)), np.eye(V)[:, :V - 1]]))[0][:, 1:]
        A = Q.T @ lap @ Q                                    # -Delta on the nonconstant modes
        d = A.shape[0]
        Dt = 2.0 * np.eye(T) - np.roll(np.eye(T), 1, axis=1) - np.roll(np.eye(T), -1, axis=1)
        P = np.kron(Dt, np.eye(d)) + np.kron(np.eye(T), A)
        C = np.linalg.inv(P)
        C00, C0n = C[:d, :d], C[:d, n * d:(n + 1) * d]
        # the slice-0 / slice-n covariance pair: its pencil eigenvalues are the canonical correlations
        cc = float(np.abs(matrix_pencil(C00, C0n).evals).max())
        e_min = float(eps(4.0 * math.sin(math.pi / N) ** 2))
        exact = math.cosh((T / 2 - n) * e_min) / math.cosh(T * e_min / 2)   # periodic-time chain
        print(f"      N={N}, T={T}, n={n}: matrix rho = {cc:.10f}, mode formula = {exact:.10f}")
        # CHOSEN: 1e-8 slack for a matrix inverse and pencil of size up to 1260; the two agree to 10 places.
        assert abs(cc - exact) < 1e-8

    # (b) the layer split on N -> 2N: old modes (representable at N) vs the new layer.
    print("   (b) layers on N -> 2N at tau = L: rho(2N) = max(rho_old, rho_new); old-mode drift:")
    drift = 0.0
    for N in NS[:-1]:
        M = 2 * N
        n2 = int(round(tau * M / L))
        k = np.arange(M)
        kk = np.minimum(k, M - k)                            # |momentum index|
        s = 4.0 * np.sin(np.pi * k / M) ** 2
        p2 = (s[:, None, None] + s[None, :, None] + s[None, None, :]).ravel()
        kmax = np.maximum(np.maximum(kk[:, None, None], kk[None, :, None]), kk[None, None, :]).ravel()
        # DERIVED: p2 = 0 exactly at the zero momentum (sin 0 = 0); the zero-mode selector, not a magnitude.
        nz = p2 > 0
        old = nz & (kmax < N / 2)                            # momenta also present at zoom N
        new = nz & ~old
        r_old = math.exp(-n2 * float(eps(p2[old]).min()))
        r_new = math.exp(-n2 * float(eps(p2[new]).min()))
        r_all = math.exp(-n2 * float(eps(p2[nz]).min()))
        rN = math.exp(-int(round(tau * N / L)) * float(eps(4.0 * math.sin(math.pi / N) ** 2)))
        step = abs(math.log(r_old) - math.log(rN))
        drift += step
        print(f"      {N:3d}->{M:3d}: rho_old = {r_old:.6f}, rho_new = {r_new:.3e},"
              f" rho(2N) = {r_all:.6f}; |log rho_old(2N) - log rho(N)| = {step:.2e}")
        # CHOSEN: 1e-15 slack on the exact max identity; r_all and max(r_old, r_new) are the same float
        # computation at values of size 2e-3.
        assert r_new < r_old and abs(r_all - max(r_old, r_new)) < 1e-15
    print(f"      total drift of log rho over the line: {drift:.4f} (geometric: ratios ~ 1/4)")
    dt = time.time() - t0
    print(f"   ({dt:.2f} s)")
    # CHOSEN: the 10 s run-time budget per section stated in the module docstring; it sees no number.
    assert dt < 10


def l2_eigs_u1(t, G=fa.G):
    th = (np.arange(G) + 0.5) * 2 * np.pi / G - np.pi
    K = np.exp(fa.log_theta(th[:, None] - th[None, :], t))
    M = K / G                                                 # measure d theta / 2 pi
    return transfer_evals(M), M


def transfer_evals(M):
    """|eigenvalues| of a one-step kernel M written in an L^2-orthonormal basis, descending: the
    pencil of the pair (zero-lag Gram = identity, one-step = M)."""
    return np.sort(np.abs(matrix_pencil(np.eye(len(M)), M).evals))[::-1]


def l2_eigs_su2(t, G=fa.G):
    th = (np.arange(G) + 0.5) * np.pi / G
    A = np.exp(fa.log_theta(th[:, None] - th[None, :], t))
    B = np.exp(fa.log_theta(th[:, None] + th[None, :], t))
    K = math.exp(t) * (A - B) / (4 * np.sin(th)[:, None] * np.sin(th)[None, :])
    w = (2 / np.pi) * np.sin(th) ** 2 * (np.pi / G)          # Haar class measure
    M = np.sqrt(w)[:, None] * K * np.sqrt(w)[None, :]
    return transfer_evals(M), M


def section2():
    t0 = time.time()
    print("2. 2D heat kernel, gauge-projected: L^2 rho of the slab (tau = L) vs the composed sup bound")
    for name, eig, lk, e1 in (("U(1)", l2_eigs_u1, fa.u1_logk, 1.0), ("SU(2)", l2_eigs_su2, fa.su2_logk, 3.0)):
        t = KAPPA * L * L
        ev, _ = eig(t)
        rho_slab = ev[1] / ev[0]
        print(f"   {name}: slab rho = {rho_slab:.6f}, e^(-{e1:g} kappa L^2) = {math.exp(-e1 * t):.6f}")
        # CHOSEN: 1e-6 slack for the G = 160 class-angle discretisation; the two agree to the 6 printed places.
        assert abs(rho_slab - math.exp(-e1 * t)) < 1e-6
        for N in NS:
            ev1, M1 = eig(t / N)
            r1 = ev1[1] / ev1[0]
            MN = np.linalg.matrix_power(M1, N)
            evN = transfer_evals(MN)
            rN = evN[1] / evN[0]
            D1 = fa.diameter(lk(t / N))
            q = math.exp(-D1)
            comp = math.exp(N * math.log1p(-2 * q / (1 + q)))   # tanh(D1/2)^N
            print(f"     N={N:3d}: one-step rho_1 = {r1:.6f}, rho_1^N = {r1 ** N:.6f},"
                  f" rho(K_1^N) = {rN:.6f};  composed sup bound tanh(D_1/2)^N = {comp:.6f}")
            # CHOSEN: 1e-4 slack for the discretised kernel and its N-th power; they agree to the 6 printed places.
            assert abs(rN - rho_slab) < 1e-4 and abs(r1 ** N - rho_slab) < 1e-4
        # CHOSEN: 0.999 as "the composed bound is lost"; at N = 64 it prints 1.000000.
        assert comp > 0.999
    dt = time.time() - t0
    print(f"   ({dt:.2f} s)")
    # CHOSEN: the 10 s run-time budget per section stated in the module docstring; it sees no number.
    assert dt < 10


def section3():
    print("3. aperture growth at fixed slab thickness tau = 1 (units L0 = 1): rho and gap = -log(rho)/tau")
    for Lb in (1.0, 2.0, 4.0, 8.0, 16.0):
        rp = math.exp(-2 * math.pi / Lb)
        rs = math.exp(-3 * KAPPA * Lb)
        print(f"   L={Lb:5.1f}: photon rho = {rp:.4f} (gap {2 * math.pi / Lb:.4f});"
              f"  2D SU(2) rho = {rs:.3e} (gap {3 * KAPPA * Lb:.2f})")


if __name__ == "__main__":
    section1()
    section2()
    section3()
