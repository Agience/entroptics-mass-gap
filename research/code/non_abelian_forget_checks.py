"""Unit checks for `MassGap.NonAbelianForget`: a flux edge that costs nothing per length carries the past,
an edge with a cost per length does not.

The Lean module proves: a power floor on a reading correlator (a free edge, perimeter law) excludes
every exponential bound and every (minorisation, memory) pair in the regime of
`ApertureFixed.reading_cluster`; edge weights `<= K q^j` with `q = exp(-(sigma - h) slab) < 1` give
memory at the rate `q` per slab and one physical mass uniform in the zoom. This script reads the
edge cost `sigma` on cases where it can be computed in seconds:

1. 2D U(1) and 2D SU(2), exact by characters: W(R, T) = u^(R T), u = I1/I0 (U(1)), I2/I1 (SU(2)),
   so sigma = -log u > 0 in both. Checked by quadrature of the one-plaquette integral and by a
   Metropolis run on a periodic 2D lattice (Creutz ratio chi(2,2) against -log u).
   What this tests: the area law is read correctly from loops and Creutz ratios. What it does not:
   2D has no propagating gauge field, so U(1) and SU(2) are both confined there; it cannot separate
   abelian from non-abelian.
2. 4D free photon (noncompact U(1) at weak coupling: a Gaussian massless vector, Feynman gauge,
   e^2 = 1, zero mode removed, direct mode sums, no FFT). Creutz ratios chi(R, R) fall toward 0
   (asserted: strictly decreasing, chi(5,5) < chi(2,2)/4; R^2 chi drifts 0.29 -> 0.16 on 16^4, the
   Coulomb tail plus finite-box terms): perimeter law, sigma = 0. The time edge (Polyakov loop, length L_t): the connected correlator of
   two time edges at distance R is ~ e^2 L_t Gt(R), Gt(R) ~ 1/(4 pi R): a power law, the edge spans
   until it is observed. With a mass M the same correlator decays like exp(-M_lat R): an edge cost
   per length. This is the abelian obstruction (must fail, and does).
3. Strong coupling, 4D U(1) and 4D SU(2) (Metropolis on 4^4): area law with
   sigma ~ -log u(beta), u = I1/I0(beta) ~ beta/2 (U(1)), I2/I1(beta) ~ beta/4 (SU(2)), leading order.
   Both gapped: compactness at strong coupling confines U(1) too, so this does not separate them.
4. The regime lemma `edge_regime` on a grid.

Not reached by any check here: 4D SU(N) at weak coupling, sigma > 0 uniform in the zoom (confinement).
That is the remaining analytic input `NonAbelianForgetting`; no 10-second computation decides it.

Each section runs in under 10 seconds; the script asserts it.
"""
import math
import time

import numpy as np
from scipy.special import iv

RNG = np.random.default_rng(20261029)  # CHOSEN: a fixed seed, for a reproducible run.
# CHOSEN: 10 s per section is the run-time budget the module docstring states; a run time, not a physics cut.
BUDGET = 10.0  # CHOSEN: the per-section wall-clock ceiling from the task brief, in seconds.


def timed(name, fn):
    t0 = time.perf_counter()
    out = fn()
    dt = time.perf_counter() - t0
    print(f"  [{name}: {dt:.2f} s]")
    assert dt < BUDGET, f"{name} exceeded {BUDGET} s"
    return out


# ---------------------------------------------------------------------------------------------
# 1. 2D U(1) and SU(2) by characters
# ---------------------------------------------------------------------------------------------

def u_u1(beta):
    return iv(1, beta) / iv(0, beta)


def u_su2(beta):
    return iv(2, beta) / iv(1, beta)


# CHOSEN: 20000 midpoint nodes; the rule is spectrally accurate on a periodic analytic integrand, so this is far past the 1e-8 agreement section 1 asks for.
def quad_u1(beta, n=20000):
    th = (np.arange(n) + 0.5) * 2 * np.pi / n
    w = np.exp(beta * np.cos(th))
    return float(np.sum(np.cos(th) * w) / np.sum(w))


# CHOSEN: 20000 midpoint nodes, the same count as quad_u1; ample for the 1e-8 agreement section 1 asks for.
def quad_su2(beta, n=20000):
    # U ~ exp(i a n.sigma): Haar density (2/pi) sin^2 a on [0, pi], action (beta/2) tr U = beta cos a.
    a = (np.arange(n) + 0.5) * np.pi / n
    w = np.sin(a) ** 2 * np.exp(beta * np.cos(a))
    return float(np.sum(np.cos(a) * w) / np.sum(w))


# --- U(1) lattice (angles), any dimension -------------------------------------------------

def u1_plaq_angles(th, mu, nu):
    return th[mu] + np.roll(th[nu], -1, axis=mu) - np.roll(th[mu], -1, axis=nu) - th[nu]


def u1_staple(th, mu):
    d = th.shape[0]
    S = np.zeros(th.shape[1:], dtype=complex)
    # NOT A READ: the loop is over the staple's nu orientations; the rolls are the forward and backward neighbour shifts of the links
    for nu in range(d):
        if nu == mu:
            continue
        up = np.roll(th[nu], -1, axis=mu) - np.roll(th[mu], -1, axis=nu) - th[nu]
        dn_nu = np.roll(th[nu], 1, axis=nu)
        dn = -np.roll(dn_nu, -1, axis=mu) - np.roll(th[mu], 1, axis=nu) + dn_nu
        S += np.exp(1j * up) + np.exp(1j * dn)
    return S


def parity(shape):
    idx = np.indices(shape).sum(axis=0)
    # DERIVED: the parity test (coordinate sum mod 2 equal to 0 or 1) splits the lattice into its two checkerboard sublattices; not a magnitude.
    return [(idx % 2) == 0, (idx % 2) == 1]


def u1_sweep(th, beta, step, masks):
    d = th.shape[0]
    acc = 0
    for mu in range(d):
        for m in masks:
            S = u1_staple(th, mu)
            new = th[mu] + RNG.uniform(-step, step, size=th[mu].shape)
            dS = beta * (np.real(np.exp(1j * new) * S) - np.real(np.exp(1j * th[mu]) * S))
            ok = m & (np.log(RNG.random(th[mu].shape)) < dS)
            th[mu] = np.where(ok, new, th[mu])
            acc += ok.sum()
    return acc


# CHOSEN: the default plane is directions 0 and 1, the only plane in 2D; the 4D section passes every plane explicitly.
def u1_wilson(th, R, T, mu=0, nu=1):
    # sum of link angles around the R x T loop based at every site
    a = np.zeros(th.shape[1:])
    # NOT A READ: the loop walks the R mu-edges of one closed rectangle; the rolls place each link on the path, so the sum is the defined holonomy of the loop, not a lag profile
    for i in range(R):
        a += np.roll(th[mu], -i, axis=mu)
        a -= np.roll(np.roll(th[mu], -i, axis=mu), -T, axis=nu)
    # NOT A READ: the T nu-edges of the same closed rectangle, completing the holonomy
    for j in range(T):
        a += np.roll(np.roll(th[nu], -j, axis=nu), -R, axis=mu)
        a -= np.roll(th[nu], -j, axis=nu)
    return float(np.mean(np.cos(a)))


# --- SU(2) lattice (unit quaternions), any dimension ----------------------------------------

def qmul(a, b):
    a0, av = a[..., 0], a[..., 1:]
    b0, bv = b[..., 0], b[..., 1:]
    c0 = a0 * b0 - np.sum(av * bv, axis=-1)
    cv = a0[..., None] * bv + b0[..., None] * av + np.cross(av, bv)
    return np.concatenate([c0[..., None], cv], axis=-1)


def qdag(a):
    return np.concatenate([a[..., :1], -a[..., 1:]], axis=-1)


def qroll(a, s, axis):
    return np.roll(a, s, axis=axis)


def su2_staple(U, mu):
    d = U.shape[0]
    S = np.zeros(U.shape[1:])
    for nu in range(d):
        if nu == mu:
            continue
        # U_mu(x) * [U_nu(x+mu) U_mu(x+nu)^dag U_nu(x)^dag]
        up = qmul(qmul(qroll(U[nu], -1, mu), qdag(qroll(U[mu], -1, nu))), qdag(U[nu]))
        # U_mu(x) * [U_nu(x+mu-nu)^dag U_mu(x-nu)^dag U_nu(x-nu)]
        Unu_m = qroll(U[nu], 1, nu)
        dn = qmul(qmul(qdag(qroll(Unu_m, -1, mu)), qdag(qroll(U[mu], 1, nu))), Unu_m)
        S += up + dn
    return S


def random_near_one(shape, eps):
    v = RNG.normal(size=shape + (3,)) * eps
    q = np.concatenate([np.ones(shape + (1,)), v], axis=-1)
    return q / np.linalg.norm(q, axis=-1, keepdims=True)


def su2_sweep(U, beta, eps, masks):
    d = U.shape[0]
    for mu in range(d):
        for m in masks:
            S = su2_staple(U, mu)
            new = qmul(random_near_one(U.shape[1:-1], eps), U[mu])
            # (beta/2) tr(U S) = beta * (U S)_0
            dS = beta * (qmul(new, S)[..., 0] - qmul(U[mu], S)[..., 0])
            ok = m & (np.log(RNG.random(m.shape)) < dS)
            U[mu] = np.where(ok[..., None], new, U[mu])


def su2_line(U, mu, x_shift_axes, n):
    P = None
    for i in range(n):
        Ui = qroll(U[mu], -i, mu)
        P = Ui if P is None else qmul(P, Ui)
    return P


# CHOSEN: the default plane is directions 0 and 1, the only plane in 2D; the 4D section passes every plane explicitly.
def su2_wilson(U, R, T, mu=0, nu=1):
    A = su2_line(U, mu, None, R)
    B = qroll(su2_line(U, nu, None, T), -R, mu)
    C = qroll(su2_line(U, mu, None, R), -T, nu)
    D = su2_line(U, nu, None, T)
    W = qmul(qmul(A, B), qmul(qdag(C), qdag(D)))
    return float(np.mean(W[..., 0]))  # (1/2) tr = quaternion real part


def creutz(W, R):
    return -math.log(W[(R, R)] * W[(R - 1, R - 1)] / (W[(R, R - 1)] * W[(R - 1, R)]))


def section1():
    print("1. 2D U(1) and SU(2) by characters (area law exact in both; does not separate them)")
    out = {}
    for beta in (1.0, 2.0, 4.0):
        a, b = u_u1(beta), quad_u1(beta)
        c, e = u_su2(beta), quad_su2(beta)
        # CHOSEN: 1e-8 is a quadrature tolerance between the Bessel ratio and the 20000-node integral; the two agree to every printed digit, so the cut is loose.
        assert abs(a - b) < 1e-8 and abs(c - e) < 1e-8
        print(f"   beta={beta}: U(1) u=I1/I0={a:.6f} quad={b:.6f} sigma={-math.log(a):.4f}; "
              f"SU(2) u=I2/I1={c:.6f} quad={e:.6f} sigma={-math.log(c):.4f}")

    def mc_u1():
        L, beta = 16, 2.0
        th = np.zeros((2, L, L))
        masks = parity((L, L))
        for _ in range(200):
            u1_sweep(th, beta, 1.5, masks)
        W = {(R, T): 0.0 for R in range(1, 4) for T in range(1, 4)}
        n = 0
        for _ in range(1500):
            u1_sweep(th, beta, 1.5, masks)
            for k in W:
                W[k] += u1_wilson(th, *k)
            n += 1
        W = {k: v / n for k, v in W.items()}
        W[(1, 0)] = W[(0, 1)] = W[(0, 0)] = 1.0
        return W, beta

    W, beta = timed("2D U(1) Metropolis 16^2", mc_u1)
    u = u_u1(beta)
    for R in (1, 2):
        print(f"   2D U(1) MC beta={beta}: W({R},{R})={W[(R, R)]:.4f} exact u^{R*R}={u**(R*R):.4f}")
    chi = creutz(W, 2)
    print(f"   2D U(1) MC chi(2,2)={chi:.3f} vs sigma=-log u={-math.log(u):.3f}")
    # CHOSEN: 0.1 is a Monte Carlo tolerance on chi(2,2) against -log u (exact 0.360); the fixed-seed run misses by 0.009, about a tenth of the cut.
    assert abs(chi - (-math.log(u))) < 0.1
    out["u1_2d"] = (chi, -math.log(u))

    def mc_su2():
        L, beta = 12, 4.0
        U = np.zeros((2, L, L, 4)); U[..., 0] = 1.0
        masks = parity((L, L))
        for _ in range(150):
            su2_sweep(U, beta, 0.8, masks)
        W = {(R, T): 0.0 for R in range(1, 3) for T in range(1, 3)}
        n = 0
        for _ in range(450):
            su2_sweep(U, beta, 0.8, masks)
            for k in W:
                W[k] += su2_wilson(U, *k)
            n += 1
        W = {k: v / n for k, v in W.items()}
        W[(1, 0)] = W[(0, 1)] = W[(0, 0)] = 1.0
        return W, beta

    W, beta = timed("2D SU(2) Metropolis 12^2", mc_su2)
    u = u_su2(beta)
    print(f"   2D SU(2) MC beta={beta}: W(1,1)={W[(1, 1)]:.4f} exact u={u:.4f}; "
          f"W(2,2)={W[(2, 2)]:.4f} exact u^4={u**4:.4f}")
    chi = creutz(W, 2)
    print(f"   2D SU(2) MC chi(2,2)={chi:.3f} vs sigma=-log u={-math.log(u):.3f}")
    # CHOSEN: Monte Carlo tolerances, 0.02 on W(1,1) against u and 0.15 on chi(2,2) against -log u; the fixed-seed run misses by 0.002 and 0.001.
    assert abs(W[(1, 1)] - u) < 0.02 and abs(chi - (-math.log(u))) < 0.15
    out["su2_2d"] = (chi, -math.log(u))
    return out


# ---------------------------------------------------------------------------------------------
# 2. 4D free photon: perimeter law and the spanning time edge
# ---------------------------------------------------------------------------------------------

def photon_G_plane(L, rmax):
    """G(dx0, dx1, 0, 0) for |dx| <= rmax on an L^4 torus, Feynman gauge, zero mode removed."""
    k = 2 * np.pi * np.arange(L) / L
    s2 = 4 * np.sin(k / 2) ** 2
    K0, K1, K2, K3 = np.meshgrid(s2, s2, s2, s2, indexing="ij")
    khat2 = (K0 + K1 + K2 + K3).ravel()
    kk0, kk1 = np.meshgrid(k, k, indexing="ij")
    kk0 = np.broadcast_to(kk0[:, :, None, None], (L, L, L, L)).ravel()
    kk1 = np.broadcast_to(kk1[:, :, None, None], (L, L, L, L)).ravel()
    # DERIVED: khat2 > 0 drops the k = 0 zero mode (the docstring's "zero mode removed"); the guard against 1/0, not a magnitude.
    keep = khat2 > 0
    inv = np.zeros_like(khat2); inv[keep] = 1.0 / khat2[keep]
    # fold the two transverse directions first: sum over k2, k3 at fixed (k0, k1)
    inv4 = inv.reshape(L, L, L * L).sum(axis=2) / L ** 4
    d = np.arange(-rmax, rmax + 1)
    C0 = np.cos(np.outer(d, k))  # (2r+1, L)
    return C0 @ inv4 @ C0.T, d  # G[i, j] at (d[i], d[j])


def photon_wilson(G, d, R, T):
    off = -d[0]
    # links: mu=0 at (i, 0) +, (i, T) -; mu=1 at (R, j) +, (0, j) -
    l0 = [((i, 0), 1) for i in range(R)] + [((i, T), -1) for i in range(R)]
    l1 = [((R, j), 1) for j in range(T)] + [((0, j), -1) for j in range(T)]
    s = 0.0
    for links in (l0, l1):
        for (x, a) in links:
            for (y, b) in links:
                s += a * b * G[x[0] - y[0] + off, x[1] - y[1] + off]
    return math.exp(-0.5 * s)  # e^2 = 1


def time_edge(Ls, M2, Rs):
    """Gt(R) = sum_t G(R e1, t) for a field of mass^2 M2 on an Ls^3 spatial torus (k0 = 0 mode)."""
    k = 2 * np.pi * np.arange(Ls) / Ls
    s2 = 4 * np.sin(k / 2) ** 2
    A, B, C = np.meshgrid(s2, s2, s2, indexing="ij")
    den = A + B + C + M2
    k1 = np.broadcast_to(k[:, None, None], den.shape)
    # DERIVED: den > 0 drops the massless zero mode; the guard against 1/0, not a magnitude.
    keep = den > 0
    inv = np.where(keep, 1.0 / np.where(keep, den, 1.0), 0.0)
    return np.array([float(np.sum(np.cos(k1 * R) * inv)) / Ls ** 3 for R in Rs])


def section2():
    print("2. 4D free photon (abelian obstruction: perimeter law, sigma = 0; must fail and does)")

    def wl():
        L, rmax = 16, 7
        G, d = photon_G_plane(L, rmax)
        W = {}
        for R in range(0, 6):
            for T in range(0, 6):
                # DERIVED: a loop with R = 0 or T = 0 encloses nothing and has W = 1 by definition; this tests for the degenerate loop, not a magnitude.
                W[(R, T)] = 1.0 if (R == 0 or T == 0) else photon_wilson(G, d, R, T)
        return W

    W = timed("4D photon loops on 16^4", wl)
    chis = [creutz(W, R) for R in range(2, 6)]
    for R, c in zip(range(2, 6), chis):
        print(f"   chi({R},{R}) = {c:.5f}   R^2 chi = {R * R * c:.4f}")
    assert all(chis[i + 1] < chis[i] for i in range(len(chis) - 1))
    assert chis[-1] < 0.25 * chis[0]
    # perimeter law: -log W(R, R) / perimeter roughly constant; / area falls
    for R in (2, 3, 4, 5):
        lw = -math.log(W[(R, R)])
        print(f"   R={R}: -log W/perimeter = {lw / (4 * R):.4f}, -log W/area = {lw / (R * R):.4f}")

    def edges():
        Ls = 96
        Rs = np.arange(2, 15)
        g0 = time_edge(Ls, 0.0, Rs)
        g1 = time_edge(Ls, 0.25, Rs)
        return Rs, g0, g1

    Rs, g0, g1 = timed("time-edge correlator, 96^3", edges)
    # The connected correlator of two time edges (Polyakov loops) of length L_t at distance R, over
    # <P>^2, is exp(e^2 L_t Gt(R)) - 1 (Gaussian). On the torus Gt(R) = 1/(4 pi R) - c_L + O(R^2/L^3),
    # c_L -> 0 with the box; the force R (R+1) (Gt(R) - Gt(R+1)) reads the 1/R law without c_L.
    force = Rs[:-1] * (Rs[:-1] + 1) * (g0[:-1] - g0[1:])
    print(f"   time edge, massless: R(R+1)(Gt(R)-Gt(R+1)) = {np.round(force, 4).tolist()}")
    print(f"     Coulomb 1/(4 pi) = {1 / (4 * np.pi):.4f}: Gt ~ 1/(4 pi R), a power law; the edge spans")
    # CHOSEN: 0.003 on the force against the Coulomb 1/(4 pi) = 0.0796, from R = 5 on; close to its read: the R = 5 value 0.0820 misses by 0.0024.
    assert np.all(np.abs(force[3:] - 1 / (4 * np.pi)) < 0.003)
    # massive: Gt(R) ~ exp(-M_lat R) / (4 pi R), M_lat = 2 asinh(M/2): a cost per unit length
    mlat = 2 * math.asinh(0.5 / 2)
    rate = -np.diff(np.log(Rs * g1))
    print(f"   time edge, mass 0.5: -dlog(R Gt)/dR = {np.round(rate, 4).tolist()} -> M_lat = {mlat:.4f}")
    # CHOSEN: 0.015 on the decay rate against M_lat = 0.4949, from R = 6 on; the R = 6 value 0.5020 misses by 0.007, about half the cut.
    assert np.all(np.abs(rate[4:] - mlat) < 0.015)
    return chis


# ---------------------------------------------------------------------------------------------
# 3. Strong coupling 4D U(1) and SU(2)
# ---------------------------------------------------------------------------------------------

def section3():
    print("3. strong coupling 4D U(1) and SU(2) (area law, sigma ~ -log u; both gapped)")

    def mc_u1():
        L, beta = 4, 0.5
        th = RNG.uniform(-np.pi, np.pi, size=(4, L, L, L, L))
        masks = parity((L,) * 4)
        for _ in range(50):
            u1_sweep(th, beta, np.pi, masks)
        acc = {(1, 1): [], (1, 2): []}
        for _ in range(500):
            u1_sweep(th, beta, np.pi, masks)
            for (R, T) in acc:
                acc[(R, T)].append(np.mean([u1_wilson(th, R, T, mu, nu)
                                            for mu in range(4) for nu in range(4) if mu != nu]))
        return {k: (np.mean(v), np.std(v) / math.sqrt(len(v))) for k, v in acc.items()}, beta

    W, beta = timed("4D U(1) Metropolis 4^4", mc_u1)
    u = u_u1(beta)
    r = W[(1, 2)][0] / W[(1, 1)][0]
    print(f"   U(1) beta={beta}: W(1,1)={W[(1, 1)][0]:.4f}+-{W[(1, 1)][1]:.4f} (LO u={u:.4f}); "
          f"W(1,2)/W(1,1)={r:.4f} (LO u); sigma=-log ratio={-math.log(r):.3f}, "
          f"LO -log u={-math.log(u):.3f}, -log(beta/2)={-math.log(beta / 2):.3f}")
    # CHOSEN: tolerances against the leading-order u, 0.02 on W(1,1) and 0.05 on W(1,2)/W(1,1); they absorb the higher strong-coupling orders and Monte Carlo noise, and the run misses by 0.005 and 0.004.
    assert abs(W[(1, 1)][0] - u) < 0.02 and abs(r - u) < 0.05

    def mc_su2():
        L, beta = 4, 1.0
        U = np.zeros((4, L, L, L, L, 4)); U[..., 0] = 1.0
        masks = parity((L,) * 4)
        for _ in range(40):
            su2_sweep(U, beta, 1.5, masks)
        acc = {(1, 1): [], (1, 2): []}
        for _ in range(120):
            su2_sweep(U, beta, 1.5, masks)
            for (R, T) in acc:
                acc[(R, T)].append(np.mean([su2_wilson(U, R, T, mu, nu)
                                            for mu in range(4) for nu in range(4) if mu < nu]))
        return {k: (np.mean(v), np.std(v) / math.sqrt(len(v))) for k, v in acc.items()}, beta

    W, beta = timed("4D SU(2) Metropolis 4^4", mc_su2)
    u = u_su2(beta)
    r = W[(1, 2)][0] / W[(1, 1)][0]
    print(f"   SU(2) beta={beta}: W(1,1)={W[(1, 1)][0]:.4f}+-{W[(1, 1)][1]:.4f} (LO u={u:.4f}); "
          f"W(1,2)/W(1,1)={r:.4f} (LO u); sigma=-log ratio={-math.log(r):.3f}, "
          f"LO -log u={-math.log(u):.3f}, -log(beta/4)={-math.log(beta / 4):.3f}")
    # CHOSEN: tolerances against the leading-order u, 0.03 on W(1,1) and 0.07 on W(1,2)/W(1,1), looser than U(1) for the shorter SU(2) run; the run misses by 0.001 and 0.003.
    assert abs(W[(1, 1)][0] - u) < 0.03 and abs(r - u) < 0.07


def section4():
    print("4. edge_regime: K/(1-q) q < 1-q for 0 <= q <= 1/(4(K+1))")

    def grid():
        worst = -1.0
        for K in np.linspace(0, 50, 201):
            for q in np.linspace(0, 1 / (4 * (K + 1)), 101):
                worst = max(worst, K / (1 - q) * q - (1 - q))
        return worst

    w = timed("regime grid", grid)
    print(f"   max of K/(1-q) q - (1-q) on the grid: {w:.4f} (< 0)")
    # DERIVED: edge_regime states the strict inequality K/(1-q) q < 1-q, so the grid maximum of the difference must be below 0.
    assert w < 0


if __name__ == "__main__":
    section1()
    section2()
    section3()
    section4()
    print("all checks passed")
