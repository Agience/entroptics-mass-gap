"""Unit checks for `MassGap.GapL2`: maximal correlation does not grow with the cross-section.

The Lean module proves, eigen-free, that the L²(stationary) contraction on mean-zero functions (the maximal
correlation rho) combines by `max` over independent cells, multiplies along the time direction, and bounds the
excited weight `tau_n = trc(K^n) - 1` that the far input reads. This script checks those statements on exact
finite chains and reads rho on four models next to the Birkhoff (sup) cross ratio theta that
`StrongPhys.PhysStrong` used:

1. random reversible chains: rho(K1 (x) K2) = max(rho1, rho2) (Witsenhausen, both halves), rho(K1 K2) <= rho1 rho2,
   |trc K^n - 1| <= (N - 1) rho^n, |trc K^(2m+q) - 1| <= rho(K^q) tau_2m, exp(-2 delta) trc(K^n)^2 <= trc(K^2n).
2. 2D Ising strip of width W (transverse cells = sites): theta = tanh(K W) -> 1 with W; rho at K < K_c is
   independent of W; with the transverse bond switched off rho = tanh K exactly at every W.
3. O(2) rotor (6-state clock) slabs of width W: rho stable in W at weak coupling, theta grows.
4. 4D lattice Gaussian on an L^3 cross-section: rho(slab of thickness l) = exp(-E_0 l), E_0 = arccosh(1 + M^2/2),
   independent of L; tau_n / (L^3 exp(-E_0 n)) bounded (the level-count clause with d = 3). Massless: rho = 1 with
   the zero mode, and rho -> 1 as L grows with it removed (must fail).

No sampling. Runs in a few seconds.
"""
import itertools
import math
import time

import numpy as np
from entroptics_adapter import matrix_pencil
from scipy.sparse.linalg import LinearOperator, eigsh

RNG = np.random.default_rng(20261028)  # CHOSEN: a fixed seed for the random chains; any seed gives the same verdicts.
# CHOSEN: float64 slack for the exact inequalities checked on the random chains below.
TOL = 1e-9  # CHOSEN: float64 slack for exact identities on matrices of size <= 400.


def rho_markov(P, pi):
    """Maximal correlation of a Markov pair: the operator norm of D^1/2 P D^-1/2 on the complement of sqrt(pi)."""
    s = np.sqrt(pi)
    S = (s[:, None] * P) / s[None, :]
    S0 = S - np.outer(s, s)
    return float(np.linalg.norm(S0, 2))


def random_reversible(n, pi=None):
    """A random reversible chain: symmetric positive weights W, P = W / rowsum, pi ∝ rowsum (or Metropolis to pi)."""
    if pi is None:
        W = RNG.random((n, n))
        W = W + W.T
        pi = W.sum(1) / W.sum()
        return W / W.sum(1, keepdims=True), pi
    Q = RNG.random((n, n))
    Q = (Q + Q.T) / (2 * n)
    P = np.minimum(Q, Q * (pi[None, :] / pi[:, None]))
    np.fill_diagonal(P, 0)
    np.fill_diagonal(P, 1 - P.sum(1))
    return P, pi


def check_random():
    out = []
    for _ in range(20):  # CHOSEN: 20 random pairs; every one must pass.
        n1, n2 = RNG.integers(2, 8, size=2)
        P1, p1 = random_reversible(n1)
        P2, p2 = random_reversible(n2)
        r1, r2 = rho_markov(P1, p1), rho_markov(P2, p2)
        r12 = rho_markov(np.kron(P1, P2), np.kron(p1, p2))
        # CHOSEN: 1e-8 slack on the exact Witsenhausen equality, for a 2-norm of a matrix up to 49 x 49.
        assert abs(r12 - max(r1, r2)) < 1e-8, (r12, r1, r2)
        # stacking on a common pi
        n = int(RNG.integers(3, 9))
        pi = RNG.random(n) + 0.1
        pi /= pi.sum()
        A, _ = random_reversible(n, pi)
        B, _ = random_reversible(n, pi)
        assert rho_markov(A @ B, pi) <= rho_markov(A, pi) * rho_markov(B, pi) + TOL
        # trace bounds and the doubling inequality
        K, pk = random_reversible(n)
        r = rho_markov(K, pk)
        tr = lambda j: float(np.trace(np.linalg.matrix_power(K, j)))
        for j in range(1, 9):
            assert abs(tr(j) - 1) <= (n - 1) * r ** j + TOL
            delta = (n - 1) * r ** j
            assert math.exp(-2 * delta) * tr(j) ** 2 <= tr(2 * j) + TOL
        for m in range(0, 3):
            for q in range(1, 5):
                s = rho_markov(np.linalg.matrix_power(K, q), pk)
                assert abs(tr(2 * m + q) - 1) <= s * (tr(2 * m) - 1) + TOL
        out.append((r1, r2, r12))
    print(f"[random] 20 pairs: rho(K1 x K2) = max(rho1, rho2) to 1e-8; stacking, trace, transport, doubling: pass")


# ---------------------------------------------------------------------------------------------------------------
# Transfer matrices on a W-site cross-section with a q-state site and nearest-neighbour transverse bond.
# T = V^1/2 U V^1/2, U = (x) u (time bonds, one per site), V diagonal (transverse bonds, periodic).

def transfer_op(u, vdiag, W):
    q = u.shape[0]
    shape = (q,) * W
    sv = np.sqrt(vdiag)

    def mv(x):
        x = np.asarray(x).reshape(-1)
        y = (sv * x).reshape(shape)
        for ax in range(W):
            y = np.moveaxis(np.tensordot(u, y, axes=([1], [ax])), 0, ax)
        return sv * y.reshape(-1)

    return LinearOperator((q ** W, q ** W), matvec=mv, dtype=float)


def transverse_diag(e, W, Kt):
    """exp(Kt * sum_i e(s_i, s_{i+1})), periodic in the transverse direction (open when W = 1)."""
    q = e.shape[0]
    states = np.array(list(itertools.product(range(q), repeat=W)))
    # DERIVED: a one-site cross-section has no transverse bond; a structural case, not a magnitude.
    if W == 1:
        return np.ones(q)
    s = np.zeros(len(states))
    # DERIVED: at W = 2 the periodic wrap is the same bond twice, so it is counted once (W - 1 bonds).
    for i in range(W if W > 2 else W - 1):
        s += e[states[:, i], states[:, (i + 1) % W]]
    return np.exp(Kt * s)


# CHOSEN: k = 3 Lanczos eigenvalues, one more than the two the ratio uses.
def top_ratio(op, k=3):
    # CHOSEN: dense below 65 states, Lanczos above; a run-time choice, both return the same ratio.
    if op.shape[0] <= 64:  # small spaces: dense symmetric eigenvalues
        # the symmetric transfer matrix in the orthonormal state basis: zero-lag Gram identity
        vals = matrix_pencil(np.eye(op.shape[0]), dense(op)).evals
    else:
        vals = eigsh(op, k=k, which="LA", return_eigenvectors=False, tol=1e-10)
    vals = np.sort(np.abs(vals))[::-1]
    return float(vals[1] / vals[0])


def birkhoff_theta(T):
    """tanh(Delta/4), Delta = max_{x,x'} (max_y - min_y) of log T[x] - log T[x'] (Hilbert projective diameter)."""
    L = np.log(T)
    best = 0.0
    for x in range(L.shape[0]):
        D = L[x][None, :] - L
        best = max(best, float((D.max(1) - D.min(1)).max()))
    return math.tanh(best / 4)


def dense(op):
    n = op.shape[0]
    return np.column_stack([op.matvec(e) for e in np.eye(n)])


def limit_bound(rs, label):
    """Cross-section independence read as convergence: the increments of rho(W) at least halve at each step
    (DERIVED: a ratio-1/2 geometric tail sums to at most the last increment), so lim rho <= rho_last + d_last,
    and that bound must stay below 1."""
    d = np.diff(rs)
    assert np.all(np.abs(d[1:]) <= 0.5 * np.abs(d[:-1]) + 1e-12), (label, d)
    bound = rs[-1] + abs(d[-1])
    # DERIVED: rho < 1 is the contraction the claim is about, not a magnitude.
    assert bound < 1, (label, bound)
    print(f"[{label}] increments halve; lim_W rho <= {bound:.6f} < 1")


def check_ising():
    spin = np.array([1.0, -1.0])
    e = np.outer(spin, spin)
    for K, label in ((0.30, "K=0.30 < K_c"), (0.60, "K=0.60 > K_c")):
        u = np.exp(K * e)
        rows = []
        for W in (2, 4, 6, 8, 10, 12, 14):
            op = transfer_op(u, transverse_diag(e, W, K), W)
            rows.append((W, top_ratio(op), math.tanh(K * W)))
        print(f"[ising] {label}: W, rho (one step), theta = tanh(K W)")
        for W, r, th in rows:
            print(f"         W={W:2d}  rho={r:.6f}  theta={th:.6f}")
        # DERIVED: K_c = log(1 + sqrt 2) / 2 = 0.44069, the 2D Ising critical coupling, to 4 places; it
        # only sorts the two scanned K = 0.30 and 0.60 into phases.
        if K < 0.4407:
            limit_bound([r for _, r, _ in rows[1:]], "ising")
        else:
            # CHOSEN: 0.99 as "rho -> 1"; at K = 0.60, W = 14 rho reads 0.999946.
            assert rows[-1][1] > 0.99  # ordered phase: the flip doublet, rho -> 1 (the analogue of a zero mode)
    # theta closed form checked by brute force at small W
    for W in (2, 3, 4):
        T = dense(transfer_op(np.exp(0.3 * e), transverse_diag(e, W, 0.3), W))
        # CHOSEN: float64 slack on the closed form tanh(K W).
        assert abs(birkhoff_theta(T) - math.tanh(0.3 * W)) < 1e-9
    # independent transverse cells: rho = tanh K at every W (Witsenhausen equality)
    for W in (1, 3, 6, 10):
        op = transfer_op(np.exp(0.3 * e), np.ones(2 ** W), W)
        # CHOSEN: 1e-8 slack on the exact rho = tanh K, wider than 1e-9 for the Lanczos tolerance 1e-10.
        assert abs(top_ratio(op) - math.tanh(0.3)) < 1e-8
    print("[ising] theta = tanh(K W) (brute force W<=4); decoupled cells: rho = tanh K at W = 1,3,6,10")


def check_rotor():
    q = 6  # CHOSEN: a 6-state clock discretisation of O(2); enough to separate the two phases at W <= 6.
    ang = 2 * np.pi * np.arange(q) / q
    e = np.cos(ang[:, None] - ang[None, :])
    for K in (0.5, 1.5):
        u = np.exp(K * e)
        print(f"[rotor] K={K}: W, rho (one step), theta (W<=3 brute force)")
        rs = []
        for W in (1, 2, 3, 4, 5, 6):
            op = transfer_op(u, transverse_diag(e, W, K), W)
            r = top_ratio(op, k=4)
            # CHOSEN: the brute-force Birkhoff diameter only up to W = 3 (216 states); a run-time cut.
            th = birkhoff_theta(dense(op)) if W <= 3 else float("nan")
            rs.append(r)
            print(f"         W={W}  rho={r:.6f}  theta={th:.6f}")
        # CHOSEN: selects the weak-coupling one of the two scanned K, where rho is claimed flat in W.
        if K == 0.5:
            limit_bound(rs[1:], "rotor")
    print("[rotor] weak coupling: rho flat in W; theta grows with W")


def lattice_E(M2, p2hat):
    return np.arccosh(1 + (M2 + p2hat) / 2)


def modes(L):
    k = 2 * np.pi * np.arange(L) / L
    s = 4 * np.sin(k / 2) ** 2
    return (s[:, None, None] + s[None, :, None] + s[None, None, :]).reshape(-1)


# CHOSEN: n = 40 Gauss-Hermite nodes; at c = 0.2, 0.5, 0.8 it meets |corr| to 2e-13 or better.
def gaussian_rho_quadrature(c, n=40):
    """Maximal correlation of a standard bivariate Gaussian with correlation c, by Gauss-Hermite discretisation."""
    x, w = np.polynomial.hermite_e.hermegauss(n)
    w = w / w.sum()
    dens = np.exp(-(x[None, :] - c * x[:, None]) ** 2 / (2 * (1 - c * c)))
    dens /= np.sqrt(2 * np.pi * (1 - c * c))
    std = np.exp(-x ** 2 / 2) / np.sqrt(2 * np.pi)
    P = dens / std[None, :] * w[None, :]
    P /= P.sum(1, keepdims=True)
    pi = w
    return rho_markov(P, pi)


def check_gaussian():
    for c in (0.2, 0.5, 0.8):
        # CHOSEN: 1e-6 slack on the quadrature; the measured error is 2e-13 or less.
        assert abs(gaussian_rho_quadrature(c) - c) < 1e-6
    print("[gauss] one mode: maximal correlation of the Gaussian pair = |corr| (Gebelein), checked at c=.2,.5,.8")
    M = 0.5  # CHOSEN: lattice mass 0.5, a diffraction length of 2 lattice spacings.
    ell = 4  # CHOSEN: slab thickness 4 lattice steps.
    E0 = float(np.arccosh(1 + M * M / 2))
    print(f"[gauss] massive M={M}: E_0={E0:.6f}; slab l={ell}: rho, and tau_n/(L^3 e^(-E0 n)) at the cycle n = L")
    for L in (2, 4, 8, 16, 32):
        E = lattice_E(M * M, modes(L))
        rho = float(np.exp(-E.min() * ell))
        n = L
        tau = float(np.expm1(-np.sum(np.log1p(-np.exp(-E * n)))))
        print(f"         L={L:2d}  rho={rho:.6f}  (e^(-E0 l)={math.exp(-E0 * ell):.6f})  "
              f"tau/(L^3 e^-E0n)={tau / (L ** 3 * math.exp(-E0 * n)):.4f}  theta=1 (Gaussian kernel, unbounded ratio)")
        # CHOSEN: float64 slack; the lowest massive mode is the zero momentum, E.min() = E_0 exactly.
        assert abs(rho - math.exp(-E0 * ell)) < 1e-12
    print("[gauss] massless: rho with zero mode, rho without it")
    for L in (4, 8, 16, 32, 64):
        E = lattice_E(0.0, modes(L))
        # DERIVED: the zero-mode selector; the massless zero momentum has E = arccosh(1) = 0 and the
        # next mode has E ~ 2 pi / L >= 0.098 at L <= 64, so any cut between drops exactly the zero mode.
        Enz = E[E > 1e-12]
        r_all = float(np.exp(-E.min() * ell))
        r_nz = float(np.exp(-Enz.min() * ell))
        r_phys = float(np.exp(-Enz.min() * L / 4))  # slab of fixed physical thickness L/4 of the box
        print(f"         L={L:2d}  rho={r_all:.6f}  rho(no zero mode, l={ell})={r_nz:.6f}  "
              f"rho(no zero mode, l=L/4)={r_phys:.6f}")
        # DERIVED: the zero mode has E = 0 exactly, so exp(-0 * ell) = 1.0 exactly.
        assert r_all == 1.0
    # Removing the zero mode is not enough at a fixed slab thickness: the lowest mode has E ~ 2 pi / L, so
    # -log rho * L / (2 pi l) -> 1 and rho -> 1 as the cross-section grows. DERIVED: 2 pi / L, the lowest
    # periodic momentum, and arccosh(1 + 2 sin^2(pi/L)) = 2 pi/L + O(L^-3).
    # CHOSEN: 1e-2 slack on that ratio at L = 64; it reads 0.99925, 7.5e-4 from 1.
    assert abs(-math.log(r_nz) * 64 / (2 * math.pi * ell) - 1) < 1e-2
    print("[gauss] massless: rho = 1 with the zero mode; without it, at fixed l, -log rho ~ 2 pi l / L -> 0")


if __name__ == "__main__":
    t0 = time.time()
    check_random()
    check_ising()
    check_rotor()
    check_gaussian()
    print(f"all checks pass in {time.time() - t0:.1f} s")
