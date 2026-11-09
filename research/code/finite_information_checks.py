"""Unit checks for `MassGap.FiniteInformation`: does a finite aperture pass a bounded fraction forward per slab?

The Lean module proves: a slab channel on a finite alphabet with full support has Dobrushin (SDPI) coefficient at
most 1 - |X| * min-entry < 1; coefficients multiply along slabs; so if the readings are a finite-state Markov chain
(`Passes`: the next slab's readings depend on the substrate only through what the aperture holds) the past is
forgotten geometrically at a rate fixed in physical units. With a per-slab Markov defect eps it forgets only down to
a floor 2 eps / c (`substrate_forgets_to_floor`), and that floor is attained (`floor_attained`).

This script reads the quantities the theorem consumes on three models:

1. 4D lattice Gaussian, massive (m = 1 physical) and massless, at zooms n = 2, 3, 4 (cell side, slab thickness
   = n sites, physical 1; spatial box 24 physical, antiperiodic so the massless field has no zero mode). Readings:
   K = 2 adjacent cell-and-slab averages. Exact Gaussian quantities from the momentum sum (no sampling):
     rho1      one-slab maximal correlation (continuous readings);
     rho_past  maximal correlation between the whole past (P slabs) and the reading n slabs ahead;
     CMI_l     Markov defect: I(X_{t+1}; X_{<=t-l} | X_{t-l+1..t}), how much the past beyond the last l slabs adds.
   Discretised readings (each cell read to 3 levels, alphabet |X| = 9), sampled from the exact Gaussian law:
     the one-slab channel's Dobrushin coefficient, its min-entry bound 1 - |X| eps, its chi^2 coefficient,
     and the order-1 Markov defect (plug-in CMI minus the same estimator on the fitted Markov chain).
2. 2D SU(2) Wilson on a cylinder of circumference 1, slab 1 (physical), beta = 4 n^2 (g^2 = 1): the Polyakov class
   is an exact Markov chain (gauge invariance), with eigenvalues a_j(beta)^(n^2). Doeblin constant c (min kernel
   density against Haar), maximal correlation, uniform in the zoom; and the 4-bin discretised class chain.

Runs in a few seconds.
"""
import math
import time

import numpy as np
from entroptics_adapter import matrix_pencil
from scipy.special import ive, ndtr

RNG = np.random.default_rng(20261028)  # CHOSEN: fixed seed for the discretised sampling; verdicts do not depend on it.
# CHOSEN: spatial box (physical units); antiperiodic, so the massless field's lowest |p| is pi*sqrt(3)/24.
LPHYS = 24
# DERIVED: PAST + 17, the slab count of the largest block in `gauss_reads` (past window, gap 16, one more);
# that block uses lags 0..PAST + 16, so lag 41 is computed and unused.
JMAX = 41
# CHOSEN: past window (slabs) standing in for the infinite past.
PAST = 24
# CHOSEN: discretised sample size for the one-slab channel (81 cells; transition entries resolved to ~2e-3).
NSAMP = 200_000
# DERIVED: the N(0,1) tercile point, Phi^{-1}(2/3): three equiprobable levels per cell.
TERC = 0.4307272992954576


# ---------------------------------------------------------------------------------------------------------------
# 4D Gaussian readings
# ---------------------------------------------------------------------------------------------------------------

def reading_lags(n, massive, lphys=LPHYS):
    """Cross-covariance C(j) (2x2) of the two cell readings at slab lag j, j = 0..JMAX, at zoom n."""
    s = b = n
    L = lphys * n
    M = 1.0 / n if massive else 0.0
    k = (np.arange(L) + 0.5) * 2 * np.pi / L
    sin2 = 4 * np.sin(k / 2) ** 2
    D = np.sin(s * k / 2) ** 2 / (s ** 2 * np.sin(k / 2) ** 2)
    psq = sin2[:, None, None] + sin2[None, :, None] + sin2[None, None, :]
    E = np.arccosh(1 + (M ** 2 + psq) / 2)
    W = D[:, None, None] * D[None, :, None] * D[None, None, :]
    Wx = W * np.cos(s * k)[:, None, None]
    base = 1.0 / (2 * np.sinh(E)) / b ** 2
    d = np.arange(1, b)
    S0 = base * (b + 2 * sum((b - dd) * np.exp(-E * dd) for dd in d))
    A = sum(np.exp(-E * dd) for dd in range(b)) * sum(np.exp(E * dd) for dd in range(b))
    C = np.zeros((JMAX + 1, 2, 2))
    r, rx = (W * S0).mean(), (Wx * S0).mean()
    C[0] = [[r, rx], [rx, r]]
    decay = np.exp(-E * b)
    cur = base * A
    for j in range(1, JMAX + 1):
        cur = cur * decay
        r, rx = (W * cur).mean(), (Wx * cur).mean()
        C[j] = [[r, rx], [rx, r]]
    return C / C[0, 0, 0]


def block(C, T):
    """Covariance of T consecutive slabs (2T x 2T), slab-major."""
    S = np.zeros((2 * T, 2 * T))
    for t in range(T):
        for u in range(T):
            S[2 * t:2 * t + 2, 2 * u:2 * u + 2] = C[abs(t - u)] if t >= u else C[abs(t - u)].T
    return S


def cca_pencil(Cxx, Cyy, Cxy):
    """The canonical-correlation pair of two blocks: zero-lag Gram diag(Cxx, Cyy), cross term
    [[0, Cxy], [Cxy^T, 0]]. Its pencil eigenvalues are +-sigma_k, sigma_k the canonical correlations."""
    a, b = len(Cxx), len(Cyy)
    C0 = np.block([[Cxx, np.zeros((a, b))], [np.zeros((b, a)), Cyy]])
    C1 = np.block([[np.zeros((a, a)), Cxy], [Cxy.T, np.zeros((b, b))]])
    return matrix_pencil(C0, C1).evals


def max_corr(Sxx, Syy, Sxy):
    """Top canonical correlation = Gaussian maximal correlation."""
    return float(cca_pencil(Sxx, Syy, Sxy)[0])


def gauss_reads(C):
    S = block(C, PAST + 17)
    out = {}
    out["rho1"] = max_corr(C[0], C[0], C[1])
    # past (slabs 0..PAST-1) against the slab PAST-1+n
    past = slice(0, 2 * PAST)
    out["rho_past"] = {}
    for gap in (1, 2, 4, 8, 12, 16):
        f = slice(2 * (PAST - 1 + gap), 2 * (PAST + gap))
        out["rho_past"][gap] = max_corr(S[past, past], S[f, f], S[past, f])
    # Markov defect: conditional covariance of slab PAST given the last l slabs vs given all PAST slabs
    f = slice(2 * PAST, 2 * PAST + 2)

    def condvar(l):
        p = slice(2 * (PAST - l), 2 * PAST)
        return S[f, f] - S[f, p] @ np.linalg.solve(S[p, p], S[p, f])
    vP = np.linalg.det(condvar(PAST))
    out["cmi"] = {l: 0.5 * math.log(np.linalg.det(condvar(l)) / vP) for l in (1, 2, 4, 8, 16)}
    return out


def letters(x):
    """Two cells, three levels each: letter in 0..8."""
    q = (x > -TERC).astype(int) + (x > TERC).astype(int)
    return 3 * q[..., 0] + q[..., 1]


# DERIVED: alphabet size |X| = 3^2, two cells read to three levels each (letters 0..8 of `letters`).
def channel(a, b, m=9):
    J = np.zeros((m, m))
    np.add.at(J, (a, b), 1.0)
    return J / J.sum()


def coefficients(J):
    """Dobrushin coefficient, min-entry bound 1 - |X| eps, chi^2 coefficient (maximal correlation) of a joint table."""
    p = J.sum(1)
    P = J / p[:, None]
    m = len(p)
    dob = max(1 - np.minimum(P[x], P[y]).sum() for x in range(m) for y in range(m))
    eps = P.min()
    q = J.sum(0)
    # the joint table against its marginals: pencil eigenvalues 1 (the constants), sigma_1, ...
    sv = cca_pencil(np.diag(p), np.diag(q), J)
    return dob, 1 - m * eps, float(sv[1])


def markov_defect(T3):
    """Of an exact three-time table p(b0, b1, b2): I(b2; b0 | b1) in nats, and the per-slab TV defect
    max_{b1, b0, b0'} TV(p(. | b0, b1), p(. | b0', b1)) -- the eps of `PassesWithin` read on the readings."""
    p1 = T3.sum((0, 2))
    p01 = T3.sum(2)
    p12 = T3.sum(0)
    # DERIVED: the guard against log of zero (0 log 0 = 0 in the CMI sum), not a magnitude.
    nz = T3 > 0
    num = (T3 * p1[None, :, None])[nz]
    den = (p01[:, :, None] * p12[None, :, :])[nz]
    I = float((T3[nz] * np.log(num / den)).sum())
    cond = T3 / p01[:, :, None]
    m = T3.shape[0]
    tv = max(0.5 * np.abs(cond[a, b1] - cond[c, b1]).sum() for b1 in range(m) for a in range(m) for c in range(m))
    return I, float(tv)


def discrete_reads(C):
    """Two cells x three levels: the one-slab channel, sampled from the exact Gaussian law."""
    S = block(C, 2)
    Z = RNG.standard_normal((NSAMP, 4)) @ np.linalg.cholesky(S).T
    X = letters(Z.reshape(NSAMP, 2, 2))
    dob, floor_bound, chi1 = coefficients(channel(X[:, 0], X[:, 1]))
    return dict(dob=dob, floor_bound=floor_bound, chi1=chi1)


# CHOSEN: 300 quadrature points on [-7, 7] per axis (spacing ~0.047); a finer grid costs G^2 work and
# moves the printed defect only through the quadrature error.
def one_cell_defect(C, G=300):
    """One cell, three levels, three consecutive slabs: the exact table by quadrature (x0, x1 on a grid, x2 by the
    conditional normal cdf), then its Markov defect."""
    r1, r2 = C[1, 0, 0], C[2, 0, 0]
    S01 = np.array([[1, r1], [r1, 1]])
    w = np.linalg.solve(S01, [r2, r1])
    sd = math.sqrt(1 - np.dot([r2, r1], w))
    x = np.linspace(-7, 7, G)
    dx = x[1] - x[0]
    X0, X1 = np.meshgrid(x, x, indexing="ij")
    Si = np.linalg.inv(S01)
    dens = np.exp(-0.5 * (Si[0, 0] * X0 ** 2 + 2 * Si[0, 1] * X0 * X1 + Si[1, 1] * X1 ** 2))
    dens *= dx * dx / (2 * np.pi * math.sqrt(np.linalg.det(S01)))
    mu = w[0] * X0 + w[1] * X1
    edges = [-np.inf, -TERC, TERC, np.inf]
    lev = np.digitize(x, edges[1:-1])
    T3 = np.zeros((3, 3, 3))
    for c in range(3):
        pc = ndtr((edges[c + 1] - mu) / sd) - ndtr((edges[c] - mu) / sd)
        M = dens * pc
        for a in range(3):
            for b in range(3):
                T3[a, b, c] = M[np.ix_(lev == a, lev == b)].sum()
    return markov_defect(T3 / T3.sum())


# ---------------------------------------------------------------------------------------------------------------
# 2D SU(2) Polyakov class chain
# ---------------------------------------------------------------------------------------------------------------

# CHOSEN: nbins = 4 equal-Haar-mass bins (the docstring's 4-bin class chain); G = 600 midpoint grid
# on (0, pi) for the Haar integral; jcut = 40 characters 2j = 0..39, truncating the character sum.
def su2_chain(n, nbins=4, G=600, jcut=40):
    beta = 4.0 * n * n
    twoj = np.arange(0, jcut)
    a = ive(twoj + 1, beta) / ive(1, beta)
    lam = a ** (n * n)
    th = (np.arange(G) + 0.5) * np.pi / G
    h = (2 / np.pi) * np.sin(th) ** 2 * (np.pi / G)  # Haar weight of each grid point
    chi = np.sin(np.outer(twoj + 1, th)) / np.sin(th)[None, :]
    K = (chi.T * lam) @ chi  # density against Haar
    c = float(K.min())
    c2 = float(((chi.T * lam ** 2) @ chi).min())  # two slabs
    rho = float(lam[1])
    # equal-Haar-mass bins
    cdf = np.cumsum(h) / h.sum()
    bins = np.minimum((cdf * nbins).astype(int), nbins - 1)
    B = np.zeros((nbins, G))
    B[bins, np.arange(G)] = 1.0
    P1 = K * h[None, :]  # one-step transition on the grid
    J = (B * h) @ P1 @ B.T
    dob, floor_bound, chi1 = coefficients(J)
    # order-1 Markov defect of the binned chain, exact: I(b2; b0 | b1)
    T3 = np.einsum("ag,g,gk,kl,bk,cl->abc", B, h, P1, P1, B, B, optimize=True)
    defect, tvdef = markov_defect(T3 / T3.sum())
    return dict(beta=beta, c=c, c2=c2, rho=rho, rho_lim=math.exp(-3 / 8), dob=dob, floor_bound=floor_bound,
                chi1=chi1, defect=defect, tvdef=tvdef)


def m_eff(rp, a, b):
    """Decay rate per slab of the past-to-future dependence between gaps a and b."""
    return math.log(rp[a] / rp[b]) / (b - a)


def main():
    t0 = time.time()
    res = {}
    print(f"4D Gaussian, K = 2 cells, physical cell = slab = 1, box {LPHYS} (antiperiodic)")
    for massive in (True, False):
        for n in (2, 3, 4):
            C = reading_lags(n, massive)
            g = gauss_reads(C)
            d = discrete_reads(C)
            I1, tv1 = one_cell_defect(C)
            res[(massive, n)] = (g, d, I1, tv1)
            tag = "massive " if massive else "massless"
            print(f"  {tag} n={n}: rho1={g['rho1']:.3f}  rho_past(gap)=" +
                  " ".join(f"{k}:{v:.3g}" for k, v in g["rho_past"].items()) +
                  f"  m_eff(4->8)={m_eff(g['rho_past'], 4, 8):.3f} m_eff(8->16)={m_eff(g['rho_past'], 8, 16):.3f}")
            print(f"      composition test rho_past(gap) / rho1^gap: " + " ".join(
                f"{k}:{v / g['rho1'] ** k:.3g}" for k, v in g["rho_past"].items() if k in (2, 8, 16)) +
                "  (<= 1 for a Markov reading chain)")
            print(f"      Markov defect CMI_l (nats) " + " ".join(f"l={k}:{v:.2e}" for k, v in g["cmi"].items()))
            print(f"      discretised |X|=9 one-slab channel: Dobrushin={d['dob']:.3f} "
                  f"(min-entry bound {d['floor_bound']:.3f}) chi2-coef={d['chi1']:.3f};  "
                  f"1 cell x 3 levels exact order-1 defect: CMI={I1:.2e} TV eps={tv1:.4f}")
    print("box dependence at n = 2 (decay rate of the past-to-future dependence, per slab)")
    box = {}
    for massive, lp in ((True, 48), (False, 48)):
        if True:
            g = gauss_reads(reading_lags(2, massive, lp))
            box[(massive, lp)] = g
            tag = "massive " if massive else "massless"
            slope = math.log(g["rho_past"][8] / g["rho_past"][16]) / math.log(2)
            print(f"  {tag} box {lp:2d}: m_eff(4->8)={m_eff(g['rho_past'], 4, 8):.3f} "
                  f"m_eff(8->16)={m_eff(g['rho_past'], 8, 16):.3f} log-slope(8->16)={slope:.2f}  "
                  f"box floor pi*sqrt(3)/box={math.pi * math.sqrt(3) / lp:.3f}  rho_past(16)={g['rho_past'][16]:.3g}  "
                  f"CMI_8={g['cmi'][8]:.2e} CMI_16={g['cmi'][16]:.2e}")
    print("2D SU(2) Polyakov class chain, cylinder 1 x slab 1, beta = 4 n^2")
    su = {}
    for n in (2, 4, 8, 16):
        r = su2_chain(n)
        su[n] = r
        print(f"  n={n:2d} beta={r['beta']:6.0f}: Doeblin c(1 slab)={r['c']:.2e} c(2 slabs)={r['c2']:.3f}  "
              f"rho={r['rho']:.4f} (limit {r['rho_lim']:.4f});  4 bins: Dobrushin={r['dob']:.3f} "
              f"chi2={r['chi1']:.3f} order-1 defect CMI={r['defect']:.2e} TV eps={r['tvdef']:.4f}")
    print(f"elapsed {time.time() - t0:.1f} s")
    return res, box, su


if __name__ == "__main__":
    main()
