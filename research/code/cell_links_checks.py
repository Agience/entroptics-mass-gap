"""Unit checks for `MassGap.CellLinks`: the three links of (B) on cells of one physical side.

Each section prints its numbers and asserts what the Lean statements use. Exact linear algebra and
exact sums only; no Monte Carlo. Total run time under 10 seconds (asserted).

1. Shell counts of the periodic cell metric (`boxDist`, `UniformAperture.ShellCount`): on M cells per
   side the number of cells at periodic l-infinity distance n from a cell is at most 26 n^2 (n >= 1)
   and 0 at n = 0. Counted for M = 1 .. 16, every n. This is the combinatorial hypothesis the Lean
   module takes for `boxDist`.
2. Link (1), shell coefficients, Gaussian fields (maximal correlation of two Gaussian sets is the
   largest canonical correlation, Lancaster; cited). Dirichlet box of odd side, nearest-neighbour
   precision -Delta + m^2 (an exact Gibbs-Markov field). Around the centre site: the core (sites at
   l-infinity distance < ell/2) and the separating surfaces S_t (sites at distance exactly t ell),
   one site thick, ell apart; S_t separates the core and S_{<t} from S_{>t}. theta_0 = rho(core, S_1),
   theta_t = rho(S_t, S_{t+1}). Checked: rho(core, S_d) <= prod_{t<d} theta_t (the Markov bound of
   `abs_cross_of_shellFactor`). Mass in units of 1/ell (massive: 1; massless: 0).
   * Refinement at fixed physical geometry (ell = 2, 4, 8 sites): the surface coefficients theta_t
     (t >= 1, sets ell apart) move by under 0.02; the coefficient across a shared face (core against
     the touching ring of cells) rises toward 1 for both fields. The L^2 coefficient is uniform in
     the zoom only across a buffer of one cell length.
   * Shell radius (2D, ell = 2, t up to 12): massless theta_t rises (0.76 -> 0.95) and rho(core, S_d)
     falls as a power; massive theta_t settles at 0.38 and rho(core, S_d) falls geometrically.
   * 3D, ell = 2, t up to 2: the same signs.
3. The equal-time slice of the 4D field (the state of a transfer slab, covariance 1/(2 sinh eps)) is
   not a nearest-neighbour Markov field: the same shell bound is read on it, and fails for the
   massless slice (printed, not asserted either way for the massive one).
4. Link (1), finite alphabet: a face of M binary links, each a binary symmetric channel BSC(p).
   Doeblin floor of `FiniteInformation.minor_of_floor` = (2 min(p, 1 - p))^M -> 0; the exact TV
   (Dobrushin) coefficient of BSC(p)^{(x)M} = TV(Bin(M, p), Bin(M, 1 - p)) -> 1; the maximal
   correlation stays |1 - 2p| at every M (it tensorises as a maximum). So only the L^2 form can be
   uniform in the face area.
5. Link (2), path sums: sum_{n >= d} z^n w^n = (zw)^d / (1 - zw) for zw < 1 (the bound of
   `faceEdgeCost_of_pathSum`), divergence for zw >= 1 (`not_summable_of_free`), and
   z e^{-sigma ell} = edgeRate sigma (log z / ell) ell.
6. Lattice character coefficients t(beta) of one plaquette: U(1) I_1/I_0, Z_2 tanh, Z_3, SU(2)
   I_2/I_1. All tend to 1 as beta grows: at the lattice scale every group's per-plaquette cost
   -log t tends to 0, so a per-length edge cost uniform in the zoom is not a lattice-scale weight.
7. 2D gauge exactness: on a ring of n links with a state whose density depends on the holonomy only
   (Haar times a class function, as the 2D Doob state), every gauge-invariant mean-zero function has
   conditional expectation 0 on every proper set of links, so all cell pieces but the last vanish
   and the cross terms are 0. Exact for Z_3 (n = 4) and for the binary tetrahedral group (a finite
   subgroup of SU(2), 24 elements, n = 3).
"""
import itertools
import math
import os
import time

# CHOSEN: four BLAS threads. The blocks are a few thousand wide; more threads contend on a shared box
# and ran slower (15 s uncapped against 3 s capped). Set before numpy loads; an explicit setting wins.
for _var in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_var, "4")

import numpy as np  # noqa: E402
from scipy.special import iv

T_START = time.time()


# ---------------------------------------------------------------------------------------------
# 1. Shell counts
# ---------------------------------------------------------------------------------------------
def pdist(M, a, b):
    d = abs(a - b)
    return min(d, M - d)


def shell_counts(M):
    """Counts of cells at each periodic l-infinity distance from cell (0,0,0) on M^3 cells."""
    counts = {}
    for i in itertools.product(range(M), repeat=3):
        n = max(pdist(M, 0, c) for c in i)
        counts[n] = counts.get(n, 0) + 1
    return counts


print("1. shell counts of the periodic cell metric (A = 26, p = 2)")
for M in range(1, 17):
    cnt = shell_counts(M)
    # DERIVED: exactly one cell sits at distance 0, the cell itself (ShellCount is 0 there).
    assert cnt.get(0, 0) == 1  # the cell itself; excluded from its row
    for n, c in cnt.items():
        # DERIVED: the shell bound 26 n^2 is stated for n >= 1; n = 0 is the cell itself.
        if n >= 1:
            assert c <= 26 * n ** 2, (M, n, c)
    if M in (4, 8, 16):
        print(f"   M = {M:2d}: " + ", ".join(f"n={n}:{c}" for n, c in sorted(cnt.items())))


# ---------------------------------------------------------------------------------------------
# 2-3. Gaussian shell coefficients
# ---------------------------------------------------------------------------------------------
def dirichlet_modes(L):
    x = np.arange(L)
    k = np.arange(1, L + 1)
    phi = np.sqrt(2.0 / (L + 1)) * np.sin(np.pi * np.outer(x + 1, k) / (L + 1))
    lam = 2.0 - 2.0 * np.cos(np.pi * k / (L + 1))
    return phi, lam


def modes_at(phi, A):
    """The product eigenvectors of the Dirichlet box evaluated on the sites A (rows)."""
    UA = phi[A[:, 0]]
    for ax in range(1, A.shape[1]):
        UA = (UA[:, :, None] * phi[A[:, ax]][:, None, :]).reshape(len(A), -1)
    return UA


def max_corr(phi, spec, A, B):
    """Largest canonical correlation of the Gaussian field on the site sets A and B."""
    UA, UB = modes_at(phi, A), modes_at(phi, B)
    CA = (UA / spec) @ UA.T
    CB = (UB / spec) @ UB.T
    CAB = (UA / spec) @ UB.T
    LA = np.linalg.cholesky(CA)
    LB = np.linalg.cholesky(CB)
    Mx = np.linalg.solve(LA, CAB)
    Mx = np.linalg.solve(LB, Mx.T).T
    return np.linalg.norm(Mx, 2)


def spectrum(lam, dim, m2, kind):
    """Inverse covariance in the product eigenbasis: precision (Euclidean) or 1/C0 (slice state)."""
    grid = lam
    for _ in range(dim - 1):
        grid = (grid[:, None] + lam[None, :]).reshape(-1)
    q = grid + m2
    if kind == "euclid":
        return q
    eps = np.arccosh(1.0 + q / 2.0)
    return 2.0 * np.sinh(eps)  # equal-time covariance of the 4D lattice transfer: 1/(2 sinh eps)


def surfaces(dim, L, ell, tmax):
    """The core, the separating surfaces S_1 .. S_tmax, and the ring of cells touching the core."""
    c = (L - 1) // 2
    pts = np.array(list(itertools.product(range(L), repeat=dim)))
    r = np.abs(pts - c).max(axis=1)
    core = pts[r <= max(ell // 2 - 1, 0)]
    surf = {t: pts[r == t * ell] for t in range(1, tmax + 1)}
    ring = pts[(r >= ell // 2) & (r <= ell // 2 + ell - 1)]
    return core, surf, ring


def shell_row(dim, ell, tmax, buf, m_phys, kind):
    """theta_t, rho(core, S_d) and the touching coefficient, mass m_phys in units of 1/ell."""
    L = (2 * tmax + 2 * buf) * ell + 1
    phi, lam = dirichlet_modes(L)
    spec = spectrum(lam, dim, (m_phys / ell) ** 2, kind)
    core, surf, ring = surfaces(dim, L, ell, tmax)
    theta = [max_corr(phi, spec, core, surf[1])]
    theta += [max_corr(phi, spec, surf[t], surf[t + 1]) for t in range(1, tmax)]
    direct = [max_corr(phi, spec, core, surf[d]) for d in range(1, tmax + 1)]
    return theta, direct, max_corr(phi, spec, core, ring)


def markov_holds(theta, direct):
    prod = np.cumprod(theta)
    return all(direct[d] <= prod[d] + 1e-9 for d in range(len(theta)))


def fmt(xs):
    return " ".join(f"{x:.3f}" for x in xs)


print("2. link (1): L2 coefficients between separating surfaces ell apart (Dirichlet, Markov field)")
# CHOSEN: 2D, surfaces to t = 4 with 3 cells of buffer to the Dirichlet wall; ell = 2, 4, 8 sites at
# the same physical geometry; mass 1 per cell length (massive) and 0 (massless).
ref = {}
for name, m in (("massless", 0.0), ("massive", 1.0)):
    for ell in (2, 4, 8):
        theta, direct, touch = shell_row(2, ell, 4, 3, m, "euclid")
        assert markov_holds(theta, direct), (name, ell)
        ref[(name, ell)] = (theta, touch)
        print(f"   refine 2D {name:8s} ell={ell}: theta = {fmt(theta)} | rho(core,S_d) = {fmt(direct)}"
              f" | across a shared face {touch:.3f}")
for name in ("massless", "massive"):
    th = [ref[(name, ell)][0][1:] for ell in (2, 4, 8)]
    # CHOSEN: 0.02 bounds the spread of theta_t (t >= 1) over ell = 2, 4, 8 against the touching
    # coefficient's rise of more than 0.15 over the same refinement.
    assert max(abs(a - b) for x in th for y in th for a, b in zip(x, y)) < 0.02, name
    tch = [ref[(name, ell)][1] for ell in (2, 4, 8)]
    assert tch[0] < tch[1] < tch[2], name
# CHOSEN: 2D, ell = 2, surfaces to t = 12 with 12 cells of buffer (97^2 sites); a 10-cell buffer
# lets the Dirichlet wall turn theta_t down from t = 8.
far = {}
for name, m in (("massless", 0.0), ("massive", 1.0)):
    theta, direct, _ = shell_row(2, 2, 12, 12, m, "euclid")
    assert markov_holds(theta, direct), name
    far[name] = (theta, direct)
    print(f"   radius 2D {name:8s}: theta = {fmt(theta)}")
    print(f"             rho(core,S_d) = " + " ".join(f"{x:.1e}" for x in direct))
tl, dl = far["massless"]
tm, dm = far["massive"]
# CHOSEN: 0.95 is the level the docstring reports massless theta_t reaching (read 0.954 at t = 9);
# range(0, 8) stops before the Dirichlet wall bends theta_t down. Just inside the read.
assert all(tl[t + 1] > tl[t] for t in range(0, 8)) and tl[8] > 0.95, "massless theta_t rises"
# CHOSEN: a ceiling just above the massive maximum (read 0.402, settling at 0.378); any value
# well below the massless 0.95 separates the two fields the same way.
assert max(tm) < 0.41, "massive theta_t uniformly below 1"
slope = math.log(dl[1] / dl[11]) / math.log(12 / 2)
print(f"   massless rho(core,S_d) ~ d^-{slope:.2f} (d = 2 .. 12); massive per-step ratio "
      f"{(dm[8] / dm[2]) ** (1 / 6):.3f}")
# CHOSEN: 3D, ell = 2, surfaces to t = 2 with 2 cells of buffer (17^3 sites).
for name, m in (("massless", 0.0), ("massive", 1.0)):
    theta, direct, touch = shell_row(3, 2, 2, 2, m, "euclid")
    assert markov_holds(theta, direct), name
    print(f"   3D {name:8s} ell=2: theta = {fmt(theta)} | rho(core,S_d) = {fmt(direct)}")

print("3. the equal-time slice state of the 4D field (not a nearest-neighbour Markov field)")
slice_held = {}
for name, m in (("massless", 0.0), ("massive", 1.0)):
    theta, direct, _ = shell_row(3, 2, 2, 2, m, "slice")
    slice_held[name] = markov_holds(theta, direct)
    print(f"   3D slice {name:8s}: theta = {fmt(theta)} | rho(core,S_d) = {fmt(direct)}"
          f" | Markov bound {'holds' if slice_held[name] else 'fails'}")
assert not slice_held["massless"]

# ---------------------------------------------------------------------------------------------
# 4. Finite alphabet through a face
# ---------------------------------------------------------------------------------------------
print("4. link (1), finite alphabet: a face of M links, BSC(p) per link")
# CHOSEN: the per-link flip probability; any p other than 0, 1/2 and 1 shows the same three trends
# (floor -> 0, TV -> 1, maximal correlation fixed at |1 - 2p|).
p = 0.2
# DERIVED: a TV coefficient is >= 0, so 0 is the start of the monotone check, not a cut.
prev = 0.0
for M in (1, 4, 16, 64, 256):
    floor = (2 * min(p, 1 - p)) ** M
    k = np.arange(M + 1)
    lb = np.array([math.lgamma(M + 1) - math.lgamma(i + 1) - math.lgamma(M - i + 1) for i in k])
    pa = np.exp(lb + k * math.log(p) + (M - k) * math.log(1 - p))
    pb = np.exp(lb + k * math.log(1 - p) + (M - k) * math.log(p))
    tv = 0.5 * np.abs(pa - pb).sum()
    mc = abs(1 - 2 * p)
    # DERIVED: the Doeblin floor is a probability mass, at most 1. CHOSEN: 1e-12 is round-off slack on
    # the monotone TV check; the TV steps here are at least 1e-5.
    assert tv >= prev - 1e-12 and floor <= 1
    prev = tv
    print(f"   M = {M:3d}: Doeblin floor {floor:.2e}, TV coefficient {tv:.4f}, maximal correlation {mc:.2f}")
# CHOSEN: closeness to the limit TV -> 1 at M = 256 (read 1.0000); the cut is far above the fixed
# maximal correlation 0.6, which is the contrast the section draws.
assert prev > 0.999

# ---------------------------------------------------------------------------------------------
# 5. Path sums
# ---------------------------------------------------------------------------------------------
print("5. link (2): path sums")
for z, w in ((26.0, 0.02), (26.0, 0.035)):
    q = z * w
    for d in (1, 3, 6):
        s = sum((z * w) ** n for n in range(d, 4000))
        assert abs(s - q ** d / (1 - q)) < 1e-9 * max(1.0, s)
    print(f"   z = {z}, w = {w}: zw = {q:.2f}, sum_(n>=3) = {q ** 3 / (1 - q):.4e}")
z, w = 26.0, 1 / 26.0
part = [sum((z * w) ** n for n in range(N)) for N in (10, 100, 1000)]
# DERIVED: at zw = 1 the partial sum to N = 1000 is N itself (read 1000). CHOSEN: 900 leaves room for
# zw rounding off 1 in float64; a convergent sum with zw < 1 by 1e-3 would stay below 632.
assert part[2] > 900
print(f"   zw = 1: partial sums {part[0]:.0f}, {part[1]:.0f}, {part[2]:.0f} (diverge)")
sigma, ell, z = 1.3, 0.7, 26.0
lhs = z * math.exp(-sigma * ell)
rhs = math.exp(-((sigma - math.log(z) / ell) * ell))
# CHOSEN: round-off tolerance for an exact identity in float64 at values near 10; any value well
# above 1e-14 reads the same.
assert abs(lhs - rhs) < 1e-12
print(f"   z e^(-sigma ell) = {lhs:.6f} = edgeRate(sigma, log z / ell, ell) = {rhs:.6f}")

# ---------------------------------------------------------------------------------------------
# 6. Character coefficients
# ---------------------------------------------------------------------------------------------
print("6. per-plaquette character coefficient t(beta) at the lattice scale")


def t_zn(N, beta):
    """Z_N with weight exp(beta cos(2 pi k / N)): ratio of the charge-1 to the charge-0 coefficient."""
    ang = 2 * np.pi * np.arange(N) / N
    wts = np.exp(beta * (np.cos(ang) - 1.0))
    return float((wts * np.cos(ang)).sum() / wts.sum())


print("   beta      U(1)    Z_2     Z_3     SU(2)")
last = None
for beta in (0.5, 2.0, 8.0, 32.0, 128.0):
    tu1 = iv(1, beta) / iv(0, beta)
    tz2 = math.tanh(beta)
    tz3 = t_zn(3, beta)
    tsu2 = iv(2, beta) / iv(1, beta)
    print(f"   {beta:6.1f}  {tu1:.4f}  {tz2:.4f}  {tz3:.4f}  {tsu2:.4f}")
    last = (tu1, tz2, tz3, tsu2)
# CHOSEN: closeness to the limit t(beta) -> 1 at beta = 128; the slowest, SU(2), reads 0.9883, so the
# cut sits just inside it and a larger cut needs a larger beta.
assert min(last) > 0.98

# ---------------------------------------------------------------------------------------------
# 7. 2D gauge exactness
# ---------------------------------------------------------------------------------------------
print("7. 2D: conditional expectations of holonomy functions on proper sets of links")


def check_ring(elems, mul, n, f, weight):
    """Max |E[f(hol) | first j links]| over j < n and conditions, under Haar x weight(hol)."""
    G = len(elems)
    configs = list(itertools.product(range(G), repeat=n))
    hol = []
    for c in configs:
        h = c[0]
        for x in c[1:]:
            h = mul[h][x]
        hol.append(h)
    hol = np.array(hol)
    wt = np.array([weight[h] for h in hol])
    fv = np.array([f[h] for h in hol])
    mean = (wt * fv).sum() / wt.sum()
    g = fv - mean
    worst = 0.0
    arr = np.array(configs)
    for j in range(1, n):
        keys = [tuple(r) for r in arr[:, :j]]
        num, den = {}, {}
        for kk, a, b in zip(keys, wt * g, wt):
            num[kk] = num.get(kk, 0.0) + a
            den[kk] = den.get(kk, 0.0) + b
        worst = max(worst, max(abs(num[kk] / den[kk]) for kk in num))
    return worst, float(np.sqrt((wt * g * g).sum() / wt.sum()))


# Z_3
mul3 = [[(a + b) % 3 for b in range(3)] for a in range(3)]
f3 = [math.cos(2 * math.pi * a / 3) for a in range(3)]
w3 = [math.exp(0.7 * math.cos(2 * math.pi * a / 3)) for a in range(3)]
worst, norm = check_ring(range(3), mul3, 4, f3, w3)
# CHOSEN: 1e-12 is round-off on an exact zero (read 0.0); norm > 0.1 keeps g non-trivial so the zero
# is not vacuous (read 0.738). Any value well below the norm reads the same.
assert worst < 1e-12 and norm > 0.1
print(f"   Z_3, 4 links: max |E[g | proper]| = {worst:.1e}, ||g|| = {norm:.3f}")


# binary tetrahedral group: unit quaternions +-1, +-i, +-j, +-k, (+-1 +-i +-j +-k)/2
def qmul(a, b):
    a0, a1, a2, a3 = a
    b0, b1, b2, b3 = b
    return (a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3, a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2,
            a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1, a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0)


els = []
for i in range(4):
    for s in (1, -1):
        v = [0.0] * 4
        v[i] = float(s)
        els.append(tuple(v))
for signs in itertools.product((0.5, -0.5), repeat=4):
    els.append(signs)
# DERIVED: the binary tetrahedral group has 8 + 16 = 24 elements.
assert len(els) == 24


def idx(q):
    for t, e in enumerate(els):
        # CHOSEN: match tolerance on quaternion entries; distinct elements differ by at least 0.5 in
        # some entry and products carry round-off near 1e-16, so any value between reads the same.
        if max(abs(x - y) for x, y in zip(e, q)) < 1e-9:
            return t
    raise ValueError(q)


mulT = [[idx(qmul(a, b)) for b in els] for a in els]
chi = [2 * e[0] for e in els]  # trace in the fundamental, a class function
wT = [math.exp(0.9 * c) for c in chi]  # a positive class-function density
worst, norm = check_ring(els, mulT, 3, chi, wT)
# CHOSEN: as for Z_3, round-off on an exact zero (read 1.9e-16) and a non-triviality floor (read 0.846).
assert worst < 1e-12 and norm > 0.1
print(f"   binary tetrahedral (in SU(2)), 3 links: max |E[g | proper]| = {worst:.1e}, ||g|| = {norm:.3f}")

elapsed = time.time() - T_START
print(f"total {elapsed:.1f} s")
# CHOSEN: the 10-second run-time budget the docstring states; it decides speed, not a result.
assert elapsed < 10.0
