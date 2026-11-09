"""UV line B numerics: the local APE-step bound and pixel dispersal.

SU(2) as unit quaternions (a0, a1, a2, a3); APE step U' = normalise(U + c * sum of 6 staples), all links
at once from the old configuration (ApeLattice.apeConf). s(g) = 1 - a0 = 1 - tr(g)/2.

Test 1: s(P') <= kappa * (s(P) + sum_{l in P} sum_i s(staple_i(l) * U_l^-1)), kappa = 1 + 96 eta^2,
        eta = c/(1+6c); also the sqrt form sqrt s(P') <= sqrt s(P) + 2 eta sum sqrt s(...). The worst ratio is read
        over the plaquettes whose right-hand side is above its float64 round-off floor; the rest are counted apart,
        and one of them with s(P') above that floor is reported as a violation (split_bound). The ensembles are
        Haar, near-identity, and a pure-gauge flat field, on which every plaquette is on the round-off branch.
Test 2: one non-central link in a flat field; total action after n steps (dispersal exponent).
"""
import numpy as np, sys

# DERIVED: argv[1] is the optional seed's position; default seed 0
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
# CHOSEN: lattice side 6 for test 1; a cost budget (the bound is local, any side >= 3 holds every staple)
L = 6
# DERIVED: the spacetime dimension of the four-dimensional lattice
D = 4


def qmul(a, b):
    a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
    b0, b1, b2, b3 = b[..., 0], b[..., 1], b[..., 2], b[..., 3]
    return np.stack([a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3,
                     a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2,
                     a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1,
                     a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0], -1)


def qinv(a):
    return a * np.array([1, -1, -1, -1])


# DERIVED: s=1 is the unit forward shift x -> x + mu
def sh(x, mu, s=1):
    return np.roll(x, -s, axis=mu)


def staples(U, mu):
    """list of the 6 staples of links in direction mu, each an array (L,L,L,L,4)."""
    out = []
    for nu in range(D):
        if nu == mu:
            continue
        up = qmul(qmul(U[nu], sh(U[mu], nu)), qinv(sh(U[nu], mu)))
        dn_base = sh(U[nu], nu, -1)  # U_nu(x - nu)
        dn = qmul(qmul(qinv(dn_base), sh(U[mu], nu, -1)), sh(sh(U[nu], nu, -1), mu))
        out += [up, dn]
    return out


def ape(U, c):
    V = np.empty_like(U)
    for mu in range(D):
        M = U[mu] + c * sum(staples(U, mu))
        V[mu] = M / np.linalg.norm(M, axis=-1, keepdims=True)
    return V


def plaq(U, mu, nu):
    return qmul(qmul(qmul(U[mu], sh(U[nu], mu)), qinv(sh(U[mu], nu))), qinv(U[nu]))


def s(g):
    return 1 - g[..., 0]


def haar(shape):
    x = rng.normal(size=shape + (4,))
    return x / np.linalg.norm(x, axis=-1, keepdims=True)


def near_id(shape, eps):
    x = np.zeros(shape + (4,)); x[..., 0] = 1
    x[..., 1:] = eps * rng.normal(size=shape + (3,))
    return x / np.linalg.norm(x, axis=-1, keepdims=True)


EPS = np.finfo(float).eps
# DERIVED: the float64 round-off floor of one s = 1 - a0. a0 is the scalar part of a product of four unit quaternions
# (a plaquette, or a staple times U_l^-1): three products, each component a four-term dot product of unit operands
# accurate to gamma_4 ~ 4 eps (Higham 2002, Sec 3.1), and the subtraction from 1 adds one eps: (4 * 3 + 1) eps. On a
# pure-gauge field, where every s is exactly 0, the largest |s| read is 5 eps.
S_FLOOR = (4 * 3 + 1) * EPS
# DERIVED: the bound's right-hand side s(P) + K sums one s(P) and the 2(D - 1) staple loops of each of P's four links
N_TERMS = 1 + 4 * 2 * (D - 1)


def split_bound(lhs, rhs, floor):
    """The bound lhs <= rhs read without dropping any plaquette. Where rhs is above `floor` (its round-off floor) the
    ratio lhs/rhs is read; where it is not, the right-hand side is zero to the arithmetic's resolution and the bound
    says lhs ~ 0 there, so those plaquettes are counted, and any with lhs above the same floor is a violation.
    Returns (worst ratio over the resolved plaquettes, NaN if none; degenerate count; violation count; the largest
    lhs on the degenerate plaquettes, 0 if none)."""
    deg = rhs <= floor
    ok = ~deg
    worst = float((lhs[ok] / rhs[ok]).max()) if ok.any() else float("nan")
    worst_deg = float(lhs[deg].max()) if deg.any() else 0.0
    return worst, int(deg.sum()), int((lhs[deg] > floor).sum()), worst_deg


def pure_gauge(shape):
    """A flat field in a random gauge, U_mu(x) = g(x) g(x + mu)^-1: every plaquette and staple loop is exactly the
    identity, so every s is 0 up to round-off and every plaquette sits on the degenerate branch of split_bound."""
    g = haar(shape)
    return np.stack([qmul(g, qinv(sh(g, mu))) for mu in range(D)])


def test1(U, c):
    """Per form (kappa, sqrt, const1): the worst ratio over plaquettes whose right-hand side is resolved, and the
    plaquettes whose right-hand side is at its round-off floor, reported separately (split_bound)."""
    eta = c / (1 + 6 * c)
    kap = 1 + 96 * eta ** 2
    # the round-off floors of the three right-hand sides: N_TERMS s's (scaled by kappa); the sqrt form sums the square
    # roots of the same s's, s(P) with weight 1 and the staple loops with weight 2 eta, each at most sqrt(S_FLOOR)
    floors = {"kappa": kap * N_TERMS * S_FLOOR, "const1": N_TERMS * S_FLOOR,
              "sqrt": (1 + 2 * eta * (N_TERMS - 1)) * np.sqrt(S_FLOOR)}
    V = ape(U, c)
    # link curvature K_l = sum_i s(staple_i U_l^-1), sqrt form Ks_l = sum_i sqrt s(...)
    K, Ks = [], []
    for mu in range(D):
        st = staples(U, mu)
        loops = [s(qmul(S, qinv(U[mu]))) for S in st]
        K.append(sum(loops)); Ks.append(sum(np.sqrt(np.maximum(l, 0)) for l in loops))
    res = {k: [float("nan"), 0, 0, 0.0] for k in floors}
    for mu in range(D):
        for nu in range(D):
            if nu == mu:
                continue
            sp, sp2 = s(plaq(U, mu, nu)), s(plaq(V, mu, nu))
            # links of P: (mu,x), (nu,x+mu), (mu,x+nu), (nu,x)
            Ksum = K[mu] + sh(K[nu], mu) + sh(K[mu], nu) + K[nu]
            Kssum = Ks[mu] + sh(Ks[nu], mu) + sh(Ks[mu], nu) + Ks[nu]
            forms = {"kappa": (sp2, kap * (sp + Ksum)),
                     "sqrt": (np.sqrt(np.maximum(sp2, 0)), np.sqrt(np.maximum(sp, 0)) + 2 * eta * Kssum),
                     "const1": (sp2, sp + Ksum)}
            for k, (lhs, rhs) in forms.items():
                w, nd, nv, wd = split_bound(lhs, rhs, floors[k])
                r = res[k]
                res[k] = [float(np.fmax(r[0], w)), r[1] + nd, r[2] + nv, max(r[3], wd)]
    return res


def total_action(U):
    return sum(float(s(plaq(U, mu, nu)).sum()) for mu in range(D) for nu in range(mu + 1, D))


if __name__ == "__main__":
    shape = (L,) * D
    print("test1: max of s(P')/[kappa(s(P)+K)], sqrt form ratio, constant-1 ratio s(P')/(s(P)+K), each over the "
          "plaquettes whose right-hand side is above its round-off floor; deg = plaquettes at the floor (not in the "
          "ratio), viol = of those, s(P') (sqrt form: sqrt s(P')) above the floor")
    # the pure-gauge rows run after the others, so the draws of the Haar and near-identity rows are those of the seed
    ens = (("haar", lambda: haar((D,) + shape)),
           ("eps0.1", lambda: near_id((D,) + shape, 0.1)),
           ("eps0.5", lambda: near_id((D,) + shape, 0.5)))
    cs = (0.05, 0.10, 0.15, 0.1666)
    rows = [(c, e) for c in cs for e in ens] + [(c, ("gauge", lambda: pure_gauge(shape))) for c in cs]
    for c, (name, mk) in rows:
        r = [test1(mk(), c) for _ in range(2)]
        cells = []
        for k in ("kappa", "sqrt", "const1"):
            w = float(np.fmax.reduce([x[k][0] for x in r]))
            nd, nv = sum(x[k][1] for x in r), sum(x[k][2] for x in r)
            wd = max(x[k][3] for x in r)
            cells.append(f"{k}-ratio {w:.4f} deg {nd} viol {nv} (max lhs at deg {wd:.1e})")
        print(f"c={c:.4f} {name:7s} " + "  ".join(cells))
    print("test2: one link g in a flat field, c = 0.15; total action after n steps")
    L2 = 12
    shape2 = (L2,) * D
    for theta in (0.5, 1.5, 3.0, 3.1):
        U = np.zeros((D,) + shape2 + (4,)); U[..., 0] = 1
        U[0, 0, 0, 0, 0] = [np.cos(theta), np.sin(theta), 0, 0]
        row = []
        for n in range(0, 65):
            if n in (0, 1, 2, 4, 8, 16, 32, 64):
                row.append((n, total_action(U)))
            U = ape(U, 0.15)
        print(f"theta={theta}: " + "  ".join(f"n={n}:{a:.3e}" for n, a in row))
