"""Weighted finite-size threshold (Gosset-Mozgunov / Lemm-Xiang scheme) for projector sums on Z^4,
for two interaction geometries:
  scalar : terms on sites, non-commuting pairs = nearest neighbours (the heat bath of a nearest-neighbour field)
  gauge  : terms on links (x, mu), non-commuting pairs = links sharing a plaquette (18 per link; the Wilson heat bath)
Derivation (same algebra as Lemm-Xiang Prop. 3.1 and Lemma 3.2, written for any term geometry):
  W_t = sum_i c(r_i - t) h_i, c = product profile F on each coordinate (doubled grid, links have one half-integer
  coordinate). Sum_t W_t^2 = P0 H + sum_{i != j} P(r_j - r_i) h_i h_j.  With K = max over distinct pairs of P:
    K H^2 - Sum_t W_t^2 >= (K - P0 - E) H,  E = max_i sum_{j NC i} (K - P_ij)   (commuting pairs: {h_i,h_j} >= 0;
    non-commuting: -{h_i,h_j} <= h_i + h_j).
  Translation-eigenvector at the bottom of spec H|ker-perp, Jensen, equal energy per term of a direction:
    Sum_t <W_t^2> >= omega * gamma_box * a1 <H>,  omega = min_type (sum of weights)/(number of terms) in the box.
  => gamma_per >= (omega a1 / K) (gamma_box - t),  t = (P0 + E - K)/(omega a1).
gamma_box is the UNWEIGHTED gap of the sum of the terms in the box [0, l]^4 (the tree's box operator).
"""
import itertools
import sys
import numpy as np

# DERIVED: 4, the spacetime dimension
D = 4


# CHOSEN: p = 1.0, the default sine power; the main loop scans p
def profile(l, kind, p=1.0):
    u = np.arange(0, 2 * l + 1)  # doubled coordinates 0 .. 2l
    if kind == "sin":
        return np.sin(np.pi * (u + 1) / (2 * l + 2)) ** p
    if kind == "flat":
        return np.ones_like(u, dtype=float)
    raise ValueError(kind)


def corr1(F, par, delta):
    """sum over u = par mod 2 of F(u) F(u + delta), F zero outside [0, 2l]"""
    s = 0.0
    for u in range(par, len(F), 2):
        v = u + delta
        # DERIVED: F is zero outside [0, 2l]
        if 0 <= v < len(F):
            s += F[u] * F[v]
    return s


def geometry(kind):
    """term types (parity vector), and for each type the list of (other type, doubled displacement, noncommuting)"""
    if kind == "scalar":
        types = [(0, 0, 0, 0)]
        nc = {(0, 0, 0, 0): [(0, tuple(2 * s * (np.arange(D) == mu))) for mu in range(D) for s in (1, -1)]}
        nc = {0: [(0, tuple(int(x) for x in d)) for _, d in nc[(0, 0, 0, 0)]]}
        return types, nc
    types = [tuple(int(m == mu) for m in range(D)) for mu in range(D)]
    nc = {}
    for mu in range(D):
        lst = []
        e = lambda a: np.array([2 * (m == a) for m in range(D)])
        for rho in range(D):
            if rho == mu:
                continue
            for s in (1, -1):  # parallel link, opposite side of a plaquette
                lst.append((mu, tuple(int(x) for x in s * e(rho))))
            # perpendicular links of the plaquettes (mu, rho) through link (x, mu): midpoint x + e_mu/2
            # links (x, rho), (x + e_mu, rho), (x - e_rho, rho), (x + e_mu - e_rho, rho); midpoints - x - e_mu/2:
            for a in (0, 1):
                for b in (0, -1):
                    d = (2 * a - 1) * e(mu) // 2 + (2 * b + 1) * e(rho) // 2
                    lst.append((rho, tuple(int(x) for x in d)))
        nc[mu] = lst
    return types, nc


# CHOSEN: p = 1.0, the default sine power, as in profile
def threshold(l, geom, kind="sin", p=1.0):
    F = profile(l, kind, p)
    types, nc = geometry(geom)
    T = len(types)

    def P(ta, tb, d):
        par_a = types[ta]
        out = 1.0
        for m in range(D):
            if (d[m] + par_a[m] - types[tb][m]) % 2:
                return None
            out *= corr1(F, par_a[m], d[m])
        return out

    P0 = max(P(a, a, (0,) * D) for a in range(T))
    # K: max over distinct pairs; P decreases with |d| per coordinate, so search displacements up to 4 (doubled)
    K = 0.0
    for a in range(T):
        for b in range(T):
            for d in itertools.product(range(-4, 5), repeat=D):
                if a == b and not any(d):
                    continue
                v = P(a, b, d)
                if v is not None:
                    K = max(K, v)
    E = max(sum(K - P(a, b, d) for b, d in nc[a]) for a in range(T))
    a1 = np.prod([sum(F[types[0][m]::2]) for m in range(D)])
    omega = min(np.prod([sum(F[ty[m]::2]) / len(F[ty[m]::2]) for m in range(D)]) for ty in types)
    t = (P0 + E - K) / (omega * a1)
    return t, omega * a1 / K


if __name__ == "__main__":
    # DERIVED: 1, argv[0] is the script, so one extra argument names the geometry
    geom = sys.argv[1] if len(sys.argv) > 1 else "scalar"
    for l in [4, 6, 8, 10, 12, 16, 20, 24, 32, 40]:
        best = min((threshold(l, geom, "sin", p)[0], p) for p in (0.5, 0.75, 1.0, 1.25, 1.5, 2.0))
        tf = threshold(l, geom, "flat")[0]
        print(f"{geom} l={l:3d}  t_l(best sin^p, p={best[1]})={best[0]:.5f}  l^2 t={l*l*best[0]:7.2f}   flat (Knabe) t={tf:.4f} l*t={l*tf:.2f}", flush=True)
