"""Numerical checks for `MassGap/GaugeE6.lean`: the cubic norm `e6Cubic` on the complexified
exceptional Jordan algebra, in the coordinates of the Lean module, has stabiliser algebra of
dimension 78 inside u(27); the algebra is closed under the bracket, consists of traceless matrices,
and the trace ratio tr_27(X^2) / tr_adj(X^2) on it is 1/4 = T(27)/h^v = 3/12.

Coordinates, as in the Lean module. An element X = [[a, z, conj y], [conj z, b, x], [y, conj x, c]]
of J3(O) (x) C is v in C^27: v[0] = a, v[1] = b, v[2] = c, and v[3:11], v[11:19], v[19:27] are
sqrt2 x, sqrt2 y, sqrt2 z (octonions, index 0 the real part), so that v is orthonormal for the trace
form tr(X^2) = a^2 + b^2 + c^2 + 2 (n(x) + n(y) + n(z)). The octonion product is that of
`GaugeF4.octMul` (cross product read off the G2 3-form of `GaugeG2.phi3`). In these coordinates
twice the cubic norm N = abc - a n(x) - b n(y) - c n(z) + 2 Re((x y) z) is

    e6Cubic(v) = 2 a b c - a n(v_x) - b n(v_y) - c n(v_z) + s Re((v_x v_y) v_z),   s = sqrt 2,

n and Re extended complex-bilinearly / trilinearly, no conjugation; it is the diagonal of the
trilinear form `e6Tri s`. The scaling matters: in J's raw coordinates the standard Hermitian form is
not the (F4-invariant) trace form, and the stabiliser of N in that U(27) is only 30-dimensional
(checked below), so the unitary group is taken in orthonormal coordinates.

Also checked: the F4 cubic of `GaugeF4.f4Cubic` is 6 sqrt6 N on the traceless part in the
coordinates of that module (so F4 sits in E6 as the stabiliser of the identity), the two Lean
witnesses (`cartanE6`, `diagE6`) satisfy the derivation condition, and cube roots of unity preserve
N with det = omega^27 = 1.

Runs in a few seconds. Usage: python e6_checks.py
"""
from __future__ import annotations

import numpy as np

# DERIVED: the seven oriented triples and signs of the G2 3-form `GaugeG2.phi3`, which defines the
# octonion product of `GaugeF4.octMul`; a definition of the object, not a tuned value.
PHI_TRIPLES = [((1, 2, 3), 1), ((1, 4, 5), 1), ((1, 6, 7), 1), ((2, 4, 6), 1),
               ((2, 5, 7), -1), ((3, 4, 7), -1), ((3, 5, 6), -1)]


def phi_tensor():
    t = np.zeros((7, 7, 7))
    for (a, b, c), s in PHI_TRIPLES:
        a, b, c = a - 1, b - 1, c - 1
        for (i, j, k), sg in [((a, b, c), 1), ((b, c, a), 1), ((c, a, b), 1),
                              ((b, a, c), -1), ((a, c, b), -1), ((c, b, a), -1)]:
            t[i, j, k] = s * sg
    return t


PHI = phi_tensor()


def omul(x, y):
    r = np.empty(8, dtype=np.result_type(x, y))
    r[0] = x[0] * y[0] - x[1:] @ y[1:]
    r[1:] = x[0] * y[1:] + y[0] * x[1:] + np.einsum("ijk,i,j->k", PHI, x[1:], y[1:])
    return r


S2 = np.sqrt(2.0)


def tri(p, q, r, s=S2):
    """`e6Tri s`: complex trilinear, diagonal 2 N in orthonormal coordinates (s = sqrt 2)."""
    return (2 * p[0] * q[1] * r[2] - p[0] * (q[3:11] @ r[3:11]) - p[1] * (q[11:19] @ r[11:19])
            - p[2] * (q[19:27] @ r[19:27]) + s * omul(omul(p[3:11], q[11:19]), r[19:27])[0])


def norm_raw(a, b, c, x, y, z):
    """The cubic norm in J's raw coordinates: abc - a n(x) - b n(y) - c n(z) + 2 Re((x y) z)."""
    return a * b * c - a * (x @ x) - b * (y @ y) - c * (z @ z) + 2 * omul(omul(x, y), z)[0]


def tri_tensor():
    """The coefficients T[i, j, k] = tri(e_i, e_j, e_k), assembled block by block."""
    E8 = np.eye(8)
    R3 = np.array([[[omul(omul(E8[a], E8[b]), E8[c])[0] for c in range(8)] for b in range(8)]
                   for a in range(8)])
    T = np.zeros((27, 27, 27))
    T[0, 1, 2] = 2
    for d, blk in ((0, slice(3, 11)), (1, slice(11, 19)), (2, slice(19, 27))):
        T[d, blk, blk] -= np.eye(8)
    T[3:11, 11:19, 19:27] += S2 * R3
    E = np.eye(27)
    for i, j, k in rng_triples():
        # CHOSEN: round-off tolerance on entries that are exact small integers times 1 or sqrt 2; any
        # value well above 1e-15 and below 1 reads the same.
        assert abs(T[i, j, k] - tri(E[i], E[j], E[k])) < 1e-12
    return T


def rng_triples():
    r = np.random.default_rng(7)
    return [tuple(r.integers(0, 27, 3)) for _ in range(300)] + [(0, 1, 2), (3, 11, 19), (0, 3, 3)]


T = tri_tensor()


def cubic(v):
    return np.einsum("ijk,i,j,k->", T, v, v, v)


def grad(v):
    return (np.einsum("ijk,j,k->i", T, v, v) + np.einsum("ijk,i,k->j", T, v, v)
            + np.einsum("ijk,i,j->k", T, v, v))


def u_basis():
    """A real basis of u(27), orthonormal for Re tr(A^dagger B)."""
    B = []
    for i in range(27):
        M = np.zeros((27, 27), complex)
        M[i, i] = 1j
        B.append(M)
    for i in range(27):
        for j in range(i + 1, 27):
            M = np.zeros((27, 27), complex)
            M[i, j], M[j, i] = 1 / np.sqrt(2), -1 / np.sqrt(2)
            B.append(M)
            M = np.zeros((27, 27), complex)
            M[i, j], M[j, i] = 1j / np.sqrt(2), 1j / np.sqrt(2)
            B.append(M)
    return np.array(B)


_BASIS = []


def u_basis_cached():
    if not _BASIS:
        _BASIS.append(u_basis())
    return _BASIS[0]


def main():
    rng = np.random.default_rng(0)

    # 1. the cubic is the diagonal of the trilinear form, and agrees with the F4 cubic on J0
    for _ in range(10):
        v = rng.standard_normal(27) + 1j * rng.standard_normal(27)
        # CHOSEN: absolute round-off tolerance for an exact identity on cubics of order-10 Gaussian
        # vectors in float64; any value well above 1e-13 and below the cubic's size reads the same.
        assert abs(cubic(v) - tri(v, v, v)) < 1e-9
    S = np.sqrt(3.0)
    for _ in range(10):
        w26 = rng.standard_normal(26)
        u, w = w26[0], w26[1]
        x, y, z = w26[2:10], w26[10:18], w26[18:26]
        f4 = (6 * u * u * w - 2 * w ** 3 - 3 * (S * u + w) * (x @ x) + 3 * (S * u - w) * (y @ y)
              + 6 * w * (z @ z) + 6 * S * omul(omul(x, y), z)[0])
        v = np.concatenate([[u / np.sqrt(2) + w / np.sqrt(6), -u / np.sqrt(2) + w / np.sqrt(6),
                             -2 * w / np.sqrt(6)], x, y, z])
        # CHOSEN: round-off tolerance for the exact identity f4Cubic = 3 sqrt6 e6Cubic; looser than the
        # line above because f4 carries a factor 3 sqrt6 and more terms. Any value well above 1e-12 reads the same.
        assert abs(f4 - 3 * np.sqrt(6) * cubic(v)) < 1e-8
    for _ in range(10):
        v = rng.standard_normal(27) + 1j * rng.standard_normal(27)
        raw = norm_raw(v[0], v[1], v[2], v[3:11] / S2, v[11:19] / S2, v[19:27] / S2)
        # CHOSEN: round-off tolerance for the exact identity e6Cubic = 2 N; any value well above 1e-13 reads the same.
        assert abs(cubic(v) - 2 * raw) < 1e-9
        # the coordinates are orthonormal for tr(X^2) = a^2 + b^2 + c^2 + 2 (n(x) + n(y) + n(z))
        tr2 = v[0] ** 2 + v[1] ** 2 + v[2] ** 2 + 2 * sum((blk / S2) @ (blk / S2)
                                                         for blk in (v[3:11], v[11:19], v[19:27]))
        # CHOSEN: round-off tolerance for the exact orthonormality identity; any value well above 1e-13 reads the same.
        assert abs(tr2 - v @ v) < 1e-9
    print("e6Cubic = diagonal of e6Tri = 2 N, coordinates orthonormal for tr(X^2); "
          "f4Cubic = 3 sqrt6 e6Cubic = 6 sqrt6 N on the traceless part")

    # 1b. in J's raw coordinates (off-diagonals unscaled) the standard Hermitian form is not the
    # trace form, and the stabiliser of N in that U(27) is smaller than 78
    Draw = np.diag([1.0] * 3 + [S2] * 24)             # raw = Draw^-1 orthonormal
    rows = []
    for _ in range(380):
        v = rng.standard_normal(27) + 1j * rng.standard_normal(27)
        # N_raw(w) = cubic(Draw w) / 2; gradient in w
        g = Draw @ grad(Draw @ v) / 2
        rows.append(np.outer(g, v).ravel())
    rr = np.array(rows) @ u_basis_cached().reshape(729, 729).T
    # NOT A READ: the rank of a linear constraint system on u(27) (a Lie-algebra dimension count); no correlation or field enters, and the library's own note on rank says to take the singular values directly
    sv = np.linalg.svd(np.vstack([rr.real, rr.imag]), compute_uv=False)
    print(f"raw coordinates: stabiliser of N in the standard u(27) has dim "
          f"{729 - int((sv > 1e-8 * sv[0]).sum())} (not 78): the coordinates must be orthonormal")

    # 2. stabiliser algebra in u(27): A anti-Hermitian with grad N(v) . (A v) = 0, v complex
    basis = u_basis_cached()                           # (729, 27, 27)
    rows = []
    for _ in range(380):
        v = rng.standard_normal(27) + 1j * rng.standard_normal(27)
        rows.append(np.outer(grad(v), v).ravel())
    r = np.array(rows) @ basis.reshape(729, 729).T
    A = np.vstack([r.real, r.imag])
    # NOT A READ: the rank and null space of the stabiliser constraint system in u(27), a Lie-algebra computation; no correlation or field enters
    _, sv, Vt = np.linalg.svd(A)
    rank = int((sv > 1e-8 * sv[0]).sum())
    null = len(basis) - rank
    print(f"u(27) has dim {len(basis)}; constraint rank {rank}; stabiliser dim {null}")
    print(f"  singular-value gap at the cut: {sv[rank - 1]:.3e} -> {sv[rank] if rank < len(sv) else 0:.3e}")
    # DERIVED: 78 = dim E6, the stabiliser dimension the Lean module states.
    assert null == 78

    K = Vt[rank:]                                      # 78 x 729, orthonormal coefficients
    gens = np.einsum("kb,bmn->kmn", K, basis)

    # traceless: the stabiliser lies in su(27)
    tr = max(abs(np.trace(g)) for g in gens)
    print(f"max |tr| over the 78 generators {tr:.2e}")
    # CHOSEN: round-off tolerance on an exact zero (read 1.6e-15); any value well above 1e-14 and well
    # below the unit-norm generators reads the same.
    assert tr < 1e-9

    # closed under the bracket
    def coords(M):
        return np.einsum("bmn,mn->b", basis.conj(), M).real
    P = K.T @ K
    worst = 0.0
    for a in range(0, 78, 7):
        for b in range(1, 78, 11):
            C = coords(gens[a] @ gens[b] - gens[b] @ gens[a])
            worst = max(worst, np.linalg.norm(C - P @ C))
    print(f"bracket closure residual {worst:.2e}")
    # CHOSEN: round-off tolerance on an exact zero (read 1.7e-15); any value well above 1e-14 reads the same.
    assert worst < 1e-8

    # 3. trace ratio tr_27(X^2) / tr_adj(X^2)
    def ad(X):
        return np.array([K @ coords(X @ Y - Y @ X) for Y in gens]).T
    for _ in range(3):
        c = rng.standard_normal(78)
        X = np.einsum("k,kmn->mn", c, gens)
        ratio = (np.trace(X @ X) / np.trace(ad(X) @ ad(X))).real
        print(f"tr_27(X^2) / tr_adj(X^2) = {ratio:.12f}  (T(27)/h^v = 3/12 = {0.25:.12f})")
        # DERIVED: 0.25 = T(27)/h^v = 3/12, the ratio the docstring states. CHOSEN: 1e-9 round-off tolerance
        # (read equal to 12 digits).
        assert abs(ratio - 0.25) < 1e-9

    # 4. the Lean witnesses, as Hermitian M: i M must lie in the algebra
    def in_alg(M):
        C = coords(1j * M)
        return np.linalg.norm(C - P @ C), np.linalg.norm(1j * M - np.einsum("b,bmn->mn", C, basis))
    cart = np.zeros((27, 27), complex)
    for off in (0, 8, 16):
        cart[5 + off, 6 + off], cart[6 + off, 5 + off] = -1j, 1j
        cart[7 + off, 8 + off], cart[8 + off, 7 + off] = 1j, -1j
    diag = np.diag([2, -2, 0] + [-1] * 8 + [1] * 8 + [0] * 8).astype(complex)
    for name, M in (("cartanE6", cart), ("diagE6", diag)):
        # CHOSEN: round-off tolerance on the trace of an integer matrix whose trace is exactly 0.
        assert np.allclose(M, M.conj().T) and abs(np.trace(M)) < 1e-12
        res = max(abs(grad(v) @ (M @ v))
                  for v in rng.standard_normal((30, 27)) + 1j * rng.standard_normal((30, 27)))
        off_alg = in_alg(M)[0]
        print(f"{name}: derivation residual {res:.2e}, distance from i^-1 e6 {off_alg:.2e}")
        # CHOSEN: round-off tolerance on two exact zeros (reads 1e-14 to 3e-14); any value well above 1e-13 reads the same.
        assert res < 1e-9 and off_alg < 1e-9
    # diagE6 does not fix the identity of J, so it is outside the F4 part
    one = np.array([1, 1, 1] + [0] * 24, complex)
    # DERIVED: diag @ one = (2, -2, 0, ...), of norm exactly 2 sqrt 2; the cut 1 only separates it from 0.
    assert np.linalg.norm(diag @ one) > 1
    # DERIVED: cartanE6 has no entries on the diagonal coordinates, so cart @ one is exactly 0.
    # CHOSEN: 1e-12 as the round-off tolerance on that zero.
    assert np.linalg.norm(cart @ one) < 1e-12

    # 5. the centre: omega 1 with omega^3 = 1 preserves N, det = omega^27 = 1
    om = np.exp(2j * np.pi / 3)
    v = rng.standard_normal(27) + 1j * rng.standard_normal(27)
    # DERIVED: omega^3 = 1 gives N(omega v) = N(v) and omega^27 = 1 exactly. CHOSEN: 1e-9 and 1e-12 as
    # round-off tolerances on a cubic of order 10 and on a unit-modulus power.
    assert abs(cubic(om * v) - cubic(v)) < 1e-9 and abs(om ** 27 - 1) < 1e-12
    print("centre: omega N-invariant, omega^27 = 1")
    print("all E6 checks passed")


if __name__ == "__main__":
    main()
