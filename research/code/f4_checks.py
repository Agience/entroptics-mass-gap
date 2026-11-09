"""Numerical checks for `MassGap/GaugeF4.lean`: the cubic form `f4Cubic` on the traceless part of
the exceptional Jordan algebra, in the coordinates of the Lean module, has stabiliser algebra of
dimension 52 inside so(26), and the trace ratio tr_26(X^2) / tr_adj(X^2) is 1/3 on it.

Coordinates, as in the Lean module. Index 0 of an octonion is the real part, 1..7 the imaginary
part; the product is x y = (x0 y0 - <x', y'>, x0 y' + y0 x' + x' x y') with the cross product
read off the G2 3-form phi of `GaugeG2.phi3`, <x' x y', z'> = phi(x', y', z'). A traceless
element of J3(O) is v in R^26: v[0] = u, v[1] = w (orthonormal coordinates of the traceless
diagonal), v[2:10] = x, v[10:18] = y, v[18:26] = z (orthonormal off-diagonal octonions). The
cubic is

    d(v) = 6 u^2 w - 2 w^3 - 3 (s u + w) n(x) + 3 (s u - w) n(y) + 6 w n(z) + 6 s Re((x y) z),

s = sqrt 3, which is 6 sqrt 6 det of the Hermitian matrix [[a, z, conj y], [conj z, b, x],
[y, conj x, c]] with a = u/sqrt2 + w/sqrt6, b = -u/sqrt2 + w/sqrt6, c = -2 w/sqrt6 and the
off-diagonal entries scaled by 1/sqrt2 (checked below against the determinant formula
abc - a n(x) - b n(y) - c n(z) + 2 Re(x y z)).

Runs in well under a second. Usage: python f4_checks.py
"""
from __future__ import annotations

import numpy as np

# Bryant's phi, 1-based triples and signs (GaugeG2.phi3), shared with e6_checks and e7_checks.
from e6_checks import PHI_TRIPLES, phi_tensor  # noqa: F401

PHI = phi_tensor()


def cross(x, y):
    return np.einsum("ijk,i,j->k", PHI, x, y)


def omul(x, y):
    r = np.empty(8)
    r[0] = x[0] * y[0] - x[1:] @ y[1:]
    r[1:] = x[0] * y[1:] + y[0] * x[1:] + cross(x[1:], y[1:])
    return r


def oconj(x):
    return np.concatenate([[x[0]], -x[1:]])


S = np.sqrt(3.0)


def cubic(v):
    u, w = v[0], v[1]
    x, y, z = v[2:10], v[10:18], v[18:26]
    return (6 * u * u * w - 2 * w ** 3 - 3 * (S * u + w) * (x @ x) + 3 * (S * u - w) * (y @ y)
            + 6 * w * (z @ z) + 6 * S * omul(omul(x, y), z)[0])


# CHOSEN: step 1e-6; truncation (h^2 times the third derivative) is ~1e-12 and the rounding term
# eps/h ~ 1e-10 relative dominates, which sets the ~1e-7 witness residual read below.
def grad(v, h=1e-6):
    # exact for a cubic up to rounding: central differences have error h^2 * (third derivative)
    g = np.empty(26)
    for i in range(26):
        e = np.zeros(26)
        e[i] = h
        g[i] = (cubic(v + e) - cubic(v - e)) / (2 * h)
    return g


def main():
    rng = np.random.default_rng(0)

    # 1. the octonion product is normed and alternative
    for _ in range(20):
        x, y = rng.standard_normal(8), rng.standard_normal(8)
        # CHOSEN: rounding tolerance on the exact identity n(xy) = n(x) n(y) at O(1) Gaussian inputs.
        assert abs(omul(x, y) @ omul(x, y) - (x @ x) * (y @ y)) < 1e-9
        assert np.allclose(omul(omul(x, x), y), omul(x, omul(x, y)))
    print("octonions: normed and left alternative on 20 random pairs")

    # 2. the cubic is 6 sqrt6 det of the traceless Hermitian matrix
    for _ in range(20):
        v = rng.standard_normal(26)
        u, w = v[0], v[1]
        a, b, c = u / np.sqrt(2) + w / np.sqrt(6), -u / np.sqrt(2) + w / np.sqrt(6), -2 * w / np.sqrt(6)
        x, y, z = v[2:10] / np.sqrt(2), v[10:18] / np.sqrt(2), v[18:26] / np.sqrt(2)
        det = a * b * c - a * (x @ x) - b * (y @ y) - c * (z @ z) + 2 * omul(omul(x, y), z)[0]
        # the trace form tr(X^2) = a^2+b^2+c^2+2(n(x)+n(y)+n(z)) is the Euclidean norm of v
        tr2 = a * a + b * b + c * c + 2 * (x @ x + y @ y + z @ z)
        # CHOSEN: rounding tolerance on the exact identity tr(X^2) = |v|^2; the residual is not printed.
        assert abs(tr2 - v @ v) < 1e-9
        # CHOSEN: rounding tolerance on the exact identity d = 6 sqrt6 det; the residual is not printed.
        assert abs(cubic(v) - 6 * np.sqrt(6) * det) < 1e-8
    print("cubic = 6 sqrt6 det on 20 random traceless elements; coordinates orthonormal")

    # 3. stabiliser algebra in so(26): B antisymmetric with grad d(v) . (B v) = 0 for all v
    basis = []
    for i in range(26):
        for j in range(i + 1, 26):
            B = np.zeros((26, 26))
            B[i, j], B[j, i] = 1.0, -1.0
            basis.append(B)
    rows = []
    for _ in range(700):
        v = rng.standard_normal(26)
        g = grad(v)
        rows.append([g @ (B @ v) for B in basis])
    A = np.array(rows)
    # NOT A READ: the rank of the so(26) stabiliser constraint system, a Lie-algebra dimension count; no correlation or field enters
    sv = np.linalg.svd(A, compute_uv=False)
    tol = 1e-6 * sv[0]
    rank = int((sv > tol).sum())
    null = len(basis) - rank
    print(f"so(26) has dim {len(basis)}; constraint rank {rank}; stabiliser dim {null}")
    print(f"  singular-value gap at the cut: {sv[rank - 1]:.3e} -> {sv[rank]:.3e}")
    # DERIVED: dim F4 = 52, the dimension the Lean module states for the stabiliser.
    assert null == 52

    # NOT A READ: the null space of the same constraint system, the basis of the stabiliser algebra; no correlation or field enters
    _, _, Vt = np.linalg.svd(A)
    K = Vt[rank:]                       # 52 x 325, orthonormal coefficients
    gens = [sum(c * B for c, B in zip(k, basis)) for k in K]

    # closed under the bracket (it is a Lie algebra)
    P = K.T @ K
    def coords(M):
        return np.array([M[i, j] for i in range(26) for j in range(i + 1, 26)])
    worst = 0.0
    for a in range(0, 52, 5):
        for b in range(1, 52, 7):
            C = coords(gens[a] @ gens[b] - gens[b] @ gens[a])
            worst = max(worst, np.linalg.norm(C - P @ C))
    print(f"bracket closure residual {worst:.2e}")
    # CHOSEN: closure tolerance on sampled brackets; the read is about 2e-10, under two decades below.
    assert worst < 1e-8

    # 4. trace ratio tr_26(X^2) / tr_adj(X^2) for random X in the algebra
    Kpinv = np.linalg.pinv(K.T)         # maps so(26) coords to the 52 coefficients
    def ad(X):
        cols = [Kpinv @ coords(X @ Y - Y @ X) for Y in gens]
        return np.array(cols).T
    for _ in range(3):
        c = rng.standard_normal(52)
        X = sum(ci * G for ci, G in zip(c, gens))
        ratio = np.trace(X @ X) / np.trace(ad(X) @ ad(X))
        print(f"tr_26(X^2) / tr_adj(X^2) = {ratio:.12f}  (T(26)/h^v = 3/9 = {1/3:.12f})")
        # CHOSEN: tolerance on the derived ratio 1/3 = T(26)/h^v; the read agrees to all 12 printed digits.
        assert abs(ratio - 1 / 3) < 1e-9

    # 5. the Lean witness: cartanB of GaugeG2 on the imaginary parts of x, y and z
    cb = np.zeros((7, 7))
    cb[1, 2], cb[2, 1], cb[3, 4], cb[4, 3] = -1, 1, 1, -1
    Bw = np.zeros((26, 26))
    for off in (3, 11, 19):
        Bw[off:off + 7, off:off + 7] = cb
    res = max(abs(grad(v) @ (Bw @ v)) for v in rng.standard_normal((50, 26)))
    print(f"witness derivation residual {res:.2e}")
    # CHOSEN: tolerance set by the finite-difference rounding of `grad`; the read is about 9e-8,
    # about one decade under the cut.
    assert res < 1e-6
    print("all F4 checks passed")


if __name__ == "__main__":
    main()
