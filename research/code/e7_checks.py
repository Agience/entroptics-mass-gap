"""Numerical checks for `MassGap/GaugeE7.lean`: Freudenthal's quartic form `e7Quartic` on the
56-dimensional Freudenthal triple system, in the coordinates of the Lean module, has stabiliser
algebra of real dimension 133 inside sp(56, C) cap u(56) (sp for the form of
`GaugeInstances.Jsp 28`), and the trace ratio tr_56(X^2) / tr_adj(X^2) on it is 1/3.

Coordinates, as in the Lean module. Octonions as in `GaugeF4` (index 0 real part, product
x y = (x0 y0 - <x', y'>, x0 y' + y0 x' + x' x y'), cross product from Bryant's phi). An element of
J = J3(O) (x C) is A in C^27: A[0] = a, A[1] = b, A[2] = c (diagonal), A[3:11] = p, A[11:19] = q,
A[19:27] = s, the off-diagonal octonions x, y, z of `GaugeF4`'s determinant
abc - a n(x) - b n(y) - c n(z) + 2 Re((x y) z) scaled by r = sqrt 2 (p = r x, q = r y, s = r z),
so that the trace form T(A, B) = tr(A o B) is the plain dot product sum_k A[k] B[k]. A point of
the triple system is v in C^56: v[0] = alpha, v[1:28] = A, v[28] = beta, v[29:56] = B.

    4 N(A)       = 4abc - 2a n(p) - 2b n(q) - 2c n(s) + 2r Re((p q) s)
    2 A#         = (2bc - n(p), 2ca - n(q), 2ab - n(s),
                    r conj(q s) - 2a p, r conj(s p) - 2b q, r conj(p q) - 2c s)
    q(v)         = (alpha beta - T(A, B))^2 - alpha 4N(A) - beta 4N(B) - T(2A#, 2B#)

i.e. q = (alpha beta - T(A,B))^2 - 4 alpha N(A) - 4 beta N(B) - 4 T(A#, B#). The sign of the last
term relative to the square is not a convention (no unitary symplectic rescaling of the blocks
changes it): with + 4 T(A#, B#) the stabiliser in sp(56) drops to dimension 79 = dim(E6 x U(1)),
which `--variants` shows. The sign of the N terms is a convention (A, B -> -A, -B). Up to these
conventions this is Freudenthal's quartic in the normalisation
4 [T(A#,B#) - alpha N(A) - beta N(B)] - (alpha beta - T(A,B))^2, which is -q at (alpha, beta, -A, -B).

The bilinear form of `Jsp 28`, v^T J w = sum_{i<28} (v[28+i] w[i] - v[i] w[28+i]), is
beta alpha' - alpha beta' + T(B, A') - T(A, B'): the symplectic form
alpha beta' - beta alpha' + T(A, B') - T(B, A') of the triple system with the labels (alpha, A) and
(beta, B) exchanged, an exchange under which q is invariant (checked).

Checks: 4N(A) = 4 det; T(A#, B) is the derivative of N at A along B; q invariant under the
exchange; the stabiliser algebra of q in sp(56) has dimension 133 (computed over R from real
points: q has real coefficients, so this is also the complex dimension of the stabiliser in
sp(56, C)); its intersection with u(56) has real dimension 133; bracket closure; the trace ratio;
the Lean witness `e7Weight`; and E6 x U(1) as the centraliser of the witness (dimension 79), with
56 = 1 + 27 + 1 + 27bar and T_E6(27) = 3 at embedding index one, so T_E7(56) = 3 + 3.

Runs in a few seconds. Usage: python e7_checks.py [--variants]
"""
from __future__ import annotations

import sys

import numpy as np

from e6_checks import PHI_TRIPLES, phi_tensor  # noqa: F401  (Bryant's phi, shared with e6 and f4)

PHI = phi_tensor()


def omul1(x, y):
    r = np.empty(8)
    r[0] = x[0] * y[0] - x[1:] @ y[1:]
    r[1:] = x[0] * y[1:] + y[0] * x[1:] + np.einsum("ijk,i,j->k", PHI, x[1:], y[1:])
    return r


# structure constants: (x y)_k = C[i, j, k] x_i y_j
E8 = np.eye(8)
C = np.array([[omul1(E8[i], E8[j]) for j in range(8)] for i in range(8)])
C64 = C.reshape(64, 8)


def omul(x, y):            # batched over leading axes
    xy = x[..., :, None] * y[..., None, :]
    return xy.reshape(xy.shape[:-2] + (64,)) @ C64


def oconj(x):
    return np.concatenate([x[..., :1], -x[..., 1:]], axis=-1)


R2 = np.sqrt(2.0)
# DERIVED: the sign of Freudenthal's quartic in these coordinates; the module docstring states it is
# not a convention (+1 drops the sp(56) stabiliser to dimension 79, which `--variants` prints).
SHARP_SIGN = -1.0         # the sign of T(2A#, 2B#) in q; +1 is the `--variants` comparison


def blocks(A):
    return A[..., 0], A[..., 1], A[..., 2], A[..., 3:11], A[..., 11:19], A[..., 19:27]


def dot(x, y):
    return (x * y).sum(-1)


def n4tri(P, Q, R):
    aP, bP, cP, pP, qP, sP = blocks(P)
    aQ, bQ, cQ, pQ, qQ, sQ = blocks(Q)
    aR, bR, cR, pR, qR, sR = blocks(R)
    return (4 * aP * bQ * cR - 2 * aP * dot(pQ, pR) - 2 * bP * dot(qQ, qR) - 2 * cP * dot(sQ, sR)
            + 2 * R2 * omul(omul(pP, qQ), sR)[..., 0])


def sharp2(P, Q):          # bilinear, S(A, A) = 2 A#
    aP, bP, cP, pP, qP, sP = blocks(P)
    aQ, bQ, cQ, pQ, qQ, sQ = blocks(Q)
    d = np.stack([2 * bP * cQ - dot(pP, pQ), 2 * cP * aQ - dot(qP, qQ), 2 * aP * bQ - dot(sP, sQ)],
                 axis=-1)
    op = R2 * oconj(omul(qP, sQ)) - 2 * aP[..., None] * pQ
    oq = R2 * oconj(omul(sP, pQ)) - 2 * bP[..., None] * qQ
    os_ = R2 * oconj(omul(pP, qQ)) - 2 * cP[..., None] * sQ
    return np.concatenate([d, op, oq, os_], axis=-1)


def split(v):
    return v[..., 0], v[..., 1:28], v[..., 28], v[..., 29:56]


def q4(v1, v2, v3, v4):
    """The 4-linear form `e7Q4` of the Lean module; its diagonal is the quartic."""
    a1, A1, b1, B1 = split(v1)
    a2, A2, b2, B2 = split(v2)
    a3, A3, b3, B3 = split(v3)
    a4, A4, b4, B4 = split(v4)
    return ((a1 * b2 - dot(A1, B2)) * (a3 * b4 - dot(A3, B4)) - a1 * n4tri(A2, A3, A4)
            - b1 * n4tri(B2, B3, B4) + SHARP_SIGN * dot(sharp2(A1, A2), sharp2(B3, B4)))


def quartic(v):
    return q4(v, v, v, v)


def grad(V):
    """Gradient of the quartic at each row of V, by the five-point stencil, exact on degree 4."""
    n = V.shape[0]
    h = 0.5
    E = np.eye(56)
    G = np.zeros((n, 56), dtype=V.dtype)
    for c, w in ((-2, 1), (-1, -8), (1, 8), (2, -1)):
        P = V[:, None, :] + c * h * E[None, :, :]
        G += w * quartic(P)
    return G / (12 * h)


E27 = np.eye(27)


def grad_fast(V):
    """The same gradient in closed form (cross-checked against `grad` in `main`):
    with P = alpha beta - T(A, B), d/dalpha = 2 P beta - 4N(A), d/dbeta = 2 P alpha - 4N(B),
    grad_A = -2 P B - alpha 2S(A, A) + sign grad_A T(S(A, A), S(B, B)), and symmetrically."""
    al, A, be, B = split(V)
    P = al * be - dot(A, B)
    SA, SB = sharp2(A, A), sharp2(B, B)

    def gS(X, W):           # v -> T(S(X, v) + S(v, X), W), as a vector over the 27 basis v
        Xb = np.broadcast_to(X[:, None, :], X.shape[:1] + (27, 27))
        Eb = np.broadcast_to(E27[None], Xb.shape)
        return dot(sharp2(Xb, Eb) + sharp2(Eb, Xb), W[:, None, :])

    gA = -2 * P[:, None] * B - al[:, None] * 2 * SA + SHARP_SIGN * gS(A, SB)
    gB = -2 * P[:, None] * A - be[:, None] * 2 * SB + SHARP_SIGN * gS(B, SA)
    return np.concatenate([(2 * P * be - n4tri(A, A, A))[:, None], gA,
                           (2 * P * al - n4tri(B, B, B))[:, None], gB], axis=-1)


# DERIVED: n = 28 = 1 + 27, half the 56-dimensional triple system; the form is the Lean `Jsp 28`.
def jsp(n=28):
    J = np.zeros((2 * n, 2 * n))
    for i in range(n):
        J[i, n + i] = -1.0      # Matrix.J = fromBlocks 0 (-1) 1 0
        J[n + i, i] = 1.0
    return J


J = jsp()
JINV = -J                       # J^2 = -1
IU = np.triu_indices(56)


# CHOSEN: 1650 random points, 54 constraint rows more than the 1596 unknowns of sp(56), so a
# generic draw has full constraint rank 1463; fewer than 1596 rows would leave spurious null vectors.
def stabiliser(rng, npts=1650):
    """Real basis of {X in sp(56, R) | grad q(v) . X v = 0}, X = S J^{-1} with S symmetric."""
    V = rng.standard_normal((npts, 56))
    G = grad_fast(V)
    Y = V @ JINV.T
    M = G[:, IU[0]] * Y[:, IU[1]] + G[:, IU[1]] * Y[:, IU[0]]
    d = IU[0] == IU[1]
    M[:, d] = G[:, IU[0][d]] * Y[:, IU[0][d]]
    # null space from the Gram matrix: eigenvalues are the squared singular values, ascending
    # NOT A READ: the null space of the sp(56) stabiliser constraint system, a Lie-algebra computation; no correlation or field enters
    ev, W = np.linalg.eigh(M.T @ M)
    sv = np.sqrt(np.clip(ev[::-1], 0, None))
    rank = int((sv > 1e-6 * sv[0]).sum())
    return W[:, :len(sv) - rank].T, sv, rank


def mat(coef):
    S = np.zeros((56, 56))
    S[IU] = coef
    S = S + S.T - np.diag(np.diag(S))
    return S @ JINV


# CHOSEN: relative singular-value cut for the numerical null space, about seven decades above double
# rounding; the dimensions it returns (79 + 54, 79) are asserted against the derived values below.
def null_rows(M, rel=1e-9):
    # NOT A READ: the null space of a linear map between Lie-algebra coordinates (a centraliser); no correlation or field enters
    _, s, Vh = np.linalg.svd(M, full_matrices=False)
    if M.shape[1] > len(s):
        raise ValueError("null_rows needs at least as many rows as columns")
    r = int((s > rel * s[0]).sum())
    return Vh[r:]


def ad(X, basis, pinv):
    return np.array([pinv @ (X @ Y - Y @ X).reshape(-1) for Y in basis]).T


def main():
    global SHARP_SIGN
    rng = np.random.default_rng(0)
    crand = lambda *s: rng.standard_normal(s) + 1j * rng.standard_normal(s)

    if "--variants" in sys.argv:
        for sgn in (1.0, -1.0):
            SHARP_SIGN = sgn
            K, _, _ = stabiliser(rng)
            print(f"sign of T(2A#, 2B#) = {sgn:+.0f}: stabiliser dim in sp(56) = {len(K)}")
        SHARP_SIGN = -1.0

    # 1. N(A) is the F4 determinant: abc - a n(x) - b n(y) - c n(z) + 2 Re(x y z), x = p / r
    for _ in range(10):
        A = rng.standard_normal(27)
        a, b, c, p, q, s = blocks(A)
        x, y, z = p / R2, q / R2, s / R2
        det = a * b * c - a * (x @ x) - b * (y @ y) - c * (z @ z) + 2 * omul(omul(x, y), z)[0]
        # CHOSEN: rounding tolerance on an exact polynomial identity at O(1) Gaussian inputs.
        assert abs(n4tri(A, A, A) - 4 * det) < 1e-9
    print("4N = 4 det on 10 random real elements of J")

    # 2. T(A#, B) = d/dt N(A + t B) at 0 (sharp2 / 2 is the Jordan adjoint)
    for _ in range(10):
        A, B = crand(27), crand(27)
        t = 1e-3
        dN = (n4tri(A + t * B, A + t * B, A + t * B)
              - n4tri(A - t * B, A - t * B, A - t * B)) / (8 * t)
        assert abs(dot(sharp2(A, A), B) / 2 - dN) < 1e-5 * (1 + abs(dN))
    print("T(A#, B) = D_B N(A) on 10 random complex pairs")

    # 3. q is invariant under (alpha, A) <-> (beta, B)
    for _ in range(5):
        v = crand(56)
        w = np.concatenate([v[28:], v[:28]])
        assert abs(quartic(v) - quartic(w)) < 1e-8 * abs(quartic(v))
    print("q invariant under the exchange of the two blocks")

    # 4. stabiliser algebra in sp(56)
    K, sv, rank = stabiliser(rng)
    print(f"sp(56) has dim {len(IU[0])}; constraint rank {rank}; stabiliser dim {len(K)}")
    print(f"  singular-value gap at the cut: {sv[rank - 1]:.3e} -> {sv[rank]:.3e}")
    # DERIVED: dim E7 = 133, the dimension the Lean module states for the stabiliser.
    assert len(K) == 133
    gens = [mat(k) for k in K]
    for X in gens[:5]:
        # CHOSEN: rounding tolerance; X = S J^{-1} with S symmetric satisfies X J + J X^T = 0 exactly.
        assert np.abs(X @ J + J @ X.T).max() < 1e-10
    Vt = crand(20, 56)
    Gt = grad(Vt)
    gerr = np.abs(Gt - grad_fast(Vt)).max() / np.abs(Gt).max()
    print(f"closed-form gradient against the five-point stencil: relative error {gerr:.1e}")
    # CHOSEN: the stencil is exact on degree 4, so only rounding remains; the read is about 2.5e-15.
    assert gerr < 1e-12
    res = max(abs(Gt[m] @ (X @ Vt[m])) for X in gens[::13] for m in range(20))
    print(f"derivation residual at fresh complex points {res:.2e}")
    # CHOSEN: absolute residual tolerance at O(1) complex points; the read is about 3e-11.
    assert res < 1e-7
    B = np.array([X.reshape(-1) for X in gens]).T               # 3136 x 133
    Bp = np.linalg.pinv(B)
    worst = 0.0
    for a in range(0, 133, 11):
        for b in range(1, 133, 17):
            Cm = (gens[a] @ gens[b] - gens[b] @ gens[a]).reshape(-1)
            worst = max(worst, np.linalg.norm(Cm - B @ (Bp @ Cm)))
    print(f"bracket closure residual {worst:.2e}")
    # CHOSEN: closure tolerance on sampled brackets; the read is about 5e-14.
    assert worst < 1e-8

    # 5. the compact part. For X = sum (u_k + i w_k) g_k with g_k real,
    #    X + X^dagger = sum u_k (g_k + g_k^T) + i sum w_k (g_k - g_k^T), so
    #    dim_R (L_C cap u(56)) = dim (L cap Sym) + dim (L cap Skew).
    Sym = np.array([(X + X.T).reshape(-1) for X in gens]).T
    Skw = np.array([(X - X.T).reshape(-1) for X in gens]).T
    Ku, Kw = null_rows(Sym), null_rows(Skw)
    print(f"real dimension of stabiliser cap u(56): {len(Ku)} + {len(Kw)} = {len(Ku) + len(Kw)}")
    # DERIVED: the compact real form of E7 has real dimension 133 = dim E7.
    assert len(Ku) + len(Kw) == 133
    cgens = [sum(c * g for c, g in zip(k, gens)) for k in Ku] + \
            [1j * sum(c * g for c, g in zip(k, gens)) for k in Kw]
    for X in cgens:
        # CHOSEN: rounding tolerance on anti-Hermiticity, exact by construction of the compact basis.
        assert np.abs(X + X.conj().T).max() < 1e-9

    # 6. trace ratio tr_56(X^2) / tr_adj(X^2) on the compact algebra
    Bc = np.array([X.reshape(-1) for X in cgens]).T
    Bcp = np.linalg.pinv(Bc)
    for _ in range(3):
        c = rng.standard_normal(133)
        X = sum(ci * Gk for ci, Gk in zip(c, cgens))
        A = ad(X, cgens, Bcp)
        ratio = np.trace(X @ X) / np.trace(A @ A)
        print(f"tr_56(X^2) / tr_adj(X^2) = {ratio.real:.12f}  (T(56)/h^v = 6/18 = {1/3:.12f})")
        # CHOSEN: tolerance on the derived ratio 1/3 = T(56)/h^v; the read agrees to all 12 printed digits.
        assert abs(ratio - 1 / 3) < 1e-9

    # 7. the Lean witness e7Weight: diag(-3 on alpha, 1 on A, 3 on beta, -1 on B)
    w = np.concatenate([[-3.0], np.ones(27), [3.0], -np.ones(27)])
    H0 = np.diag(w)
    # DERIVED: exact zero; w[28 + i] = -w[i] and the entries are small integers, so no rounding enters.
    assert np.abs(H0 @ J + J @ H0.T).max() == 0
    res = max(abs(Gt[m] @ (H0 @ Vt[m])) for m in range(20))
    print(f"witness e7Weight derivation residual {res:.2e}")
    # CHOSEN: absolute residual tolerance at O(1) complex points; the read is about 4e-12.
    assert res < 1e-7
    z = np.linalg.lstsq(Bc, (1j * H0).reshape(-1), rcond=None)[0]
    # CHOSEN: least-squares membership tolerance for i e7Weight in the compact span; residual not printed.
    assert np.linalg.norm(Bc @ z - (1j * H0).reshape(-1)) < 1e-8
    print("i e7Weight lies in the compact stabiliser algebra")

    # 8. E6 x U(1): centraliser of H0 in the real stabiliser algebra
    adH = ad(H0, gens, Bp)
    Z = null_rows(adH)
    print(f"centraliser of e7Weight: dim {len(Z)} (E6 x U(1) = 79)")
    # DERIVED: dim (E6 x U(1)) = 78 + 1 = 79.
    assert len(Z) == 79
    cent = [(B @ zz).reshape(56, 56) for zz in Z]
    brk = [cent[i] @ cent[j] - cent[j] @ cent[i] for i in range(0, 79, 3) for j in range(1, 79, 4)]
    Bb = np.array([X.reshape(-1) for X in brk]).T
    # NOT A READ: the dimension and a basis of the span of the brackets (the derived algebra), a Lie-algebra computation; no correlation or field enters
    ub, sb, _ = np.linalg.svd(Bb, full_matrices=False)
    e6dim = int((sb > 1e-9 * sb[0]).sum())
    print(f"derived algebra of the centraliser: dim {e6dim} (E6 = 78)")
    # DERIVED: dim E6 = 78.
    assert e6dim == 78
    e6 = [ub[:, k].reshape(56, 56) for k in range(78)]
    E6p = np.linalg.pinv(np.array([X.reshape(-1) for X in e6]).T)
    for _ in range(2):
        c = rng.standard_normal(78)
        X = sum(ci * Gk for ci, Gk in zip(c, e6))
        # X kills alpha and beta and does not mix A with B: 56 = 1 + 27 + 1 + 27bar
        # CHOSEN: rounding tolerance on entries that vanish exactly on e6; the residual is not printed.
        assert np.abs(X[0]).max() < 1e-9 and np.abs(X[:, 0]).max() < 1e-9
        # CHOSEN: rounding tolerance on entries that vanish exactly on e6; the residual is not printed.
        assert np.abs(X[28]).max() < 1e-9 and np.abs(X[:, 28]).max() < 1e-9
        # CHOSEN: rounding tolerance on the A-B mixing blocks, exactly zero on e6; residual not printed.
        assert np.abs(X[1:28, 29:56]).max() < 1e-9 and np.abs(X[29:56, 1:28]).max() < 1e-9
        XA = X[1:28, 1:28]
        A6 = ad(X, e6, E6p)
        A7 = ad(X, gens, Bp)
        t27 = 12 * np.trace(XA @ XA) / np.trace(A6 @ A6)
        t56 = 18 * np.trace(X @ X) / np.trace(A7 @ A7)
        idx = (np.trace(A7 @ A7) / 18) / (np.trace(A6 @ A6) / 12)
        print(f"on e6: T_E6(27) = {t27:.9f}, embedding index {idx:.9f}, "
              f"T_E7(56) = {t56:.9f} = (T(27) + T(27bar)) / index")
        # CHOSEN: tolerance on the derived targets T_E6(27) = 3, index 1, T_E7(56) = 6; reads agree to 9 digits.
        assert abs(t27 - 3) < 1e-8 and abs(idx - 1) < 1e-8 and abs(t56 - 6) < 1e-8
    print("all E7 checks passed")


if __name__ == "__main__":
    main()
