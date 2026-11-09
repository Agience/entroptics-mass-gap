"""Structure constants of the compact real form of e8, for `MassGap/GaugeE8.lean`.

Construction (Kac, *Infinite-dimensional Lie algebras*, section 7.8). The root lattice of E8 is the
even unimodular lattice; with simple roots alpha_1..alpha_8 (Bourbaki, standard coordinates of R^8)
the bimultiplicative cocycle

    eps(alpha, beta) = (-1)^( sum_i a_i b_i + sum_{i<j} a_i b_j (alpha_i, alpha_j) ),

a, b the simple-root coordinates, gives the complex Lie algebra with basis H_1..H_8, e_alpha:

    [H_k, e_alpha] = alpha_k e_alpha,   [e_alpha, e_-alpha] = -sum_k alpha_k H_k,
    [e_alpha, e_beta] = eps(alpha, beta) e_(alpha+beta)   (alpha + beta a root),

with invariant form (H_k | H_l) = delta_kl, (e_alpha | e_beta) = -delta_(alpha,-beta).

Real basis (248 vectors, each of norm (x|x) = -2, mutually orthogonal):

    index 0..7          i H'_m,  H'_(2s) = H_(2s) + H_(2s+1),  H'_(2s+1) = H_(2s) - H_(2s+1);
    index 8 + 2r        a_r = e_alpha + e_-alpha,
    index 9 + 2r        b_r = i (e_alpha - e_-alpha),

alpha = alpha_r the r-th representative of the 120 pairs {alpha, -alpha}, chosen with
lam(alpha) = alpha_1 + alpha_2 >= 0 and ordered by lam descending (one pair with lam = 2, then 56
with lam = 1, then 63 with lam = 0). The map e_alpha -> e_-alpha, H -> -H is an automorphism for
this cocycle, so the real span is the compact form, and the form <x, y> = -(x|y)/2 is positive
definite with the basis orthonormal. The structure constants f_ijk = <[x_i, x_j], x_k> are then
totally antisymmetric and integers in {-2, -1, 1, 2}.

Lean encoding. Each triple i < j < k with f_ijk != 0 is the natural number
((i * 248 + j) * 248 + k) * 5 + (f + 2). Triples are grouped into blocks by their unordered triple
of slots (slot of i < 8 is i; slot of 8 + 2r and 9 + 2r is 8 + r). The derivation D = ad(i H'_0)
maps x_(8+2r) -> lam_r x_(9+2r), x_(9+2r) -> -lam_r x_(8+2r) and kills the Cartan, so it preserves
slots; the Lean check is per block: in D acting on the 3-form, the coefficients of every
non-degenerate index triple cancel within the block.

Run as `python e8_structure.py` (no arguments): checks, then rewrites the data section between
`-- BEGIN E8 DATA` and `-- END E8 DATA` in research/lean/MassGap/GaugeE8.lean if the markers exist.
"""
from __future__ import annotations

import itertools
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN_FILE = os.path.join(os.path.dirname(HERE), "lean", "MassGap", "GaugeE8.lean")

# DERIVED: dim e8 = 8 + 240, the Cartan plus one vector per root.
N = 248


def roots_doubled():
    """The 240 roots in doubled standard coordinates (integer tuples)."""
    out = []
    for i, j in itertools.combinations(range(8), 2):
        for si in (2, -2):
            for sj in (2, -2):
                v = [0] * 8
                v[i], v[j] = si, sj
                out.append(tuple(v))
    for signs in itertools.product((1, -1), repeat=8):
        # DERIVED: parity test; E8 keeps the half-integer vectors with an even number of minus signs.
        if signs.count(-1) % 2 == 0:
            out.append(tuple(signs))
    # DERIVED: |roots of E8| = 112 (integer type) + 128 (half-integer type) = 240.
    assert len(out) == 240
    return out


def ip(A, B):
    """(alpha, beta) for doubled coordinates."""
    return sum(a * b for a, b in zip(A, B)) // 4


# DERIVED: the Bourbaki simple roots of E8 in doubled standard coordinates, as the docstring states.
SIMPLE = [
    (1, -1, -1, -1, -1, -1, -1, 1),
    (2, 2, 0, 0, 0, 0, 0, 0),
    (-2, 2, 0, 0, 0, 0, 0, 0),
    (0, -2, 2, 0, 0, 0, 0, 0),
    (0, 0, -2, 2, 0, 0, 0, 0),
    (0, 0, 0, -2, 2, 0, 0, 0),
    (0, 0, 0, 0, -2, 2, 0, 0),
    (0, 0, 0, 0, 0, -2, 2, 0),
]


def build():
    R = roots_doubled()
    Rset = set(R)
    S = np.array(SIMPLE, dtype=float).T
    coords = {}
    for A in R:
        a = np.linalg.solve(S, np.array(A, dtype=float))
        ai = np.rint(a).astype(int)
        assert np.allclose(a, ai)
        coords[A] = ai
    G = np.array([[ip(x, y) for y in SIMPLE] for x in SIMPLE])

    def eps(A, B):
        a, b = coords[A], coords[B]
        e = int(np.dot(a, b))
        for i in range(8):
            for j in range(i + 1, 8):
                e += int(a[i] * b[j] * G[i, j])
        return -1 if e % 2 else 1

    def add(A, B):
        return tuple(x + y for x, y in zip(A, B))

    def neg(A):
        return tuple(-x for x in A)

    # Chevalley bracket on basis keys: ('H', k) or a root tuple. Returns dict key -> complex.
    def cbr(X, Y):
        if X[0] == 'H' and Y[0] == 'H':
            return {}
        if X[0] == 'H':
            return {Y: Y[X[1]] / 2}
        if Y[0] == 'H':
            return {X: -X[Y[1]] / 2}
        s = add(X, Y)
        # DERIVED: exact integer test for alpha + beta = 0, the [e_alpha, e_-alpha] case.
        if all(v == 0 for v in s):
            # DERIVED: exact integer test skipping zero coordinates of alpha, not a magnitude.
            return {('H', k): -X[k] / 2 for k in range(8) if X[k] != 0}
        if s in Rset:
            return {s: eps(X, Y)}
        return {}

    # pair representatives
    def lam(A):
        return (A[0] + A[1]) // 2

    # DERIVED: the docstring's choice of representative, lam(alpha) >= 0 with ties broken by order.
    reps = [A for A in R if lam(A) > 0 or (lam(A) == 0 and A > neg(A))]
    # DERIVED: 240 roots form 120 pairs {alpha, -alpha}.
    assert len(reps) == 120
    reps.sort(key=lambda A: (-lam(A), A))
    lams = [lam(A) for A in reps]
    # DERIVED: the lam counts the docstring states (1 + 56 + 63 = 120 pairs).
    assert lams.count(2) == 1 and lams.count(1) == 56 and lams.count(0) == 63

    # real basis as complex combinations of Chevalley keys
    basis = []
    for s in range(4):
        basis.append({('H', 2 * s): 1j, ('H', 2 * s + 1): 1j})
        basis.append({('H', 2 * s): 1j, ('H', 2 * s + 1): -1j})
    for A in reps:
        basis.append({A: 1, neg(A): 1})
        basis.append({A: 1j, neg(A): -1j})
    assert len(basis) == N

    # inverse: Chevalley key -> real-basis combination
    inv = {}
    for s in range(4):
        # H_2s = -i (iH'_2s + iH'_2s+1)/2, H_2s+1 = -i (iH'_2s - iH'_2s+1)/2
        inv[('H', 2 * s)] = {2 * s: -0.5j, 2 * s + 1: -0.5j}
        inv[('H', 2 * s + 1)] = {2 * s: -0.5j, 2 * s + 1: 0.5j}
    for r, A in enumerate(reps):
        # e_A = (a - i b)/2, e_-A = (a + i b)/2
        inv[A] = {8 + 2 * r: 0.5, 9 + 2 * r: -0.5j}
        inv[neg(A)] = {8 + 2 * r: 0.5, 9 + 2 * r: 0.5j}

    def to_real(v):
        out = {}
        for key, c in v.items():
            for idx, w in inv[key].items():
                out[idx] = out.get(idx, 0) + c * w
        # CHOSEN: drops cancelled coefficients; true values are multiples of 1/4, so any cut far below that works.
        return {k: x for k, x in out.items() if abs(x) > 1e-12}

    c = {}  # (i, j) -> {k: real}
    for i in range(N):
        for j in range(N):
            acc = {}
            for X, xc in basis[i].items():
                for Y, yc in basis[j].items():
                    for Z, zc in cbr(X, Y).items():
                        acc[Z] = acc.get(Z, 0) + xc * yc * zc
            rv = to_real(acc)
            out = {}
            for k, x in rv.items():
                # CHOSEN: rounding tolerance; structure constants of the compact form are real.
                assert abs(x.imag) < 1e-9, (i, j, k, x)
                xr = x.real
                # CHOSEN: rounding tolerance; the docstring states the constants are integers.
                assert abs(xr - round(xr)) < 1e-9, (i, j, k, x)
                # DERIVED: exact integer test keeping nonzero constants, not a magnitude.
                if round(xr) != 0:
                    out[k] = int(round(xr))
            if out:
                c[(i, j)] = out
    return c, lams


def checks(c, lams):
    t0 = time.time()
    # total antisymmetry
    for (i, j), out in c.items():
        for k, v in out.items():
            assert c.get((j, i), {}).get(k) == -v
            assert c.get((j, k), {}).get(i) == v, (i, j, k)
            assert c.get((k, i), {}).get(j) == v, (i, j, k)
    vals = {v for out in c.values() for v in out.values()}
    assert vals <= {-2, -1, 1, 2}, vals
    E = np.array([(i, j, k, v) for (i, j), out in c.items() for k, v in out.items()],
                 dtype=np.int64)
    jac_terms, nbad = jacobi(E)
    # DERIVED: the Jacobi identity holds exactly on integer data, so no coefficient may be nonzero.
    assert nbad == 0, nbad
    # negative control: flip the sign of one triple in all six orderings; Jacobi must fail
    (i0, j0), out0 = next(iter(sorted(c.items())))
    k0 = next(iter(out0))
    trip = {(i0, j0, k0), (j0, k0, i0), (k0, i0, j0), (j0, i0, k0), (k0, j0, i0), (i0, k0, j0)}
    E2 = E.copy()
    for r in range(len(E2)):
        if tuple(E2[r, :3]) in trip:
            E2[r, 3] = -E2[r, 3]
    _, nbad2 = jacobi(E2)
    # DERIVED: the negative control must break Jacobi somewhere; any nonzero count suffices.
    assert nbad2 > 0
    # Killing form K_ij = tr(ad_i ad_j) = sum_{k,l} c^l_ik c^k_jl
    adm = np.zeros((N, N, N))
    for (i, j), out in c.items():
        for k, v in out.items():
            adm[i, k, j] = v  # (ad x_i)_{kj}
    K = adm.reshape(N, N * N) @ adm.transpose(0, 2, 1).reshape(N, N * N).T
    # Killing = 60 (.|.) (2 h^vee with long roots of length^2 2), and (x_i|x_j) = -2 delta_ij
    assert np.allclose(K, -120 * np.eye(N)), (K[:3, :3])
    t1 = time.time()
    # the witness: D = ad(x_0) has (D x)_n = d_n x_(p n)
    D = adm[0]
    for n in range(N):
        for m in range(N):
            exp = 0
            # DERIVED: indices 0..7 are the Cartan (rank 8), which D = ad(i H'_0) kills.
            if n >= 8 and m == p(n):
                exp = dval(n, lams)
            assert D[n, m] == exp, (n, m, D[n, m], exp)
    return jac_terms, nbad2, t1 - t0


def jacobi(E):
    """Exact Jacobi: sum_k c^k_ij c^m_kl + cyclic(i, j, l) for all (i, j, l, m); returns the
    number of coefficients accumulated and how many are nonzero."""
    order = np.argsort(E[:, 0], kind="stable")
    F = E[order]                                   # entries sorted by first index
    start = np.searchsorted(F[:, 0], np.arange(N + 1))
    cnt = start[1:] - start[:-1]
    # join: entry (i, j, k, v) with every (k, l, m, w); product v w is c^k_ij c^m_kl
    rep = cnt[E[:, 2]]
    left = np.repeat(np.arange(len(E)), rep)
    offs = np.arange(len(left)) - np.repeat(np.cumsum(rep) - rep, rep)
    right = start[E[left, 2]] + offs
    i, j = E[left, 0], E[left, 1]
    l, m = F[right, 1], F[right, 2]
    prod = E[left, 3] * F[right, 3]
    keys = []
    for a, b, cc in ((i, j, l), (j, l, i), (l, i, j)):   # cyclic images of J(i, j, l)^m
        keys.append(((a * N + b) * N + cc) * N + m)
    keys = np.concatenate(keys)
    uk, inv = np.unique(keys, return_inverse=True)
    tot = np.bincount(inv, weights=np.tile(prod, 3).astype(float))
    return len(uk), int(np.count_nonzero(tot))


def p(n):
    # DERIVED: indices 0..7 are the Cartan (rank 8), fixed by the rotation.
    if n < 8:
        return n
    # DERIVED: parity test; 8 + 2r (a_r) pairs with 9 + 2r (b_r), per the docstring's basis.
    return n + 1 if n % 2 == 0 else n - 1


def dval(n, lams):
    # DERIVED: indices 0..7 are the Cartan (rank 8), killed by D.
    if n < 8:
        return 0
    lam = lams[(n - 8) // 2]
    # DERIVED: parity test; D x_(8+2r) and D x_(9+2r) carry opposite signs, per the docstring.
    return -lam if n % 2 == 0 else lam


def slot(n):
    # DERIVED: the docstring's slots; Cartan index i < 8 is its own slot, 8 + 2r and 9 + 2r share 8 + r.
    return n if n < 8 else 8 + (n - 8) // 2


def blocks_of(c):
    triples = {}
    for (i, j), out in c.items():
        for k, v in out.items():
            if i < j < k:
                triples[(i, j, k)] = v
    blocks = {}
    for (i, j, k), v in sorted(triples.items()):
        key = tuple(sorted((slot(i), slot(j), slot(k))))
        blocks.setdefault(key, []).append(((i * N + j) * N + k) * 5 + (v + 2))
    return triples, [blocks[k] for k in sorted(blocks)]


def lean_check(blocks, lams):
    """The check `GaugeE8.blockOK` performs, step for step."""
    for blk in blocks:
        terms = []
        for t in blk:
            key, f = t // 5, t % 5 - 2
            a, b, cc = key // (N * N), (key // N) % N, key % N
            for (x, y, z, w) in ((p(a), b, cc, a), (a, p(b), cc, b), (a, b, p(cc), cc)):
                coef = f * dval(w, lams)
                # DERIVED: exact integer test; degenerate triples and zero coefficients drop out, as in `blockOK`.
                if x != y and y != z and x != z and coef != 0:
                    terms.append(((x * N + y) * N + z, coef))
        for kk, _ in terms:
            # DERIVED: exact integer cancellation within the block, the condition `blockOK` checks.
            if sum(cf for k2, cf in terms if k2 == kk) != 0:
                return False
    return True


def lean_lam_bounds(lams):
    n2 = lams.count(2)
    n1 = lams.count(1)
    assert lams == [2] * n2 + [1] * n1 + [0] * (120 - n2 - n1)
    return n2, n2 + n1


#: Blocks per Lean definition. The code generator recurses once per list cons, and one literal of
#: all 1576 blocks exceeds its default depth; chunks of this size stay well inside it.
# CHOSEN: 128 blocks per chunk (13 chunks); any size under the recursion limit gives the same e8Blocks.
CHUNK = 128


def emit(blocks):
    lines = ["-- BEGIN E8 DATA"]
    chunks = [blocks[s:s + CHUNK] for s in range(0, len(blocks), CHUNK)]
    for ci, ch in enumerate(chunks):
        # The provenance label the Lean numeral gates require on each data table.
        lines.append(f"/-- Blocks {ci * CHUNK} to {ci * CHUNK + len(ch) - 1} of `e8Blocks`. "
                     "DERIVED: computed — the entries are the codes")
        lines.append("`t = 5 (248² i + 248 j + k) + f_{ijk} + 2` of `e8Blocks`, produced by "
                     "`research/code/e8_structure.py` from")
        lines.append("the `E₈` root system and checked block by block by `e8Blocks_ok`. CHOSEN: "
                     f"`{CHUNK}` blocks per chunk, under")
        if ci + 1 < len(chunks):
            lines.append("the code generator's recursion limit; any size gives the same `e8Blocks`. -/")
        else:
            lines.append("the code generator's recursion limit; any size gives the same `e8Blocks`; "
                         f"`{ci * CHUNK + len(ch) - 1}` the last of the")
            lines.append(f"`{len(blocks)}` blocks. -/")
        lines.append(f"def e8Chunk{ci} : List (List ℕ) := [")
        for bi, blk in enumerate(ch):
            sep = "," if bi + 1 < len(ch) else ""
            lines.append("  [" + ", ".join(str(t) for t in blk) + "]" + sep)
        lines.append("]")
        lines.append("")
    lines += ["/-- The structure constants of compact `e₈` in the orthonormal basis of the module "
              "docstring,",
              "grouped into blocks by slot triple. A code `t` stands for the triple "
              "`(i, j, k) = (t / 5 / 248², t / 5 / 248 % 248, t / 5 % 248)`, `i < j < k`, with",
              "`f_{ijk} = t % 5 − 2`. Generated by `research/code/e8_structure.py`.",
              "",
              "DERIVED: the root system of `E₈` and the cocycle of the generator; no numeral is "
              "chosen here. -/",
              "def e8Blocks : List (List ℕ) :=",
              "  " + " ++ ".join(f"e8Chunk{ci}" for ci in range(len(chunks))),
              "-- END E8 DATA"]
    return "\n".join(lines)


def main():
    t0 = time.time()
    c, lams = build()
    t1 = time.time()
    jac_terms, nbad2, tcheck = checks(c, lams)
    triples, blocks = blocks_of(c)
    ok = lean_check(blocks, lams)
    # negative control for the block check: flip the sign of one triple carrying a nonzero d
    bi = next(b for b, blk in enumerate(blocks)
              # DERIVED: exact integer test for a block carrying a nonzero d, not a magnitude.
              if any(dval((t // 5) // (N * N), lams) != 0 for t in blk))
    t = blocks[bi][0]
    bad = [list(b) for b in blocks]
    bad[bi][0] = t - (t % 5) + (4 - t % 5)
    ok_bad = lean_check(bad, lams)
    assert not ok_bad
    t2 = time.time()
    nterms = sum(len(b) for b in blocks)
    print(f"structure constants: {sum(len(o) for o in c.values())} ordered entries, "
          f"{len(triples)} triples i<j<k, {len(blocks)} blocks (max {max(map(len, blocks))})")
    print(f"values: { {v: list(triples.values()).count(v) for v in (-2, -1, 1, 2)} }")
    print(f"Jacobi: {jac_terms} (i,j,l,m) coefficients accumulated, all zero; "
          f"one flipped triple gives {nbad2} nonzero")
    print(f"block check on the same data with one flipped sign: {ok_bad} "
          f"(block {bi}: {blocks[bi]}, code {t} -> {bad[bi][0]})")
    print("Killing form: tr(ad x_i ad x_j) = -120 delta_ij (negative definite)")
    print(f"ad(x_0) = rotation with d, p as in the Lean module: yes; Lean block check: {ok}")
    print(f"lam bounds for Lean: {lean_lam_bounds(lams)}")
    print(f"times: build {t1 - t0:.2f} s, checks+emit {t2 - t1:.2f} s (Jacobi+Killing {tcheck:.2f} s)")
    assert ok and nterms == len(triples)
    if os.path.exists(LEAN_FILE):
        with open(LEAN_FILE, encoding="utf-8") as fh:
            src = fh.read()
        b0, b1 = src.find("-- BEGIN E8 DATA"), src.find("-- END E8 DATA")
        # DERIVED: str.find returns -1 when a marker is absent; both markers present and in order.
        if b0 >= 0 and b1 > b0:
            new = src[:b0] + emit(blocks) + src[b1 + len("-- END E8 DATA"):]
            with open(LEAN_FILE, "w", encoding="utf-8", newline="\n") as fh:
                fh.write(new)
            print(f"wrote data section of {LEAN_FILE}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
