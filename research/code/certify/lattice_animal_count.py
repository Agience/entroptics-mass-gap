"""How many touch-connected plaquette sets of a given size hold a fixed plaquette.

WHAT THIS MEASURES. `MassGap.StrongCoupling.card_connected_rooted_le` proves

    number of touch-connected S with p0 in S and |S| = m, at most ((touchDeg bd + 1)^2)^m

with `touchDeg` read off the boundary word `bd` and the lattice extent `n` nowhere in it. This
script enumerates the left-hand side by brute force on the same `bd` the Lean development uses --
the periodic hypercubic word `U_mu(x) U_nu(x+mu) U_mu(x+nu)^-1 U_nu(x)^-1`, degenerate planes
`mu = nu` included, exactly as `WilsonHypercubic.bd` carries them -- and prints it beside the bound.

WHAT IT IS FOR. Three separate questions, and the table answers all three at once.

  * Is the bound true? The enumerated count must sit under it at every `m`.
  * Is it vacuous? A bound that over-counts by a hundred orders of magnitude proves nothing useful,
    so the ratio is printed rather than a pass mark.
  * Is it volume-free? The count is measured at `n = 3, 4, 5`. Once `n` exceeds the diameter a
    size-`m` set can reach, the count MUST stop moving; the same table prints the count with
    connectedness dropped, which is `C(P-1, m-1)` and grows without limit in `n`. That contrast is
    the whole content of the connectedness hypothesis.

THE ENUMERATOR IS ITSELF CHECKED. `_selfcheck` runs the extension-and-forbidden enumeration against
an exhaustive pass over all 2^V subsets on small graphs -- a path, a cycle, a grid and random
graphs -- and a disagreement stops the run. An enumerator validated only against its own output
would answer its own design.
"""
from __future__ import annotations

import argparse
import itertools
import math
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------------------- the lattice geometry

def sites(d, n):
    return list(itertools.product(range(n), repeat=d))


def shift(mu, x, n):
    y = list(x)
    y[mu] = (y[mu] + 1) % n
    return tuple(y)


def plaquettes(d, n):
    """Every `((mu, nu), x)`, degenerate planes included -- the inhabitants of `Plaq d n`."""
    return [((mu, nu), x)
            for mu in range(d) for nu in range(d) for x in sites(d, n)]


def link_supp(p, n):
    """The links the boundary word names, as a set -- `StrongCoupling.linkSupp` on `WilsonHypercubic.bd`."""
    (mu, nu), x = p
    return frozenset({(mu, x), (nu, shift(mu, x, n)), (mu, shift(nu, x, n)), (nu, x)})


def adjacency(d, n):
    """Touch-neighbours by shared link, as index lists. `p` touches itself whenever its word is
    non-empty, which the Lean `touchNbrs` also counts -- no exclusion is applied here either."""
    ps = plaquettes(d, n)
    supp = [link_supp(p, n) for p in ps]
    by_link = {}
    for i, s in enumerate(supp):
        for l in s:
            by_link.setdefault(l, []).append(i)
    adj = []
    for i, s in enumerate(supp):
        nb = set()
        for l in s:
            nb.update(by_link[l])
        adj.append(sorted(nb))
    return ps, adj


def touch_deg(adj):
    """`touchDeg bd` -- the largest touch-neighbour count, self included, as Lean defines it."""
    return max(len(a) for a in adj)


# ------------------------------------------------------------------- rooted connected enumeration

def count_rooted(adj, root, m, must_contain=None):
    """Connected vertex sets of size exactly `m` containing `root` (and `must_contain` if given).

    Extension-and-forbidden: each set is produced once, because the order its vertices enter is
    fixed by the branch that forbids a candidate for every later branch.
    """
    total = 0
    nbr = [set(a) for a in adj]

    def rec(sub, ext, forb):
        nonlocal total
        if len(sub) == m:
            if must_contain is None or must_contain in sub:
                total += 1
            return
        # No frontier-size prune. `len(sub) + len(ext) < m` looks like a safe cut and is not:
        # extending by one frontier vertex opens its own neighbours, so a short frontier does not
        # bound how large the set can still grow. The self-check below caught it undercounting
        # 99 cases, most of them to zero.
        ext = list(ext)
        forb = set(forb)
        while ext:
            v = ext.pop()
            forb.add(v)
            new_ext = list(ext)
            seen = set(ext) | sub | forb
            for u in nbr[v]:
                if u not in seen:
                    new_ext.append(u)
                    seen.add(u)
            rec(sub | {v}, new_ext, forb)

    start_ext = [u for u in adj[root] if u != root]
    rec({root}, start_ext, {root})
    return total


def _exhaustive_rooted(adj, root, m):
    """All size-`m` subsets containing `root`, kept if connected. Only for tiny graphs."""
    v = len(adj)
    nbr = [set(a) for a in adj]
    total = 0
    others = [u for u in range(v) if u != root]
    for combo in itertools.combinations(others, m - 1):
        s = set(combo) | {root}
        seen = {root}
        stack = [root]
        while stack:
            x = stack.pop()
            for y in nbr[x]:
                if y in s and y not in seen:
                    seen.add(y)
                    stack.append(y)
        if len(seen) == len(s):
            total += 1
    return total


def _selfcheck():
    """The enumerator against exhaustive subset enumeration. A mismatch stops the run."""
    cases = []
    # a path
    # DERIVED: 10 is the path's vertex count and 9 its last index, so the guards are the
    # endpoints of the test graph itself. Self-check fixtures, not parameters of the bound.
    cases.append([[i - 1] * (i > 0) + [i + 1] * (i < 9) for i in range(10)])
    # a cycle
    cases.append([[(i - 1) % 9, (i + 1) % 9] for i in range(9)])
    # a 3x3 grid
    grid = {}
    for a in range(3):
        for b in range(3):
            k = a * 3 + b
            grid[k] = [aa * 3 + bb for aa, bb in
                       ((a - 1, b), (a + 1, b), (a, b - 1), (a, b + 1))
                       # DERIVED: 3 is the side of the 3x3 self-check grid and 0 its origin, so
                       # the guard is the grid's own extent -- a shape, not a threshold.
                       if 0 <= aa < 3 and 0 <= bb < 3]
    cases.append([grid[k] for k in range(9)])
    # random graphs, self-loops included so the loop handling is exercised too
    rng = random.Random(20260917)
    for _ in range(6):
        v = rng.randint(6, 11)
        adj = [set() for _ in range(v)]
        for i in range(v):
            for j in range(i, v):
                # CHOSEN: 0.35 is the edge probability of the random self-check graphs. It buys
                # graphs that are neither trees nor complete, which is where a counting bug
                # hides; the self-check compares against exhaustive enumeration, so ANY value
                # gives a valid check and this one only affects how searching it is.
                if rng.random() < 0.35:
                    adj[i].add(j)
                    adj[j].add(i)
        cases.append([sorted(a) for a in adj])

    bad = 0
    for ci, adj in enumerate(cases):
        for root in range(min(len(adj), 4)):
            for m in range(1, min(len(adj), 6) + 1):
                got = count_rooted(adj, root, m)
                want = _exhaustive_rooted(adj, root, m)
                if got != want:
                    bad += 1
                    print(f"  SELFCHECK MISMATCH case {ci} root {root} m {m}: "
                          f"enumerator {got} exhaustive {want}")
    if bad:
        raise SystemExit(f"enumerator disagrees with exhaustive enumeration in {bad} cases")
    print("selfcheck: enumerator matches exhaustive subset enumeration on "
          f"{len(cases)} graphs, all roots 0..3, m = 1..6")


# ------------------------------------------------------------------------------------- the tables

def far_plaquette(ps, adj, root, steps):
    """A plaquette at touch-distance exactly `steps` from `root`, or None."""
    seen = {root}
    frontier = [root]
    for _ in range(steps):
        nxt = []
        for v in frontier:
            for u in adj[v]:
                if u not in seen:
                    seen.add(u)
                    nxt.append(u)
        frontier = nxt
        if not frontier:
            return None
    return frontier[0] if frontier else None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--dims", type=int, nargs="*", default=[2, 3, 4])
    ap.add_argument("--exts", type=int, nargs="*", default=[3, 4, 5])
    ap.add_argument("--mmax", type=int, default=5)
    ap.add_argument("--mmax-dim4", type=int, default=4)
    a = ap.parse_args()

    _selfcheck()
    print()

    for d in a.dims:
        # DERIVED: 4 is the dimension the Clay problem is stated in, and the only one whose
        # enumeration is cut short; the cut is a RUNTIME budget on the control, not a
        # parameter of the bound, and the bound is checked at every dim in a.dims.
        mmax = a.mmax_dim4 if d >= 4 else a.mmax
        print(f"================ dim = {d} ================")
        deg_by_n = {}
        for n in a.exts:
            ps, adj = adjacency(d, n)
            deg = touch_deg(adj)
            deg_by_n[n] = deg
            root = ps.index(((0, 1), tuple([0] * d)))
            P = len(ps)
            K = (deg + 1) ** 2
            Kproved = (16 * d + 1) ** 2
            print(f"\n  n = {n}:  plaquettes P = {P}   touchDeg = {deg}   "
                  f"touchDeg bound 16*dim = {16 * d}")
            print(f"    K = (touchDeg+1)^2 = {K}    K from the proved degree bound "
                  f"= (16*dim+1)^2 = {Kproved}")
            print(f"    {'m':>2} {'true rooted':>14} {'proved (D)^(2m-2)':>20} {'K^m':>22} "
                  f"{'K^m / true':>12} {'no-connectedness':>18}")
            for m in range(1, mmax + 1):
                true = count_rooted(adj, root, m)
                D = deg + 1
                proved = D ** (2 * m - 2)
                km = K ** m
                free = math.comb(P - 1, m - 1)
                print(f"    {m:>2} {true:>14} {proved:>20} {km:>22} "
                      f"{km / true:>12.3e} {free:>18}")
            # the pair-anchored count: both endpoints fixed, p_d two touch-steps out
            pd = far_plaquette(ps, adj, root, 2)
            if pd is not None:
                print(f"    with p_d fixed at touch-distance 2 (index {pd}):")
                for m in range(1, mmax + 1):
                    both = count_rooted(adj, root, m, must_contain=pd)
                    print(f"      m = {m}: connected sets holding p_0 and p_d = {both}"
                          f"   K^m = {K ** m}")
        print(f"\n  touchDeg by extent: "
              + ", ".join(f"n={n}: {deg_by_n[n]}" for n in sorted(deg_by_n))
        # DERIVED: 1 is the number of DISTINCT values a constant takes. The claim being checked
        # is that touchDeg does not move with the extent, so the test is that the set of
        # measured degrees is a singleton -- a property of the data, not a tolerance.
              + ("  -- constant in n" if len(set(deg_by_n.values())) == 1 else "  -- MOVES IN n"))
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
