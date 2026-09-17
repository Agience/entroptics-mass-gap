"""floor_branch_family.py -- the numerical check behind `MassGap.CubeBranch`.

WHAT THE LEAN PROVES, AND WHAT THIS CHECKS. `MassGap/CubeBranch.lean` counts a family of closed
vortex surfaces that is strictly richer than `Floor`+`CubeArea`'s directed cube-paths, and therefore
raises the entropy-density floor above `(1/4) log 3 = 0.2746531`. The family is a directed cube-path
(the SPINE) of `(d+1)k+1` steps carrying ONE extra cube per block of `d+1` steps, at one of `d`
positions inside the block. Nothing here is an approximation: this file re-derives the same three
facts the Lean proves, by brute force over the whole parameter set, so that a construction error
would show up as a counted discrepancy rather than as a Lean proof of the wrong statement.

  1. TREE. Every cube but the origin has EXACTLY ONE face-neighbour of lower coordinate sum. That is
     what makes the boundary area `6n - 2(n-1) = 4n+2` -- the SAME area law the directed path obeys
     with `n = k+1`, which is why the two densities are comparable at all.
  2. AREA. `|dC| = 4n+2` at `n = (d+2)k+2`, counted by direct face enumeration rather than by the
     formula.
  3. INJECTIVITY. Distinct parameters give distinct cube sets AND distinct boundaries, so the count
     of surfaces really is `3^((d+1)k+1) * d^k`.
  4. CONNECTED. Every boundary is edge-connected. This one is checked here and NOT proved in Lean:
     `CubeConnected.boundary_connected` descends on the path's own one-cube-per-layer indexing, which
     a tree does not have, so the Lean for the branched family stops at count + area + closed.

THE DENSITY, AND WHY `d > 3` IS THE CONDITION. Per block the family has `3^(d+1) * d` members at a
cost of `d+2` cubes, i.e. `4(d+2)` of area, against the path's `3^(d+2)` members at the same cost. So

    density = ((d+1) log 3 + log d) / (4(d+2))   vs   (d+2) log 3 / (4(d+2)) = (1/4) log 3,

which the family wins exactly when `log d > log 3`. The maximum is at `d = 10`:

    kappa_0 >= (11 log 3 + log 10)/48 = 0.2997358 > 0.2746531 = (1/4) log 3.

THE NEGATIVE CONTROLS, which are the point of running this at all.
  * `d = 3` must give EXACTLY `(1/4) log 3` -- at `d = 3` the count `3^(d+1)*3 = 3^(d+2)` is the path
    count over the same cubes, so a family that "wins" there would be miscounted. `d < 3` must lose.
  * The extra cube's axis is forced to avoid BOTH the spine direction at its own index and the spine
    direction one step on. Replacing it by the forbidden `s(i+1)` must BREAK the tree property, and
    does: cubes appear with two parents and the area drops below `4n+2`.
  * Blocks are two spine steps apart by construction (`tau m < d`, block length `d+1`). Allowing
    adjacent extra cubes must be able to break the tree, and does.

Prints a table; writes nothing.
"""
from __future__ import annotations

import itertools
import math
import random
import sys
from collections import Counter

#: DERIVED: the three forward unit steps of a directed cube-path in 3-D -- the same alphabet
#: `Floor.directed_paths_card` counts over. `3` is the dimension, not a choice.
E = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]

#: DERIVED: `(1/4) log 3` is the floor `Floor.floor_pos` and `CubeArea.boundary_card_eq` establish --
#: one unit of `log 3` of directional entropy per four units of area. It is the bar to clear.
KAPPA0_PATH = math.log(3) / 4


def rot1(a):
    """`CubeArea.rot1`: the next axis round."""
    return (a + 1) % 3


def rot2(a):
    """`CubeArea.rot2`: the axis after that."""
    return (a + 2) % 3


def step(p, a):
    e = E[a]
    return (p[0] + e[0], p[1] + e[1], p[2] + e[2])


def branch_dir(s, i, forbidden_rule=True):
    """`CubeBranch.branchDir`: rot1 of the spine direction, unless that IS the next spine
    direction, in which case rot2. With `forbidden_rule=False` this returns the axis the rule
    exists to avoid -- the negative control."""
    if not forbidden_rule:
        return s[i + 1] if s[i + 1] != s[i] else rot1(s[i])
    return rot2(s[i]) if rot1(s[i]) == s[i + 1] else rot1(s[i])


def build(d, k, s, t, forbidden_rule=True, allow_adjacent=False):
    """The cube set of `CubeBranch.config d k s t`, as a list (so repeats are visible)."""
    nsteps = (d + 1) * k + 1
    spine = [(0, 0, 0)]
    for j in range(nsteps):
        spine.append(step(spine[j], s[j]))
    extra = []
    for m in range(k):
        i = (d + 1) * m + t[m] if not allow_adjacent else t[m]
        extra.append(step(spine[i], branch_dir(s, i, forbidden_rule)))
    return spine + extra


def parents(c, cells):
    out = []
    for a in range(3):
        p = (c[0] - E[a][0], c[1] - E[a][1], c[2] - E[a][2])
        # DERIVED: `0` is the FLOOR of N^3, where the cubes live -- a cube with a negative
        # coordinate is not a cube, so this is the type's own bound and not a cutoff.
        if min(p) >= 0 and p in cells:
            out.append(a)
    return out


def boundary(cells):
    """The faces with exactly one owner -- `CubeArea.boundaryFaces`, named (axis, low corner)."""
    cnt = Counter()
    for c in cells:
        for a in range(3):
            cnt[(a, c)] += 1
            cnt[(a, step(c, a))] += 1
    # DERIVED: `1` is the ARITY of the owner count. `CubeArea.owners_one_or_two` proves every
    # face of a configuration has one owner or two, so "exactly one" IS the boundary and the
    # only other case is interior. Not a threshold.
    return frozenset(f for f, n in cnt.items() if n == 1)


def face_edges(f):
    """`CubeClosed.faceEdges`: a face spans the two axes its normal is not, and its four edges run
    along those two -- one pair at the corner, one pair a step along the other axis."""
    a, y = f
    r1, r2 = rot1(a), rot2(a)
    return {(r1, y), (r2, step(y, r1)), (r1, step(y, r2)), (r2, y)}


def boundary_is_connected(b):
    """`CubeConnected.boundary_connected`'s conclusion, checked rather than proved: the boundary's
    faces are connected through shared EDGES. The Lean for this family is NOT written -- CubeConnected
    descends on the path's own one-cube-per-layer indexing, which a tree does not have."""
    b = list(b)
    if not b:
        return True
    by_edge = {}
    for i, f in enumerate(b):
        for e in face_edges(f):
            by_edge.setdefault(e, []).append(i)
    seen, stack = {0}, [0]
    while stack:
        i = stack.pop()
        for e in face_edges(b[i]):
            for j in by_edge.get(e, ()):
                if j not in seen:
                    seen.add(j)
                    stack.append(j)
    return len(seen) == len(b)


def check(d, k, s, t, forbidden_rule=True, allow_adjacent=False):
    cubes = build(d, k, s, t, forbidden_rule, allow_adjacent)
    cs = set(cubes)
    n_expected = (d + 2) * k + 2
    is_tree = all(len(parents(c, cs)) == (0 if c == (0, 0, 0) else 1) for c in cs)
    b = boundary(cs)
    return dict(distinct=len(cs) == len(cubes), n=len(cs), n_expected=n_expected,
                tree=is_tree, area=len(b), area_expected=4 * len(cs) + 2,
                connected=boundary_is_connected(b), cubes=frozenset(cs), boundary=b)


# CHOSEN: `cap` only decides which (d, k) are small enough to enumerate EXHAUSTIVELY here; a
# larger cap checks more rungs and a smaller one fewer. It carries no rigour -- every rung it
# admits is checked completely, and the Lean proof is over all (d, k) regardless.
def exhaustive(d, k, forbidden_rule=True, cap=500_000):
    nsteps = (d + 1) * k + 1
    total = 3 ** nsteps * d ** k
    if total > cap:
        return None
    seen_cubes, seen_bdry = set(), set()
    first_bad = None
    for s in itertools.product(range(3), repeat=nsteps):
        for t in itertools.product(range(d), repeat=k):
            r = check(d, k, s, t, forbidden_rule)
            ok = (r["distinct"] and r["tree"] and r["connected"]
                  and r["n"] == r["n_expected"]
                  and r["area"] == r["area_expected"] == 4 * ((d + 2) * k + 2) + 2)
            if not ok and first_bad is None:
                first_bad = (s, t, r)
            seen_cubes.add(r["cubes"])
            seen_bdry.add(r["boundary"])
    return dict(total=total, first_bad=first_bad, configs=len(seen_cubes),
                surfaces=len(seen_bdry), area=4 * ((d + 2) * k + 2) + 2)


def sampled(d, k, trials, seed):
    rng = random.Random(seed)
    nsteps = (d + 1) * k + 1
    bad, seen = 0, set()
    for _ in range(trials):
        s = [rng.randrange(3) for _ in range(nsteps)]
        t = [rng.randrange(d) for _ in range(k)]
        r = check(d, k, s, t)
        if not (r["distinct"] and r["tree"] and r["connected"] and r["n"] == r["n_expected"]
                and r["area"] == 4 * ((d + 2) * k + 2) + 2):
            bad += 1
        seen.add(r["boundary"])
    return bad, len(seen), 4 * ((d + 2) * k + 2) + 2


def density(d):
    """`CubeBranch.branch_density_limit`'s value."""
    return ((d + 1) * math.log(3) + math.log(d)) / (4 * (d + 2))


def main():
    rc = 0
    print(f"path floor (1/4) log 3            = {KAPPA0_PATH:.9f}")
    print(f"branched floor at d = 10          = {density(10):.9f}   "
          f"= (11 log 3 + log 10)/48")
    print()

    print("--- exhaustive: EVERY (sigma, tau) checked for tree / area / connected / injectivity ---")
    for d, k in ((4, 1), (1, 2), (2, 2), (4, 2)):
        r = exhaustive(d, k)
        if r is None:
            print(f"d={d} k={k}: parameter set too large, skipped")
            continue
        exp = 3 ** ((d + 1) * k + 1) * d ** k
        good = (r["first_bad"] is None and r["configs"] == exp and r["surfaces"] == exp
                and r["total"] == exp)
        print(f"d={d} k={k}: {r['total']:>7} parameters, {r['configs']:>7} distinct cube sets, "
              f"{r['surfaces']:>7} distinct surfaces, every area {r['area']}   "
              f"{'OK' if good else '*** FAIL ***'}")
        if not good:
            rc = 1

    print()
    print("--- sampled at larger k (d = 10, the best d) ---")
    for k in range(1, 9):
        bad, nsurf, area = sampled(10, k, 1200, seed=k)
        # DERIVED: `0` violations is the claim itself -- the family is a tree of the stated area
        # for EVERY parameter, so a single violation refutes it. Not a tolerance.
        verdict = "OK" if bad == 0 else "*** FAIL ***"
        print(f"d=10 k={k}: 1200 random parameters, violations={bad}, "
              f"distinct surfaces {nsurf}, area {area}   {verdict}")
        if bad:
            rc = 1

    print()
    print("--- the density itself, at d = 10, k = 1..8 (what CubeBranch.branch_density_limit takes"
          " the limit of) ---")
    for k in range(1, 9):
        cnt = 3 ** (11 * k + 1) * 10 ** k
        area = 4 * (12 * k + 2) + 2
        print(f"  k={k}: count = 3^{11*k+1} * 10^{k} = {cnt:.6e}, area = {area}, "
              f"log(count)/area = {math.log(cnt) / area:.9f}")
    print(f"  limit  (11 log 3 + log 10)/48                                    = "
          f"{density(10):.9f}")
    print(f"  path   (1/4) log 3                                               = "
          f"{KAPPA0_PATH:.9f}")

    print()
    print("--- NEGATIVE CONTROL 1: the forbidden branch axis b = s(i+1) must break the tree ---")
    for d, k in ((4, 1), (2, 2), (1, 2)):
        r = exhaustive(d, k, forbidden_rule=False)
        if r is None:
            print(f"d={d} k={k}: parameter set too large, skipped")
            continue
        broke = r["first_bad"] is not None
        print(f"d={d} k={k}: {'BROKEN as predicted' if broke else '*** unexpectedly intact ***'}"
              + (f"  (a cube has two parents: tree={r['first_bad'][2]['tree']}, "
                 f"area {r['first_bad'][2]['area']} vs {r['first_bad'][2]['area_expected']})"
                 if broke else ""))
        if not broke:
            rc = 1

    print()
    print("--- NEGATIVE CONTROL 2: adjacent extra cubes (block spacing dropped) ---")
    found = False
    for s in itertools.product(range(3), repeat=(4 + 1) * 2 + 1):
        r = check(4, 2, s, (0, 1), allow_adjacent=True)
        if not (r["tree"] and r["distinct"] and r["area"] == r["area_expected"]):
            found = True
            break
    print(f"adjacent positions (0,1): {'BROKEN as predicted' if found else '*** intact ***'}")
    if not found:
        rc = 1

    print()
    print("--- the density, and where it beats the path floor ---")
    print("   d   count per block      density               beats (1/4) log 3?")
    for d in range(1, 16):
        val = density(d)
        verdict = ("YES" if val > KAPPA0_PATH else
                   # CHOSEN: `1e-12` separates the EXACT equality at d = 3 from float noise in
                   # two logarithms. The equality is algebraic ((d+1)log3 + log 3 = (d+2)log3 at
                   # d = 3), so any tolerance above float epsilon reports it and none decides it.
                   "EQUAL  <-- negative control" if abs(val - KAPPA0_PATH) < 1e-12 else
                   "no     <-- negative control")
        print(f"  {d:2}   3^{d+1} * {d:<3} = {3**(d+1)*d:<12}  {val:.9f}   {verdict}")
    best = max(range(1, 60), key=density)
    print(f"\nbest d = {best}, kappa_0 >= {density(best):.9f}")
    # DERIVED: `3` is the condition `log d > log 3` written as an integer -- the density exceeds the
    # path floor exactly when the extra cube buys more entropy than a spine step does, and it costs
    # the same `4` of area. Not a tolerance.
    assert abs(density(3) - KAPPA0_PATH) < 1e-12, "d = 3 must reproduce the path floor exactly"
    assert density(2) < KAPPA0_PATH and density(4) > KAPPA0_PATH, "the crossing must be at d = 3"
    print("[validation] d = 3 reproduces (1/4) log 3 exactly; d = 2 loses, d = 4 wins  OK")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
