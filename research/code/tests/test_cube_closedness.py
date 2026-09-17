"""The cube-boundary theorems, recomputed independently of Lean.

WHAT THIS IS FOR. `MassGap.CubeClosed.edge_parity` and `MassGap.CubeArea.boundary_card_eq` are
machine-checked, so their truth is not in question. What a kernel cannot check is whether the
statement means what the paper says it means: `boundaryFaces`, `edgeFaces` and `step` are definitions
in that file, and a theorem about them is only a theorem about cube surfaces if those definitions are
the ones intended. So the same combinatorics is written again here, from the geometry rather than
from the Lean, and the two are compared on concrete configurations.

THE NEGATIVE CONTROL IS THE POINT. A parity check passes trivially if it is examining nothing. So a
single face is removed from a boundary and the parity MUST break -- and where it does not, the reason
must be the one the theorem states, not an accident. Measured: removing a face breaks the parity in
about five cases in eight, and EVERY case where it does not is a face all of whose edges lie outside
the theorem's scope. That is what makes the scope claim ("interior edges") a measurement rather than
a hedge.

WHAT "INTERIOR" MEANS, and getting it wrong is easy. For a face `(a, x)` the four edges run along the
two axes OTHER than `a`, and an edge along `b` is interior only when both its transverse coordinates
are at least one -- where one of those transverse axes is `a` itself. Every corner of the face shares
its `a` coordinate, so `x[a] == 0` makes all four edges non-interior at once. Testing the other two
coordinates instead was the first guess here, and it left 47 of 77 survivors unexplained.
"""
from __future__ import annotations

import itertools
import random

#: DERIVED: the number of axes the cube lattice of `CubeArea` is built on -- `Fin 3`, the step
#: alphabet `Floor.directed_paths_card` counts over. Not a size, an arity.
BOX = 3


def step(a, x):
    y = list(x)
    y[a] += 1
    return tuple(y)


def faces(x):
    """The six faces of cube `x`, as `(axis, corner)` -- `CubeArea.faces`."""
    return [(a, x) for a in range(BOX)] + [(a, step(a, x)) for a in range(BOX)]


def boundary(cubes):
    """Faces owned by exactly one cube -- `CubeArea.boundaryFaces`."""
    owners = {}
    for x in cubes:
        for f in faces(x):
            owners.setdefault(f, []).append(x)
    # DERIVED: `1` is the definition of a boundary face -- one owner means the two sides of it
    # disagree about being inside. `owners_one_or_two` proves there is no third case.
    return {f for f, o in owners.items() if len(o) == 1}


def edge_faces(a1, a2, w):
    """The four faces meeting an edge, indexed by stepping FORWARD from a base cube `w`.

    The same parametrisation `CubeClosed.edgeFaces` uses, and for the same reason: a cube one step
    back need not exist in the nonnegative octant.
    """
    return [(a1, step(a1, w)),
            (a2, step(a2, step(a1, w))),
            (a1, step(a1, step(a2, w))),
            (a2, step(a2, w))]


def odd_interior_edges(cubes, faceset):
    """Interior edges lying in an ODD number of `faceset` -- what the theorem forbids.

    The window is DERIVED from the configuration rather than fixed: only a base cube whose edge can
    touch `cubes` matters, so `max coordinate + 2` covers them all. A fixed window silently stops
    looking, which is how one negative-control case went unexplained here before.
    """
    reach = max((max(x) for x in cubes), default=0) + 2
    bad = []
    for w in itertools.product(range(reach), repeat=BOX):
        for a1, a2 in itertools.combinations(range(BOX), 2):
            if sum(1 for f in edge_faces(a1, a2, w) if f in faceset) % 2:
                bad.append((a1, a2, w))
    return bad


def cube_path(steps):
    """The cube configuration of a directed path -- `Floor.cubePos` over `range (k+1)`."""
    x = tuple([0] * BOX)
    out = [x]
    for s in steps:
        x = step(s, x)
        out.append(x)
    return out


def test_every_interior_edge_of_a_boundary_is_even():
    """`CubeClosed.edge_parity`, recomputed: no interior edge lies in an odd number of faces."""
    rng = random.Random(20260917)
    for trial in range(120):
        if trial % 2:
            cubes = {tuple(rng.randrange(4) for _ in range(BOX))
                     for _ in range(rng.randrange(1, 10))}
        else:
            cubes = set(cube_path([rng.randrange(BOX) for _ in range(rng.randrange(1, 7))]))
        bad = odd_interior_edges(cubes, boundary(cubes))
        assert not bad, (
            f"an interior edge lies in an odd number of boundary faces, which `edge_parity` "
            f"forbids: cubes={sorted(cubes)}, first offending edge={bad[0]}")


def test_removing_one_face_breaks_the_parity_or_the_scope_says_why():
    """PROOF THAT THE CHECK ABOVE IS NOT VACUOUS, and that its scope claim is exact.

    Remove one face from a boundary. Either the parity breaks -- so the check can fail -- or every
    edge that face touches is outside the theorem's scope, which is the only way it may survive.
    """
    rng = random.Random(4477)
    broke = scoped = 0
    for _ in range(80):
        cubes = set(cube_path([rng.randrange(BOX) for _ in range(rng.randrange(2, 7))]))
        faceset = boundary(cubes)
        if not faceset:
            continue
        victim = sorted(faceset)[rng.randrange(len(faceset))]
        if odd_interior_edges(cubes, faceset - {victim}):
            broke += 1
            continue
        a, corner = victim
        # DERIVED: `0` is the floor of the nonnegative octant -- the coordinate below which no cube
        # exists -- so it is where an edge stops having four cubes around it, not a tolerance.
        assert corner[a] == 0, (
            f"removing {victim} left every interior edge even, and it is NOT a face whose edges are "
            f"all outside the scope -- so the parity check is passing on something it should catch. "
            f"cubes={sorted(cubes)}")
        scoped += 1
    assert broke, "removing a face never broke the parity; the check above proves nothing"
    assert broke > scoped, (
        f"only {broke} of {broke + scoped} removals broke the parity; the check is mostly being "
        f"satisfied by the excluded scope rather than by the theorem")


def test_the_boundary_area_is_four_k_plus_six():
    """`CubeArea.boundary_card_eq`, recomputed: a `k`-step directed path bounds `4k+6` faces."""
    rng = random.Random(991)
    for k in (0, 1, 2, 3, 5, 8, 13, 21):
        cubes = set(cube_path([rng.randrange(BOX) for _ in range(k)]))
        assert len(cubes) == k + 1, f"a directed path of {k} steps should visit {k + 1} cubes"
        assert len(boundary(cubes)) == 4 * k + 6, (
            f"a {k}-step directed path bounds {len(boundary(cubes))} faces, not {4 * k + 6}")


def test_distinct_paths_bound_distinct_surfaces_exhaustively():
    """`CubeArea.boundaryFaces_cubeConfig_injective`, checked on EVERY path, not a sample.

    This is the theorem the entropy floor's count rests on: if two paths bounded the same surface the
    `3^k` would be an over-count and `κ₀` would be too large. Small `k` is enough to be decisive
    because a collision would be a local coincidence between two walks, and there are `3^k` of them
    to try — 1093 paths over `k = 0..6`, every pair distinguished.

    It also checks the count itself: the number of distinct boundaries IS `3^k`
    (`Floor.directed_surface_count` transported along the boundary map).
    """
    for k in range(7):
        seen = {}
        for steps in itertools.product(range(BOX), repeat=k):
            surface = frozenset(boundary(set(cube_path(list(steps)))))
            clash = seen.get(surface)
            assert clash is None, (
                f"two distinct {k}-step paths bound the SAME surface: {clash} and {steps}. The "
                f"entropy floor counts 3^k surfaces, so this would make the count an over-count")
            seen[surface] = steps
        assert len(seen) == BOX ** k, (
            f"{len(seen)} distinct surfaces from {BOX ** k} paths at k={k}")


def plane_of(a):
    """`SurfaceEmbed.planeOf`: the two axes the normal is not, in cyclic order."""
    return ((a + 1) % BOX, (a + 2) % BOX)


def site_of(n, x):
    """`SurfaceEmbed.siteOf`: the corner placed in the time-zero slice of a periodic 4-box."""
    return tuple((x[mu] % n) if mu < BOX else 0 for mu in range(4))


def face_to_plaq(n, f):
    """`SurfaceEmbed.faceToPlaq`."""
    a, corner = f
    return (plane_of(a), site_of(n, corner))


def test_the_embedding_is_faithful_and_preserves_the_area():
    """`SurfaceEmbed.card_plaqSurface`: the 4-D image of a `k`-step boundary has `4k+6` plaquettes.

    The embedding is only injective while the path fits the box, and this checks the area survives it
    at every `k` the hypothesis allows.
    """
    rng = random.Random(5150)
    for k in (0, 1, 2, 3, 5, 8):
        n = k + 2                      # the smallest box the hypothesis `k + 1 < n` permits
        cubes = set(cube_path([rng.randrange(BOX) for _ in range(k)]))
        faceset = boundary(cubes)
        image = {face_to_plaq(n, f) for f in faceset}
        assert len(image) == len(faceset) == 4 * k + 6, (
            f"at k={k}, n={n} the boundary has {len(faceset)} faces and its image {len(image)} "
            f"plaquettes; both should be {4 * k + 6}, so the embedding lost or merged faces")


def test_the_box_hypothesis_is_load_bearing():
    """PROOF THAT `k + 1 < n` IS DOING WORK, not decorating the statement.

    `siteOf` reduces each coordinate modulo `n`. Shrink the box below what the hypothesis allows and
    the embedding must start identifying distinct faces -- otherwise the hypothesis could be dropped
    and the theorem would be stronger than it claims.
    """
    collided = False
    for k in range(2, 12):
        cubes = set(cube_path([0] * k))            # a straight path, extent k along one axis
        faceset = boundary(cubes)
        tight = {face_to_plaq(k + 2, f) for f in faceset}
        assert len(tight) == len(faceset), (
            f"at the permitted box n={k + 2} the embedding already collides at k={k}")
        too_small = {face_to_plaq(max(k, 2), f) for f in faceset}   # n <= k, hypothesis violated
        if len(too_small) < len(faceset):
            collided = True
    assert collided, (
        "shrinking the box below `k + 1 < n` never made the embedding collide, so the hypothesis is "
        "not what makes it injective and the theorem is understated")


def test_the_origin_faces_are_always_on_the_boundary():
    """`CubeClosed.origin_face_mem_boundary`: the fixed plaquette every directed surface passes."""
    rng = random.Random(1213)
    for _ in range(60):
        cubes = set(cube_path([rng.randrange(BOX) for _ in range(rng.randrange(0, 9))]))
        faceset = boundary(cubes)
        for a in range(BOX):
            assert (a, tuple([0] * BOX)) in faceset, (
                f"the origin's low face on axis {a} is not on the boundary of {sorted(cubes)}; "
                f"every directed path starts at the origin, so it must be")
