"""Frozen links in the SU(2) heat bath: the boundary-condition option leaves the unconstrained chain
unchanged and holds the frozen links exactly."""
import numpy as np

import lattice_generator as G

# CHOSEN: the smallest even lattice the checkerboard heat bath accepts; the checks are identities.
DIMS = (4, 4, 4, 4)


# CHOSEN: any seed; the two chains compared share it.
def _chain(frozen, seed=3):
    b = G._Backend(None).seed(seed)
    q = G._su2_init(b, DIMS, ())
    start = q.copy()
    for _ in range(3):
        G._su2_hb_sweep(b, q, DIMS, 2.3, None, n_or=1, frozen=frozen)
    return start, q


def test_no_frozen_links_is_the_unconstrained_chain():
    _s0, q0 = _chain(None)
    _s1, q1 = _chain(np.zeros((*DIMS, G.D), dtype=bool))
    assert np.array_equal(q0, q1)


def test_frozen_links_hold_and_free_links_move():
    frozen = np.zeros((*DIMS, G.D), dtype=bool)
    frozen[..., 0, :3] = True                       # the spatial links of the time slice t = 0
    start, q = _chain(frozen)
    assert np.array_equal(q[frozen], start[frozen])
    assert not np.array_equal(q[~frozen], start[~frozen])
    assert np.allclose(np.linalg.norm(q, axis=-1), 1.0)
