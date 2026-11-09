"""Rotational invariance of the observer's energy-density two-point function, read per shard (CPU).

The observer of ObserverFlow.obsConfFlow (observer_step.step: BlockSU2.blockLink on the same lattice, all four
directions, every link from the old configuration) is run n times at constant c on each configuration. On the
smeared links the clover energy density
    e(x) = sum_{mu<nu} (1/4) sum_{the four plaquettes of plane (mu, nu) touching x} (1 - (1/2) tr P)
is formed: a field fixed by every axis permutation and every axis reflection about x (ContinuumHypercubic.HypScalar),
so its two-point function depends on the displacement only through the hypercubic orbit, and the lattice
anisotropy is the difference between orbits of equal Euclidean length.

The step runs on a component-major copy of the links (fast_step: four contiguous real arrays per direction, the
same quaternion products, staples and normalisation as observer_step.step, in float32); `python rot_read.py
--check CAMPAIGN_DIR` compares it with observer_step.step and the clover density with observer_step.planes;
`python rot_read.py --scale CAMPAIGN_DIR nmax nchains` prints n^2 <e>(n), the observer's own scale.

For every displacement class v (VECS) the read is the volume average of e(x) e(x + u) averaged over the distinct
signed permutations u of v, u and -u counted once (on the periodic lattice the two averages are equal), each
average the library's periodic lagged covariance with nothing subtracted (entroptics_adapter.torus_product). Output per
chain of each shard, shape (2 + len(VECS),): [mean e, mean e^2, <e e(+u)> for each v]. rot_agg.py forms the connected
function with the ensemble mean subtracted and jackknifes over blocks.

    python rot_read.py CAMPAIGN_DIR c nsteps OUT_DIR [maxshards] [workers]
Reads verified.list when present, else SHA256SUMS; a shard whose output exists is skipped.

The torch path (OBS_DEVICE set to a torch device, e.g. cuda or cpu; OBS_FP 32 default): observer_step.step on the
stored (chain, x, y, z, t, mu, 4) layout at the backend precision, the clover density in float64 from
observer_step.planes; the density is then copied to the host once and the image products are read there by the
library, as on the CPU path (image_row: entroptics_adapter.torus_product). One process, chains in order (workers is ignored);
the output file, its name, shape (2 + len(VECS),) and dtype float64 are those of the CPU path. Unset (or
OBS_DEVICE=numpy) runs the CPU path above.
"""
import itertools
import os
import sys
import time

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")

import numpy as np
from multiprocessing import Pool

import observer_step as O
from lattice_generator import _Backend

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code: the adapter
import entroptics_adapter as E  # noqa: E402

# displacement classes in lattice units; equal-length groups are the anisotropy test
# CHOSEN: the axis up to 14, the three diagonal directions, and off-axis integer vectors whose length is an
# integer (rot_agg.PAIRS); a coverage budget of displacements, not derived. rot_agg.load_vecs parses this
# literal from the source text, so it stays a single bracketed list
VECS = [
    (1, 0, 0, 0), (2, 0, 0, 0), (3, 0, 0, 0), (4, 0, 0, 0), (5, 0, 0, 0), (6, 0, 0, 0), (7, 0, 0, 0),
    (8, 0, 0, 0), (9, 0, 0, 0), (10, 0, 0, 0), (11, 0, 0, 0), (12, 0, 0, 0), (13, 0, 0, 0), (14, 0, 0, 0),
    (1, 1, 0, 0), (2, 2, 0, 0), (3, 3, 0, 0), (4, 4, 0, 0), (5, 5, 0, 0), (6, 6, 0, 0), (7, 7, 0, 0),
    (8, 8, 0, 0),
    (1, 1, 1, 0), (2, 2, 2, 0), (3, 3, 3, 0), (4, 4, 4, 0), (5, 5, 5, 0), (6, 6, 6, 0),
    (1, 1, 1, 1), (2, 2, 2, 2), (3, 3, 3, 3), (4, 4, 4, 4), (5, 5, 5, 5), (6, 6, 6, 6),
    (2, 2, 1, 0),                                   # |v| = 3
    (3, 4, 0, 0), (4, 2, 2, 1),                     # |v| = 5
    (4, 4, 2, 0), (5, 3, 1, 1),                     # |v| = 6
    (6, 3, 2, 0), (4, 4, 4, 1),                     # |v| = 7
    (6, 6, 3, 0), (8, 4, 1, 0),                     # |v| = 9
    (6, 8, 0, 0),                                   # |v| = 10
    (8, 8, 4, 0),                                   # |v| = 12
]


def images(v):
    """The distinct signed permutations of v, one of each pair {u, -u}."""
    seen, out = set(), []
    for p in itertools.permutations(v):
        for s in itertools.product((1, -1), repeat=4):
            u = tuple(si * pi for si, pi in zip(s, p))
            if u in seen or tuple(-x for x in u) in seen:
                continue
            seen.add(u)
            out.append(u)
    return out


def _qm(a, b):
    a0, a1, a2, a3 = a
    b0, b1, b2, b3 = b
    return (a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3,
            a0 * b1 + a1 * b0 - a2 * b3 + a3 * b2,
            a0 * b2 + a2 * b0 - a3 * b1 + a1 * b3,
            a0 * b3 + a3 * b0 - a1 * b2 + a2 * b1)


def _qc(a):
    return (a[0], -a[1], -a[2], -a[3])


def _r(a, s, ax):
    return tuple(np.roll(x, s, ax) for x in a)


def split(q):
    """Batch-of-one links (1, X, Y, Z, T, 4, 4) -> L[mu][k], contiguous float32 arrays (X, Y, Z, T)."""
    return [[np.ascontiguousarray(q[0, ..., mu, k], dtype=np.float32) for k in range(4)] for mu in range(4)]


def fast_step(L, c):
    """observer_step.step on the component-major layout: every link from the old configuration."""
    new = []
    for mu in range(4):
        U = tuple(L[mu])
        V = [x.copy() for x in U]
        for nu in range(4):  # NOT A READ: the six staples
            if nu == mu:
                continue
            Un = tuple(L[nu])
            up = _qm(_qm(Un, _r(U, -1, nu)), _qc(_r(Un, -1, mu)))
            Unm = _r(Un, 1, nu)
            dn = _qm(_qm(_qc(Unm), _r(U, 1, nu)), _r(Unm, -1, mu))
            for k in range(4):
                V[k] += np.float32(c) * (up[k] + dn[k])
        nrm = np.sqrt(V[0] * V[0] + V[1] * V[1] + V[2] * V[2] + V[3] * V[3])
        new.append([x / nrm for x in V])
    return new


def clover_fast(L):
    """The clover energy density on the component-major layout, float64, shape (X, Y, Z, T)."""
    e = 0.0
    for mu in range(4):
        for nu in range(mu + 1, 4):  # NOT A READ: the plaquette planes
            P = _qm(_qm(tuple(L[mu]), _r(L[nu], -1, mu)), _qc(_r(L[mu], -1, nu)))
            p = 1.0 - _qm(P, _qc(tuple(L[nu])))[0].astype(np.float64)
            e = e + 0.25 * (p + np.roll(p, 1, mu) + np.roll(p, 1, nu) + np.roll(np.roll(p, 1, mu), 1, nu))
    return e


def clover(bg, q):
    """The clover energy density of a batch-of-one configuration, float64, shape (X, Y, Z, T); numpy or torch."""
    e = 0.0
    for (mu, nu), p in zip([(m, n) for m in range(4) for n in range(m + 1, 4)], O.planes(bg, q)):
        p = p[0]
        am, an = mu - 4, nu - 4
        e = e + 0.25 * (p + bg.roll(p, 1, am) + bg.roll(p, 1, an) + bg.roll(bg.roll(p, 1, am), 1, an))
    return e


torch_device = O.torch_device


def torch_row(tb, q, nst, cw, img):
    """The torch path for one chain q (batch of one, observer_step.chain): (row, e, q) with row the CPU path's
    output row as a list of floats, e the clover density on the device (float64) and q the stepped links."""
    for _ in range(nst):  # NOT A READ: the observer's n steps
        q = O.step(tb, q, cw)
    e = clover(tb, q)
    return image_row(e, img), e, q


def image_row(e, img):
    """[mean e, mean e^2, <e(x) e(x + u)> averaged over the images u of each class]: the raw periodic products read
    by entroptics_adapter.torus_product (the library's lagged covariance on the ring, nothing subtracted)."""
    e = np.asarray(e.detach().cpu().numpy() if hasattr(e, "detach") else e, dtype=np.float64)
    row = [float(e.mean()), E.torus_product(e, (0, 0, 0, 0))]
    for ims in img:
        row.append(sum(E.torus_product(e, u) for u in ims) / len(ims))
    return row


bg = _Backend(None)
# DERIVED: argv[1] is the first argument, the mode flag position (usage)
CHECK = len(sys.argv) > 1 and sys.argv[1] == "--check"
# DERIVED: argv[1] is the first argument, the mode flag position (usage)
if not CHECK and not (len(sys.argv) > 1 and sys.argv[1] == "--scale"):
    camp, cw, nst, out = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
IMG = [images(v) for v in VECS]


def one(job):
    """One chain of one shard: n observer steps, then the image-averaged products. Writes (2 + len(VECS),)."""
    name, ch = job
    dst = os.path.join(out, name.replace(".npy", f"_ch{ch}_c{cw}_n{nst}_rot.npy"))
    if os.path.exists(dst):
        return dst
    links = np.load(os.path.join(camp, name), mmap_mode="r")
    L = split(np.asarray(links[ch:ch + 1]))
    del links
    for _ in range(nst):  # NOT A READ: the observer's n steps
        L = fast_step(L, cw)
    e = clover_fast(L)
    del L
    row = image_row(e, IMG)
    np.save(dst + ".tmp.npy", np.array(row))
    os.replace(dst + ".tmp.npy", dst)
    return dst


def one_torch(tb, job):
    """one() on the torch path: the same output file, name and layout."""
    name, ch = job
    dst = os.path.join(out, name.replace(".npy", f"_ch{ch}_c{cw}_n{nst}_rot.npy"))
    if os.path.exists(dst):
        return dst
    t0 = time.time()
    links = np.load(os.path.join(camp, name), mmap_mode="r")
    q = O.chain(tb, links, ch)
    del links
    row, _, _ = torch_row(tb, q, nst, cw, IMG)
    np.save(dst + ".tmp.npy", np.array(row))
    os.replace(dst + ".tmp.npy", dst)
    return f"{dst} {time.time() - t0:.1f}s"


def check(campdir):
    """fast_step against observer_step.step (three steps), clover_fast against clover."""
    name = O.shards(campdir, prefer_verified=False)[0]
    links = np.load(os.path.join(campdir, name), mmap_mode="r")
    q = O.chain(bg, links, 0)
    L = split(q)
    for _ in range(3):
        q = O.step(bg, q, 0.15)
        L = fast_step(L, 0.15)
    d = max(float(np.abs(q[0, ..., mu, k] - L[mu][k]).max()) for mu in range(4) for k in range(4))
    e1, e2 = clover(bg, q), clover_fast(L)
    print("max link diff", d, "max clover diff", float(np.abs(e1 - e2).max()), "mean e", float(e1.mean()))


def scale(campdir, nmax, nch):
    """The observer's own scale (paper section 3): n^2 <e>(n) along the steps, <e> the six-plane plaquette density,
    averaged over the first nch chains of the first shard; prints n, <e>, n^2 <e>."""
    name = O.shards(campdir, prefer_verified=False)[0]
    links = np.load(os.path.join(campdir, name), mmap_mode="r")
    Ls = [split(np.asarray(links[ch:ch + 1])) for ch in range(nch)]
    for n in range(1, nmax + 1):
        Ls = [fast_step(L, 0.15) for L in Ls]
        m = float(np.mean([clover_fast(L).mean() for L in Ls]))
        print(n, m, n * n * m, flush=True)


if __name__ == "__main__":
    if CHECK:
        check(sys.argv[2])
        sys.exit(0)
    # DERIVED: argv[1] is the first argument, the mode flag position (usage)
    if len(sys.argv) > 1 and sys.argv[1] == "--scale":
        scale(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]))
        sys.exit(0)
    maxsh = O.opt(5, 10 ** 9)
    workers = O.opt(6, 4)
    os.makedirs(out, exist_ok=True)
    names = O.shards(camp, maxsh, prefer_verified=False)
    nch = np.load(os.path.join(camp, names[0]), mmap_mode="r").shape[0]
    jobs = [(n, ch) for n in names for ch in range(nch)]
    if torch_device():
        tb = O.backend()
        for job in jobs:  # NOT A READ: one device, chains in order
            print(one_torch(tb, job), flush=True)
        sys.exit(0)
    with Pool(workers) as p:
        for d in p.imap_unordered(one, jobs):
            print(d, flush=True)
