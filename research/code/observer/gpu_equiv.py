"""The torch paths of rot_read.py and cell_read.py against their CPU paths, on one stored configuration.

    python gpu_equiv.py inproc CAMPAIGN_DIR nsteps [perturb]
        chain 0 of the first shard, n observer steps at c = 0.15 on both paths: the stepped links (torch
        observer_step.step against rot_read.fast_step and against numpy observer_step.step), the clover density
        (rot_read.clover on torch against rot_read.clover_fast), the six-plane density (torch against numpy
        observer_step.energy_density), the rot row and its connected part G(v) = row[2 + i] - row[0]^2.
        `perturb` replaces one link of the torch input (site 0, direction 0) by a different unit quaternion:
        the negative control, which must FAIL.
    python gpu_equiv.py files DIR_A DIR_B
        every *_rot.npy / *.npz present in both directories: same keys, shapes and dtypes; max abs and max rel
        differences per array.

The torch device and precision are OBS_DEVICE (default cpu here) and OBS_FP (default 32). The gate (exit 1 when
it fails): inproc, the largest difference of the stepped links and of both densities in units of the largest
reference value, and the largest relative difference of the rot row, below TOL (OBS_TOL, default 1e-4); files,
the same layout (keys, order, shapes, dtypes) and the largest normalised difference of every array below TOL
(the connected G is printed, not gated). Per-element relative differences are printed; on link components
near 0 they are not a measure of agreement.
"""
import glob
import os
import sys

os.environ.setdefault("OBS_DEVICE", "cpu")
os.environ.setdefault("OMP_NUM_THREADS", "1")

import numpy as np

sys.argv, _argv = ["rot_read.py", "--check"], sys.argv  # import rot_read without its command line
import rot_read as R  # noqa: E402
sys.argv = _argv
import observer_step as O  # noqa: E402
from lattice_generator import _Backend  # noqa: E402

TOL = float(os.environ.get("OBS_TOL", 1e-4))


def diff(a, b):
    a, b = np.asarray(a, dtype=np.float64), np.asarray(b, dtype=np.float64)
    d = np.abs(a - b)
    return float(d.max()), float((d / np.maximum(np.abs(b), 1e-300)).max()), float(d.max() / np.abs(b).max())


def inproc(camp, nst, perturb):
    nb = _Backend(None)
    tb = O.backend()
    name = O.shards(camp, prefer_verified=False)[0]
    links = np.load(os.path.join(camp, name), mmap_mode="r")
    qn = O.chain(nb, links, 0)                          # numpy float32, batch of one
    qt = O.chain(tb, links, 0)
    if perturb:
        u = np.array([0.6, 0.0, 0.8, 0.0], dtype=np.float32)
        qt[0, 0, 0, 0, 0, 0] = tb.t.as_tensor(R._qm(tuple(qn[0, 0, 0, 0, 0, 0]), tuple(u)), dtype=tb.f)
    L = R.split(qn)
    qs = qn
    for _ in range(nst):  # NOT A READ: the n steps on the two CPU paths
        L = R.fast_step(L, 0.15)
        qs = O.step(nb, qs, 0.15)
    rowt, et_dev, qt = R.torch_row(tb, qt, nst, 0.15, R.IMG)  # the torch path under test
    qt_np = tb.to_numpy(qt)
    Lq = np.stack([np.stack(L[mu], -1) for mu in range(4)], -2)[None]
    rep = {}
    rep["links vs fast_step (abs, rel, abs/max)"] = diff(qt_np, Lq)
    rep["links vs numpy step"] = diff(qt_np, qs)
    ec = R.clover_fast(L)
    rep["clover density"] = diff(tb.to_numpy(et_dev), ec)
    e6t = tb.to_numpy(O.energy_density(tb, qt))
    e6n = O.energy_density(nb, qs)
    rep["six-plane density"] = diff(e6t, e6n)
    rowc = [ec.mean(), (ec * ec).mean()]  # rot_read.one's row on the CPU density
    for ims in R.IMG:
        acc = 0.0
        for u in ims:
            acc += float((ec * np.roll(ec, u, axis=(0, 1, 2, 3))).mean())
        rowc.append(acc / len(ims))
    rowc, rowt = np.array(rowc), np.array(rowt)
    rep["rot row"] = diff(rowt, rowc)
    Gc, Gt = rowc[2:] - rowc[0] ** 2, rowt[2:] - rowt[0] ** 2
    rep["rot connected G(v)"] = diff(Gt, Gc)
    print(f"{camp} {name} chain 0, n = {nst}, device {tb.dev} fp {os.environ.get('OBS_FP', '32')}, "
          f"perturb = {perturb}, <e> = {rowc[0]:.6g}")
    for k, (a, r, s) in rep.items():
        print(f"  {k:40s} max abs {a:.3e}  max rel {r:.3e}  abs/max|ref| {s:.3e}")
    gate = max([rep[k][2] for k in ("links vs fast_step (abs, rel, abs/max)", "links vs numpy step",
                                     "clover density", "six-plane density")] + [rep["rot row"][1]])
    ok = gate < TOL
    print(f"GATE max(abs/max|ref| of links and densities, rel of the rot row) = {gate:.3e} vs TOL {TOL:g}: "
          f"{'PASS' if ok else 'FAIL'}")
    return ok


def files(da, db):
    ok = True
    pa = sorted(os.path.basename(f) for f in glob.glob(os.path.join(da, "*_rot.npy")) + glob.glob(os.path.join(da, "*.npz")))
    common = [f for f in pa if os.path.exists(os.path.join(db, f))]
    print(f"{len(common)} files in both {da} and {db}")
    worst = {}
    for f in common:
        A, B = np.load(os.path.join(da, f)), np.load(os.path.join(db, f))
        if f.endswith(".npz"):
            if list(A.files) != list(B.files):
                print("  KEYS DIFFER", f, A.files, B.files)
                ok = False
                continue
            items = [(k, A[k], B[k]) for k in A.files]
        else:
            items = [("row", A, B)]
            items.append(("G", A[2:] - A[0] ** 2, B[2:] - B[0] ** 2))
        for k, a, b in items:
            if a.shape != b.shape or a.dtype != b.dtype:
                print("  LAYOUT DIFFERS", f, k, a.shape, a.dtype, b.shape, b.dtype)
                ok = False
                continue
            d = diff(a, b)
            w = worst.get(k, (0.0, 0.0, 0.0))
            worst[k] = tuple(max(x, y) for x, y in zip(w, d))
            print(f"  {f} {k:5s} {str(a.shape):24s} {a.dtype}  max abs {d[0]:.3e}  max rel {d[1]:.3e}  abs/max {d[2]:.3e}")
    for k, (a, r, s) in worst.items():
        print(f"WORST {k:5s} max abs {a:.3e}  max rel {r:.3e}  abs/max|ref| {s:.3e}")
    print("LAYOUT", "PASS" if ok else "FAIL")
    gate = max([s for k, (a, r, s) in worst.items() if k != "G"] + [0.0])
    print(f"GATE max abs/max|ref| over arrays (G reported, not gated) = {gate:.3e} vs TOL {TOL:g}: "
          f"{'PASS' if gate < TOL else 'FAIL'}")
    return ok and gate < TOL and bool(common)


if __name__ == "__main__":
    if sys.argv[1] == "inproc":
        # DERIVED: 4 is [perturb]'s position in the usage line (inproc CAMPAIGN_DIR nsteps [perturb])
        good = inproc(sys.argv[2], int(sys.argv[3]), len(sys.argv) > 4 and sys.argv[4] == "perturb")
    else:
        good = files(sys.argv[2], sys.argv[3])
    sys.exit(0 if good else 1)
