"""Checks of the SU(N) observer step and readers in observer_step.py, on numpy and (when importable) torch.

  1. N = 2: the SU(N) code on phi(q) (lattice_generator._su2_matrix) against phi of the quaternion code on q,
     for the step, the plaquette energy, the slice sums and the spatial APE smearing;
  2. the SU(2) path bit-identical to observer_step.py at git HEAD (`OBS_HEAD` names a copy of that file);
  3. gauge covariance of the SU(N) step: step(U^g) = step(U)^g, U^g_mu(x) = g(x) U_mu(x) g(x+mu)^dagger;
  4. the step's output in SU(N): max |W^dagger W - 1| and max |det W - 1|.

    python sun_check.py SU2_SHARD|- SUN_SHARD|- [N] [L]
A shard is a stored campaign file (chain axis first, chain 0 is read; an SU(2) shard is cut to a 8^4 corner
sub-block only when `CUT` is set, which breaks periodicity and is therefore not done by default); `-` draws a
thermalised configuration with the generator instead (SU(2) beta 2.3, SU(N) beta 5.85 for N = 3, L^4, 40 sweeps).
"""
import importlib.util
import json
import os
import sys

import numpy as np

import observer_step as O
import lattice_generator as G
from lattice_generator import _Backend, _sax, D

# CHOSEN: the observer step coefficient the campaigns use (below the 1/6 bound); any c in range tests the code
C = 0.15


def gen(group, L, beta, seed):
    return np.asarray(G.gauge_field((L,) * 4, beta, group=group, seed=seed, therm=40, method="heatbath"))


def phi(q):
    return G._su2_matrix(_Backend(None), q.astype(np.float64))


def gauge(bg, U, g):
    N = U.shape[-1]
    out = bg.clone(U)
    gd = bg.conj(bg.swap(g))
    for mu in range(D):
        out[..., mu, :, :] = g @ U[..., mu, :, :] @ bg.roll(gd, -1, _sax(mu, 2))
    return out


def rand_sun(bg, shape, N):
    Z = bg.randn((*shape, N, N)) + 1j * bg.randn((*shape, N, N))
    Q, _ = bg.qr(Z)
    return O.proj_sun(bg, Q)


def num(bg, x):
    return bg.to_numpy(x)


def checks(bg, q2, U, label):
    r = {}
    tq = O.tensor(bg, q2.astype(np.float64)) if bg.torch else q2.astype(np.float64)
    # 1. N = 2 equivalence
    Uq = O.tensor(bg, phi(q2))
    a = phi(num(bg, O.step(bg, tq, C)))
    b = num(bg, O.step(bg, Uq, C))
    r["n2_step_maxabs"] = float(np.abs(a - b).max())
    s1 = O.step(bg, O.step(bg, tq, C), C)
    s2 = O.step(bg, O.step(bg, Uq, C), C)
    r["n2_step2_maxabs"] = float(np.abs(phi(num(bg, s1)) - num(bg, s2)).max())
    r["n2_energy_maxabs"] = float(np.abs(num(bg, O.energy_density(bg, s1)) - num(bg, O.energy_density(bg, s2))).max())
    r["n2_slice_maxabs"] = float(np.abs(O.slice_sums(bg, s1) - O.slice_sums(bg, s2)).max())
    if not bg.torch:
        a = phi(np.asarray(O.smear(bg, q2.astype(np.float64)[None], 4)))[0]
        b = num(bg, O.smear(bg, Uq[None], 4))[0]
        r["n2_ape4_maxabs"] = float(np.abs(a - b).max())
    # 2. SU(2) path against git HEAD
    head = os.environ.get("OBS_HEAD")
    if head:
        spec = importlib.util.spec_from_file_location("obs_head", head)
        H = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(H)
        for prec in ((np.float32, np.float64) if not bg.torch else (None,)):
            x = tq if bg.torch else q2.astype(prec)
            r[f"su2_identical_to_head_{'torch' if bg.torch else np.dtype(prec).name}"] = bool(
                np.array_equal(num(bg, O.step(bg, x, C)), num(bg, H.step(bg, x, C)))
                and np.array_equal(num(bg, O.energy_density(bg, x)), num(bg, H.energy_density(bg, x)))
                and np.array_equal(O.slice_sums(bg, x), H.slice_sums(bg, x)))
    # 3. gauge covariance, 4. SU(N)
    Ut = O.tensor(bg, U)
    N = U.shape[-1]
    g = rand_sun(bg, U.shape[:4], N)
    W = O.step(bg, Ut, C)
    r["cov_step_maxabs"] = float(np.abs(num(bg, O.step(bg, gauge(bg, Ut, g), C)) - num(bg, gauge(bg, W, g))).max())
    r["cov_energy_maxabs"] = float(np.abs(num(bg, O.energy_density(bg, gauge(bg, Ut, g)))
                                          - num(bg, O.energy_density(bg, Ut))).max())
    if not bg.torch:
        r["cov_ape4_maxabs"] = float(np.abs(num(bg, O.smear(bg, gauge(bg, Ut, g)[None], 4))[0]
                                            - num(bg, gauge(bg, O.smear(bg, Ut[None], 4)[0], g))).max())
    Wn = num(bg, W)
    eye = np.eye(N)
    r["unitarity_maxabs"] = float(np.abs(np.conj(np.swapaxes(Wn, -1, -2)) @ Wn - eye).max())
    r["det_maxabs"] = float(np.abs(np.linalg.det(Wn) - 1).max())
    W8 = Ut
    for _ in range(8):  # NOT A READ: eight steps, the drift of the constraint
        W8 = O.step(bg, W8, C)
    Wn = num(bg, W8)
    r["unitarity8_maxabs"] = float(np.abs(np.conj(np.swapaxes(Wn, -1, -2)) @ Wn - eye).max())
    r["det8_maxabs"] = float(np.abs(np.linalg.det(Wn) - 1).max())
    r["e_before_after1_after8"] = [float(num(bg, O.energy_density(bg, x)).mean()) for x in (Ut, W, W8)]
    print(label, json.dumps(r), flush=True)
    return r


if __name__ == "__main__":
    s2, sn = sys.argv[1], sys.argv[2]
    N, L = O.opt(3, 3), O.opt(4, 8)
    q2 = gen("su2", L, 2.3, 1) if s2 == "-" else np.load(s2, mmap_mode="r")[0]
    U = gen(f"su{N}", L, 5.85, 2) if sn == "-" else np.load(sn, mmap_mode="r")[0]
    if os.environ.get("CUT"):
        q2 = q2[:8, :8, :8, :8]
    q2, U = np.array(q2), np.asarray(U, dtype=np.complex128)
    _Backend(None).seed(7)
    np.random.seed(7)
    bgn = _Backend(None).seed(7)
    checks(bgn, q2, U, "numpy")
    try:
        import torch  # noqa: F401
    except ImportError:
        sys.exit(0)
    for fp in ("64", "32"):
        checks(_Backend("cpu", fp=fp).seed(7), q2, U, f"torch-cpu-fp{fp}")
