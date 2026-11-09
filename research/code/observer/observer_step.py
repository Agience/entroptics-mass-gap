"""The pieces every observer-route read shares: the Lean observer step, the factor-2 block step, the
plaquette, the energy density, and the shard list of a campaign.

All functions take a lattice_generator backend `bg` (numpy: `_Backend(None)`; torch: `_Backend("cuda", fp=...)`)
and links in one of the generator's two layouts:
  SU(2): unit quaternions, real, (..., x, y, z, t, mu, 4), (1/2) tr U = U[..., 0]; rolls by `_sax(mu, 1)`;
  SU(N): N x N complex matrices, (..., x, y, z, t, mu, N, N) (`lattice_generator._sun_init`); rolls by
         `_sax(mu, 2)`. `is_sun(q)` tells them apart by dtype (complex is SU(N)).
Rolls index spacetime by a negative axis, so the same code reads one configuration or a batch with a
leading chain axis. The two layouts are related by `lattice_generator._su2_matrix`, a homomorphism for the
generator's `_qmul` (phi(a b) = phi(a) phi(b), phi(a*) = phi(a)^dagger, (1/2) tr phi(a) = a_0), so every SU(2)
quantity below equals its SU(N) form at N = 2 under phi.

Normalisation, the same for both layouts: the plaquette energy is 1 - Re tr P / N per plane (N = 2 gives
1 - (1/2) tr P), summed over the six planes (or the three spatial ones); Wilson loops are Re tr W / N.

  step(bg, q, c)       the observer step of ObserverFlow.obsConfFlow: BlockSU2.blockLink on the same lattice
                       (ApeLattice.apeConf), U_mu(x) -> V / |V|, V = U_mu(x) + c * (sum of the six staples),
                       all four directions, every link from the old configuration;
  block2(bg, q, c)     the factor-2 block step: V_mu(x) = Proj[U_mu(x) U_mu(x+mu) + c * (six bent paths)],
                       coarse lattice on the even sites; c = 0 is plain decimation;
  halftr(bg, q, mu, nu)   (1/2) tr P of the plaquette based at x in plane (mu, nu) (SU(2));
  retrN(bg, q, mu, nu)    Re tr P / N, either layout;
  planes(bg, q, spatial)  1 - Re tr P / N per plane, float64, over the six planes or the three spatial ones;
  energy_density(bg, q, spatial)   their sum, accumulated plane by plane;
  slice_sums(bg, q, spatial)       energy_density summed over x, y, z (the zero-momentum time slices);
  shards(camp, maxsh, prefer_verified)   the shard names of a campaign directory;
  chain_blocks(names)                    the shards grouped by chain (jackknife blocks);
  chain(bg, links, ch), backend()        chain ch of a shard on the backend; the backend OBS_DEVICE/OBS_FP name;
  opt(i, default, cast)                  an optional command-line argument.

The SU(N) layout's own pieces:
  proj_sun(bg, V)      the projection of the SU(N) step: polar factor W = V (V^dagger V)^(-1/2), computed from
                       the SVD V = A S B^dagger as W = A B^dagger, then W det(W)^(-1/N) with the principal
                       branch of the phase (arg det W in (-pi, pi]);
  ape_sun(bg, U, nsweep, alpha)   spatial APE smearing, U_k -> proj_sun[(1-alpha) U_k + (alpha/4) (four spatial
                       staples)], temporal links untouched: lattice_generator.ape_smear's form (that function is
                       SU(2)/U(1) only) with the SU(N) projection, which at N = 2 is ape_smear's normalisation;
  smear(bg, q, nsweep, alpha)     ape_sun for SU(N), lattice_generator.ape_smear for SU(2);
  tensor(bg, arr)      a stored shard as a backend array of the backend's precision, real or complex.
For SU(2) quaternions `step`, `planes`, `energy_density` and `slice_sums` run the quaternion code unchanged.
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code (parent of observer/)
from lattice_generator import D, _qconj, _qmul, _sax


def _f64(bg, x):
    return x.double() if bg.torch else x.astype(np.float64)


def _unit(bg, V):
    return V / bg.norm(V, -1, True)


def is_sun(q):
    """True for the SU(N) matrix layout (complex), False for SU(2) quaternions (real)."""
    return bool(q.is_complex()) if hasattr(q, "is_complex") else bool(np.iscomplexobj(q))


def _dag(bg, M):
    return bg.conj(bg.swap(M))


def proj_sun(bg, V):
    """V -> the SU(N) element of the observer step: polar factor, then the determinant-phase fix."""
    N = V.shape[-1]
    A, _, Bh = bg.t.linalg.svd(V) if bg.torch else np.linalg.svd(V)
    W = A @ Bh                                        # the unitary polar factor V (V^dagger V)^(-1/2)
    th = bg.angle(bg.det(W))                          # principal branch, in (-pi, pi]
    return W * bg.expi(-th / N)[..., None, None]


def _staples_sun(bg, U, mu, dirs):
    """Sum over nu in dirs (nu != mu) of the two staples parallel to U_mu(x):
    U_nu(x) U_mu(x+nu) U_nu(x+mu)^dagger + U_nu(x-nu)^dagger U_mu(x-nu) U_nu(x-nu+mu),
    the quaternion `up` and `dn` of `step` under phi."""
    Umu = U[..., mu, :, :]
    S = bg.zeros_like(Umu)
    for nu in dirs:  # NOT A READ: the staple orientations
        if nu == mu:
            continue
        Unu = U[..., nu, :, :]
        S = S + Unu @ bg.roll(Umu, -1, _sax(nu, 2)) @ _dag(bg, bg.roll(Unu, -1, _sax(mu, 2)))
        Unm = bg.roll(Unu, 1, _sax(nu, 2))
        S = S + _dag(bg, Unm) @ bg.roll(Umu, 1, _sax(nu, 2)) @ bg.roll(Unm, -1, _sax(mu, 2))
    return S


def _step_sun(bg, U, c):
    out = bg.clone(U)
    for mu in range(D):
        out[..., mu, :, :] = proj_sun(bg, U[..., mu, :, :] + c * _staples_sun(bg, U, mu, range(D)))
    return out


# CHOSEN: alpha=0.5, the APE weight of lattice_generator.ape_smear's default, so SU(N) and SU(2) smear alike
def ape_sun(bg, U, nsweep, alpha=0.5):
    """Spatial APE smearing of SU(N) links with proj_sun; every link of a sweep from the old configuration."""
    for _ in range(int(nsweep)):
        Un = bg.clone(U)
        for mu in range(D - 1):
            V = (1 - alpha) * U[..., mu, :, :] + (alpha / 4.0) * _staples_sun(bg, U, mu, range(D - 1))
            Un[..., mu, :, :] = proj_sun(bg, V)
        U = Un
    return U


# CHOSEN: alpha=0.5, lattice_generator.ape_smear's default APE weight
def smear(bg, q, nsweep, alpha=0.5):
    """Spatial APE: ape_sun for SU(N); for SU(2) the generator's ape_smear, unchanged."""
    if is_sun(q):
        return ape_sun(bg, q, nsweep, alpha)
    from lattice_generator import ape_smear
    return ape_smear(q, nsweep, alpha=alpha, device=(str(bg.dev) if bg.torch else None))


def tensor(bg, arr):
    """A stored shard as a backend array: on torch real -> bg.f, complex -> bg.c; on numpy complex links are
    promoted to complex128 and quaternions kept as stored."""
    if bg.torch:
        return bg.t.as_tensor(np.asarray(arr), device=bg.dev).to(bg.c if np.iscomplexobj(arr) else bg.f)
    return np.asarray(arr, dtype=np.complex128) if np.iscomplexobj(arr) else np.asarray(arr)


def step(bg, q, c):
    if is_sun(q):
        return _step_sun(bg, q, c)
    out = bg.clone(q)
    for mu in range(D):
        U = q[..., mu, :]
        V = bg.clone(U)
        for nu in range(D):  # NOT A READ: the six staples
            if nu == mu:
                continue
            Un = q[..., nu, :]
            up = _qmul(bg, _qmul(bg, Un, bg.roll(U, -1, _sax(nu, 1))), _qconj(bg, bg.roll(Un, -1, _sax(mu, 1))))
            Unm = bg.roll(Un, 1, _sax(nu, 1))
            dn = _qmul(bg, _qmul(bg, _qconj(bg, Unm), bg.roll(U, 1, _sax(nu, 1))), bg.roll(Unm, -1, _sax(mu, 1)))
            V = V + c * (up + dn)
        out[..., mu, :] = _unit(bg, V)
    return out


def block2(bg, q, c):
    out = bg.clone(q)
    for mu in range(D):
        qmu = q[..., mu, :]
        V = _qmul(bg, qmu, bg.roll(qmu, -1, _sax(mu, 1)))
        # DERIVED: c = 0 is plain decimation; its staple term vanishes, so skipping it is exact
        if c != 0.0:
            for nu in range(D):  # NOT A READ: the transverse directions of the block step
                if nu == mu:
                    continue
                qnu = q[..., nu, :]
                up = _qmul(bg, _qmul(bg, _qmul(bg, qnu, bg.roll(qmu, -1, _sax(nu, 1))),
                                     bg.roll(bg.roll(qmu, -1, _sax(nu, 1)), -1, _sax(mu, 1))),
                           _qconj(bg, bg.roll(qnu, -2, _sax(mu, 1))))
                qnm = bg.roll(qnu, 1, _sax(nu, 1))
                dn = _qmul(bg, _qmul(bg, _qmul(bg, _qconj(bg, qnm), bg.roll(qmu, 1, _sax(nu, 1))),
                                     bg.roll(bg.roll(qmu, 1, _sax(nu, 1)), -1, _sax(mu, 1))),
                           bg.roll(qnm, -2, _sax(mu, 1)))
                V = V + c * (up + dn)
        out[..., mu, :] = _unit(bg, V)
    coarse = out[..., ::2, ::2, ::2, ::2, :, :]
    return coarse.contiguous() if bg.torch else np.ascontiguousarray(coarse)


def retrN(bg, q, mu, nu):
    """Re tr P / N of the plaquette based at x in plane (mu, nu); for SU(2) quaternions, halftr."""
    if not is_sun(q):
        return halftr(bg, q, mu, nu)
    N = q.shape[-1]
    P = (q[..., mu, :, :] @ bg.roll(q[..., nu, :, :], -1, _sax(mu, 2))
         @ _dag(bg, bg.roll(q[..., mu, :, :], -1, _sax(nu, 2))) @ _dag(bg, q[..., nu, :, :]))
    return bg.real(bg.trace(P)) / N


def halftr(bg, q, mu, nu):
    P = _qmul(bg, _qmul(bg, _qmul(bg, q[..., mu, :], bg.roll(q[..., nu, :], -1, _sax(mu, 1))),
                        _qconj(bg, bg.roll(q[..., mu, :], -1, _sax(nu, 1)))), _qconj(bg, q[..., nu, :]))
    return P[..., 0]


def planes(bg, q, spatial=False):
    n = D - 1 if spatial else D
    for mu in range(n):
        for nu in range(mu + 1, n):  # NOT A READ: the plaquette planes
            yield 1.0 - _f64(bg, retrN(bg, q, mu, nu))


def energy_density(bg, q, spatial=False):
    tot = 0.0
    for e in planes(bg, q, spatial):
        tot = tot + e
    return tot


def slice_sums(bg, q, spatial=True):
    e = energy_density(bg, q, spatial)
    return bg.to_numpy(e.sum(dim=(-4, -3, -2)) if bg.torch else e.sum(axis=(-4, -3, -2)))


def chain_blocks(names):
    """Shards grouped into jackknife blocks: `links_c{k}_m{j}.npy` (one chain per file, the SU(N) campaigns)
    joins block `links_c{k}`; any other name (`links_000.npy`, one measurement of every chain) is its own
    block, so the SU(2) delete-one-shard jackknife is unchanged."""
    blocks = {}
    for n in names:
        key = n.split("_m")[0] if n.startswith("links_c") and "_m" in n else n
        blocks.setdefault(key, []).append(n)
    return [blocks[k] for k in sorted(blocks)]


def chain(bg, links, ch):
    """Chain ch of a stored shard as a batch of one on the backend. SU(2) quaternions go through float32 as the
    SU(2) campaigns are stored; SU(N) matrices through `tensor`."""
    if np.iscomplexobj(links):
        return tensor(bg, np.array(links[ch:ch + 1]))
    if bg.torch:
        return bg.t.as_tensor(np.array(links[ch:ch + 1], dtype=np.float32), dtype=bg.f, device=bg.dev)
    return np.array(links[ch:ch + 1], dtype=np.float32)


def backend():
    """The reads' backend: `OBS_DEVICE` (default cuda; `numpy` is the CPU path) at `OBS_FP` (default 32)."""
    from lattice_generator import _Backend
    dev = os.environ.get("OBS_DEVICE", "cuda")
    return _Backend(None) if dev == "numpy" else _Backend(dev, fp=os.environ.get("OBS_FP", "32"))


def torch_device():
    """`OBS_DEVICE` when it names a torch device, else None (the numpy path). Unlike `backend`, an unset
    `OBS_DEVICE` reads as numpy here: the reads that ask this run on the CPU unless a device is named."""
    dev = os.environ.get("OBS_DEVICE", "")
    return None if dev in ("", "numpy") else dev


def opt(i, default, cast=int):
    """Optional positional argument i of the command line, or the default when it is absent."""
    try:
        return cast(sys.argv[i])
    except IndexError:
        return default


def shards(camp, maxsh=10 ** 9, prefer_verified=True):
    """verified.list when present and preferred, else SHA256SUMS; sorted, de-duplicated."""
    lst = os.path.join(camp, "verified.list")
    if prefer_verified and os.path.exists(lst):
        names = [l.strip() for l in open(lst) if l.strip()]
    else:
        names = [l.split()[1] for l in open(os.path.join(camp, "SHA256SUMS")) if l.strip()]
    return sorted(set(names))[:maxsh]
