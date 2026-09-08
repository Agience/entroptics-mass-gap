"""
lattice_generator.py -- config generator (research/code/), backend-agnostic (numpy | torch/GPU), BATCHED.

This module GENERATES configurations for the entroptics read to consume. ``config`` hands back a
ready-to-read scalar field (the gauge-invariant local action density phi(x) = sum_{mu<nu}(1 - (1/N) Re tr U_p)).

The Monte Carlo is one vectorised checkerboard Metropolis. It runs on numpy (default) or, by passing
``device="cuda"`` (or any torch device), entirely on the GPU. Pass ``batch=n`` to evolve ``n``
independent chains in parallel as a leading batch dimension, each slot with its own RNG stream: on a
GPU this saturates the device and returns all ``n`` configs from one call, the fast path for
regenerating an ensemble.

Generation is reproducible in ``(group, L, T, beta, seed, therm, method)``. The spacetime rolls index
by negative axes (``k - D - trailing``), which resolve to the same axes with or without a batch
dimension, so a batched run and an unbatched one at the same seed agree on the numpy path. The torch
path carries its own deterministic generator.

Gauge groups (one vectorised checkerboard Metropolis) plus a free scalar particle:
  * ``group="u1"``  -- compact U(1), the abelian FOIL: confines at small beta,
    deconfines to a Coulomb phase near beta_c ~ 1.01 (it CROSSES).
  * ``group="su2"`` -- SU(2), non-abelian: confines at every beta, a smooth crossover (the NO-BUMP).
  * ``group="su3"``, ``"su4"``, ... -- SU(N) via Cabibbo-Marinari SU(2)-subgroup rotations (any N>=3).
  * ``free_scalar`` -- a free scalar of mass m with KNOWN gap E0 = arccosh(1 + m^2/2); the calibration.

    from lattice_generator import config, config_batch, stream
    field  = config((8,8,8,16), 2.3, group="su2", seed=0)                       # 1 config, numpy (CPU)
    field  = config((8,8,8,16), 2.3, group="su2", seed=0, device="cuda")        # 1 config, GPU
    fields = config((8,8,8,16), 0.8, group="u1", seed=0, device="cuda", batch=18)  # (18, 8,8,8,16) on GPU
"""
from __future__ import annotations

import os

import numpy as np

D = 4  # spacetime dimensions


# ══════════════════════════════════════════════════════════════════════════════
# backend: numpy (device=None) or torch on a device ("cpu"/"cuda"/"cuda:0"/...).
# ══════════════════════════════════════════════════════════════════════════════
class _Backend:
    def __init__(self, device=None):
        self.torch = device is not None
        if self.torch:
            import torch
            self.t = torch
            self.dev = torch.device(device)
            # GEN_FP=32 runs generation in single precision (fp64 default). fp32 is fine for producing
            # thermalised configs -- links reunitarise every sweep and outputs are stored fp32 -- and it
            # unlocks cheap consumer GPUs (4090 etc.) whose fp64 is ~64x slower than fp32.
            _fp32 = os.environ.get("GEN_FP", "64") == "32"
            self.f = torch.float32 if _fp32 else torch.float64
            self.c = torch.complex64 if _fp32 else torch.complex128
        else:
            self.dev = None

    def seed(self, seed):
        if self.torch:
            self.gen = self.t.Generator(device=self.dev).manual_seed(int(seed))
        else:
            self.rng = np.random.default_rng(seed)
        return self

    # ---- random ----
    def uniform(self, lo, hi, shape):
        if self.torch:
            return (hi - lo) * self.t.rand(tuple(shape), generator=self.gen, device=self.dev, dtype=self.f) + lo
        return self.rng.uniform(lo, hi, size=shape)

    def randn(self, shape):
        if self.torch:
            return self.t.randn(tuple(shape), generator=self.gen, device=self.dev, dtype=self.f)
        return self.rng.standard_normal(shape)

    def rand(self, shape):
        if self.torch:
            return self.t.rand(tuple(shape), generator=self.gen, device=self.dev, dtype=self.f)
        return self.rng.random(shape)

    # ---- array ops ----
    def roll(self, a, shift, axis):
        return self.t.roll(a, shift, dims=axis) if self.torch else np.roll(a, shift, axis=axis)

    def stack(self, xs, axis):
        return self.t.stack(xs, dim=axis) if self.torch else np.stack(xs, axis=axis)

    def cat(self, xs, axis):
        return self.t.cat(xs, dim=axis) if self.torch else np.concatenate(xs, axis=axis)

    def where(self, c, a, b):
        return self.t.where(c, a, b) if self.torch else np.where(c, a, b)

    def norm(self, a, axis, keepdims):
        return (self.t.linalg.vector_norm(a, dim=axis, keepdim=keepdims)
                if self.torch else np.linalg.norm(a, axis=axis, keepdims=keepdims))

    def mod(self, a, m):
        return self.t.remainder(a, m) if self.torch else np.mod(a, m)

    def cos(self, x): return self.t.cos(x) if self.torch else np.cos(x)
    def exp(self, x): return self.t.exp(x) if self.torch else np.exp(x)
    def log(self, x): return self.t.log(x) if self.torch else np.log(x)
    def allbool(self, x): return bool(x.all()) if self.torch else bool(np.all(x))
    def falsemask(self, shape):
        return (self.t.zeros(tuple(shape), dtype=self.t.bool, device=self.dev) if self.torch
                else np.zeros(shape, dtype=bool))
    def conj(self, x): return self.t.conj(x) if self.torch else np.conj(x)
    def real(self, x): return self.t.real(x) if self.torch else np.real(x)
    def imag(self, x): return self.t.imag(x) if self.torch else np.imag(x)

    def expi(self, th):                                     # exp(i*th), th real -> complex
        return self.t.exp(1j * th.to(self.c)) if self.torch else np.exp(1j * th)

    def trace(self, M):                                     # trace over the last two dims
        return self.t.diagonal(M, dim1=-2, dim2=-1).sum(-1) if self.torch else np.trace(M, axis1=-2, axis2=-1)

    def swap(self, a):
        return self.t.swapaxes(a, -1, -2) if self.torch else np.swapaxes(a, -1, -2)

    def qr(self, Z): return self.t.linalg.qr(Z) if self.torch else np.linalg.qr(Z)
    def det(self, Q): return self.t.linalg.det(Q) if self.torch else np.linalg.det(Q)
    def eigh(self, M): return self.t.linalg.eigh(M) if self.torch else np.linalg.eigh(M)

    def zeros(self, shape, cplx=False):
        if self.torch:
            return self.t.zeros(tuple(shape), dtype=(self.c if cplx else self.f), device=self.dev)
        return np.zeros(shape, dtype=(np.complex128 if cplx else np.float64))

    def zeros_like(self, a): return self.t.zeros_like(a) if self.torch else np.zeros_like(a)

    def ones(self, shape):
        return self.t.ones(tuple(shape), dtype=self.f, device=self.dev) if self.torch else np.ones(shape)

    def const(self, lst):
        return self.t.tensor(lst, dtype=self.f, device=self.dev) if self.torch else np.array(lst)

    def broadcast_eye(self, N, shape):                      # (*shape, N, N) identity (complex)
        if self.torch:
            return self.t.eye(N, dtype=self.c, device=self.dev).expand(*shape, N, N)
        return np.broadcast_to(np.eye(N, dtype=complex), (*shape, N, N))

    def clone(self, a): return a.clone() if self.torch else a.copy()

    def parity(self, dims):                                 # even/odd coordinate-sum checkerboard masks
        if self.torch:
            idx = self.t.zeros(tuple(dims), dtype=self.t.int64, device=self.dev)
            for ax, L in enumerate(dims):
                shp = [1] * len(dims); shp[ax] = L
                idx = idx + self.t.arange(L, device=self.dev).reshape(shp)
            return [idx % 2 == 0, idx % 2 == 1]
        g = np.indices(dims).sum(axis=0)
        return [g % 2 == 0, g % 2 == 1]

    # ---- fft (free scalar) ----
    def fftfreq(self, L):
        return self.t.fft.fftfreq(L, device=self.dev, dtype=self.f) if self.torch else np.fft.fftfreq(L)

    def sin(self, x): return self.t.sin(x) if self.torch else np.sin(x)
    def sqrt(self, x): return self.t.sqrt(x) if self.torch else np.sqrt(x)

    def meshgrid(self, arrs):
        return self.t.meshgrid(*arrs, indexing="ij") if self.torch else np.meshgrid(*arrs, indexing="ij")

    def fftn(self, x): return self.t.fft.fftn(x) if self.torch else np.fft.fftn(x)
    def ifftn(self, x): return self.t.fft.ifftn(x) if self.torch else np.fft.ifftn(x)

    def to_numpy(self, a):
        return a.detach().cpu().numpy() if (self.torch and hasattr(a, "detach")) else np.asarray(a)


# The spacetime roll axis for direction k, as a NEGATIVE index into a link slice whose spacetime axes
# are its last D axes followed by ``tr`` group-structure axes.  Negative indexing skips any leading
# batch dims; with no batch it equals the original positive axis k (so the numpy path is unchanged).
def _sax(k, tr):
    return k - D - tr


# ══════════════════════════════════════════════════════════════════════════════
# compact U(1): links are phases theta, U = exp(i theta).  Slices roll with tr=0.
# ══════════════════════════════════════════════════════════════════════════════
def _u1_init(b, dims, batch):
    return b.uniform(-np.pi, np.pi, (*batch, *dims, D))


def _u1_staple(b, U, mu):
    S = b.zeros_like(U[..., 0])
    Umu = U[..., mu]
    for nu in range(D):
        if nu == mu:
            continue
        Unu = U[..., nu]
        Unu_pmu = b.roll(Unu, -1, _sax(mu, 0))
        S = S + Unu_pmu * b.conj(b.roll(Umu, -1, _sax(nu, 0))) * b.conj(Unu)          # forward
        S = S + (b.roll(Unu, 1, _sax(nu, 0)) * b.conj(b.roll(Unu_pmu, 1, _sax(nu, 0)))
                 * b.conj(b.roll(Umu, 1, _sax(nu, 0))))                               # backward
    return S


def _u1_sweep(b, theta, sdims, beta, step):
    for mu in range(D):
        for mask in b.parity(sdims):
            U = b.expi(theta)
            S = _u1_staple(b, U, mu)
            th = theta[..., mu]
            prop = th + b.uniform(-step, step, th.shape)
            dS = -beta * b.real((b.expi(prop) - b.expi(th)) * S)
            acc = (b.rand(th.shape) < b.exp(-dS)) & mask
            theta[..., mu] = b.where(acc, b.mod(prop + np.pi, 2 * np.pi) - np.pi, th)


def _u1_action(b, theta):
    phi = b.zeros(theta.shape[:-1])
    for mu in range(D):
        for nu in range(mu + 1, D):
            P = (theta[..., mu] + b.roll(theta[..., nu], -1, _sax(mu, 0))
                 - b.roll(theta[..., mu], -1, _sax(nu, 0)) - theta[..., nu])
            phi = phi + (1.0 - b.cos(P))
    return phi


# ══════════════════════════════════════════════════════════════════════════════
# SU(2): unit quaternions q.  Slices (with the quaternion axis kept) roll with tr=1.
# ══════════════════════════════════════════════════════════════════════════════
def _qmul(b, a, c):
    a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
    b0, b1, b2, b3 = c[..., 0], c[..., 1], c[..., 2], c[..., 3]
    return b.stack([
        a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3,
        a0 * b1 + a1 * b0 - a2 * b3 + a3 * b2,
        a0 * b2 + a2 * b0 - a3 * b1 + a1 * b3,
        a0 * b3 + a3 * b0 - a1 * b2 + a2 * b1,
    ], -1)


def _qconj(b, a):
    return a * b.const([1.0, -1.0, -1.0, -1.0])


def _sdot(q, a):
    return q[..., 0] * a[..., 0] - (q[..., 1] * a[..., 1]
                                    + q[..., 2] * a[..., 2] + q[..., 3] * a[..., 3])


def _su2_init(b, dims, batch):
    q = b.randn((*batch, *dims, D, 4))
    return q / b.norm(q, -1, True)


def _su2_staple(b, q, mu):
    A = b.zeros((*q.shape[:-2], 4))
    qmu = q[..., mu, :]
    for nu in range(D):
        if nu == mu:
            continue
        qnu = q[..., nu, :]
        qnu_pmu = b.roll(qnu, -1, _sax(mu, 1))
        A = A + _qmul(b, _qmul(b, qnu_pmu, _qconj(b, b.roll(qmu, -1, _sax(nu, 1)))), _qconj(b, qnu))
        A = A + _qmul(b, _qmul(b, _qconj(b, b.roll(qnu_pmu, 1, _sax(nu, 1))),
                               _qconj(b, b.roll(qmu, 1, _sax(nu, 1)))), b.roll(qnu, 1, _sax(nu, 1)))
    return A


def _su2_sweep(b, q, sdims, beta, step):
    full = q.shape[:-2]                                     # (*batch, *spacetime): the RNG shape
    for mu in range(D):
        for mask in b.parity(sdims):
            A = _su2_staple(b, q, mu)
            qmu = q[..., mu, :]
            r = b.cat([b.ones((*full, 1)), step * b.randn((*full, 3))], -1)
            r = r / b.norm(r, -1, True)
            qp = _qmul(b, r, qmu)
            dS = -beta * (_sdot(qp, A) - _sdot(qmu, A))
            acc = (b.rand(full) < b.exp(-dS)) & mask
            q[..., mu, :] = b.where(acc[..., None], qp, qmu)


def _qdot4(q, a):
    """Standard 4-D quaternion dot q0a0+q1a1+q2a2+q3a3 (not sdot, which flips the vector sign)."""
    return (q * a).sum(-1)


# The heat-bath a0 sampler is split across two proposals because neither covers the range on its
# own.  Kennedy-Pendleton is efficient only where betak is large; Creutz only where it is small.
# Measured on the beta=0.2 strong-coupling ensemble (betak ~ 0.465), KP accepted ~8% per trial, so
# a capped loop could not drain: 48% of link updates ran the cap out and ~0.05% of links were left
# holding a0 = 0 -- the equator of S^3, which is not a heat-bath draw and is not a sample of
# anything.  SU(N) is worse still: Cabibbo-Marinari passes beta/N, so SU(3) at beta=0.2 samples at
# betak/3.  Below, each site takes the proposal that suits its own betak, per-trial acceptance
# never drops below ~0.5, and the loop runs until every site has an accepted draw.
_KP_MIN = 2.0        # betak at/above which Kennedy-Pendleton is the efficient proposal
_A0_ITMAX = 10_000   # not a cap on the answer -- a runaway guard that RAISES, see below


def _su2_a0(b, betak):
    """Sample ``a0 ~ sqrt(1-a0^2) exp(betak*a0)`` on [-1,1], vectorised, with **no truncation**.

    Every site returns an accepted draw from its own density.  There is no iteration budget that
    can expire and no fallback value: the loop ends when the last site accepts.  ``_A0_ITMAX``
    exists only so that a corrupted ``betak`` (NaN, inf) cannot spin forever -- it RAISES rather
    than returning a partly-sampled array: the accept-reject loop either samples the distribution
    or reports that it could not.

    Two proposals, chosen per site:

      * ``betak >= _KP_MIN`` -- **Kennedy-Pendleton** (1985): lambda^2 from three uniforms, accept
        with probability sqrt(1-lambda^2), a0 = 1-2*lambda^2.  Acceptance -> 1 as betak grows.
      * ``betak <  _KP_MIN`` -- **Creutz** (1980): draw a0 from exp(betak*a0) alone by inverse CDF,
        then accept with probability sqrt(1-a0^2).  Acceptance -> pi/4 ~ 0.785 as betak -> 0, where
        the density is the Haar semicircle and KP degenerates.
    """
    shape = tuple(betak.shape)
    a0 = b.zeros(shape)
    acc = b.falsemask(shape)
    use_kp = betak >= _KP_MIN
    # Each branch is evaluated on every site and then selected, so each one's input is clamped into
    # its own valid range: the KP divide never sees betak ~ 0, and the Creutz exponential never sees
    # a large betak it would overflow on.  The clamped values land only where they are discarded.
    kp_b = b.where(use_kp, betak, betak * 0.0 + _KP_MIN)
    cr_b = b.where(use_kp, betak * 0.0, betak)
    it = 0
    while True:
        # -- Kennedy-Pendleton proposal --
        x1 = b.rand(shape); x2 = b.rand(shape); x3 = b.rand(shape); x4 = b.rand(shape)
        lam2 = -(1.0 / (2.0 * kp_b)) * (b.log(x1) + b.cos(2.0 * np.pi * x2) ** 2 * b.log(x3))
        kp_val = 1.0 - 2.0 * lam2
        kp_ok = x4 * x4 <= 1.0 - lam2
        # -- Creutz proposal: inverse CDF of exp(cr_b*a) on [-1,1], then the sqrt(1-a^2) accept --
        y = b.rand(shape); z = b.rand(shape)
        eb = b.exp(cr_b); ebi = b.exp(-cr_b)
        # a = log(e^-b + y*(e^b - e^-b))/b, whose b -> 0 limit is the uniform draw 2y-1; taken
        # directly there because the quotient is 0/0 at b = 0 (Haar, the beta = 0 heat bath).
        safe = b.where(cr_b > 1e-8, cr_b, cr_b * 0.0 + 1.0)
        cr_val = b.where(cr_b > 1e-8,
                         b.log(ebi + y * (eb - ebi)) / safe,
                         2.0 * y - 1.0)
        cr_ok = z * z <= 1.0 - cr_val * cr_val
        # -- take each site's own proposal --
        newacc = b.where(use_kp, kp_ok, cr_ok) & (~acc)
        a0 = b.where(newacc, b.where(use_kp, kp_val, cr_val), a0)
        acc = acc | newacc
        if b.allbool(acc):
            return a0
        it += 1
        if it >= _A0_ITMAX:
            raise RuntimeError(
                f"_su2_a0: {_A0_ITMAX} passes and sites are still unsampled -- betak is not a "
                f"finite non-negative array (min={float(b.to_numpy(betak).min())}, "
                f"max={float(b.to_numpy(betak).max())}). Refusing to return a partly-sampled "
                f"array: an unsampled site would carry a stand-in, not a draw.")


def _su2_heatbath_link(b, A, beta):
    """New link quaternion q ~ exp(beta*sdot(q,A)) via KP heat-bath (A: staple quaternion sum)."""
    full = A.shape[:-1]
    k = b.norm(A, -1, True)                              # (*full,1) quaternion norm |A|
    e = _qconj(b, A) / (k + 1e-30)                       # unit quat; sdot(q,Abar) = qdot4(q,e)
    a0 = _su2_a0(b, beta * k[..., 0])                    # (*full,)
    r = b.randn((*full, 4))
    r = r - _qdot4(r, e)[..., None] * e                  # component orthogonal to e in 4-D
    r = r / b.norm(r, -1, True)
    perp = 1.0 - a0 * a0
    s = b.sqrt(b.where(perp > 0.0, perp, perp * 0.0))
    return a0[..., None] * e + s[..., None] * r          # sdot(q,A) = k*a0, heat-bath distributed


def _su2_overrelax_link(b, q, A):
    """Microcanonical reflection q -> 2*sdot(q,Abar)*conj(Abar) - q (preserves sdot(q,A))."""
    k = b.norm(A, -1, True)
    e = _qconj(b, A) / (k + 1e-30)
    return 2.0 * _qdot4(q, e)[..., None] * e - q


def _su2_hb_sweep(b, q, sdims, beta, step, n_or=None):
    """One SU(2) update: a heat-bath checkerboard sweep + n_or over-relaxation sweeps (each
    recomputes staples, so the reflections are non-trivial decorrelating moves). ``step`` unused.
    Over-relaxation is microcanonical (preserves the equilibrium distribution) -- it DECORRELATES,
    it is not needed to reach equilibrium -- so ``GEN_NOR=0`` skips it for a ~5x-faster thermalisation
    (default 4 for well-decorrelated draws)."""
    if n_or is None:
        n_or = int(os.environ.get("GEN_NOR", "4"))
    for mu in range(D):
        for mask in b.parity(sdims):
            A = _su2_staple(b, q, mu)
            qn = _su2_heatbath_link(b, A, beta)
            q[..., mu, :] = b.where(mask[..., None], qn, q[..., mu, :])
    for _ in range(int(n_or)):
        for mu in range(D):
            for mask in b.parity(sdims):
                A = _su2_staple(b, q, mu)
                qn = _su2_overrelax_link(b, q[..., mu, :], A)
                q[..., mu, :] = b.where(mask[..., None], qn, q[..., mu, :])


def _su2_action(b, q):
    phi = b.zeros(q.shape[:-2])
    for mu in range(D):
        for nu in range(mu + 1, D):
            Up = _qmul(b, _qmul(b, _qmul(b, q[..., mu, :], b.roll(q[..., nu, :], -1, _sax(mu, 1))),
                                _qconj(b, b.roll(q[..., mu, :], -1, _sax(nu, 1)))), _qconj(b, q[..., nu, :]))
            phi = phi + (1.0 - Up[..., 0])                  # 1 - (1/2) Re tr U_p
    return phi


def _su2_sign(b, q):
    """Centre projection SU(2) -> Z2 per link: z = sign(Re tr U) = sign(q0) in {+1,-1}, shape (..., D)."""
    q0 = q[..., 0]
    return b.where(q0 >= 0.0, b.ones(q0.shape), -1.0 * b.ones(q0.shape))


def _su2_action_centre(b, q):
    """The Z2 centre-projected action density: each link carries z = sign(q0); the plaquette is the
    product of the four link signs, phi_Z(x) = sum_{mu<nu}(1 - z_p) with z_p in {+1,-1} (a Z2 vortex is
    z_p = -1). The rolls carry no quaternion axis (tr=0), as for the U(1) phase field."""
    z = _su2_sign(b, q)                                     # (..., D)  +-1 per link
    phi = b.zeros(q.shape[:-2])
    for mu in range(D):
        for nu in range(mu + 1, D):
            zp = (z[..., mu] * b.roll(z[..., nu], -1, _sax(mu, 0))
                  * b.roll(z[..., mu], -1, _sax(nu, 0)) * z[..., nu])
            phi = phi + (1.0 - zp)
    return phi


def _su2_action_coset(b, q):
    """The coset SU(2)/Z2 (centre-removed) action density: each link -> sign(q0) * q, the q0 >= 0
    representative, then the ordinary SU(2) plaquette action on the coset links."""
    s = _su2_sign(b, q)                                     # (..., D)
    qc = q * s[..., None]                                   # flip each link so q0 >= 0
    return _su2_action(b, qc)


def _su2_line(b, q, mu, R):
    """Ordered SU(2) link product along direction mu of length R:
    P(x) = U_mu(x) U_mu(x+mu) ... U_mu(x+(R-1)mu), as a quaternion field."""
    P = q[..., mu, :]
    sh = P
    for _ in range(1, R):
        sh = b.roll(sh, -1, _sax(mu, 1))
        P = _qmul(b, P, sh)
    return P


def _su2_wilson(b, q, R, T, planes="all"):
    """Mean SU(2) Wilson loop W(R,T) = < (1/2) Re tr U(R x T) >, averaged over sites and over the
    ordered planes selected by ``planes``: R links in mu, T in nu, closed with the reverse edges
    (quaternion conjugates).  ``planes="all"`` averages every ordered mu != nu pair.  ``planes="rt"``
    keeps only mu spatial, nu = time, which is where the static potential is defined: R is a spatial
    separation and T a Euclidean time, so W(R,T) ~ exp(-V(R) T).  The spatial-spatial planes carry
    loops of a different kinematic meaning and belong only in the ``"all"`` average."""
    if planes == "all":
        pairs = [(mu, nu) for mu in range(D) for nu in range(D) if nu != mu]
    elif planes == "rt":
        pairs = [(mu, D - 1) for mu in range(D - 1)]
    else:
        raise ValueError(f"unknown planes='{planes}' (all | rt)")
    tot, cnt = 0.0, 0
    for mu, nu in pairs:
        bottom = _su2_line(b, q, mu, R)                # mu edge at x
        left = _su2_line(b, q, nu, T)                  # nu edge at x
        right = b.roll(left, -R, _sax(mu, 1))          # nu edge at x + R mu
        top = b.roll(bottom, -T, _sax(nu, 1))          # mu edge at x + T nu
        loop = _qmul(b, _qmul(b, _qmul(b, bottom, right), _qconj(b, top)), _qconj(b, left))
        tot += float(loop[..., 0].mean()); cnt += 1
    return tot / cnt


def _su2_wilson_centre(b, q, R, T):
    """Mean Z2 centre-projected Wilson loop W_Z(R,T): each link -> z = sign(q0); the loop is the product
    of the boundary signs (Z2, so the reverse edges carry the same sign)."""
    z = _su2_sign(b, q)                                    # (..., D)  +-1 per link
    tot, cnt = 0.0, 0
    for mu in range(D):
        for nu in range(D):
            if nu == mu:
                continue
            bottom, sh = z[..., mu], z[..., mu]
            for _ in range(1, R):
                sh = b.roll(sh, -1, _sax(mu, 0)); bottom = bottom * sh
            left, sh = z[..., nu], z[..., nu]
            for _ in range(1, T):
                sh = b.roll(sh, -1, _sax(nu, 0)); left = left * sh
            right = b.roll(left, -R, _sax(mu, 0))
            top = b.roll(bottom, -T, _sax(nu, 0))
            loop = bottom * right * top * left
            tot += float(loop.mean()); cnt += 1
    return tot / cnt


def _su2_spatial_staple(b, q, mu):
    """Sum of the four SPATIAL staples around link mu (mu spatial): the smearing kernel.  Only spatial
    nu contribute, so the time direction is left untouched and the transfer matrix is unchanged."""
    A = b.zeros((*q.shape[:-2], 4))
    qmu = q[..., mu, :]
    for nu in range(D - 1):
        if nu == mu:
            continue
        qnu = q[..., nu, :]
        qnu_pmu = b.roll(qnu, -1, _sax(mu, 1))
        A = A + _qmul(b, _qmul(b, qnu_pmu, _qconj(b, b.roll(qmu, -1, _sax(nu, 1)))), _qconj(b, qnu))
        A = A + _qmul(b, _qmul(b, _qconj(b, b.roll(qnu_pmu, 1, _sax(nu, 1))),
                               _qconj(b, b.roll(qmu, 1, _sax(nu, 1)))), b.roll(qnu, 1, _sax(nu, 1)))
    return A


def ape_smear(link, nsweep, *, alpha=0.5, group="su2", device=None):
    """APE-smear the SPATIAL links: U_mu <- Proj_SU(2)[ (1-alpha) U_mu + (alpha/4) sum(spatial staples) ],
    ``nsweep`` times.  Suppresses the excited-state overlap of spatial operators (Wilson-loop ends,
    plaquette operators) while leaving the temporal links -- and so the transfer matrix and every
    energy it carries -- untouched.  For SU(2) the projection is quaternion normalisation."""
    if group != "su2":
        raise ValueError(f"ape_smear supports group='su2'; got '{group}'")
    b = _Backend(device)
    q = link.clone() if hasattr(link, "clone") else np.copy(link)
    for _ in range(int(nsweep)):
        qn = q.clone() if hasattr(q, "clone") else np.copy(q)
        for mu in range(D - 1):
            V = (1 - alpha) * q[..., mu, :] + (alpha / 4.0) * _qconj(b, _su2_spatial_staple(b, q, mu))
            qn[..., mu, :] = V / (b.norm(V, -1, True) + 1e-12)
        q = qn
    return q


def wilson_loop(link, R, T, *, group="su2", project="full", planes="all", device=None):
    """Mean planar Wilson loop W(R,T) from a raw LINK field (SU(2)). ``project="full"`` the SU(2) loop;
    ``project="centre"`` the Z2 centre-projected loop (z = sign(q0)).  ``planes="all"`` averages every
    ordered plane; ``planes="rt"`` keeps only spatial-x-time, the static-potential planes."""
    b = _Backend(device)
    if group != "su2":
        raise ValueError(f"wilson_loop supports group='su2'; got '{group}'")
    if project == "full":
        return _su2_wilson(b, link, R, T, planes)
    if project == "centre":
        if planes != "all":
            raise ValueError("project='centre' has no planes= selection")
        return _su2_wilson_centre(b, link, R, T)
    raise ValueError(f"unknown project='{project}' (full | centre)")


def creutz_sigma(link, R, T, *, group="su2", project="full", device=None):
    """The Creutz ratio chi(R,T) = -log[ W(R,T) W(R-1,T-1) / ( W(R,T-1) W(R-1,T) ) ], the string-tension
    estimate from the R x T Wilson loops of a raw LINK field (R, T >= 2)."""
    def w(r, t):
        return wilson_loop(link, r, t, group=group, project=project, device=device)
    ratio = (w(R, T) * w(R - 1, T - 1)) / (w(R, T - 1) * w(R - 1, T))
    return float(-np.log(ratio)) if ratio > 0 else float("nan")


def _su2_mcg(b, q, sdims, iters):
    """Maximal centre gauge: maximize F = sum_{x,mu} (tr U_mu(x))^2 by iterated local gauge updates
    U_mu(x) -> g(x) U_mu(x) g(x+mu)^dag.  With every other site fixed, F is quadratic in g(x):
    F_local = 4 g^T M(x) g with M(x) = sum_mu [ conj(U_mu(x)) conj(U_mu(x))^T + U_mu(x-mu) U_mu(x-mu)^T ],
    so the optimal g(x) is the leading eigenvector of the 4x4 M(x).  Checkerboard sweeps; returns a COPY."""
    q = b.clone(q)
    qid = b.const([1.0, 0.0, 0.0, 0.0])
    full = tuple(q.shape[:-2])
    for _ in range(int(iters)):
        for mask in b.parity(sdims):
            M = b.zeros((*full, 4, 4))
            for mu in range(D):
                cf = _qconj(b, q[..., mu, :])                     # conj(U_mu(x))
                bk = b.roll(q[..., mu, :], 1, _sax(mu, 1))        # U_mu(x-mu)
                M = M + cf[..., :, None] * cf[..., None, :]
                M = M + bk[..., :, None] * bk[..., None, :]
            v = M[..., 0] + M[..., 1] + M[..., 2] + M[..., 3]     # M @ 1: a vector in range(M) (PSD)
            for _ in range(24):                                   # power iteration -> leading eigenvector
                v = (M @ v[..., None])[..., 0]                    # batched matvec; no cusolver batch cap
                v = v / (b.norm(v, -1, True) + 1e-30)
            g = v                                                 # (*full, 4) unit quaternion
            g = b.where(mask[..., None], g, qid)                  # update this parity only
            for mu in range(D):
                q[..., mu, :] = _qmul(b, g, q[..., mu, :])                                   # left: g(x)
                q[..., mu, :] = _qmul(b, q[..., mu, :], _qconj(b, b.roll(g, -1, _sax(mu, 1))))  # right: g(x+mu)^dag
    return q


def maximal_centre_gauge(link, *, group="su2", iters=60, device=None):
    """Gauge-fix a raw SU(2) LINK field to maximal centre gauge (maximize sum_{x,mu} (tr U_mu(x))^2),
    the gauge in which the Z2 centre projection exposes the confining P-vortices.  Returns fixed links."""
    if group != "su2":
        raise ValueError(f"maximal_centre_gauge supports group='su2'; got '{group}'")
    return _su2_mcg(_Backend(device), link, tuple(link.shape[-6:-2]), iters)


# ══════════════════════════════════════════════════════════════════════════════
# SU(N), N>=3: NxN special-unitary matrices.  Slices (matrix axes kept) roll with tr=2.
# ══════════════════════════════════════════════════════════════════════════════
def _sun_subgroups(N):
    return [(i, j) for i in range(N) for j in range(i + 1, N)]


def _dag(b, M):
    return b.conj(b.swap(M))


def _sun_init(b, dims, batch, N):
    Z = b.randn((*batch, *dims, D, N, N)) + 1j * b.randn((*batch, *dims, D, N, N))
    Q, _ = b.qr(Z)
    det = b.det(Q)
    return Q / (det[..., None, None] ** (1.0 / N))


def _sun_staple(b, U, mu):
    A = b.zeros_like(U[..., mu, :, :])
    Umu = U[..., mu, :, :]
    for nu in range(D):
        if nu == mu:
            continue
        Unu = U[..., nu, :, :]
        Unu_pmu = b.roll(Unu, -1, _sax(mu, 2))
        A = A + Unu_pmu @ _dag(b, b.roll(Umu, -1, _sax(nu, 2))) @ _dag(b, Unu)                    # forward
        A = A + (_dag(b, b.roll(Unu_pmu, 1, _sax(nu, 2))) @ _dag(b, b.roll(Umu, 1, _sax(nu, 2)))
                 @ b.roll(Unu, 1, _sax(nu, 2)))                                                   # backward
    return A


def _su2_matrix(b, q):
    q0, q1, q2, q3 = q[..., 0], q[..., 1], q[..., 2], q[..., 3]
    row0 = b.stack([q0 + 1j * q3, q2 + 1j * q1], -1)
    row1 = b.stack([-q2 + 1j * q1, q0 - 1j * q3], -1)
    return b.stack([row0, row1], -2)


def _sun_sweep(b, U, sdims, N, beta, step):
    full = U.shape[:-3]                                     # (*batch, *spacetime)
    eyeN = b.broadcast_eye(N, full)
    subs = _sun_subgroups(N)
    for mu in range(D):
        for mask in b.parity(sdims):
            A = _sun_staple(b, U, mu)
            for (i, j) in subs:
                Umu = U[..., mu, :, :]
                q = b.cat([b.ones((*full, 1)), step * b.randn((*full, 3))], -1)
                q = q / b.norm(q, -1, True)
                r2 = _su2_matrix(b, q)
                R = b.clone(eyeN)
                R[..., i, i] = r2[..., 0, 0]; R[..., i, j] = r2[..., 0, 1]               # noqa: E702
                R[..., j, i] = r2[..., 1, 0]; R[..., j, j] = r2[..., 1, 1]               # noqa: E702
                Uprop = R @ Umu
                dS = -(beta / N) * b.real(b.trace((Uprop - Umu) @ A))
                acc = (b.rand(full) < b.exp(-dS)) & mask
                U[..., mu, :, :] = b.where(acc[..., None, None], Uprop, Umu)


def _sun_cm_pass(b, U, sdims, N, beta, *, overrelax):
    """One Cabibbo-Marinari checkerboard pass over U: heat-bath (``overrelax=False``) or micro-canonical
    OVER-RELAXATION (``overrelax=True``) of each SU(2) subgroup. For the 2x2 block m of M=Umu@A the effective
    quaternion is c=(Re m00+Re m11, -(Im m01+Im m10), Re m10-Re m01, -(Im m00-Im m11)) with
    Re tr(su2(q)@m)=qdot4(q,c); it is fed to the SU(2) heat-bath as conj(c) at beta/N. The over-relaxation
    reflects the TRIVIAL rotation about the effective staple, q=2<I,e>e-I with e=conj(Asub)/|Asub|=c/|c|:
    this gives S(R)=qdot4(2 e0 e - I, c)=2 e0|c|-c0=c0=S(I), so it PRESERVES Re tr(R Umu A) exactly
    (micro-canonical) while moving the link -- the SU(N) analog of the SU(2) over-relaxation."""
    full = U.shape[:-3]
    eyeN = b.broadcast_eye(N, full)
    conj4 = b.const([1.0, -1.0, -1.0, -1.0])
    qid = b.const([1.0, 0.0, 0.0, 0.0])
    subs = _sun_subgroups(N)
    for mu in range(D):
        for mask in b.parity(sdims):
            A = _sun_staple(b, U, mu)
            for (i, j) in subs:
                Umu = U[..., mu, :, :]
                M = Umu @ A
                m00 = M[..., i, i]; m01 = M[..., i, j]; m10 = M[..., j, i]; m11 = M[..., j, j]   # noqa: E702
                c0 = b.real(m00) + b.real(m11)
                c1 = -(b.imag(m01) + b.imag(m10))
                c2 = b.real(m10) - b.real(m01)
                c3 = -(b.imag(m00) - b.imag(m11))
                Asub = b.stack([c0, c1, c2, c3], -1) * conj4
                if overrelax:
                    k = b.norm(Asub, -1, True)
                    e = _qconj(b, Asub) / (k + 1e-30)          # = c/|c|, the action-maximising direction
                    q = 2.0 * e[..., 0:1] * e - qid            # reflect the trivial rotation about e
                else:
                    q = _su2_heatbath_link(b, Asub, beta / N)
                r2 = _su2_matrix(b, q)
                R = b.clone(eyeN)
                R[..., i, i] = r2[..., 0, 0]; R[..., i, j] = r2[..., 0, 1]                       # noqa: E702
                R[..., j, i] = r2[..., 1, 0]; R[..., j, j] = r2[..., 1, 1]                       # noqa: E702
                U[..., mu, :, :] = b.where(mask[..., None, None], R @ Umu, Umu)


def _sun_hb_sweep(b, U, sdims, N, beta, step, n_or=4):
    """One SU(N) update: a Cabibbo-Marinari HEAT-BATH pass + ``n_or`` micro-canonical OVER-RELAXATION passes
    (each recomputes staples, so the reflections are non-trivial decorrelating moves). The over-relaxation is
    action-preserving (see ``_sun_cm_pass``), so heat-bath + over-relaxation samples the SAME equilibrium as
    the heat-bath alone but decorrelates far faster -- the SU(N) analog of ``_su2_hb_sweep``. ``step`` unused."""
    _sun_cm_pass(b, U, sdims, N, beta, overrelax=False)
    for _ in range(int(n_or)):
        _sun_cm_pass(b, U, sdims, N, beta, overrelax=True)


def _sun_action(b, U, N):
    phi = b.zeros(U.shape[:-3])
    for mu in range(D):
        for nu in range(mu + 1, D):
            Up = (U[..., mu, :, :] @ b.roll(U[..., nu, :, :], -1, _sax(mu, 2))
                  @ _dag(b, b.roll(U[..., mu, :, :], -1, _sax(nu, 2))) @ _dag(b, U[..., nu, :, :]))
            phi = phi + (1.0 - b.real(b.trace(Up)) / N)
    return phi


# ══════════════════════════════════════════════════════════════════════════════
# group dispatch: (init, sweep, action, default_step); init(b,dims,batch),
# sweep(b,link,sdims,beta,step), action(b,link)
# ══════════════════════════════════════════════════════════════════════════════
def _ops(group: str, method: str = "metropolis"):
    """``method="heatbath"`` selects the Kennedy-Pendleton / Cabibbo-Marinari heat-bath +
    over-relaxation sweep for SU(2)/SU(N) (same equilibrium as Metropolis, ~10x faster to
    thermalise); U(1) keeps its already-fast Metropolis."""
    hb = (method == "heatbath")
    if group == "u1":
        return _u1_init, _u1_sweep, _u1_action, 1.0
    if group == "su2":
        return _su2_init, (_su2_hb_sweep if hb else _su2_sweep), _su2_action, 0.35
    if group.startswith("su") and group[2:].isdigit():
        N = int(group[2:])
        if N < 2:
            raise ValueError(f"N must be >= 2; got '{group}'")
        sweep = ((lambda b, link, sdims, beta, s, _N=N: _sun_hb_sweep(b, link, sdims, _N, beta, s)) if hb
                 else (lambda b, link, sdims, beta, s, _N=N: _sun_sweep(b, link, sdims, _N, beta, s)))
        return (lambda b, dims, batch, _N=N: _sun_init(b, dims, batch, _N),
                sweep,
                lambda b, link, _N=N: _sun_action(b, link, _N),
                0.30 * 3.0 / N)
    raise ValueError(f"unknown group '{group}' (use 'u1', 'su2', 'su3', 'su4', ...)")


def _batch_tuple(batch):
    return () if not batch else (int(batch),)


def _require_even_for_heatbath(method, sdims):
    """The checkerboard heat-bath colours sites by coordinate parity; an ODD extent makes a site and its
    periodic neighbour share a colour, so they update simultaneously -- detailed balance breaks and the
    field silently stays disordered (mean plaquette ~ 0 at any beta). Fail loud rather than return
    garbage. Metropolis is unaffected (it accepts/rejects per site, no two-colour sublattice)."""
    if method == "heatbath" and any(int(d) % 2 for d in sdims):
        raise ValueError(
            f"checkerboard heat-bath requires EVEN lattice extents; got dims={tuple(sdims)}. "
            f"Odd extents silently disorder the field under periodic boundary conditions. "
            f"Use an even lattice, or method='metropolis' (which handles odd extents).")


def config(dims=(8, 8, 8, 16), beta=1.0, *, group="u1", seed=0, therm=250, step=None,
           device=None, batch=0, method="metropolis"):
    """Thermalise and return the action-density field phi(x). ``device=None`` runs on numpy (CPU); a
    torch device (e.g. ``"cuda"``) runs on the GPU. ``batch=n`` evolves ``n`` INDEPENDENT chains at once
    and returns a leading batch axis of size ``n`` (the GPU fast path for an ensemble)."""
    b = _Backend(device).seed(seed)
    init, sweep, action, dstep = _ops(group, method)
    step = dstep if step is None else step
    bt, sdims = _batch_tuple(batch), tuple(dims)
    _require_even_for_heatbath(method, sdims)
    link = init(b, sdims, bt)
    for _ in range(therm):
        sweep(b, link, sdims, beta, step)
    return action(b, link)


def config_batch(dims=(8, 8, 8, 16), beta=1.0, *, group="u1", seed=0, therm=250, n=16,
                 step=None, device=None, method="metropolis"):
    """``n`` independent thermalised action-density fields as one ``(n, *dims)`` array (all chains run
    in parallel). The ensemble fast path; on a GPU this is one saturating call instead of ``n`` serial
    generations. Read each with ``field[i]``."""
    return config(dims, beta, group=group, seed=seed, therm=therm, step=step, device=device, batch=n, method=method)


def gauge_field(dims=(8, 8, 8, 16), beta=1.0, *, group="u1", seed=0, therm=250, step=None,
                device=None, batch=0, method="metropolis"):
    """Thermalise and return the raw LINK field (for export via configio)."""
    b = _Backend(device).seed(seed)
    init, sweep, _action, dstep = _ops(group, method)
    step = dstep if step is None else step
    bt, sdims = _batch_tuple(batch), tuple(dims)
    _require_even_for_heatbath(method, sdims)
    link = init(b, sdims, bt)
    for _ in range(therm):
        sweep(b, link, sdims, beta, step)
    return link


def action_density(link, *, group="u1", dims=None, device=None, project="full"):
    """The gauge-invariant action density phi(x) from a raw LINK field. ``dims`` is unused (kept for
    call-compat); the reduction is intrinsic. ``device`` selects the backend the link lives on.
    ``project`` (SU(2)): ``"full"`` the SU(2) action; ``"centre"`` the Z2 centre-projected field
    (z = sign(q0)); ``"coset"`` the centre-removed SU(2)/Z2 field (sign(q0)*q)."""
    b = _Backend(device)
    if project == "full":
        return _ops(group)[2](b, link)
    if group != "su2":
        raise ValueError(f"project='{project}' is SU(2)-only; got group='{group}'")
    if project == "centre":
        return _su2_action_centre(b, link)
    if project == "coset":
        return _su2_action_coset(b, link)
    raise ValueError(f"unknown project='{project}' (full | centre | coset)")


def stream(dims=(8, 8, 8, 16), beta=1.0, *, group="u1", seed=0, therm=250, gap=5, n=1, step=None,
           device=None, method="metropolis"):
    """Yield ``n`` decorrelated action-density fields from one chain: thermalise, then one every ``gap``
    sweeps. For an independent-chain ensemble in one parallel call use ``config_batch``."""
    b = _Backend(device).seed(seed)
    init, sweep, action, dstep = _ops(group, method)
    step = dstep if step is None else step
    sdims = tuple(dims)
    _require_even_for_heatbath(method, sdims)
    link = init(b, sdims, ())
    for _ in range(therm):
        sweep(b, link, sdims, beta, step)
    for _ in range(n):
        for _ in range(gap):
            sweep(b, link, sdims, beta, step)
        yield action(b, link)


def free_scalar(dims=(8, 8, 64), m=0.5, *, seed=0, device=None):
    """A free scalar field of mass m, sampled in momentum space with the lattice propagator
    G(p) = 1/(phat^2 + m^2). Its time-correlation has an EXACT gap E0 = arccosh(1 + m^2/2). ``device``
    selects the backend; use a long time axis (last) for the DMD."""
    b = _Backend(device).seed(seed)
    ks = [b.fftfreq(L) * 2 * np.pi for L in dims]
    phat2 = b.zeros(dims)
    for g in b.meshgrid(ks):
        phat2 = phat2 + 4 * b.sin(g / 2) ** 2
    G = 1.0 / (phat2 + m * m)
    return b.real(b.ifftn(b.fftn(b.randn(dims)) * b.sqrt(G)))


# ══════════════════════════════════════════════════════════════════════════════
# CLI: batch-generate action-density configs to .npy (the GPU fast path).
#   python lattice_generator.py --group su2 --L 16 --betas 0.8:2.7:0.1 --n 256 --out /workspace/out
# ``--betas`` is a comma list (0.8,0.9,1.0) or an inclusive range lo:hi:step.
# Each beta -> one (n, L,L,L,T) float32 file  <group>_L<L>_b<beta>.s000.npy  (T defaults to 2L).
# ══════════════════════════════════════════════════════════════════════════════
def _parse_betas(spec: str):
    if ":" in spec:
        lo, hi, step = (float(x) for x in spec.split(":"))
        out, b = [], lo
        while b <= hi + 1e-9:
            out.append(round(b, 4)); b += step
        return out
    return [round(float(x), 4) for x in spec.split(",")]


def campaign_seed(seed0, beta, shard):
    """Index -> RNG seed for a sharded campaign: seed0 + 1000*round(100*beta) + shard.

    A dataset is reproducible only if the seed of every shard can be recovered from its FILENAME,
    which carries just (group, L, beta, shard index). Published alongside the data, this is the
    'seed map' half of the (group, L, T, beta, seed, therm, method) tuple."""
    return int(seed0) + 1000 * int(round(100 * float(beta))) + int(shard)


def _cli():
    import argparse
    import os
    import time
    ap = argparse.ArgumentParser(
        description="Batch-generate thermalised lattice configs (.npy): the gauge-invariant action "
                    "density, or the raw LINK field the Wilson-loop reads need.")
    ap.add_argument("--group", default="su2", help="u1 | su2 | su3 | su4 ...")
    ap.add_argument("--L", type=int, default=16, help="spatial extent; lattice is L^3 x T")
    ap.add_argument("--T", type=int, default=0, help="temporal extent (default 2L)")
    ap.add_argument("--betas", required=True, help="comma list 0.8,0.9,1.0  or inclusive range lo:hi:step")
    ap.add_argument("--n", type=int, default=256, help="configs per beta (independent batched chains)")
    ap.add_argument("--therm", type=int, default=100, help="thermalisation sweeps (su2 equilibrates ~25)")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--device", default="cuda", help="cuda | cpu | numpy")
    ap.add_argument("--method", default="heatbath", help="heatbath (su2/su3) | metropolis")
    ap.add_argument("--out", default=".", help="output directory")
    # The action density is an intrinsic REDUCTION of the links: one gauge-invariant scalar per site,
    # with the direction and group axes summed away. Wilson loops are ordered products of link
    # matrices around a contour, so they cannot be rebuilt from it -- which is why a links campaign
    # is a distinct product and not a post-processing step.
    ap.add_argument("--field", default="density", choices=("density", "links"),
                    help="density: phi(x), shape (n,L,L,L,T)  |  links: raw U_mu(x), (n,L,L,L,T,4,4)")
    ap.add_argument("--shards", type=int, default=1,
                    help="shards per beta; each is an independent batch of --n chains")
    a = ap.parse_args()
    T = a.T or 2 * a.L
    dev = None if a.device.lower() in ("none", "numpy") else a.device
    betas = _parse_betas(a.betas)
    os.makedirs(a.out, exist_ok=True)
    print(f"{a.group} L{a.L}^3 x{T}  field={a.field}  n={a.n}x{a.shards} shards  therm={a.therm}  "
          f"device={dev or 'numpy'}  method={a.method}")
    print(f"betas ({len(betas)}): {betas}\nout: {a.out}", flush=True)
    for beta in betas:
        for k in range(a.shards):
            path = os.path.join(a.out, f"{a.group}_L{a.L}_b{beta:.2f}.s{k:03d}.npy")
            if os.path.exists(path):                  # a resumed campaign must not redo finished work
                print(f"  {os.path.basename(path)} exists -- skipping", flush=True)
                continue
            seed = campaign_seed(a.seed, beta, k)
            t0 = time.time()
            if a.field == "links":
                field = gauge_field((a.L, a.L, a.L, T), beta, group=a.group, seed=seed,
                                    therm=a.therm, device=dev, batch=a.n, method=a.method)
            else:
                field = config_batch((a.L, a.L, a.L, T), beta, group=a.group, seed=seed,
                                     therm=a.therm, n=a.n, device=dev, method=a.method)
            field = field.detach().cpu().numpy() if hasattr(field, "detach") else np.asarray(field)
            field = field.astype(np.float32)
            tmp = path + ".tmp"                       # never leave a half-written shard behind
            np.save(tmp, field, allow_pickle=False)
            os.replace(tmp + ".npy" if os.path.exists(tmp + ".npy") else tmp, path)
            print(f"  {a.group} b{beta:.2f} s{k:03d} seed={seed}: {tuple(field.shape)}  "
                  f"mean={field.mean():.4f}  ({time.time()-t0:.0f}s)  -> {path}", flush=True)
    print("done.", flush=True)


if __name__ == "__main__":
    _cli()


def resolve_device(requested=None):
    """None (numpy) or a torch device string, from an explicit request or by probing for CUDA.

    One copy: string_tension_eq_centre and 8_7_run_transfer_gap both stated this, and a change to
    the probing rule in one would have silently left the other on a different device.
    """
    if requested is not None:
        return None if requested.strip().lower() in {"", "numpy", "cpu", "none"} else requested
    try:
        import torch
        return "cuda" if torch.cuda.is_available() else None
    except Exception:
        return None
