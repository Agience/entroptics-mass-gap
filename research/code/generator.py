"""
generator.py -- config generator (research/code/).

Not a read and not a diagnostic: this only GENERATES configurations for the
entroptics read to consume. ``config`` hands back a ready-to-read scalar field
(the gauge-invariant local action density phi(x) = sum_{mu<nu}(1 - (1/N) Re tr U_p)).

Two gauge groups, one vectorised checkerboard Metropolis:
  * ``group="u1"``  -- compact U(1), the abelian FOIL: confines at small beta,
    deconfines to a Coulomb phase near beta_c ~ 1.01 (it CROSSES).
  * ``group="su2"`` -- SU(2), non-abelian: confines at every beta, a smooth
    crossover with no deconfinement (the NO-BUMP contrast).

    from generator import config, stream
    field = config((8, 8, 8, 16), beta=2.3, group="su2", seed=0)
    for field in stream((8, 8, 8, 16), 0.8, group="u1", seed=0, n=40): ...
"""
from __future__ import annotations

import numpy as np

D = 4  # spacetime dimensions


def _site_parity(dims):
    """Even/odd site masks (coordinate-sum parity): a checkerboard sweep updates one
    parity at a time so links updated together never share a plaquette."""
    g = np.indices(dims).sum(axis=0)
    return [g % 2 == 0, g % 2 == 1]


# ══════════════════════════════════════════════════════════════════════════════
# compact U(1): links are phases theta, U = exp(i theta)
# ══════════════════════════════════════════════════════════════════════════════
def _u1_init(dims, rng):
    return rng.uniform(-np.pi, np.pi, size=(*dims, D))


def _u1_staple(U, mu):
    S = np.zeros_like(U[..., 0])
    Umu = U[..., mu]
    for nu in range(D):
        if nu == mu:
            continue
        Unu = U[..., nu]
        Unu_pmu = np.roll(Unu, -1, axis=mu)
        S += Unu_pmu * np.conj(np.roll(Umu, -1, axis=nu)) * np.conj(Unu)          # forward
        S += (np.roll(Unu, 1, axis=nu) * np.conj(np.roll(Unu_pmu, 1, axis=nu))
              * np.conj(np.roll(Umu, 1, axis=nu)))                                # backward
    return S


def _u1_sweep(theta, beta, rng, step):
    for mu in range(D):
        for mask in _site_parity(theta.shape[:-1]):
            U = np.exp(1j * theta)
            S = _u1_staple(U, mu)
            th = theta[..., mu]
            prop = th + rng.uniform(-step, step, size=th.shape)
            dS = -beta * np.real((np.exp(1j * prop) - np.exp(1j * th)) * S)
            acc = (rng.random(th.shape) < np.exp(-dS)) & mask
            theta[..., mu] = np.where(acc, np.mod(prop + np.pi, 2 * np.pi) - np.pi, th)


def _u1_action(theta):
    phi = np.zeros(theta.shape[:-1])
    for mu in range(D):
        for nu in range(mu + 1, D):
            P = (theta[..., mu] + np.roll(theta[..., nu], -1, axis=mu)
                 - np.roll(theta[..., mu], -1, axis=nu) - theta[..., nu])
            phi += 1.0 - np.cos(P)
    return phi


# ══════════════════════════════════════════════════════════════════════════════
# SU(2): links are unit quaternions q, U = q0 I + i (q1 s1 + q2 s2 + q3 s3)
# quaternion product uses sigma_i sigma_j = d_ij + i eps_ijk sigma_k.
# ══════════════════════════════════════════════════════════════════════════════
def _qmul(a, b):
    a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
    b0, b1, b2, b3 = b[..., 0], b[..., 1], b[..., 2], b[..., 3]
    return np.stack([
        a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3,
        a0 * b1 + a1 * b0 - a2 * b3 + a3 * b2,
        a0 * b2 + a2 * b0 - a3 * b1 + a1 * b3,
        a0 * b3 + a3 * b0 - a1 * b2 + a2 * b1,
    ], axis=-1)


def _qconj(a):
    return a * np.array([1.0, -1.0, -1.0, -1.0])


def _sdot(q, a):
    """Scalar part of the SU(2) product U_q U_a = (1/2) Re tr(U_q U_a)."""
    return q[..., 0] * a[..., 0] - (q[..., 1] * a[..., 1]
                                    + q[..., 2] * a[..., 2] + q[..., 3] * a[..., 3])


def _su2_init(dims, rng):
    q = rng.standard_normal((*dims, D, 4))
    return q / np.linalg.norm(q, axis=-1, keepdims=True)


def _su2_staple(q, mu):
    """Sum of the six staple quaternions A_mu(x) with Re tr(U_mu(x) A) = sum_p Re tr U_p."""
    dims = q.shape[:-2]
    A = np.zeros((*dims, 4))
    qmu = q[..., mu, :]
    for nu in range(D):
        if nu == mu:
            continue
        qnu = q[..., nu, :]
        qnu_pmu = np.roll(qnu, -1, axis=mu)                                  # U_nu(x+mu)
        # forward: U_nu(x+mu) U_mu(x+nu)^dag U_nu(x)^dag
        A = A + _qmul(_qmul(qnu_pmu, _qconj(np.roll(qmu, -1, axis=nu))), _qconj(qnu))
        # backward: U_nu(x+mu-nu)^dag U_mu(x-nu)^dag U_nu(x-nu)
        A = A + _qmul(_qmul(_qconj(np.roll(qnu_pmu, 1, axis=nu)),
                            _qconj(np.roll(qmu, 1, axis=nu))), np.roll(qnu, 1, axis=nu))
    return A


def _su2_sweep(q, beta, rng, step):
    dims = q.shape[:-2]
    for mu in range(D):
        A = None
        for mask in _site_parity(dims):
            A = _su2_staple(q, mu)
            qmu = q[..., mu, :]
            r = np.concatenate([np.ones((*dims, 1)), step * rng.standard_normal((*dims, 3))], axis=-1)
            r = r / np.linalg.norm(r, axis=-1, keepdims=True)
            qp = _qmul(r, qmu)                                               # proposed link
            dS = -beta * (_sdot(qp, A) - _sdot(qmu, A))
            acc = (rng.random(dims) < np.exp(-dS)) & mask
            q[..., mu, :] = np.where(acc[..., None], qp, qmu)


def _su2_action(q):
    dims = q.shape[:-2]
    phi = np.zeros(dims)
    for mu in range(D):
        for nu in range(mu + 1, D):
            Up = _qmul(_qmul(_qmul(q[..., mu, :], np.roll(q[..., nu, :], -1, axis=mu)),
                             _qconj(np.roll(q[..., mu, :], -1, axis=nu))), _qconj(q[..., nu, :]))
            phi += 1.0 - Up[..., 0]                     # 1 - (1/2) Re tr U_p
    return phi


# ══════════════════════════════════════════════════════════════════════════════
# group dispatch
# ══════════════════════════════════════════════════════════════════════════════
_GROUPS = {
    "u1":  (_u1_init, _u1_sweep, _u1_action, 1.0),      # (init, sweep, action, default step)
    "su2": (_su2_init, _su2_sweep, _su2_action, 0.35),
}


def config(dims=(8, 8, 8, 16), beta=1.0, *, group="u1", seed=0, therm=250, step=None):
    """Thermalise a configuration and return its action-density field phi(x) directly."""
    init, sweep, action, dstep = _GROUPS[group]
    step = dstep if step is None else step
    rng = np.random.default_rng(seed)
    link = init(dims, rng)
    for _ in range(therm):
        sweep(link, beta, rng, step)
    return action(link)


def stream(dims=(8, 8, 8, 16), beta=1.0, *, group="u1", seed=0, therm=250, gap=5, n=1, step=None):
    """Yield ``n`` decorrelated action-density fields: thermalise, then one every ``gap`` sweeps."""
    init, sweep, action, dstep = _GROUPS[group]
    step = dstep if step is None else step
    rng = np.random.default_rng(seed)
    link = init(dims, rng)
    for _ in range(therm):
        sweep(link, beta, rng, step)
    for _ in range(n):
        for _ in range(gap):
            sweep(link, beta, rng, step)
        yield action(link)
