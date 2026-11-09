"""The heat-bath gap of one box under a frozen boundary.

The finite check of a weighted finite-size criterion is a lower bound
gamma on the gap of the box heat-bath generator H_box = sum_{l in box} (1 - E_l) on L^2 of the box law
given the frozen links W, for every W. This script reads, for a given W, the variational UPPER bound

    gamma <= min_f  E(f, f) / Var(f),   E(f, f) = sum_l E[ Var_l(f) ]   (= <f, H_box f>),

over the span of a basis of gauge-invariant observables linear in each free link: plaquettes (SU(2):
(1/2) tr U_p; U(1): cos and sin of the plaquette angle). For such an f the conditional variance at a link
is explicit: the link law is von Mises-Fisher on S^{p-1} (p = 4 for SU(2), 2 for U(1)) with
kappa = beta |staple sum|, and f = <u_l, x_l> + (rest), so Var_l(f) = x_l^T Cov_vMF x_l. The bound is
min generalised eigenvalue of (D, C): D the mean Dirichlet matrix, C the covariance matrix of the basis
under the box law (sampled). It refutes (gamma < t_l) and cannot certify.

Scalar Gaussian control: real spins, nearest-neighbour precision Q = -Lap + m^2, observables phi_x; the
bound equals the exact box gap ((ma)^2 + 8(1 - cos(pi/(n+1))))/(8 + (ma)^2), reached in the linear sector.

Geometry. The box has n sites a side, and every link whose base site
is in the box is free (4 n^4 links, the upper-face links leaving the box included); every other link is
frozen. It sits at offset 1 in an array of even side >= n + 3. Rolls are periodic but no plaquette
through a free link wraps.

Usage:
  python box_gap_read.py OUT.json GROUP BETA_OR_MASS N BOUNDARY NSAMP [SPACING] [THERM] [NMODE] [SEED]
    GROUP     su2 | u1 | gauss
    BOUNDARY  thermal | cold | hot | twist | bpst:R   (gauss: ignored; the boundary only shifts the mean)
  env BOUNDARY_NPZ=file.npz (array U) replaces the boundary; SAVE_U=file.npz saves the final configuration;
      BASIS=layer: the boundary-layer basis (run_layer): each free link's alignment with its frozen staples,
      link by link (NMODE = 0) or under cosine envelopes by direction and frozen-staple count (NMODE > 0);
      LAYER_CORNER=r keeps only links based within Chebyshev distance r of a box corner; an output file named
      "..._layer..." or "..._layerc<r>..." sets these for queues that pass no environment;
      AUTOCORR=T (or a file AUTOCORR in the working directory) runs T heat-bath-only sweeps after the read and reports the autocorrelation of the slowest
      mode and of the box topological charge (entroptics.reads.decay, biased 1/T at every lag; corr_slow_Q: their
      correlation over the samples, entroptics.reads.coupling at one coordinate)
"""
import json
import os
import sys
import time

import numpy as np
from scipy.special import ive
from scipy.linalg import eigh

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import lattice_generator as lg  # noqa: E402
import entroptics_adapter as E  # noqa: E402

# DERIVED: the spacetime dimension of the four-dimensional lattice
D4 = 4


def geometry(n):
    """The box: every link whose base site lies in the n^4 box, in every
    direction (links leaving the box at its upper faces included)."""
    S = n + 3 + ((n + 3) % 2)
    x = np.indices((S,) * D4)
    # DERIVED: the box sits at offset 1 in the array (module docstring, Geometry), so its sites are 1..n
    inbox = np.all((x >= 1) & (x <= n), axis=0)
    free = np.zeros((S,) * D4 + (D4,), bool)
    for mu in range(D4):
        free[..., mu] = inbox
    return S, free


def vmf_cov(e, kappa, p):
    """Covariance of u ~ exp(kappa <u, e>) on S^{p-1}; e unit (..., p), kappa (...)."""
    k = np.maximum(kappa, 1e-12)
    nu = p / 2.0
    A = ive(nu, k) / ive(nu - 1.0, k)                       # mean resultant length A_p(kappa)
    a_k = A / k
    # CHOSEN: below this kappa the Bessel ratio is replaced by its kappa -> 0 limit (A/k -> 1/p, A -> 0); a
    # numerical switch where the ratio loses precision, not a cut on any read
    small = kappa < 1e-6
    a_k = np.where(small, 1.0 / p, a_k)
    A = np.where(small, 0.0, A)
    I = np.eye(p)
    ee = e[..., :, None] * e[..., None, :]
    return a_k[..., None, None] * I + (1.0 - p * a_k - A * A)[..., None, None] * ee


# ---------------------------------------------------------------- SU(2)
def su2_staples(b, q, mu):
    """The six individual staples of links in direction mu, with their plaquette ids (site, plane)."""
    out = []
    qmu = q[..., mu, :]
    for nu in range(D4):
        if nu == mu:
            continue
        qnu = q[..., nu, :]
        qnu_pmu = np.roll(qnu, -1, axis=mu)
        fwd = lg._qmul(b, lg._qmul(b, qnu_pmu, lg._qconj(b, np.roll(qmu, -1, axis=nu))), lg._qconj(b, qnu))
        bwd = lg._qmul(b, lg._qmul(b, lg._qconj(b, np.roll(qnu_pmu, 1, axis=nu)),
                                   lg._qconj(b, np.roll(qmu, 1, axis=nu))), np.roll(qnu, 1, axis=nu))
        out.append((nu, 0, fwd))
        out.append((nu, -1, bwd))
    return out


def plane_index(mu, nu):
    a, c = min(mu, nu), max(mu, nu)
    return [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)].index((a, c))


def plaq_id(S, site, mu, nu, shift):
    """Flat id of the plaquette in plane {mu, nu} based at site + shift * e_nu."""
    s = np.array(site)
    s[:, nu] = (s[:, nu] + shift) % S
    flat = np.ravel_multi_index(tuple(s.T), (S,) * D4)
    return flat * 6 + plane_index(mu, nu)


def link_terms(group, b, U, S, free, beta, ret_u=False):
    """For every free link: the coefficient vectors x (n_free, 6 or 12, p), plaquette-basis ids, and the
    vMF covariance (n_free, p, p). U(1) carries cos and sin per plaquette (ids 2*pid, 2*pid+1)."""
    X, P, C, Us = [], [], [], []
    for mu in range(D4):
        sites = np.argwhere(free[..., mu])
        # DERIVED: no free link in this direction leaves nothing to collect (a count, exact)
        if len(sites) == 0:
            continue
        idx = tuple(sites.T)
        if group == "su2":
            st = su2_staples(b, U, mu)
            Asum = sum(s[2] for s in st)[idx]                       # (n, 4)
            kap = beta * np.linalg.norm(Asum, axis=-1)
            e = lg._qconj(b, Asum) / np.maximum(np.linalg.norm(Asum, axis=-1, keepdims=True), 1e-30)
            # (1/2) tr U_p = sdot(q_l, staple) = <q_l, conj(staple)>
            xs = np.stack([lg._qconj(b, s[2][idx]) for s in st], axis=1)
            ps = np.stack([plaq_id(S, sites[:, :D4], mu, s[0], s[1]) for s in st], axis=1)
            X.append(xs); P.append(ps); C.append(vmf_cov(e, kap, 4)); Us.append(U[..., mu, :][idx])
        else:
            th = U
            Ue = np.exp(1j * th)
            Umu = Ue[..., mu]
            xs, ps = [], []
            Ssum = 0
            for nu in range(D4):
                if nu == mu:
                    continue
                Unu = Ue[..., nu]
                Unu_pmu = np.roll(Unu, -1, axis=mu)
                fwd = Unu_pmu * np.conj(np.roll(Umu, -1, axis=nu)) * np.conj(Unu)
                bwd = (np.roll(Unu, 1, axis=nu) * np.conj(np.roll(Unu_pmu, 1, axis=nu))
                       * np.conj(np.roll(Umu, 1, axis=nu)))
                for shift, Sst in ((0, fwd), (-1, bwd)):
                    Ss = Sst[idx]
                    Ssum = Ssum + Ss
                    # e^{i theta_l} Ss = e^{+-i theta_p}; the sign makes sin read the oriented angle
                    # DERIVED: shift 0 is the forward staple, -1 the backward one (the loop above)
                    sgn = (1.0 if mu < nu else -1.0) * (1.0 if shift == 0 else -1.0)
                    pid = plaq_id(S, sites[:, :D4], mu, nu, shift)
                    # cos(th + phi) = <u, (Re S, -Im S)>, sin(th + phi) = <u, (Im S, Re S)>
                    xs.append(np.stack([Ss.real, -Ss.imag], -1)); ps.append(2 * pid)
                    xs.append(sgn * np.stack([Ss.imag, Ss.real], -1)); ps.append(2 * pid + 1)
            kap = beta * np.abs(Ssum)
            e = np.stack([Ssum.real, -Ssum.imag], -1) / np.maximum(np.abs(Ssum), 1e-30)[..., None]
            X.append(np.stack(xs, 1)); P.append(np.stack(ps, 1)); C.append(vmf_cov(e, kap, 2))
            Us.append(np.stack([np.cos(th[..., mu][idx]), np.sin(th[..., mu][idx])], -1))
    if ret_u:
        return np.concatenate(X), np.concatenate(P), np.concatenate(C), np.concatenate(Us)
    return np.concatenate(X), np.concatenate(P), np.concatenate(C)


def check_terms(group, b, U, S, free, beta):
    """Every link's coefficient vectors reproduce its plaquettes: <u_l, x_{p,l}> = f_p(U)."""
    X, P, _, Ul = link_terms(group, b, U, S, free, beta, ret_u=True)
    vals = basis_values(group, b, U, S)
    pred = np.einsum("lsi,li->ls", X, Ul)
    err = float(np.abs(pred - vals[P]).max())
    # CHOSEN: a float64 round-off tolerance on an algebraic identity (exact in exact arithmetic); values are
    # O(1), so 1e-9 sits several decades above the error of a few quaternion products
    assert err < 1e-9, f"linear coefficients do not reproduce the plaquettes: max error {err}"
    return err


def basis_values(group, b, U, S):
    """All plaquette basis values on the array (flat id order)."""
    vals = np.zeros((S,) * D4 + (6,) + ((2,) if group == "u1" else ()))
    for mu in range(D4):
        for nu in range(mu + 1, D4):
            k = plane_index(mu, nu)
            if group == "su2":
                Up = lg._qmul(b, lg._qmul(b, lg._qmul(b, U[..., mu, :], np.roll(U[..., nu, :], -1, axis=mu)),
                                          lg._qconj(b, np.roll(U[..., mu, :], -1, axis=nu))),
                              lg._qconj(b, U[..., nu, :]))
                vals[..., k] = Up[..., 0]
            else:
                th = (U[..., mu] + np.roll(U[..., nu], -1, axis=mu) - np.roll(U[..., mu], -1, axis=nu)
                      - U[..., nu])
                vals[..., k, 0] = np.cos(th)
                vals[..., k, 1] = np.sin(th)
    return vals.reshape(-1)


def u1_hb_sweep(rng, th, beta, free):
    S = th.shape[0]
    par = np.indices((S,) * D4).sum(0) % 2
    for mu in range(D4):
        for p in (0, 1):
            Ue = np.exp(1j * th)
            Umu = Ue[..., mu]
            Ss = 0
            for nu in range(D4):
                if nu == mu:
                    continue
                Unu = Ue[..., nu]
                Unu_pmu = np.roll(Unu, -1, axis=mu)
                Ss = Ss + Unu_pmu * np.conj(np.roll(Umu, -1, axis=nu)) * np.conj(Unu)
                Ss = Ss + (np.roll(Unu, 1, axis=nu) * np.conj(np.roll(Unu_pmu, 1, axis=nu))
                           * np.conj(np.roll(Umu, 1, axis=nu)))
            m = free[..., mu] & (par == p)
            kap = beta * np.abs(Ss[m])
            new = rng.vonmises(-np.angle(Ss[m]), np.maximum(kap, 1e-12))
            th[..., mu][m] = new


def qexp(v):
    """exp of a pure-imaginary quaternion field v (..., 3) as a unit quaternion (..., 4)."""
    a = np.linalg.norm(v, axis=-1, keepdims=True)
    # CHOSEN: a division guard for sin(a)/a at a = 0, where the limit 1 is used; any tiny value serves
    s = np.where(a > 1e-15, np.sin(a) / np.maximum(a, 1e-15), 1.0)
    return np.concatenate([np.cos(a), s * v], -1)


def init_boundary(group, b, rng, boundary, sd, beta, therm, free, n):
    """The configuration whose frozen links are the boundary W.
      thermal  equilibrium of the whole periodic array at beta
      cold     identity links
      hot      Haar-random links (U(1): uniform phases)
      twist    cold, with the links of direction 1 on the plane x_0 = 0 (outside the box) times the centre
               element -1 (U(1): phase pi): a flux sheet against the box's lower x_0 face
      bpst:R   SU(2) only: the regular-gauge BPST field of size R (lattice units) centred in the box,
               U_mu(x) = exp(Im(conj(q) e_mu)/(|q|^2 + R^2)), q the link midpoint as a quaternion"""
    S = sd[0]
    if group == "su2":
        U = lg._su2_init(b, sd, ())
        if boundary in ("cold", "twist") or boundary.startswith("bpst"):
            U = np.zeros_like(U); U[..., 0] = 1.0
        if boundary == "thermal":
            for _ in range(therm):
                lg._su2_hb_sweep(b, U, sd, beta, None, n_or=2)
        if boundary == "twist":
            U[0, :, :, :, 1, :] *= -1.0
        if boundary.startswith("bpst"):
            R = float(boundary.split(":")[1])
            c = (n + 1) / 2.0 + 0.5
            x = np.indices(sd).astype(float) - c                      # (4, S, S, S, S)
            for mu in range(D4):
                q = np.moveaxis(x, 0, -1).copy()
                q[..., mu] += 0.5
                r2 = (q ** 2).sum(-1)
                e = np.zeros(4); e[mu] = 1.0
                prod = lg._qmul(b, lg._qconj(b, q), np.broadcast_to(e, q.shape))
                v = prod[..., 1:] / (r2 + R * R)[..., None]
                U[..., mu, :] = qexp(v)
        return U
    U = rng.uniform(-np.pi, np.pi, sd + (D4,))
    if boundary in ("cold", "twist"):
        U = np.zeros_like(U)
    if boundary == "thermal":
        allf = np.ones_like(free)
        for _ in range(therm):
            u1_hb_sweep(rng, U, beta, allf)
    if boundary == "twist":
        U[0, :, :, :, 1] += np.pi
    return U


def run_gauge(group, beta, l, boundary, nsamp, spacing, therm, nmode, seed):
    S, free = geometry(l)
    b = lg._Backend(None).seed(seed)
    rng = np.random.default_rng(seed)
    sd = (S,) * D4
    U = init_boundary(group, b, rng, boundary, sd, beta, therm, free, l)
    if os.environ.get("BOUNDARY_NPZ"):                         # a boundary handed in by the search driver
        U = np.load(os.environ["BOUNDARY_NPZ"])["U"]
    if group == "su2":
        frozen = ~free
        sweep = lambda: lg._su2_hb_sweep(b, U, sd, beta, None, n_or=2, frozen=frozen)
    else:
        sweep = lambda: u1_hb_sweep(rng, U, beta, free)
    for _ in range(therm):                                   # thermalise the box at the frozen boundary
        sweep()
    # the basis: plaquettes through a free link (all of them, or low cosine modes when too many)
    X0, P0, _ = link_terms(group, b, U, S, free, beta)
    used = np.unique(P0)
    nb = len(used)
    remap = lambda P: np.searchsorted(used, P)
    meta_check = check_terms(group, b, U, S, free, beta)
    if nmode and nb > max(nsamp // 20, 1):
        ncomp = 2 if group == "u1" else 1
        site = used // (6 * ncomp)
        coords = np.array(np.unravel_index(site, sd)).T
        # classes: plane, component, and whether the plaquette touches the boundary layer (a base-site
        # coordinate 0, 1 or n: plaquettes holding frozen links or links leaving the box). The slowest
        # mode of a box sits there (read at n = 3 with the full basis: 99% of its weight on the layer).
        # DERIVED: the box sites are 1..l (geometry), so base coordinate <= 1 or >= l is the boundary layer
        layer = np.any((coords <= 1) | (coords >= l), axis=1).astype(int)
        cls = ((used // ncomp) % 6 * ncomp + used % ncomp) * 2 + layer
        ncls = 6 * ncomp * 2
        ph = np.array([np.prod([np.cos(np.pi * k[mm] * (coords[:, mm] - 0.5) / (l + 1)) for mm in range(D4)],
                               axis=0) for k in np.ndindex(*(nmode,) * D4)], dtype=np.float32)   # (nsp, nb)
        Phi = (ph, cls, ncls)          # mode a = sp * ncls + cl: ph[sp, p] on the plaquettes of class cl
    else:
        Phi = None
    m = nb if Phi is None else Phi[0].shape[0] * Phi[2]
    Dsum = np.zeros((m, m))
    F, Q, DQ = [], [], []
    QEVERY = int(os.environ.get("QEVERY", "20"))
    t0 = time.time()
    for s in range(nsamp):
        for _ in range(spacing):
            sweep()
        X, P, Cv = link_terms(group, b, U, S, free, beta)
        Pi = remap(P)
        vals = basis_values(group, b, U, S)[used]
        if Phi is None:
            # D[a, c] += x_a^T Cov x_c over the plaquettes a, c of each link
            G = np.einsum("lai,lij,lcj->lac", X, Cv, X)
            Ii = np.repeat(Pi[:, :, None], Pi.shape[1], 2)
            Jj = np.repeat(Pi[:, None, :], Pi.shape[1], 1)
            np.add.at(Dsum, (Ii.ravel(), Jj.ravel()), G.ravel())
            F.append(vals)
            Q.append(qbox(group, b, U, S, l))
            # DERIVED: every QEVERY-th sample (a remainder test; the cadence itself is the QEVERY setting)
            if s % QEVERY == 0:
                DQ.append(q_dirichlet(group, b, rng, U, S, l, free, beta))
        else:
            Dsum += mode_dirichlet(Phi, Pi, X, Cv)
            F.append(mode_values(Phi, vals))
            Q.append(qbox(group, b, U, S, l))
            # DERIVED: every QEVERY-th sample (a remainder test; the cadence itself is the QEVERY setting)
            if s % QEVERY == 0:
                DQ.append(q_dirichlet(group, b, rng, U, S, l, free, beta))
    F = np.array(F)
    if os.environ.get("SAVE_U"):
        np.savez_compressed(os.environ["SAVE_U"], U=U)
    Dm = Dsum / nsamp
    Cm = np.cov(F.T)
    meta = finish(Dm, Cm, F, dict(group=group, beta=beta, l=l, boundary=boundary, nsamp=nsamp,
                                  spacing=spacing, therm=therm, basis=int(m), nfree=int(free.sum()),
                                  seconds=round(time.time() - t0, 1), term_check=meta_check))
    cvec = np.array(meta.pop("slow_coef"))
    if os.environ.get("KEEP_SLOW") and Phi is None:
        # the slowest combination on the plaquettes: weight (coefficient times standard deviation), with
        # each plaquette's base site and plane
        sd_f = F.std(0)
        npl = 2 if group == "u1" else 1
        sites = np.array(np.unravel_index(used // (6 * npl), sd)).T
        meta["slow_weight"] = (cvec * sd_f).tolist()
        meta["slow_site"] = sites.tolist()
        meta["slow_plane"] = ((used // npl) % 6).tolist()
        meta["slow_coef_raw"] = cvec.tolist()
        meta["used"] = used.tolist()
    Q = np.array(Q)
    slow = F @ cvec
    meta["Q_var"] = float(np.var(Q))
    # DERIVED: a correlation with a constant series is undefined; zero variance is the exact degenerate case
    meta["corr_slow_Q"] = E.correlation(slow, Q) if np.var(Q) > 0 else 0.0
    # DERIVED: the Rayleigh quotient divides by Var(Q); zero variance is the exact degenerate case
    if DQ and np.var(Q) > 0:
        # the box charge's own Rayleigh quotient: an upper bound on the gap from Q alone
        meta["gamma_Q"] = float(np.mean(DQ) / np.var(Q, ddof=1))
        meta["gamma_Q_err"] = float(np.std(DQ, ddof=1) / np.sqrt(len(DQ)) / np.var(Q, ddof=1))
    nac = int(os.environ.get("AUTOCORR", "0"))
    if not nac and os.path.exists("AUTOCORR"):                # a run directory may set it for its queue
        nac = int(open("AUTOCORR").read().strip() or 0)
    if nac:
        # heat bath only (no over-relaxation): the generator the bound is about, swept systematically
        if group == "su2":
            hb = lambda: lg._su2_hb_sweep(b, U, sd, beta, None, n_or=0, frozen=frozen)
        else:
            hb = lambda: u1_hb_sweep(rng, U, beta, free)
        ts, tq = [], []
        for _ in range(nac):
            hb()
            v = basis_values(group, b, U, S)[used]
            ts.append((mode_values(Phi, v) if Phi is not None else v) @ cvec)
            tq.append(qbox(group, b, U, S, l))
        meta["autocorr_sweeps"] = nac
        meta["acf_slow"] = acf(np.array(ts), 30)
        meta["acf_Q"] = acf(np.array(tq), 30)
    return meta


# DERIVED: nres=2 is the least number of resamples for which the unbiased (ddof=1) sample variance exists
def q_dirichlet(group, b, rng, U, S, n, free, beta, nres=2):
    """sum_l Var_l(Q) at the configuration U, by resampling: the links of one direction and one checkerboard
    parity are conditionally independent, and Q is linear in each link with no term holding two of them,
    so the variance of Q over a joint resample of the class is the sum of its single-link variances. Each
    class is resampled nres times and the sample variance taken (unbiased); U is restored."""
    tot = 0.0
    par = np.indices((S,) * D4).sum(0) % 2
    for mu in range(D4):
        for p in (0, 1):
            m = free[..., mu] & (par == p)
            if not m.any():
                continue
            keep = U[..., mu, :].copy() if group == "su2" else U[..., mu].copy()
            qs = []
            for _ in range(nres):
                if group == "su2":
                    A = lg._su2_staple(b, U, mu)
                    new = lg._su2_heatbath_link(b, A, beta)
                    U[..., mu, :] = np.where(m[..., None], new, keep)
                else:
                    Ue = np.exp(1j * U)
                    Umu = Ue[..., mu]
                    Ss = 0
                    for nu in range(D4):
                        if nu == mu:
                            continue
                        Unu = Ue[..., nu]
                        Unu_pmu = np.roll(Unu, -1, axis=mu)
                        Ss = Ss + Unu_pmu * np.conj(np.roll(Umu, -1, axis=nu)) * np.conj(Unu)
                        Ss = Ss + (np.roll(Unu, 1, axis=nu) * np.conj(np.roll(Unu_pmu, 1, axis=nu))
                                   * np.conj(np.roll(Umu, 1, axis=nu)))
                    th = keep.copy()
                    th[m] = rng.vonmises(-np.angle(Ss[m]), np.maximum(beta * np.abs(Ss[m]), 1e-12))
                    U[..., mu] = th
                qs.append(qbox(group, b, U, S, n))
            tot += float(np.var(qs, ddof=1))
            if group == "su2":
                U[..., mu, :] = keep
            else:
                U[..., mu] = keep
    return tot


def acf(x, kmax):
    """C(k)/C(0) for k = 1..kmax, C the chain's own autocovariance from entroptics.reads.decay (own mean removed,
    open record, the biased 1/T normalisation at every lag)."""
    c = np.asarray(E.decay(np.asarray(x, dtype=float)[:, None]), dtype=float)
    # DERIVED: the normalised autocorrelation divides by the variance C(0); a constant series has none
    return [float(v) for v in c[1:kmax + 1] / c[0]] if c[0] > 0 else []


def mode_dirichlet(Phi, Pi, X, Cv):
    ph, cls, ncls = Phi
    nsp = ph.shape[0]
    D = np.zeros((nsp * ncls, nsp * ncls))
    for c0 in range(0, len(Pi), 4096):                        # chunks of links bound the memory
        sl = slice(c0, c0 + 4096)
        P_ = Pi[sl]
        Y = np.zeros((nsp, ncls, P_.shape[0], X.shape[-1]))
        g = ph[:, P_]                                          # (nsp, chunk, k)
        cl = cls[P_]                                           # (chunk, k)
        for c in range(ncls):
            Y[:, c] = np.einsum("slk,lki->sli", g * (cl == c), X[sl])
        Y = Y.reshape(nsp * ncls, P_.shape[0], -1)
        Z = np.einsum("ali,lij->alj", Y, Cv[sl], optimize=True)
        D += Y.reshape(Y.shape[0], -1) @ Z.reshape(Z.shape[0], -1).T
    return D


def mode_values(Phi, vals):
    ph, cls, ncls = Phi
    out = np.zeros((ph.shape[0], ncls))
    for c in range(ncls):
        m = cls == c
        out[:, c] = ph[:, m] @ vals[m]
    return out.reshape(-1)


def qbox(group, b, U, S, n):
    """A topological-charge density summed over the box: sum_x (v01.v23 - v02.v13 + v03.v12), v the
    vector part of the plaquette (SU(2)) or the sine of its angle (U(1)). The normalisation is free: the
    read uses it only through correlations."""
    v = {}
    for mu in range(D4):
        for nu in range(mu + 1, D4):
            if group == "su2":
                Up = lg._qmul(b, lg._qmul(b, lg._qmul(b, U[..., mu, :], np.roll(U[..., nu, :], -1, axis=mu)),
                                          lg._qconj(b, np.roll(U[..., mu, :], -1, axis=nu))),
                              lg._qconj(b, U[..., nu, :]))
                v[mu, nu] = Up[..., 1:]
            else:
                th = (U[..., mu] + np.roll(U[..., nu], -1, axis=mu) - np.roll(U[..., mu], -1, axis=nu)
                      - U[..., nu])
                v[mu, nu] = np.sin(th)[..., None]
    q = (v[0, 1] * v[2, 3]).sum(-1) - (v[0, 2] * v[1, 3]).sum(-1) + (v[0, 3] * v[1, 2]).sum(-1)
    return float(q[(slice(1, n + 1),) * D4].sum())


def finish(Dm, Cm, F, meta):
    w, V = np.linalg.eigh(Cm)
    keep = w > w.max() * 1e-8
    T = V[:, keep] / np.sqrt(w[keep])
    lam, Z = eigh(T.T @ Dm @ T)
    meta["gamma_var"] = float(lam[0])
    meta["slow_coef"] = (T @ Z[:, 0]).tolist()
    meta["gamma_var_next"] = [float(x) for x in lam[1:5]]
    # jackknife over 8 blocks of samples for the leading bound
    nblk = 8
    blk = np.array_split(np.arange(F.shape[0]), nblk)
    jk = []
    for i in range(nblk):
        idx = np.concatenate([blk[j] for j in range(nblk) if j != i])
        Cj = np.cov(F[idx].T)
        wj, Vj = np.linalg.eigh(Cj)
        kj = wj > wj.max() * 1e-8
        Tj = Vj[:, kj] / np.sqrt(wj[kj])
        jk.append(eigh(Tj.T @ Dm @ Tj, eigvals_only=True)[0])
    jk = np.array(jk)
    meta["gamma_var_jk_err"] = float(np.sqrt((nblk - 1) * np.var(jk)))
    meta["rank_C"] = int(keep.sum())
    return meta


def frozen_staples(group, b, U, free):
    """For every free link: the sum of its staples made only of frozen links (computed on the configuration
    with the free links set to zero, so a staple holding a free link vanishes), as the coefficient vector
    of the link's alignment with the frozen layer, and the number of such staples. SU(2): 4-vectors
    conj(staple); U(1): the 2-vector (Re S, -Im S) and its rotation (Im S, Re S) (cos and sin)."""
    Z = U.copy()
    if group == "su2":
        Z[free] = 0.0
    else:
        Ze = np.exp(1j * U)
        Ze[free] = 0.0
    out, cnt, pos, dirs = [], [], [], []
    for mu in range(D4):
        sites = np.argwhere(free[..., mu])
        idx = tuple(sites.T)
        if group == "su2":
            st = su2_staples(b, Z, mu)
            tot = sum(lg._qconj(b, x[2][idx]) for x in st)
            # DERIVED: a staple holding a free link was zeroed above, so a nonzero staple is an all-frozen one
            k = sum((np.abs(x[2][idx]).sum(-1) > 0).astype(int) for x in st)
            out.append(tot[:, None, :])
        else:
            Umu = Ze[..., mu]
            Ss = 0
            k = 0
            for nu in range(D4):
                if nu == mu:
                    continue
                Unu = Ze[..., nu]
                Unu_pmu = np.roll(Unu, -1, axis=mu)
                fwd = Unu_pmu * np.conj(np.roll(Umu, -1, axis=nu)) * np.conj(Unu)
                bwd = (np.roll(Unu, 1, axis=nu) * np.conj(np.roll(Unu_pmu, 1, axis=nu))
                       * np.conj(np.roll(Umu, 1, axis=nu)))
                Ss = Ss + fwd[idx] + bwd[idx]
                # DERIVED: a staple holding a free link was zeroed above, so a nonzero staple is an all-frozen one
                k = k + (np.abs(fwd[idx]) > 0).astype(int) + (np.abs(bwd[idx]) > 0).astype(int)
            out.append(np.stack([np.stack([Ss.real, -Ss.imag], -1), np.stack([Ss.imag, Ss.real], -1)], 1))
        cnt.append(k)
        pos.append(sites)
        dirs.append(np.full(len(sites), mu))
    return np.concatenate(out), np.concatenate(cnt), np.concatenate(pos), np.concatenate(dirs)


def link_vectors_and_cov(group, b, U, S, free, beta):
    """u_l and the vMF covariance of every free link, in the order of frozen_staples."""
    _, _, C, Ul = link_terms(group, b, U, S, free, beta, ret_u=True)
    return Ul, C


def run_layer(group, beta, l, boundary, nsamp, spacing, therm, nmode, seed):
    """The boundary-layer basis: the alignment g_l = <u_l, s_l> of every free link with its frozen staples
    (U(1): cos and sin), either link by link (nmode = 0) or summed against cosine envelopes over the link
    base sites, by link direction and number of frozen staples (1, 2, 3+) (nmode > 0). Each g is linear in
    one link, so its Dirichlet form is s_l^T Cov_l s_l exactly."""
    S, free = geometry(l)
    b = lg._Backend(None).seed(seed)
    rng = np.random.default_rng(seed)
    sd = (S,) * D4
    U = init_boundary(group, b, rng, boundary, sd, beta, therm, free, l)
    if os.environ.get("BOUNDARY_NPZ"):
        U = np.load(os.environ["BOUNDARY_NPZ"])["U"]
    if group == "su2":
        frozen = ~free
        sweep = lambda: lg._su2_hb_sweep(b, U, sd, beta, None, n_or=2, frozen=frozen)
    else:
        sweep = lambda: u1_hb_sweep(rng, U, beta, free)
    for _ in range(therm):
        sweep()
    Sv, cnt, pos, dirs = frozen_staples(group, b, U, free)       # fixed: the frozen links do not move
    # DERIVED: the layer basis is the links with at least one all-frozen staple (a count, exact)
    keep = cnt > 0
    if os.environ.get("LAYER_CORNER") is not None:
        # only links whose base site lies within Chebyshev distance r of a corner of the box
        r = int(os.environ["LAYER_CORNER"])
        dc = np.minimum(np.abs(pos - 1), np.abs(pos - l)).max(axis=1)
        keep &= dc <= r
    Sv, cnt, pos, dirs = Sv[keep], cnt[keep], pos[keep], dirs[keep]
    ncomp = Sv.shape[1]
    if nmode:
        cls = dirs * 3 + np.minimum(cnt, 3) - 1
        env = np.array([np.prod([np.cos(np.pi * k[mm] * (pos[:, mm] - 0.5) / (l + 1)) for mm in range(D4)], axis=0)
                        for k in np.ndindex(*(nmode,) * D4)])                     # (nsp, nl)
        W = np.zeros((env.shape[0], 12, ncomp, len(cls)))
        for c in range(12):
            W[:, c, :, :] = (env * (cls == c))[:, None, :]
        W = W.reshape(-1, len(cls))                                               # (m, nl) per component
        Wc = W.reshape(env.shape[0] * 12, ncomp, len(cls))
        m = Wc.shape[0] * ncomp
    else:
        m = len(cls) * ncomp if False else Sv.shape[0] * ncomp
    Dsum = np.zeros((m, m))
    F = []
    t0 = time.time()
    for s_ in range(nsamp):
        for _ in range(spacing):
            sweep()
        Ul, Cv = link_vectors_and_cov(group, b, U, S, free, beta)
        Ul, Cv = Ul[keep], Cv[keep]
        g = np.einsum("lci,li->lc", Sv, Ul)                                      # (nl, ncomp)
        Gd = np.einsum("lci,lij,ldj->lcd", Sv, Cv, Sv)                            # (nl, ncomp, ncomp)
        if nmode:
            vals = np.einsum("acl,lc->ac", Wc, g).reshape(-1)
            Dsum += np.einsum("acl,lcd,bdl->acbd", Wc, Gd, Wc).reshape(m, m)
        else:
            vals = g.reshape(-1)
            Dl = np.zeros((m, m))
            for c in range(ncomp):
                for d in range(ncomp):
                    Dl[np.arange(len(g)) * ncomp + c, np.arange(len(g)) * ncomp + d] = Gd[:, c, d]
            Dsum += Dl
        F.append(vals)
    F = np.array(F)
    Dm = Dsum / nsamp
    Cm = np.cov(F.T)
    meta = finish(Dm, Cm, F, dict(group=group, beta=beta, l=l, boundary=boundary, nsamp=nsamp, spacing=spacing,
                                  therm=therm, basis=int(m), basis_kind="layer", nmode=nmode,
                                  layer_links=int(len(Sv)), seconds=round(time.time() - t0, 1)))
    meta.pop("slow_coef")
    return meta


def run_gauss(mass, l, nsamp, spacing, seed):
    """Exact-sampled scalar Gaussian box of l sites a side (frozen boundary at 0: the boundary only
    shifts the mean)."""
    n = l
    N = n ** D4
    import scipy.sparse as sp
    T = sp.diags([2 * np.ones(n), -np.ones(n - 1), -np.ones(n - 1)], [0, 1, -1])
    I = sp.identity(n)
    Q = mass * mass * sp.identity(N)
    for mu in range(D4):
        ops = [I] * D4; ops[mu] = T
        K = ops[0]
        for o in ops[1:]:
            K = sp.kron(K, o)
        Q = Q + K
    Q = Q.toarray()
    rng = np.random.default_rng(seed)
    Lc = np.linalg.cholesky(np.linalg.inv(Q))
    F = (Lc @ rng.standard_normal((N, nsamp))).T
    Dm = np.diag(1.0 / np.diag(Q))
    Cm = np.cov(F.T)
    meta = finish(Dm, Cm, F, dict(group="gauss", mass=mass, l=l, nsamp=nsamp, basis=N))
    meta.pop("slow_coef")
    meta["gamma_exact"] = float((mass ** 2 + 8 * (1 - np.cos(np.pi / (l + 1)))) / (8 + mass ** 2))
    return meta


if __name__ == "__main__":
    out, group = sys.argv[1], sys.argv[2]
    par = float(sys.argv[3]); l = int(sys.argv[4]); boundary = sys.argv[5]; nsamp = int(sys.argv[6])
    # DERIVED: 7 is SPACING's position in the Usage line. CHOSEN: default 2 sweeps between samples (budget)
    spacing = int(sys.argv[7]) if len(sys.argv) > 7 else 2
    # DERIVED: 8 is THERM's position in the Usage line. CHOSEN: default 200 thermalisation sweeps (budget)
    therm = int(sys.argv[8]) if len(sys.argv) > 8 else 200
    # DERIVED: 9 is NMODE's position in the Usage line. CHOSEN: default 2 cosine modes per direction (basis size)
    nmode = int(sys.argv[9]) if len(sys.argv) > 9 else 2
    # DERIVED: 10 is SEED's position in the Usage line. CHOSEN: default seed 1
    seed = int(sys.argv[10]) if len(sys.argv) > 10 else 1
    # job queues that cannot set the environment name the basis in the output file:
    # "..._layer..." selects BASIS=layer, "..._layerc<r>..." also LAYER_CORNER=r
    import re
    mlay = re.search(r"_layer(c(\d+))?", os.path.basename(out))
    if mlay and not os.environ.get("BASIS"):
        os.environ["BASIS"] = "layer"
        if mlay.group(2) is not None:
            os.environ["LAYER_CORNER"] = mlay.group(2)
    if group == "gauss":
        res = run_gauss(par, l, nsamp, spacing, seed)
    elif os.environ.get("BASIS") == "layer":
        res = run_layer(group, par, l, boundary, nsamp, spacing, therm, nmode, seed)
    else:
        res = run_gauge(group, par, l, boundary, nsamp, spacing, therm, nmode, seed)
    print(json.dumps(res))
    with open(out, "w") as fh:
        json.dump(res, fh, indent=1)
