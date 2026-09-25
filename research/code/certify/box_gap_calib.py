#!/usr/bin/env python3
"""box_gap_calib.py -- an upper read of the box local gap in `BoxPatch.BoxLocalGap`, SU(2).

WHAT THE LEAN CONSTANT IS. On the torus of extent L = 2(j + 1), a box of side n <= L/2 at corner k owns
the 4 n^4 links (mu, x) with every coordinate of x - k in [0, n). Its patch operator is
A = sum_{l in box} (I - E_l), E_l the single-link heat-bath conditional expectation, acting on the
periodic gauge-invariant observables with the Gibbs L^2 form. A is self-adjoint, 0 <= A <= |B| I, and
`gamma * <Ax, x> <= <Ax, Ax>` for every x holds exactly when gamma <= lambda_1(beta, n, L), the least
non-zero spectral value of A (its kernel is the observables reading no box link; the projection onto
it is E_B = conditional expectation given the links outside the box). `BoxPatchGap beta n gamma` then
holds for some gamma exactly when (40n - 36)/n^2 < inf_L lambda_1(beta, n, L).

WHAT THIS SCRIPT MEASURES. Statistical UPPER bounds on lambda_1(beta, n, L), from equilibrium
boundaries and the exact random-scan box heat bath P = I - A/|B|:

  rq  (Rayleigh):   for y = x - E_B x,  lambda_1 <= <Ay, y>/<y, y> = sum_l E Var_l(x) / E Var_B(x).
                    The numerator is closed form per configuration (SU(2) heat-bath moments); the
                    denominator is the fibre variance read from the box chain.
  ac  (semigroup):  <y, P^K y>/<y, y> <= (1 - lambda_1/|B|)^K because P >= 0 on ker(A)^perp, so
                    lambda_1 <= |B| (1 - rho_K^(1/K)), rho_K the fibre autocorrelation after K = s|B|
                    single-link updates (s sweeps). Tighter than rq as s grows; valid at every s.
  ritz:             the same two bounds minimised over a family of observables (generalised
                    eigenproblem), CROSS-FITTED: the combination is chosen on one half of the
                    boundaries and evaluated on the other, so the selection cannot bias the bound low.

Every one of these is >= lambda_1 at population level. So a measured value (its upper confidence
limit) below (40n - 36)/n^2 REFUTES BoxPatchGap at (beta, n); a value above it certifies nothing.

TRANSFER IN n. For an observable reading only links of the measured box B0 and links on the NEGATIVE
side of its corner (the `transferable` family, nunsafe = 0), the rq bound at B0 is also a bound at
every larger box B with the same corner on the same torus: the numerator is unchanged and E Var_B
only grows. The ac bound has no such monotonicity; it is a bound at the measured box only. Beyond
n = L/2 the transfer rests on the L-independence of the read, which the grid checks by varying L.

THE ANALYTIC CEILING. The plaquette through the corner link (0, k) and three links at k - e_1 reads one
box link, so its rq is E Var_l / E Var_B <= 1 at every beta: lambda_1 <= 1 always, and since
(40n - 36)/n^2 >= 1 for n <= 39 no box side below 40 can satisfy BoxPatchGap at any coupling. The
`corner` observable measures how far below 1 that ceiling sits.

COUPLING CONVENTION. `--betas` are STANDARD Wilson couplings (weight exp(beta sum_{mu<nu} Re tr U_p/2)),
the generator's convention. The Lean plaquette type runs over ORDERED direction pairs (the diagonal
ones contribute the constant 0), so the Lean action is twice the standard one: beta_lean = beta_std/2.
Both are written to the CSV.

KNOWN-ANSWER CONTROL. At beta = 0 the heat bath is Haar and a plaquette with j box links is an exact
eigenvector of A with eigenvalue j: rq and ac both read j for the class c{j}*, and the corner reads 1.

    python box_gap_calib.py --selftest
    python box_gap_calib.py --betas 0,2.3 --L 4 --n 2 --samples 4 --inner-sweeps 8 --therm 5 --out toy.csv
"""
from __future__ import annotations

import os

# Thread caps BEFORE numpy loads: the shared compute node must not see BLAS fan out across its cores.
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ.setdefault(_v, "1")

import argparse
import csv
import hashlib
import importlib.util
import itertools
import json
import math
import platform
import socket
import sys
import time

import numpy as np
from scipy.special import ive

D = 4
EYE = np.eye(D, dtype=np.int64)
CONJ = np.array([1.0, -1.0, -1.0, -1.0])
# Staple j of a link: j = 2*(index of nu among the three others) + (0 forward, 1 backward).
# Forward  W = q_nu(x+mu) . conj q_mu(x+nu) . conj q_nu(x)
# Backward W = conj q_nu(x+mu-nu) . conj q_mu(x-nu) . q_nu(x-nu)
# (the generator's `_su2_staple`); the plaquette through the link is then sdot(q_l, W).
STP_CONJ = np.array([[False, True, True], [True, True, False]] * 3)          # (6, 3)
PLQ_CONJ = np.array([False, False, True, True])                               # (4,)


# ---------------------------------------------------------------------------------------------
# The generator: reused, not duplicated. Its heat bath, over-relaxation, staple and quaternion
# product are the ones the rest of the program trusts; the file and its hash are recorded.
# ---------------------------------------------------------------------------------------------
def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def load_generator(lg_dir=None):
    cands = []
    if lg_dir:
        cands.append(lg_dir)
    if os.environ.get("LG_DIR"):
        cands.append(os.environ["LG_DIR"])
    here = os.path.dirname(os.path.abspath(__file__))
    cands += [here, os.path.expanduser("~/research/code"),
              os.path.join(os.path.expanduser("~"), "Workspace", "Ikailo", "Repos", "agience",
                           "entroptics-mass-gap", "research", "code")]
    for d in cands:
        p = os.path.join(d, "lattice_generator.py")
        if os.path.isfile(p):
            spec = importlib.util.spec_from_file_location("lattice_generator", p)
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            assert os.path.abspath(mod.__file__) == os.path.abspath(p)
            return mod, os.path.abspath(p)
    raise SystemExit(f"lattice_generator.py not found in {cands}; pass --lg-dir")


# ---------------------------------------------------------------------------------------------
# Geometry
# ---------------------------------------------------------------------------------------------
def site_flat(x, L):
    x = np.mod(x, L)
    return ((x[..., 0] * L + x[..., 1]) * L + x[..., 2]) * L + x[..., 3]


class BoxGeom:
    """One box of side n, corner at the origin, in offset space on the torus of extent L."""

    def __init__(self, L, n):
        if not (2 * n <= L and n + 2 <= L):
            raise ValueError(f"need 2n <= L (Lean: n <= j + 1) and n + 2 <= L; got L={L}, n={n}")
        self.L, self.n = L, n
        offs = list(itertools.product(range(n), repeat=D))
        links = [(mu, o) for o in offs for mu in range(D)]
        self.nB = nB = len(links)
        index = {(mu, tuple(o)): i for i, (mu, o) in enumerate(links)}
        self.link_dir = np.array([mu for mu, _ in links], dtype=np.int64)
        self.link_off = np.array([o for _, o in links], dtype=np.int64)

        def kind(off):
            off = np.mod(off, L)
            if np.all(off < n):
                return "in"
            if np.any(off == L - 1):
                return "safe"      # outside every box of side <= L/2 with this corner
            return "unsafe"        # outside this box, inside a larger one with the same corner

        # plaquettes touching the box
        plq_dir, plq_off, info, pindex = [], [], [], {}
        for y in itertools.product(range(-1, n + 1), repeat=D):
            y = np.array(y, dtype=np.int64)
            for a in range(D):
                for b_ in range(a + 1, D):
                    ls = [(a, y), (b_, y + EYE[a]), (a, y + EYE[b_]), (b_, y)]
                    kinds = [kind(o) for _, o in ls]
                    nbox = kinds.count("in")
                    if nbox == 0:
                        continue
                    key = (a, b_, tuple(np.mod(y, L)))
                    if key in pindex:
                        continue
                    pindex[key] = len(plq_dir)
                    plq_dir.append([d_ for d_, _ in ls])
                    plq_off.append([o for _, o in ls])
                    depth = -1
                    if nbox == 4:
                        depth = int(min(min(int(c), n - 1 - int(c))
                                        for _, o in ls for c in np.mod(o, L)))
                    info.append(dict(nbox=nbox, nsafe=kinds.count("safe"),
                                     nunsafe=kinds.count("unsafe"), depth=depth,
                                     centre=y + 0.5 * (EYE[a] + EYE[b_]), key=key))
        self.plq_dir = np.array(plq_dir, dtype=np.int64)
        self.plq_off = np.array(plq_off, dtype=np.int64)
        self.plq_info = info
        self.P = len(info)

        # staples, their plaquettes, and the interaction neighbourhoods inside the box
        stp_dir = np.zeros((nB, 6, 3), dtype=np.int64)
        stp_off = np.zeros((nB, 6, 3, D), dtype=np.int64)
        stp_pid = np.zeros((nB, 6), dtype=np.int64)
        nbr = []
        for i, (mu, o) in enumerate(links):
            o = np.array(o, dtype=np.int64)
            j = 0
            near = {i}
            for nu in range(D):
                if nu == mu:
                    continue
                em, en = EYE[mu], EYE[nu]
                fwd = [(nu, o + em), (mu, o + en), (nu, o)]
                bwd = [(nu, o + em - en), (mu, o - en), (nu, o - en)]
                for sl, base in ((fwd, o), (bwd, o - en)):
                    for t, (d_, oo) in enumerate(sl):
                        stp_dir[i, j, t] = d_
                        stp_off[i, j, t] = oo
                        if kind(oo) == "in":
                            near.add(index[(d_, tuple(np.mod(oo, L)))])
                    stp_pid[i, j] = pindex[(min(mu, nu), max(mu, nu), tuple(np.mod(base, L)))]
                    j += 1
            nbr.append(tuple(sorted(near)))
        self.stp_dir, self.stp_off, self.stp_pid, self.nbr = stp_dir, stp_off, stp_pid, nbr

        self._observables()

    def _observables(self):
        """Plaquette-sum observables: class means, one interior profile, the corner probe."""
        L, n = self.L, self.n
        classes = {}
        for p, inf in enumerate(self.plq_info):
            if inf["nbox"] < 4:
                name = f"c{inf['nbox']}s{inf['nsafe']}u{inf['nunsafe']}"
            else:
                name = f"i4d{inf['depth']}"
            classes.setdefault(name, []).append(p)
        names, rows, transf = [], [], []

        def smooth(p):   # lowest box mode, evaluated at the plaquette centre (clipped into the box)
            c = np.clip(self.plq_info[p]["centre"], -0.5, n - 0.5)
            return float(np.prod(np.sin(np.pi * (c + 1.0) / (n + 1.0))))

        for name in sorted(classes):
            members = classes[name]
            tr = all(self.plq_info[p]["nunsafe"] == 0 for p in members)
            w = np.zeros(self.P)
            w[members] = 1.0 / len(members)
            names.append(name)
            rows.append(w)
            transf.append(tr)
            # the same class weighted by the lowest box mode: a slower combination than the flat mean
            ws = np.zeros(self.P)
            ws[members] = [smooth(p) for p in members]
            if ws.sum() > 0 and np.ptp(ws[members]) > 1e-9 * ws.sum():
                names.append(name + "~s")
                rows.append(ws / ws.sum())
                transf.append(tr)
        # lowest Dirichlet-like profile over all the interior plaquettes
        w = np.zeros(self.P)
        for p, inf in enumerate(self.plq_info):
            if inf["nbox"] == 4:
                w[p] = smooth(p)
        if w.sum() > 0:
            names.append("prof")
            rows.append(w / w.sum())
            transf.append(True)
        # the corner probe: plaquette (0,1) based at -e_1, reading only the box link (0, origin)
        key = (0, 1, (0, L - 1, 0, 0))
        pid = [p for p, inf in enumerate(self.plq_info) if inf["key"] == key]
        assert len(pid) == 1 and self.plq_info[pid[0]]["nbox"] == 1
        w = np.zeros(self.P)
        w[pid[0]] = 1.0
        names.append("corner")
        rows.append(w)
        transf.append(True)
        self.obs_names = names
        self.Wobs = np.array(rows)                                  # (m, P)
        self.obs_transferable = np.array(transf)
        self.Wp = self.Wobs[:, self.stp_pid]                        # (m, nB, 6)


def box_corners(L, n, per_axis):
    if per_axis == 0:            # auto: the most boxes whose staples and records cannot meet
        per_axis = max(b for b in range(1, L + 1) if L % b == 0 and L // b >= n + 1)
    if L % per_axis or L // per_axis < n + 1:
        raise ValueError(f"boxes-per-axis {per_axis}: need L % b == 0 and L/b >= n + 1")
    sp = L // per_axis
    return [np.array(c, dtype=np.int64) for c in itertools.product(range(0, L, sp), repeat=D)]


class Placed:
    """Flat link ids of every box on the torus (boxes are translates of one BoxGeom)."""

    def __init__(self, geom, corners):
        L = geom.L
        self.geom, self.nb = geom, len(corners)
        c = np.array(corners)[:, None, :]
        self.box_flat = (site_flat(c + geom.link_off[None], L) * D + geom.link_dir[None])
        cs = np.array(corners)[:, None, None, None, :]
        self.stp_flat = site_flat(cs + geom.stp_off[None], L) * D + geom.stp_dir[None]
        cp = np.array(corners)[:, None, None, :]
        self.plq_flat = site_flat(cp + geom.plq_off[None], L) * D + geom.plq_dir[None]
        nB = geom.nB
        self.box_flat_all = self.box_flat.reshape(-1)
        self.stp_flat_all = self.stp_flat.reshape(self.nb * nB, 6, 3)
        assert len(np.unique(self.box_flat_all)) == self.nb * nB, "boxes overlap"


# ---------------------------------------------------------------------------------------------
# SU(2) pieces on gathered links
# ---------------------------------------------------------------------------------------------
def staple_from(LG, b, Qf, stp_flat):
    """(..., 6, 3) flat ids -> the six staple quaternions (..., 6, 4)."""
    G = Qf[stp_flat]
    G = np.where(STP_CONJ[..., None], G * CONJ, G)
    return LG._qmul(b, LG._qmul(b, G[..., 0, :], G[..., 1, :]), G[..., 2, :])


def plaquettes(LG, b, Qf, plq_flat):
    """(..., P, 4) flat ids -> (1/2) Re tr U_p, shape (..., P)."""
    G = Qf[plq_flat]
    G = np.where(PLQ_CONJ[:, None], G * CONJ, G)
    U = LG._qmul(b, LG._qmul(b, LG._qmul(b, G[..., 0, :], G[..., 1, :]), G[..., 2, :]), G[..., 3, :])
    return U[..., 0]


def hb_moments(alpha):
    """Heat-bath law of q . e = a0 with density sqrt(1-a0^2) exp(alpha a0):
    m = E a0 = I2/I1, s_perp = (1 - E a0^2)/3 = I2/(alpha I1), s_e = Var a0 = 1 - 3 s_perp - m^2."""
    alpha = np.asarray(alpha, dtype=float)
    small = alpha < 1e-6
    a = np.where(small, 1.0, alpha)
    r = ive(2, a) / ive(1, a)
    m = np.where(small, alpha / 4.0, r)
    sp = np.where(small, 0.25, r / a)
    se = 1.0 - 3.0 * sp - m * m
    return m, sp, se


def rq_numerator(LG, b, Qf, placed, beta):
    """sum_{l in box} Cov_l(x_o, x_p) for every box, averaged over boxes: (m, m).

    x_o's dependence on q_l is sdot(q_l, C_o) with C_o = sum_j w_o(p_j) W_j, and under the heat bath
    q_l = a0 e + sqrt(1 - a0^2) r with e = conj(A)/|A|, so
    Cov_l = s_perp (<C_o, C_p> - a_o a_p) + s_e a_o a_p,   a_o = <C_o, A>/|A|."""
    g = placed.geom
    W = staple_from(LG, b, Qf, placed.stp_flat)                     # (nb, nB, 6, 4)
    A = W.sum(-2)
    k = np.linalg.norm(A, axis=-1)
    Ah = A / np.maximum(k, 1e-300)[..., None]
    _, sp, se = hb_moments(beta * k)
    C = np.einsum("onj,bnjq->bonq", g.Wp, W)                        # (nb, m, nB, 4)
    a = np.einsum("bonq,bnq->bon", C, Ah)
    M = (np.einsum("bn,bonq,bpnq->op", sp, C, C)
         + np.einsum("bn,bon,bpn->op", se - sp, a, a))
    return M / placed.nb


# ---------------------------------------------------------------------------------------------
# The exact random-scan box heat bath, executed in layers
# ---------------------------------------------------------------------------------------------
def schedule(seq, nbr, nB, nslots):
    """Greedy layering of a sequence of single-link updates (global slots bx*nB + i).

    An update goes one layer past the latest earlier update of any link it interacts with (shares a
    plaquette with, itself included). Updates in one layer are pairwise non-interacting, so their heat
    baths commute as random maps and the layered execution IS the sequential random-scan chain."""
    last = [0] * nslots
    layers = []
    for g in seq:
        off = (g // nB) * nB
        lay = 0
        for j in nbr[g - off]:
            v = last[off + j]
            if v > lay:
                lay = v
        last[g] = lay + 1
        if lay == len(layers):
            layers.append([g])
        else:
            layers[lay].append(g)
    return layers


def run_layers(LG, b, Qf, placed, layers, beta, update="hb"):
    for lay in layers:
        g = np.asarray(lay, dtype=np.int64)
        fl = placed.box_flat_all[g]
        A = staple_from(LG, b, Qf, placed.stp_flat_all[g]).sum(-2)
        if update == "hb":
            Qf[fl] = LG._su2_heatbath_link(b, A, beta)
        else:                                   # deterministic over-relaxation: the layering test
            Qf[fl] = LG._su2_overrelax_link(b, Qf[fl], A)


def segment(rng, placed, n_updates):
    nB, nb = placed.geom.nB, placed.nb
    seqs = [rng.integers(0, nB, n_updates) + bx * nB for bx in range(nb)]
    return np.concatenate(seqs).tolist()


# ---------------------------------------------------------------------------------------------
# Estimation
# ---------------------------------------------------------------------------------------------
def theta(n):
    return (40.0 * n - 36.0) / (n * n)


def n_min_implied(U):
    """Least integer side n' >= 2 with (40n' - 36)/n'^2 < U, i.e. the least side a gap <= U allows."""
    if not np.isfinite(U) or U <= 0:
        return ""
    disc = 1600.0 - 144.0 * U
    if disc < 0:
        return 2
    n0 = max(2, int(math.floor((40.0 + math.sqrt(disc)) / (2.0 * U))) - 1)
    while theta(n0) >= U:
        n0 += 1
    return n0


def ritz_vector(num, den, idx, largest, rtol=1e-10):
    """v (zero off idx) extremising v'num v / v'den v over span(idx), den positive semidefinite."""
    Gs = den[np.ix_(idx, idx)]
    Gs = 0.5 * (Gs + Gs.T)
    w, U = np.linalg.eigh(Gs)
    keep = w > rtol * max(w.max(), 1e-300)
    T = U[:, keep] / np.sqrt(w[keep])
    H = T.T @ (0.5 * (num[np.ix_(idx, idx)] + num[np.ix_(idx, idx)].T)) @ T
    ev, V = np.linalg.eigh(0.5 * (H + H.T))
    v = np.zeros(den.shape[0])
    v[idx] = T @ V[:, -1 if largest else 0]
    return v


def rate_from(kind, vnum, vden, nB, K):
    if kind == "rq":
        return vnum / vden if vden > 0 else np.inf
    rho = vnum / vden if vden > 0 else -1.0
    if rho <= 0:
        return np.inf
    return nB * (1.0 - rho ** (1.0 / K))


def percentile_ci(x, lo=2.5, hi=97.5):
    x = np.asarray(x, dtype=float)
    return (float(np.percentile(x, lo, method="lower")), float(np.percentile(x, hi, method="higher")))


def analyse(Cs, Ms, lags_sw, nB, obs_names, transf, n_boot, rng, primary_lag):
    """Rows (estimator, family, observable, lag, value, ci_lo, ci_hi, transferable, primary)."""
    Ks, nl, m, _ = Cs.shape
    G = Cs[:, 0]
    rows = []
    idx_all = list(range(m))
    idx_T = [o for o in range(m) if transf[o]]
    boots = [rng.integers(0, Ks, Ks) for _ in range(n_boot)]

    def fixed(kind, num_k, K, o):
        f = lambda sel: rate_from(kind, num_k[sel][:, o, o].mean(), G[sel][:, o, o].mean(), nB, K)
        val = f(slice(None))
        return val, percentile_ci([f(s) for s in boots])

    # fixed observables: no selection, no fitting
    for o, name in enumerate(obs_names):
        val, (lo, hi) = fixed("rq", Ms, 0, o)
        rows.append(("rq_fixed", "fixed", name, 0.0, val, lo, hi, bool(transf[o]), False))
        for li in range(1, nl):
            K = int(round(lags_sw[li] * nB))
            val, (lo, hi) = fixed("ac", Cs[:, li], K, o)
            rows.append(("ac_fixed", "fixed", name, lags_sw[li], val, lo, hi, False, False))

    # cross-fitted Ritz: fit on one half of the boundaries, evaluate on the other
    halves = (np.arange(0, Ks, 2), np.arange(1, Ks, 2))
    if min(len(h) for h in halves) >= 2:
        def crossfit(kind, num_k, K, idx):
            vs = []
            for fit in halves:
                vs.append(ritz_vector(num_k[fit].mean(0), G[fit].mean(0), idx, largest=(kind == "ac")))

            def ev(selA, selB):
                out = []
                for v, ev_idx in ((vs[0], selB), (vs[1], selA)):
                    out.append(rate_from(kind, v @ num_k[ev_idx].mean(0) @ v,
                                         v @ G[ev_idx].mean(0) @ v, nB, K))
                return 0.5 * (out[0] + out[1])

            val = ev(halves[0], halves[1])
            bs = []
            for _ in range(n_boot):
                a = halves[0][rng.integers(0, len(halves[0]), len(halves[0]))]
                c = halves[1][rng.integers(0, len(halves[1]), len(halves[1]))]
                bs.append(ev(a, c))
            return val, percentile_ci(bs)

        for fam, idx in (("T", idx_T), ("F", idx_all)):
            val, (lo, hi) = crossfit("rq", Ms, 0, idx)
            rows.append(("rq_ritz", fam, "", 0.0, val, lo, hi, fam == "T", fam == "T"))
            for li in range(1, nl):
                K = int(round(lags_sw[li] * nB))
                val, (lo, hi) = crossfit("ac", Cs[:, li], K, idx)
                prim = (fam == "F" and abs(lags_sw[li] - primary_lag) < 1e-9)
                rows.append(("ac_ritz", fam, "", lags_sw[li], val, lo, hi, False, prim))
    return rows


# ---------------------------------------------------------------------------------------------
# One (beta, n, L) point
# ---------------------------------------------------------------------------------------------
def point_rng(seed, beta, n, L, stream):
    return np.random.default_rng(np.random.SeedSequence([seed, int(round(beta * 1e6)), n, L, stream]))


def run_point(LG, args, beta, n, L, log):
    t0 = time.time()
    geom = BoxGeom(L, n)
    placed = Placed(geom, box_corners(L, n, args.boxes_per_axis))
    nB, nb, m = geom.nB, placed.nb, len(geom.obs_names)
    r = args.records_per_sweep
    if nB % r:
        raise ValueError(f"|B| = {nB} not divisible by records-per-sweep {r}")
    delta = nB // r
    lags_sw = [0.0] + [float(s) for s in args.lags.split(",")]
    lag_rec = [int(round(s * r)) for s in lags_sw]
    if any(abs(lr - s * r) > 1e-9 for lr, s in zip(lag_rec, lags_sw)):
        raise ValueError("every lag times records-per-sweep must be an integer")
    T = args.inner_sweeps * r
    if max(lag_rec) >= T // 2:
        raise ValueError("inner chain too short for the largest lag")

    b = LG._Backend(None).seed(0)
    b.rng = point_rng(args.seed, beta, n, L, 0)          # the generator's draws
    seq_rng = point_rng(args.seed, beta, n, L, 1)        # the random-scan link choices
    boot_rng = point_rng(args.seed, beta, n, L, 2)
    sdims = (L,) * D
    q = (LG.cold_init(b, "su2", sdims, ()) if args.start == "cold"
         else LG._su2_init(b, sdims, ()))
    q = np.ascontiguousarray(q)
    Qf = q.reshape(-1, 4)
    assert np.shares_memory(Qf, q)

    def outer_sweep():
        LG._su2_hb_sweep(b, q, sdims, beta, None, n_or=args.n_or)

    for _ in range(args.therm):
        outer_sweep()
    t_therm = time.time() - t0

    Ks = args.samples
    Cs = np.zeros((Ks, len(lags_sw), m, m))
    Ms = np.zeros((Ks, m, m))
    plaq = np.zeros(Ks)
    t_outer = t_inner = t_rec = t_rq = 0.0
    for k in range(Ks):
        ta = time.time()
        for _ in range(args.outer_gap):
            outer_sweep()
        plaq[k] = 1.0 - float(LG._su2_action(b, q).mean()) / 6.0
        t_outer += time.time() - ta
        X = np.empty((nb, T + 1, m))
        tb = time.time()
        X[:, 0] = plaquettes(LG, b, Qf, placed.plq_flat) @ geom.Wobs.T
        t_rec += time.time() - tb
        Macc = np.zeros((m, m))
        nM = 0
        for t in range(1, T + 1):
            ta = time.time()
            layers = schedule(segment(seq_rng, placed, delta), geom.nbr, nB, nb * nB)
            run_layers(LG, b, Qf, placed, layers, beta)
            tb = time.time()
            t_inner += tb - ta
            X[:, t] = plaquettes(LG, b, Qf, placed.plq_flat) @ geom.Wobs.T
            tc = time.time()
            t_rec += tc - tb
            if t % args.rq_every == 0:
                Macc += rq_numerator(LG, b, Qf, placed, beta)
                nM += 1
            t_rq += time.time() - tc
        Ms[k] = Macc / max(nM, 1)
        Xc = X - X.mean(axis=1, keepdims=True)           # fibre mean: E_B x for this boundary
        for li, lr in enumerate(lag_rec):
            c = np.einsum("btm,btp->mp", Xc[:, :T + 1 - lr], Xc[:, lr:]) / (nb * (T + 1 - lr))
            Cs[k, li] = 0.5 * (c + c.T)
        if (k + 1) % max(1, Ks // 10) == 0 or k == Ks - 1:
            log(f"  beta={beta:g} n={n} L={L}: sample {k + 1}/{Ks}  plaq={plaq[:k + 1].mean():.5f}  "
                f"elapsed={time.time() - t0:.1f}s")

    timing = dict(therm=t_therm, outer=t_outer, inner=t_inner, record=t_rec, rq=t_rq,
                  total=time.time() - t0, boxes=nb, links_per_box=nB,
                  inner_sweeps_total=Ks * args.inner_sweeps,
                  sec_per_inner_sweep_per_box=(t_inner + t_rec + t_rq) / max(1, Ks * args.inner_sweeps * nb))
    rows = analyse(Cs, Ms, lags_sw, nB, geom.obs_names, geom.obs_transferable,
                   args.n_boot, boot_rng, args.primary_lag)
    pl_err = float(plaq.std(ddof=1) / math.sqrt(Ks)) if Ks > 1 else float("nan")
    rows.insert(0, ("plaquette", "", "", 0.0, float(plaq.mean()),
                    float(plaq.mean() - 1.96 * pl_err), float(plaq.mean() + 1.96 * pl_err), False, False))
    if args.save_raw:
        os.makedirs(args.save_raw, exist_ok=True)
        np.savez_compressed(os.path.join(args.save_raw, f"raw_su2_b{beta:g}_n{n}_L{L}_s{args.seed}.npz"),
                            Cs=Cs, Ms=Ms, plaq=plaq, lags=np.array(lags_sw), obs=np.array(geom.obs_names),
                            transferable=geom.obs_transferable, nB=nB, boxes=nb)
    return rows, timing, geom


# ---------------------------------------------------------------------------------------------
# Self-test: positive controls for every piece the bound rests on
# ---------------------------------------------------------------------------------------------
def selftest(LG, log):
    L, n, beta = 4, 2, 2.3
    b = LG._Backend(None).seed(0)
    b.rng = np.random.default_rng(12345)
    sdims = (L,) * D
    q = np.ascontiguousarray(LG._su2_init(b, sdims, ()))
    for _ in range(3):
        LG._su2_hb_sweep(b, q, sdims, beta, None, n_or=1)
    Qf = q.reshape(-1, 4)
    geom = BoxGeom(L, n)
    placed = Placed(geom, box_corners(L, n, 0))
    ok = True

    # 1. gathered staples == the generator's staples
    W = staple_from(LG, b, Qf, placed.stp_flat)
    A = W.sum(-2).reshape(-1, 4)
    ref = np.stack([LG._su2_staple(b, q, mu) for mu in range(D)], axis=-2).reshape(-1, 4)
    err = np.abs(A - ref[placed.box_flat_all]).max()
    log(f"[selftest] staple vs generator: max|diff| = {err:.2e}")
    ok &= err < 1e-12

    # 2. sdot(q_l, W_j) == the plaquette the staple closes
    P = plaquettes(LG, b, Qf, placed.plq_flat)                         # (nb, P)
    ql = Qf[placed.box_flat]                                           # (nb, nB, 4)
    sd = LG._sdot(ql[:, :, None, :], W)                                # (nb, nB, 6)
    err = np.abs(sd - P[:, geom.stp_pid]).max()
    log(f"[selftest] staple closes its plaquette: max|diff| = {err:.2e}")
    ok &= err < 1e-12

    # 3. closed-form conditional covariance vs Monte Carlo heat-bath draws
    rng = np.random.default_rng(7)
    for bt in (0.0, 0.7, 2.3):
        Av = rng.standard_normal(4) * 2.0
        C1, C2 = rng.standard_normal(4), rng.standard_normal(4)
        Nmc = 400_000
        qs = LG._su2_heatbath_link(b, np.tile(Av, (Nmc, 1)), bt)
        x1, x2 = LG._sdot(qs, C1), LG._sdot(qs, C2)
        k = np.linalg.norm(Av)
        _, sp, se = hb_moments(bt * k)
        a1, a2 = C1 @ Av / k, C2 @ Av / k
        cf = sp * (C1 @ C2 - a1 * a2) + se * a1 * a2
        v11 = sp * (C1 @ C1 - a1 * a1) + se * a1 * a1
        v22 = sp * (C2 @ C2 - a2 * a2) + se * a2 * a2
        mc = np.cov(x1, x2)[0, 1]
        sig = math.sqrt((v11 * v22 + cf * cf) / Nmc)
        log(f"[selftest] Cov_l beta={bt}: closed {cf:+.5f}  MC {mc:+.5f}  ({(mc - cf) / sig:+.1f} sigma)")
        ok &= abs(mc - cf) < 5 * sig

    # 4. the layered schedule reproduces the sequential chain exactly (deterministic OR updates)
    Q1 = Qf.copy()
    Q2 = Qf.copy()
    seq = segment(np.random.default_rng(3), placed, 3 * geom.nB)
    run_layers(LG, b, Q1, placed, schedule(seq, geom.nbr, geom.nB, placed.nb * geom.nB), beta, update="or")
    for g in seq:
        fl = placed.box_flat_all[[g]]
        A1 = staple_from(LG, b, Q2, placed.stp_flat_all[[g]]).sum(-2)
        Q2[fl] = LG._su2_overrelax_link(b, Q2[fl], A1)
    err = np.abs(Q1 - Q2).max()
    log(f"[selftest] layered == sequential (over-relaxation): max|diff| = {err:.2e}")
    ok &= err < 1e-12
    # and the test can fail: a wrong schedule (no layering: all at once) must differ
    Q3 = Qf.copy()
    run_layers(LG, b, Q3, placed, [sorted(set(seq))], beta, update="or")
    bad = np.abs(Q3 - Q2).max()
    log(f"[selftest] negative control (unlayered): max|diff| = {bad:.2e} (must be large)")
    ok &= bad > 1e-3

    # 5. the analytic facts the README quotes
    log(f"[selftest] theta(39) = {theta(39):.5f} >= 1, theta(40) = {theta(40):.5f} < 1; "
        f"n_min_implied(1.0) = {n_min_implied(1.0)}, n_min_implied(0.5) = {n_min_implied(0.5)}")
    ok &= theta(39) >= 1 > theta(40) and n_min_implied(1.0) == 40
    log(f"[selftest] observables (m={len(geom.obs_names)}): "
        + ", ".join(f"{nm}{'*' if t else ''}" for nm, t in zip(geom.obs_names, geom.obs_transferable))
        + "   (* = transferable)")
    log("[selftest] " + ("PASS" if ok else "FAIL"))
    return ok


# ---------------------------------------------------------------------------------------------
FIELDS = ["group", "beta_std", "beta_lean", "L", "n", "links_per_box", "boxes", "samples",
          "inner_sweeps", "records_per_sweep", "seed", "start", "estimator", "family", "observable",
          "lag_sweeps", "value", "ci_lo", "ci_hi", "theta_n", "refutes_at_n", "n_min_implied",
          "transferable", "primary"]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--group", default="su2", choices=["su2", "su3"])
    ap.add_argument("--betas", default="0,1.0,1.5,1.8,2.0,2.2,2.3,2.4,2.5,2.7,3.0",
                    help="STANDARD Wilson couplings (beta_lean = beta/2)")
    ap.add_argument("--n", default="2,3,4", help="box sides, comma list; each needs 2n <= L")
    ap.add_argument("--L", type=int, default=8, help="torus extent (even)")
    ap.add_argument("--samples", type=int, default=200, help="equilibrium boundaries (torus samples)")
    ap.add_argument("--inner-sweeps", type=int, default=200, help="box sweeps per boundary")
    ap.add_argument("--records-per-sweep", type=int, default=4)
    ap.add_argument("--lags", default="0.25,0.5,1,2,3,4,6,8,12,16", help="lags in box sweeps")
    ap.add_argument("--primary-lag", type=float, default=4.0,
                    help="the pre-registered ac_ritz lag for a verdict")
    ap.add_argument("--rq-every", type=int, default=4, help="records between Rayleigh numerators")
    ap.add_argument("--therm", type=int, default=300, help="torus compound sweeps before sampling")
    ap.add_argument("--outer-gap", type=int, default=2, help="torus compound sweeps between boundaries")
    ap.add_argument("--n-or", type=int, default=4, help="over-relaxation passes per compound sweep")
    ap.add_argument("--start", default="hot", choices=["hot", "cold"])
    ap.add_argument("--boxes-per-axis", type=int, default=0, help="0 = as many as fit")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--n-boot", type=int, default=400)
    ap.add_argument("--out", default="box_gap_calib.csv")
    ap.add_argument("--save-raw", default="", help="directory for per-point npz aggregates")
    ap.add_argument("--lg-dir", default="", help="directory holding lattice_generator.py")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()

    def log(s):
        print(s, flush=True)

    if args.group != "su2":
        raise SystemExit("SU(3) is not implemented: the Lean E_l is the exact SU(3) link heat bath, "
                         "which Cabibbo-Marinari only approximates, and the closed-form Rayleigh "
                         "numerator is SU(2)'s. See README.md.")
    LG, lg_path = load_generator(args.lg_dir or None)
    log(f"lattice_generator: {lg_path}  sha256={sha256_file(lg_path)}")
    log(f"threads: " + " ".join(f"{v}={os.environ.get(v)}" for v in
                                ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS")))
    if args.selftest:
        raise SystemExit(0 if selftest(LG, log) else 1)

    betas = [float(x) for x in args.betas.split(",")]
    ns = [int(x) for x in args.n.split(",")]
    prov = dict(argv=sys.argv, args=vars(args), host=socket.gethostname(), platform=platform.platform(),
                python=sys.version, numpy=np.__version__, lattice_generator=lg_path,
                lattice_generator_sha256=sha256_file(lg_path),
                script_sha256=sha256_file(os.path.abspath(__file__)),
                started=time.strftime("%Y-%m-%dT%H:%M:%S"), points=[])
    new = not os.path.exists(args.out)
    with open(args.out, "a", newline="", encoding="utf-8") as fh:
        wr = csv.writer(fh)
        if new:
            wr.writerow(FIELDS)
        for n in ns:
            for beta in betas:
                rows, timing, geom = run_point(LG, args, beta, n, args.L, log)
                th = theta(n)
                for (est, fam, obs, lag, val, lo, hi, transf, prim) in rows:
                    is_rate = est != "plaquette"
                    wr.writerow(["su2", beta, beta / 2.0, args.L, n, geom.nB, timing["boxes"],
                                 args.samples, args.inner_sweeps, args.records_per_sweep, args.seed,
                                 args.start, est, fam, obs, lag, f"{val:.6g}", f"{lo:.6g}", f"{hi:.6g}",
                                 f"{th:.6g}", (bool(hi < th) if is_rate else ""),
                                 (n_min_implied(hi) if is_rate else ""), transf, prim])
                fh.flush()
                prov["points"].append(dict(beta=beta, n=n, L=args.L, timing=timing))
                log(f"point beta={beta:g} n={n} L={args.L}: {timing['total']:.1f}s "
                    f"({timing['sec_per_inner_sweep_per_box'] * 1e3:.2f} ms per box-sweep incl. records)")
    prov["finished"] = time.strftime("%Y-%m-%dT%H:%M:%S")
    with open(os.path.splitext(args.out)[0] + ".provenance.json", "a", encoding="utf-8") as fh:
        fh.write(json.dumps(prov) + "\n")


if __name__ == "__main__":
    main()
