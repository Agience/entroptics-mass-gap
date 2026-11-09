"""The coarse link's conditional law beyond its plaquette staple sum: a direct read of the rectangle and
adjoint couplings of the observer's coarse view, for the rows `influence_local_agg.py` adds to the
plaquette row of `influence_agg.py` (`ObserverEnergyMDob.CoarseViewDobrushin`). numpy only.

Blocking. The first `nsub` levels are the observer's factor-2 block step `observer_step.block2` (coarse
lattice on the even sites). The remaining levels are the same step taken a trous: the block is evaluated at
every site with the link shifts scaled by the current stride s (rolls of s and 2s), and nothing is
subsampled. The sites x = o (mod S), S the final stride, then carry exactly the coarse configuration of the
block lattice with origin o (`atrous_check`), so one array holds the coarse views of all S^4 origins. Each
origin's view is the same observer at a shifted origin; translation invariance gives them one law. They are
correlated, so errors are taken over shards (one shard = one measurement of every chain).

Per coarse link u (direction mu, stride S), with its six plaquette staples s_p, staple sum A (a = conj A,
r = |a|, a^ = a/r, t = <u, a^>), rectangle staple sum B (the 18 2x1 closing paths, b = conj B):

  * the histograms influence_agg.py reads (cnt, rsum, ch, chN, rect, rectn, adj, adjn, rectN, adjN), with
    the same definitions as influence_read.py;
  * the perpendicular tilts. A rectangle term tilts u along b_perp (b minus its a^ part); an adjoint term
    sum_p <u, s_p>^2 tilts it along W_perp, W = sum_p <a^, s_p> s_p, with a weight odd in t. A log-density
    term lam(t) <u, X_perp> gives, to first order, E[<u, X_perp> | t] = lam(t) (1 - t^2) |X_perp|^2 / 3.
    With lam_B = aB + bB t and lam_W = aW + bW t read jointly (B_perp and W_perp are not orthogonal), the
    moments Sum t^i <u, X_perp> and Sum t^j m <X_perp, Y_perp> (m = (1 - t^2)/3) per r bin determine the
    four coefficients;
  * the quadrupole of the adjoint term: y_T = sum_p <u_perp, s_p,perp>^2 - (1 - t^2) tr T / 3, whose mean
    under a term mu(t) <u_perp, T0 u_perp> is mu(t) (1 - t^2)^2 (2/15) |T0|_F^2;
  * the parallel dependence: within each fine r bin the cross moments of the characters U_n(t), n <= NK,
    with X = (r, b_par = <b, a^>, Q = sum_p <s_p, a^>^2), from which the agg regresses c_n on (b_par, Q)
    with r partialled out;
  * all of these again with u replaced by the link of a random other site of the same direction (null).

Control mode (INF_SYN = "bp,br,ba"): each u is replaced by a draw from the known kernel
exp(bp sdot(u, A) + br sdot(u, B) + ba sum_p sdot(u, s_p)^2) given its real neighbourhood (heat bath on
bp A + br B, then rejection for the adjoint term). The read's couplings must return br and ba.

    [INF_SYN=bp,br,ba] python influence_local.py CAMPAIGN_DIR levels nsub c OUT_PREFIX shard_lo shard_hi
levels: comma list of block levels read (0 = the unblocked configuration). Writes OUT_PREFIX.npz (all
origins) and OUT_PREFIX_o0.npz (origin 0 only: the view influence_read.py reads).
"""
import json
import os
import sys
import time

import numpy as np

import observer_step as O
import lattice_generator as G

# CHOSEN: theta bins, as influence_read.py (0.25 degree), so influence_agg reads both alike
NT = 720
RMAX, NB = 6.0, 120   # CHOSEN: as influence_read.py
# CHOSEN: characters U_1..U_6 in the parallel regression; a basis-size budget
NK = 6
bg = G._Backend(None)


def roll(x, n, ax):
    return np.roll(x, n, axis=G._sax(ax, 1))


def block_atrous(q, c, s):
    """observer_step.block2 evaluated at every site with stride s; nothing is subsampled."""
    out = q.copy()
    for mu in range(O.D):
        qmu = q[..., mu, :]
        qmu_f = roll(qmu, -s, mu)
        V = G._qmul(bg, qmu, qmu_f)
        # DERIVED: at c = 0 the staple terms carry weight zero, so the block step is the bare product
        if c != 0.0:
            for nu in range(O.D):  # NOT A READ: the transverse directions of the block step
                if nu == mu:
                    continue
                qnu = q[..., nu, :]
                up = G._qmul(bg, G._qmul(bg, G._qmul(bg, qnu, roll(qmu, -s, nu)), roll(roll(qmu, -s, nu), -s, mu)),
                             G._qconj(bg, roll(qnu, -2 * s, mu)))
                qnm = roll(qnu, s, nu)
                dn = G._qmul(bg, G._qmul(bg, G._qmul(bg, G._qconj(bg, qnm), roll(qmu, s, nu)), roll(roll(qmu, s, nu), -s, mu)),
                             roll(qnm, -2 * s, mu))
                V = V + c * (up + dn)
        out[..., mu, :] = V / np.linalg.norm(V, axis=-1, keepdims=True)
    return out


def path_close(q, mu, steps, S):
    disp = [0] * O.D
    disp[mu] = 1
    out = None
    for d, sg in steps:
        # DERIVED: sg is the step's sign (+1 forward, -1 backward)
        if sg > 0:
            at = list(disp); disp[d] += 1; conj = False
        else:
            disp[d] -= 1; at = list(disp); conj = True
        f = q[..., d, :]
        for ax in range(O.D):  # NOT A READ: shift the link field to the step's base site
            if at[ax]:
                f = roll(f, -at[ax] * S, ax)
        if conj:
            f = G._qconj(bg, f)
        out = f if out is None else G._qmul(bg, out, f)
    # DERIVED: a closed path returns to its start, zero net displacement (exact integers)
    assert all(x == 0 for x in disp)
    return out


def staples(q, mu, S):
    out = []
    for nu in range(O.D):
        if nu == mu:
            continue
        for sg in (1, -1):  # NOT A READ: the two plaquette orientations
            out.append(path_close(q, mu, [(nu, sg), (mu, -1), (nu, -sg)], S))
    return out


def rect_sum(q, mu, S):
    B = None
    for nu in range(O.D):
        if nu == mu:
            continue
        for sg in (1, -1):  # NOT A READ: three rectangles per plaquette orientation
            for st in ([(mu, 1), (nu, sg), (mu, -1), (mu, -1), (nu, -sg)],
                       [(nu, sg), (mu, -1), (mu, -1), (nu, -sg), (mu, 1)],
                       [(nu, sg), (nu, sg), (mu, -1), (nu, -sg), (nu, -sg)]):
                p = path_close(q, mu, st, S)
                B = p if B is None else B + p
    return B


def bar(x):
    return (x * np.array([1.0, -1.0, -1.0, -1.0], dtype=x.dtype)).reshape(-1, 4).astype(np.float64)


from influence_agg import cheb  # noqa: E402  (U_1..U_n, the one Chebyshev recursion both scripts use)


LOCAL = (["yB0", "yB1", "yW0", "yW1", "zBB0", "zBB1", "zBB2", "zBW0", "zBW1", "zBW2", "zWW0", "zWW1", "zWW2",
          "yT0", "yT1", "zT0", "zT1", "zT2", "n"])


def fresh():
    z = lambda *s: np.zeros(s)
    d = {k: z(NB) for k in ["cnt", "rsum", "rect", "rectn", "adj", "adjn", "rectN", "adjN"]}
    d["ch"], d["chN"] = z(NB, NT), z(NB, NT)
    for pre in ("L", "LN"):  # NOT A READ: data and null
        d[pre] = z(len(LOCAL), NB)
        d[pre + "X"] = z(3, NB); d[pre + "XX"] = z(3, 3, NB); d[pre + "U"] = z(NK, NB); d[pre + "UX"] = z(NK, 3, NB)
    return d


def bc(idx, w):
    return np.bincount(idx, weights=w, minlength=NB)


def accumulate(out, idx, t, u, ah, r, Bp, nb, Wp, nw, Bpar, Q, sp, null):
    """All the per-r-bin sums of one view (data or null): u is the read link (or the permuted one)."""
    tb = np.clip((np.arccos(t) / np.pi * NT).astype(np.int64), 0, NT - 1)
    key = "chN" if null else "ch"
    out[key] += np.bincount(idx * NT + tb, minlength=NB * NT).reshape(NB, NT)
    sfx = "N" if null else ""
    out["rect" + sfx] += bc(idx, (u * Bp).sum(-1) / np.maximum(nb, 1e-12))
    out["adj" + sfx] += bc(idx, (u * Wp).sum(-1) / np.maximum(nw, 1e-12))
    if not null:
        out["cnt"] += np.bincount(idx, minlength=NB)
        out["rsum"] += bc(idx, r)
        out["rectn"] += bc(idx, nb)
        out["adjn"] += bc(idx, nw)
    m = (1 - t * t) / 3
    yB, yW = (u * Bp).sum(-1), (u * Wp).sum(-1)
    BB, WW, BW = nb * nb, nw * nw, (Bp * Wp).sum(-1)
    up = u - t[:, None] * ah
    yT = sum((up * s).sum(-1) ** 2 for s in sp) - (1 - t * t) * sum((s * s).sum(-1) for s in sp) / 3
    G2 = sum(((sp[i] * sp[j]).sum(-1) ** 2) * (1 if i == j else 2) for i in range(6) for j in range(i, 6))
    trT = sum((s * s).sum(-1) for s in sp)
    T0 = G2 - trT * trT / 3                    # |T0|_F^2
    zT = (1 - t * t) ** 2 * (2.0 / 15.0) * T0
    t2 = t * t
    vals = [yB, yB * t, yW, yW * t, m * BB, m * BB * t, m * BB * t2, m * BW, m * BW * t, m * BW * t2,
            m * WW, m * WW * t, m * WW * t2, yT, yT * t, zT, zT * t, zT * t2, np.ones_like(t)]
    pre = "LN" if null else "L"
    for i, v in enumerate(vals):  # NOT A READ: the moments listed in LOCAL
        out[pre][i] += bc(idx, v)
    X = (r, Bpar, Q)
    Uc = cheb(t, NK)
    for i in range(3):  # NOT A READ: the regressors
        out[pre + "X"][i] += bc(idx, X[i])
        for j in range(3):  # NOT A READ: their cross moments
            out[pre + "XX"][i, j] += bc(idx, X[i] * X[j])
    for n in range(NK):  # NOT A READ: the characters
        out[pre + "U"][n] += bc(idx, Uc[n])
        for i in range(3):  # NOT A READ: the regressors
            out[pre + "UX"][n, i] += bc(idx, Uc[n] * X[i])


def synth(A, Bq, S6, bp, br, ba, shape):
    """Draws u ~ exp(bp sdot(u,A) + br sdot(u,B) + ba sum_p sdot(u,s_p)^2), given the neighbourhood."""
    K = (bp * A + br * Bq).reshape(-1, 4).astype(np.float64)
    u = G._su2_heatbath_link(bg, K, 1.0)
    # DERIVED: the rejection step accepts with exp(ba (q2 - 6)) <= 1 (q2 <= 6, six unit staples), valid for
    # ba > 0; ba = 0 needs no rejection. (A negative ba is not handled: it skips the adjoint term.)
    if ba > 0:
        sb = [bar(s) for s in S6]
        todo = np.ones(len(u), bool)
        while todo.any():
            q2 = sum((u * s).sum(-1) ** 2 for s in sb)
            acc = np.random.rand(len(u)) < np.exp(ba * (q2 - 6.0))
            todo &= ~acc
            if todo.any():
                Ki = K[todo]
                u[todo] = G._su2_heatbath_link(bg, Ki, 1.0)
    return u


def read_level(q, S, outs, rng, syn):
    L = q.shape[0]
    o0 = np.zeros(q.shape[:4], bool)
    o0[::S, ::S, ::S, ::S] = True
    o0 = o0.ravel()
    for mu in range(O.D):  # NOT A READ: the four link directions
        S6 = staples(q, mu, S)
        A = S6[0] + S6[1] + S6[2] + S6[3] + S6[4] + S6[5]
        # DERIVED: at stride 1 the paths are the unblocked staples, which _su2_staple computes independently
        if S == 1:
            err = float(np.abs(G._su2_staple(bg, q, mu) - A).max())
            # CHOSEN: float32 round-off tolerance on a sum of six triple quaternion products (O(1) values)
            assert err < 1e-4, err
        Bq = rect_sum(q, mu, S)
        a = bar(A)
        r = np.linalg.norm(a, axis=-1)
        ah = a / r[:, None]
        if syn is None:
            u = q[..., mu, :].reshape(-1, 4).astype(np.float64)
        else:
            u = synth(A, Bq, S6, *syn, q.shape)
        t = np.clip((u * ah).sum(-1), -1, 1)
        idx = np.clip((r / RMAX * NB).astype(np.int64), 0, NB - 1)
        B = bar(Bq)
        Bpar = (B * ah).sum(-1)
        Bp = B - Bpar[:, None] * ah
        nb = np.linalg.norm(Bp, axis=-1)
        sb = [bar(s) for s in S6]
        cp = [(s * ah).sum(-1) for s in sb]
        W = sum(c[:, None] * s for c, s in zip(cp, sb))
        Wp = W - (W * ah).sum(-1, keepdims=True) * ah
        nw = np.linalg.norm(Wp, axis=-1)
        Q = sum(c * c for c in cp)
        sp = [s - c[:, None] * ah for c, s in zip(cp, sb)]
        perm = rng.permutation(len(u))
        un = u[perm]
        tn = np.clip((un * ah).sum(-1), -1, 1)
        for out, sel in ((outs[0], None), (outs[1], o0)):  # NOT A READ: all origins, origin 0
            if sel is None:
                f = lambda x: x
            else:
                f = lambda x: x[sel] if not isinstance(x, list) else [y[sel] for y in x]
            args = (f(r), f(Bp), f(nb), f(Wp), f(nw), f(Bpar), f(Q), f(sp))
            ia, aa = f(idx), f(ah)
            rr, Bp_, nb_, Wp_, nw_, Bpar_, Q_, sp_ = args
            accumulate(out, ia, f(t), f(u), aa, rr, Bp_, nb_, Wp_, nw_, Bpar_, Q_, sp_, False)
            accumulate(out, ia, f(tn), f(un), aa, rr, Bp_, nb_, Wp_, nw_, Bpar_, Q_, sp_, True)


def atrous_check():
    """The origin-0 sublattice of the a trous levels equals block2 applied level by level."""
    rng = np.random.default_rng(1)
    q = rng.normal(size=(16, 16, 16, 16, 4, 4)).astype(np.float32)
    q /= np.linalg.norm(q, axis=-1, keepdims=True)
    ref, at, s = q, q, 1
    for _ in range(3):  # NOT A READ: three levels
        ref = O.block2(bg, ref, 0.15)
        at = block_atrous(at, 0.15, s)
        s *= 2
        e = float(np.abs(at[::s, ::s, ::s, ::s] - ref).max())
        # CHOSEN: float32 round-off tolerance; the two computations are the same algebra in a different order
        assert e < 1e-5, f"a trous level differs from block2: {e}"
    # origin (1,0,0,0) of level 1 is block2 of the configuration shifted by one site
    sh = np.roll(q, -1, axis=0)          # the whole configuration translated by one site in x
    e = float(np.abs(block_atrous(q, 0.15, 1)[1::2, ::2, ::2, ::2] - O.block2(bg, sh, 0.15)).max())
    # CHOSEN: float32 round-off tolerance, as above
    assert e < 1e-5, e
    return True


KEYS = None


if __name__ == "__main__":
    camp, levels, nsub, cw, outp = sys.argv[1], [int(x) for x in sys.argv[2].split(",")], int(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
    lo, hi = int(sys.argv[6]), int(sys.argv[7])
    syn = tuple(float(x) for x in os.environ["INF_SYN"].split(",")) if os.environ.get("INF_SYN") else None
    assert atrous_check()
    names = O.shards(camp, prefer_verified=True)[lo:hi]
    np.random.seed(20261003 + lo)
    bg.seed(20261003 + lo)               # the backend RNG the heat bath of the control mode draws from
    rng = np.random.default_rng(20261003 + lo)
    kmax = max(levels)
    store = [{} for _ in range(2)]
    t0 = time.time()
    for si, name in enumerate(names):
        arr = np.load(os.path.join(camp, name), mmap_mode="r")
        per = {k: (fresh(), fresh()) for k in levels}
        for ch in range(arr.shape[0]):  # NOT A READ: one chain at a time
            q = np.array(arr[ch], dtype=np.float32)
            s = 1
            for k in range(kmax + 1):  # NOT A READ: the block levels
                # DERIVED: level 0 is the unblocked configuration (usage line), so blocking starts at k = 1
                if k > 0:
                    if k <= nsub:
                        q = O.block2(bg, q, cw)
                    else:
                        q = block_atrous(q, cw, s)
                        s *= 2
                if k in levels:
                    read_level(q, s, per[k], rng, syn)
            del q
        for v in range(2):  # NOT A READ: all origins, origin 0
            for kk in per[levels[0]][v]:
                store[v].setdefault(kk, []).append(np.stack([per[k][v][kk] for k in levels]))
        print(f"{name} {si + 1}/{len(names)} {time.time() - t0:.0f}s", file=sys.stderr, flush=True)
    params = json.load(open(os.path.join(camp, "params.json")))
    for v, suf in ((0, ""), (1, "_o0")):  # NOT A READ: the two outputs
        meta = {"campaign": camp, "params": params, "kmax": len(levels) - 1, "kmin": 0, "levels": levels,
                "nsub": nsub, "c": cw, "shards": names, "NT": NT, "RMAX": RMAX, "NB": NB, "NK": NK,
                # DERIVED: output 0 is all origins, output 1 origin 0 (the loop above)
                "local_keys": LOCAL, "synthetic": syn, "origins": "all" if v == 0 else "0",
                "script": "influence_local.py"}
        np.savez(outp + suf + ".npz", meta=json.dumps(meta), **{k: np.stack(x) for k, x in store[v].items()})
    print("wrote", outp, file=sys.stderr)
