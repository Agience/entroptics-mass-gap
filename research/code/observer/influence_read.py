"""The single-link conditional law of the observer's coarse configuration, read per staple-sum bin, for the
Dobrushin influence matrix (`ObserverEnergyMClose.CoarseViewInBox`). This script reads; `influence_agg.py`
turns the read into influences.

The configurations are blocked k = 0..kmax times by the observer's factor-2 block step
(`observer_step.block2`, coefficient c). On each blocked configuration, for every coarse link U_l:

  * A_l, the sum of its six plaquette staples (`lattice_generator._su2_staple`; a Wilson law is
    exp(beta * sdot(U, A)) in this orientation), r = |A_l| and t = sdot(U_l, A_l) / r;
  * the joint histogram of (r, theta = arccos t), NB x NT bins. influence_agg.py reads from it the
    character moments U_n(t) (Chebyshev polynomials of the second kind, the SU(2) characters, orthonormal
    under the Haar law of t); their bin means in r are the expansion coefficients of the conditional density
    of U_l relative to Haar, given r: g_r(t) = 1 + sum_n c_n(r) U_n(t);
  * two staple-sufficiency statistics. If the law of U_l given its neighbourhood depends on the
    neighbourhood only through A_l, it is invariant under the rotations fixing the direction a of A_l, and
    E[<u, v>] = 0 for every unit v perpendicular to a built from the neighbourhood. Two such v:
      rect: the perpendicular part of the sum of the 18 rectangle (2x1) staples of l;
      adj:  the perpendicular part of sum_p <a, s_p> s_p over the six plaquette staples s_p (what an
            adjoint, (tr)^2, plaquette term tilts toward).
    Their bin means, with the bin mean of t for scale, are recorded;
  * the same moments with the link field permuted across sites (each U_l paired with the staples of a
    random other link of the same direction): the shuffled-neighbourhood null.

All sums are accumulated per shard (one shard = one measurement of every chain) and per r bin, in float64.
Configuration arithmetic runs in fp32, one chain at a time, on CUDA or (INF_DEV=cpu) on the CPU.

    [INF_DEV=cpu INF_THREADS=8 INF_KMIN=0] python influence_read.py CAMPAIGN_DIR kmax c OUT.npz [maxshards]
"""
import json
import os
import sys
import time

import numpy as np
import torch

import observer_step as O
import lattice_generator as G

# CHOSEN: theta = arccos t bins of 0.25 degree; influence_agg.py takes the characters from them (a resolution
# budget: the bins must resolve U_n up to NMAX = 48 there)
NT = 720
RMAX, NB = 6.0, 120   # CHOSEN: r bins of width 0.05 over [0, 6] (|A| <= 6)


def path_close(bg, q, mu, steps):
    """Product of links along the path that starts at x + mu and takes `steps` ((direction, sign) pairs),
    as a field over x. With steps a closing path back to x, sdot(U_mu(x), result) = (1/2) tr of the loop."""
    disp = [0] * O.D
    disp[mu] = 1
    out = None
    for d, s in steps:
        # DERIVED: s is the step's sign (+1 forward, -1 backward)
        if s > 0:
            at = list(disp)
            disp[d] += 1
            conj = False
        else:
            disp[d] -= 1
            at = list(disp)
            conj = True
        f = q[..., d, :]
        for ax in range(O.D):  # NOT A READ: shift the link field to the step's base site
            if at[ax]:
                f = bg.roll(f, -at[ax], G._sax(ax, 1))
        if conj:
            f = G._qconj(bg, f)
        out = f if out is None else G._qmul(bg, out, f)
    # DERIVED: a closed path returns to its start, zero net displacement (exact integers)
    assert all(x == 0 for x in disp), "path does not close at x"
    return out


def staples(bg, q, mu):
    """The six plaquette closing paths of U_mu(x), in _su2_staple's orientation."""
    out = []
    for nu in range(O.D):
        if nu == mu:
            continue
        for s in (1, -1):  # NOT A READ: the two orientations of the plaquette in the (mu, nu) plane
            out.append(path_close(bg, q, mu, [(nu, s), (mu, -1), (nu, -s)]))
    return out


def rect_sum(bg, q, mu):
    """Sum of the 18 rectangle (2x1) closing paths of U_mu(x)."""
    B = None
    for nu in range(O.D):
        if nu == mu:
            continue
        for s in (1, -1):  # NOT A READ: three rectangles per plaquette orientation
            for st in ([(mu, 1), (nu, s), (mu, -1), (mu, -1), (nu, -s)],
                       [(nu, s), (mu, -1), (mu, -1), (nu, -s), (mu, 1)],
                       [(nu, s), (nu, s), (mu, -1), (nu, -s), (nu, -s)]):
                p = path_close(bg, q, mu, st)
                B = p if B is None else B + p
    return B


def bar(bg, x):
    # sdot(u, A) = <u, conj(A)> (4-vector dot): the conditional's direction in R^4 is conj(A)
    return G._qconj(bg, x).double()


def accumulate(acc, idx, t):
    """acc[r bin, theta bin] += 1 per link, theta = arccos t in NT equal bins over [0, pi]."""
    tb = (torch.arccos(t) / np.pi * NT).long().clamp(0, NT - 1)
    acc += torch.bincount(idx * NT + tb, minlength=NB * NT).double().reshape(NB, NT)


def read_level(bg, q, gen, out):
    for mu in range(O.D):  # NOT A READ: the four link directions
        S = staples(bg, q, mu)
        A = S[0] + S[1] + S[2] + S[3] + S[4] + S[5]
        if out["checked"] is False:
            ref = G._su2_staple(bg, q, mu)
            err = float((ref - A).abs().max())
            # CHOSEN: fp32 round-off tolerance on a sum of six triple quaternion products (O(1) values)
            assert err < 1e-4, f"staple paths disagree with _su2_staple: {err}"
            out["checked"] = True
        u = q[..., mu, :].double().reshape(-1, 4)
        a = bar(bg, A).reshape(-1, 4)
        r = a.norm(dim=-1)
        ah = a / r[:, None]
        t = (u * ah).sum(-1).clamp(-1, 1)
        idx = (r / RMAX * NB).long().clamp(0, NB - 1)
        out["cnt"] += torch.bincount(idx, minlength=NB).double()
        out["rsum"] += torch.bincount(idx, weights=r, minlength=NB)
        accumulate(out["ch"], idx, t)
        # staple-sufficiency statistics
        B = bar(bg, rect_sum(bg, q, mu)).reshape(-1, 4)
        Bp = B - (B * ah).sum(-1, keepdim=True) * ah
        nb = Bp.norm(dim=-1)
        W = 0
        for s in S:  # NOT A READ: the six plaquette staples of the adjoint direction
            sb = bar(bg, s).reshape(-1, 4)
            W = W + (sb * ah).sum(-1, keepdim=True) * sb
        Wp = W - (W * ah).sum(-1, keepdim=True) * ah
        nw = Wp.norm(dim=-1)
        out["rect"] += torch.bincount(idx, weights=(u * Bp).sum(-1) / nb.clamp_min(1e-12), minlength=NB)
        out["rectn"] += torch.bincount(idx, weights=nb, minlength=NB)
        out["adj"] += torch.bincount(idx, weights=(u * Wp).sum(-1) / nw.clamp_min(1e-12), minlength=NB)
        out["adjn"] += torch.bincount(idx, weights=nw, minlength=NB)
        # null: the same reads with U_l paired to the neighbourhood of a random other link
        perm = torch.randperm(u.shape[0], generator=gen, device=u.device)
        un = u[perm]
        tn = (un * ah).sum(-1).clamp(-1, 1)
        accumulate(out["chN"], idx, tn)
        out["rectN"] += torch.bincount(idx, weights=(un * Bp).sum(-1) / nb.clamp_min(1e-12), minlength=NB)
        out["adjN"] += torch.bincount(idx, weights=(un * Wp).sum(-1) / nw.clamp_min(1e-12), minlength=NB)
        # conditioning beyond |A|: the (r, theta) histogram split in terciles of two further neighbourhood
        # scalars, qr = <b, a>/|b| (rectangle staples' alignment with the staple sum) and
        # qa = sum_p <s_p, a>^2 (the adjoint invariant, not a function of r)
        qa = 0
        for s in S:  # NOT A READ: the six plaquette staples of the adjoint invariant
            qa = qa + ((bar(bg, s).reshape(-1, 4) * ah).sum(-1)) ** 2
        qr = (B * ah).sum(-1) / B.norm(dim=-1).clamp_min(1e-12)
        for j, qv in enumerate((qr, qa)):  # NOT A READ: the two further scalars
            if out["edges"][j] is None:
                out["edges"][j] = torch.quantile(qv[: 1 << 20].float(), torch.tensor([1 / 3, 2 / 3], device=qv.device)).double()
            ter = torch.bucketize(qv, out["edges"][j])
            tb = (torch.arccos(t) / np.pi * NT).long().clamp(0, NT - 1)
            flat = (ter * NB + idx) * NT + tb
            out["chQ"][j] += torch.bincount(flat, minlength=3 * NB * NT).double().reshape(3, NB, NT)
            out["cntQ"][j] += torch.bincount(ter * NB + idx, minlength=3 * NB).double().reshape(3, NB)
            out["rsumQ"][j] += torch.bincount(ter * NB + idx, weights=r, minlength=3 * NB).reshape(3, NB)
        del S, A, B, Bp, W, Wp, u, un, a, ah, t, tn, idx, r, perm


def fresh(dev):
    z = lambda *s: torch.zeros(s, dtype=torch.float64, device=dev)
    return {"cnt": z(NB), "rsum": z(NB), "ch": z(NB, NT), "chN": z(NB, NT), "rect": z(NB), "rectn": z(NB),
            "adj": z(NB), "adjn": z(NB), "rectN": z(NB), "adjN": z(NB), "checked": False,
            "chQ": z(2, 3, NB, NT), "cntQ": z(2, 3, NB), "rsumQ": z(2, 3, NB), "edges": [None, None]}


if __name__ == "__main__":
    camp, kmax, cw, outp = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), sys.argv[4]
    maxsh = O.opt(5, 10 ** 9)
    kmin = int(os.environ.get("INF_KMIN", "0"))  # CHOSEN per run: levels below kmin are blocked through, not read
    dev = os.environ.get("INF_DEV", "cuda")  # CHOSEN: cpu for 64^4, whose blocked temporaries exceed the shared GPU
    if dev == "cpu":
        torch.set_num_threads(int(os.environ.get("INF_THREADS", "8")))
    bg = G._Backend(dev, fp="32")
    gen = torch.Generator(device=bg.dev).manual_seed(20261003)
    haar = camp.startswith("haar:")  # haar:L:chains:shards -- Haar-random links, the beta = 0 substrate
    if haar:
        _, hl, hc, hs = camp.split(":")
        names = [f"haar_{i:03d}" for i in range(int(hs))]
        hgen = np.random.default_rng(int(hl) * 1000 + int(hc))
    else:
        names = O.shards(camp, maxsh, prefer_verified=False)
        if os.environ.get("INF_SHARDS"):  # a list of shards whose SHA-256 was checked against SHA256SUMS
            ok = {l.strip() for l in open(os.environ["INF_SHARDS"]) if l.strip()}
            names = [n for n in names if n in ok]
    TC = torch.cos((torch.arange(NT, dtype=torch.float64, device=bg.dev) + 0.5) * np.pi / NT)
    keys = ["cnt", "rsum", "ch", "chN", "rect", "rectn", "adj", "adjn", "rectN", "adjN", "chQ", "cntQ", "rsumQ"]
    edges = {}  # per level: the tercile edges, fixed by the first chain read
    store = {k: [] for k in keys}
    t0 = time.time()
    checked = False
    for si, name in enumerate(names):
        if haar:
            arr = hgen.normal(size=(int(hc), *([int(hl)] * O.D), O.D, 4)).astype(np.float32)
            arr /= np.linalg.norm(arr, axis=-1, keepdims=True)
        else:
            arr = np.load(os.path.join(camp, name), mmap_mode="r")
        per = [fresh(bg.dev) for _ in range(kmax + 1)]
        for ch in range(arr.shape[0]):  # NOT A READ: one chain at a time (memory)
            q = torch.as_tensor(np.array(arr[ch]), dtype=torch.float32, device=bg.dev)
            for k in range(kmax + 1):  # NOT A READ: the block levels
                # DERIVED: level 0 is the unblocked configuration, so blocking starts at k = 1
                if k > 0:
                    q = O.block2(bg, q, cw)
                if k < kmin:
                    continue
                per[k]["checked"] = checked
                per[k]["edges"] = edges.setdefault(k, [None, None])
                read_level(bg, q, gen, per[k])
                checked = True
            del q
            if bg.dev.type == "cuda":
                torch.cuda.empty_cache()
        for kk in keys:
            store[kk].append(np.stack([p[kk].cpu().numpy() for p in per]))
        print(f"{name} {si + 1}/{len(names)} {time.time() - t0:.0f}s "
              f"mean t k=0..: " + " ".join(f"{float((p['ch'].sum(0) * TC).sum() / p['cnt'].sum()):.4f}" for p in per),
              file=sys.stderr, flush=True)
    meta = {"edges": {str(k): [e.tolist() for e in v] for k, v in edges.items()}, "kmin": kmin, "campaign": camp, "params": ({"beta": 0.0, "dims": [int(hl)] * O.D, "chains": int(hc)} if haar
                       else json.load(open(os.path.join(camp, "params.json")))), "kmax": kmax, "c": cw,
            "shards": names, "NT": NT, "RMAX": RMAX, "NB": NB, "script": "influence_read.py"}
    np.savez(outp, meta=json.dumps(meta), **{k: np.stack(v) for k, v in store.items()})
    print("wrote", outp, file=sys.stderr)
