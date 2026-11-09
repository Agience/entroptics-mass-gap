"""The observer's connected three-point function at separated supports, read.

The cube triple puts three cube energies of the observer's reading (cubeSum a l (O o V_k): the Lean
observer step, then the six-plane plaquette energy 1 - (1/2) tr P summed over a cube of side b sites) at base sites
0, D e_mu, D e_nu, and the separation ratio reads

    sepRatio = cum3(A, B, C)^2 / |cov2(A, B) cov2(B, C) cov2(C, A)|,
    cov2(A, B) = nu((A - nu A)(B - nu B)),  cum3(A, B, C) = nu((A - nu A)(B - nu B)(C - nu C)),

with nu the Wilson state: here the ensemble average over configurations and, the state being translation invariant,
over every base site of the periodic lattice; nu A is the mean over all cubes. The pair of axes (mu, nu) is (0, 1),
as tripleBase places them, and, separately, pooled over the six planes (the state and the six-plane density are
hypercubic invariant).

The support of one reading. After n steps the energy density at x depends on links within n lattice units (each
step reads the staples); the observer's weight on them falls off as the step's heat kernel. `reach` and `flatreach`
read that fall-off: the change |delta e(x)| of the energy density after n steps when one link is rotated, summed over
the shell at sup-norm distance d from the link, and the radius rho_eps beyond which the fraction eps of the total
change lies. `reach` does it on a stored configuration with the full step; `flatreach` on the flat field with the
step's small-field (abelian) linearisation A_mu -> [A_mu + c sum_nu (A_nu(x) + A_mu(x+nu) - A_nu(x+mu)
- A_nu(x-nu) + A_mu(x-nu) + A_nu(x-nu+mu))] / (1 + 6c), which needs no SU(2) arithmetic and so reaches n = 105.
A cube of side b then has support b + 2 rho + 1 sites per axis (the +1 is the plaquette's extent), and two cubes
whose bases are D sites apart along an axis have supports separated by the gap D - b - 2 rho - 1.

Errors: delete-one jackknife over chains. Nothing is fitted.

    python three_point_read.py field CAMP c n OUT_DIR shard_lo shard_hi shard_step
        energy-density fields after n Lean steps, float32 (chain, L, L, L, L) per shard; numpy (OBS_DEVICE unset)
        or the generator's torch backend (OBS_DEVICE=cuda)
    python three_point_read.py reach CAMP shard chain c n theta OUT.json
    python three_point_read.py flatreach L c n OUT.json
    python three_point_read.py triple OUT.json b D1,D2,... NAME:r0lo-r0hi:DIR[+DIR] ...
        from `field` outputs: cubes of side b sites at every base site, offsets D sites, periodic
    python three_point_read.py cells OUT.json key S1,S2,... NAME:b:r0lo-r0hi:DIR ...
        from cell_read.py outputs: the periodic grid of cubes `key` (side b), offsets s cells
"""
import glob
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # research/code: the adapter
import entroptics_adapter as E  # noqa: E402

# DERIVED: the six coordinate planes (mu < nu) of four dimensions
PLANES = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


# ---------------------------------------------------------------------------------------------- estimator

def block_sums(x, planes, s):
    """Raw sums over the triples (base, base + s e_mu, base + s e_nu) of one block x, shape (nconf, m, m, m, m),
    periodic; the centred cumulants follow from them at any mean. The pair sums AB, BC, CA are the library's periodic
    lagged products (entroptics_adapter.torus_product, nothing subtracted, times the site count): AB at s e_mu, CA at
    s e_nu, BC at s (e_nu - e_mu) by translation. The library has no third-order read, so ABC is summed here."""
    keys = ("n", "A", "B", "C", "AB", "BC", "CA", "ABC")
    t = dict.fromkeys(keys, 0.0)

    def disp(smu, snu):
        """The displacement smu e_mu + snu e_nu on the (config, x, y, z, t) array; the config axis is not moved."""
        d = [0] * x.ndim
        d[1 + mu] += smu
        d[1 + nu] += snu
        return tuple(d)

    for mu, nu in planes:
        # NOT A READ: the partner fields of the third-order sum, which the library does not read
        B = np.roll(x, -s, axis=1 + mu)
        C = np.roll(x, -s, axis=1 + nu)
        t["n"] += x.size
        t["A"] += x.sum()
        t["B"] += B.sum()
        t["C"] += C.sum()
        t["AB"] += x.size * E.torus_product(x, disp(s, 0))
        t["BC"] += x.size * E.torus_product(x, disp(-s, s))
        t["CA"] += x.size * E.torus_product(x, disp(0, s))
        t["ABC"] += (x * B * C).sum()
    t["N1"] = float(x.size)
    t["S1"] = float(x.sum())
    return t


def cumulants(t):
    """mean, cov01, cov12, cov20, cum3, sepRatio from summed raw moments; the mean is the all-cube mean."""
    mu = t["S1"] / t["N1"]
    n = t["n"]
    EA, EB, EC = t["A"] / n, t["B"] / n, t["C"] / n
    EAB, EBC, ECA, EABC = t["AB"] / n, t["BC"] / n, t["CA"] / n, t["ABC"] / n
    c01 = EAB - mu * (EA + EB) + mu * mu
    c12 = EBC - mu * (EB + EC) + mu * mu
    c20 = ECA - mu * (EC + EA) + mu * mu
    k3 = EABC - mu * (EAB + EBC + ECA) + mu * mu * (EA + EB + EC) - mu ** 3
    den = abs(c01 * c12 * c20)
    # CHOSEN: a division guard that returns sepRatio 0 when a covariance is exactly zero. 0 is the value that
    # reads as "separated", so this degenerate case lands on the favourable side rather than as undefined
    r = k3 * k3 / den if den != 0 else 0.0
    return np.array([mu, c01, c12, c20, k3, r])


def jackknife(sums):
    tot = {k: sum(s[k] for s in sums) for k in sums[0]}
    full = cumulants(tot)
    nb = len(sums)
    reps = np.array([cumulants({k: tot[k] - s[k] for k in tot}) for s in sums])
    err = np.sqrt((nb - 1) / nb * ((reps - reps.mean(0)) ** 2).sum(0))
    return full, err


def row_of(name, nblocks, nconf, b, D, label, side, sep, full, err, extra=None):
    row = {"ensemble": name, "blocks": nblocks, "configs": nconf, "b": b, "D_sites": D, "planes": label,
           "side_r0": side, "D_r0": sep,
           "mean": [full[0], err[0]], "cov01": [full[1], err[1]], "cov12": [full[2], err[2]],
           "cov20": [full[3], err[3]], "cum3": [full[4], err[4]], "sepRatio": [full[5], err[5]]}
    row.update(extra or {})
    print(f"{name:8s} b={b} D={D} {label:10s} blocks={nblocks} cum3={full[4]:+.4g}±{err[4]:.2g} "
          f"cov01={full[1]:.4g}±{err[1]:.2g} cov12={full[2]:.4g}±{err[2]:.2g} cov20={full[3]:.4g}±{err[3]:.2g} "
          f"sepRatio={full[5]:.4g}±{err[5]:.2g}", flush=True)
    return row


def dump(out, res):
    with open(out + ".tmp", "w") as fh:
        json.dump(res, fh, indent=1)
    os.replace(out + ".tmp", out)


# ---------------------------------------------------------------------------------------------- the reach

def sup_dist(L, y, mu):
    """Periodic sup-norm distance of every site to the link (y, mu), the link taken as the segment y..y+e_mu."""
    d = np.zeros((L,) * 4, dtype=np.int64)
    for ax in range(4):  # NOT A READ: the four axes
        r = np.arange(L)
        if ax == mu:
            lo = np.minimum((r - y[ax]) % L, (y[ax] - r) % L)
            hi = np.minimum((r - y[ax] - 1) % L, (y[ax] + 1 - r) % L)
            da = np.minimum(lo, hi)
        else:
            da = np.minimum((r - y[ax]) % L, (y[ax] - r) % L)
        shape = [1, 1, 1, 1]
        shape[ax] = L
        d = np.maximum(d, da.reshape(shape))
    return d


def profile(de, d):
    """Shell sums of |delta e| by distance, tail fractions, and rho_eps for eps = 1e-2, 1e-3, 1e-4."""
    a = np.abs(de)
    shell = np.bincount(d.ravel(), weights=a.ravel())
    tot = shell.sum()
    tail = tot - np.cumsum(shell)
    frac = tail / tot
    rho = {f"{eps:g}": int(np.argmax(frac <= eps)) if (frac <= eps).any() else None for eps in (1e-2, 1e-3, 1e-4)}
    return {"shell": shell.tolist(), "tail_fraction": frac.tolist(), "rho": rho}


def lin_step(A, c):
    """The small-field limit of observer_step.step: one abelian component per direction, A shape (4, L, L, L, L)."""
    out = np.empty_like(A)
    for mu in range(4):
        s = A[mu].copy()
        for nu in range(4):  # NOT A READ: the six staples
            if nu == mu:
                continue
            up = A[nu] + np.roll(A[mu], -1, nu) - np.roll(A[nu], -1, mu)
            Anm = np.roll(A[nu], 1, nu)
            dn = -Anm + np.roll(A[mu], 1, nu) + np.roll(Anm, -1, mu)
            s = s + c * (up + dn)
        out[mu] = s / (1 + 6 * c)
    return out


def lin_energy(A):
    """Six-plane energy of the small field, sum over planes of F^2 / 2 (1 - cos F to second order)."""
    e = 0.0
    for mu in range(4):
        for nu in range(mu + 1, 4):  # NOT A READ: the planes
            F = A[mu] + np.roll(A[nu], -1, mu) - np.roll(A[mu], -1, nu) - A[nu]
            e = e + 0.5 * F * F
    return e


# ---------------------------------------------------------------------------------------------- reads of the fields

def cube_field(e, b):
    """Sum of e over the cube of side b based at every site, periodic; e shape (..., L, L, L, L)."""
    s = e.astype(np.float64)
    for ax in range(-4, 0):  # NOT A READ: the four axes
        t = s.copy()
        for k in range(1, b):  # NOT A READ: the cube's extent
            t += np.roll(s, -k, axis=ax)
        s = t
    return s


def load_fields(dirs):
    """Energy-density fields grouped by chain (the jackknife blocks): list of arrays (nconf, L, L, L, L)."""
    blocks = {}
    for d in dirs:
        for f in sorted(glob.glob(os.path.join(d, "links_*_e.npy"))):
            x = np.load(f)
            for ch in range(x.shape[0]):  # NOT A READ: the chains of a shard
                blocks.setdefault(ch, []).append(x[ch])
    return [np.stack(blocks[k]) for k in sorted(blocks)]


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "field":
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import observer_step as O
        camp, cw, nst, outd = sys.argv[2], float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
        lo, hi, st = int(sys.argv[6]), int(sys.argv[7]), int(sys.argv[8])
        bg = O.backend() if os.environ.get("OBS_DEVICE") else __import__("lattice_generator")._Backend(None)
        os.makedirs(outd, exist_ok=True)
        for name in O.shards(camp)[lo:hi:st]:
            dst = os.path.join(outd, name.replace(".npy", f"_c{cw}_n{nst}_e.npy"))
            if os.path.exists(dst):
                continue
            links = np.load(os.path.join(camp, name), mmap_mode="r")
            rows = []
            for ch in range(links.shape[0]):  # NOT A READ: one chain at a time bounds the memory
                q = O.chain(bg, links, ch)
                for _ in range(nst):
                    q = O.step(bg, q, cw)
                e = O.energy_density(bg, q)[0]
                rows.append(np.asarray(e.cpu().numpy() if hasattr(e, "cpu") else e, dtype=np.float32))
                del q, e
            np.save(dst + ".tmp.npy", np.stack(rows))
            os.replace(dst + ".tmp.npy", dst)
            print(name, flush=True)

    elif mode == "reach":
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import observer_step as O
        from lattice_generator import _Backend, _qmul
        camp, shard, ch, cw, nst, th, out = (sys.argv[2], sys.argv[3], int(sys.argv[4]), float(sys.argv[5]),
                                             int(sys.argv[6]), float(sys.argv[7]), sys.argv[8])
        bg = _Backend(None)
        links = np.load(os.path.join(camp, shard), mmap_mode="r")
        q0 = np.array(links[ch:ch + 1], dtype=np.float64)
        L = q0.shape[1]
        y = (L // 2,) * 4
        rot = np.array([np.cos(th), np.sin(th), 0.0, 0.0])
        q1 = q0.copy()
        q1[(0,) + y + (0,)] = _qmul(bg, rot, q0[(0,) + y + (0,)])
        q = np.concatenate([q0, q1])
        for _ in range(nst):
            q = O.step(bg, q, cw)
        e = O.energy_density(bg, q)
        res = {"campaign": camp, "shard": shard, "chain": ch, "c": cw, "n": nst, "theta": th, "L": L}
        res.update(profile(e[1] - e[0], sup_dist(L, y, 0)))
        print(json.dumps({k: res[k] for k in ("n", "L", "rho")}), flush=True)
        dump(out, res)

    elif mode == "flatreach":
        L, cw, nst, out = int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
        A = np.zeros((4,) + (L,) * 4)
        y = (L // 2,) * 4
        A[(0,) + y] = 1.0
        res = {"L": L, "c": cw, "rows": []}
        for k in range(1, nst + 1):
            A = lin_step(A, cw)
            if k in (8, 30, 31, 105, 113) or k == nst:
                r = {"n": k}
                r.update(profile(lin_energy(A), sup_dist(L, y, 0)))
                res["rows"].append(r)
                print(json.dumps({"n": k, "rho": r["rho"]}), flush=True)
        dump(out, res)

    elif mode == "triple":
        out, b, Ds = sys.argv[2], int(sys.argv[3]), [int(v) for v in sys.argv[4].split(",")]
        res = []
        for spec in sys.argv[5:]:
            name, r0, dirs = spec.split(":", 2)
            r0lo, r0hi = (float(v) for v in r0.split("-"))
            blocks = [cube_field(x, b) for x in load_fields(dirs.split("+"))]
            for D in Ds:
                for label, planes in (("plane01", PLANES[:1]), ("six_planes", PLANES)):
                    full, err = jackknife([block_sums(x, planes, D) for x in blocks])
                    res.append(row_of(name, len(blocks), int(sum(x.shape[0] for x in blocks)), b, D, label,
                                      [b / r0hi, b / r0lo], [D / r0hi, D / r0lo], full, err))
            dump(out, res)

    elif mode == "cells":
        out, key, seps = sys.argv[2], sys.argv[3], [int(v) for v in sys.argv[4].split(",")]
        res = []
        for spec in sys.argv[5:]:
            name, b, r0, d = spec.split(":", 3)
            b = int(b)
            r0lo, r0hi = (float(v) for v in r0.split("-"))
            per = {}
            for f in sorted(glob.glob(os.path.join(d, "*.npz"))):
                x = np.load(f)[key]
                for ch in range(x.shape[0]):  # NOT A READ: the chains of a shard
                    per.setdefault(ch, []).append(x[ch])
            blocks = [np.stack(per[k]) for k in sorted(per)]
            for s in seps:
                for label, planes in (("plane01", PLANES[:1]), ("six_planes", PLANES)):
                    full, err = jackknife([block_sums(x, planes, s) for x in blocks])
                    res.append(row_of(name, len(blocks), int(sum(x.shape[0] for x in blocks)), b, s * b, label,
                                      [b / r0hi, b / r0lo], [s * b / r0hi, s * b / r0lo], full, err))
        dump(out, res)
    else:
        raise SystemExit(__doc__)
