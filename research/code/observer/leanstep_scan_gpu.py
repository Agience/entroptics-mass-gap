"""The Lean observer step read at every step count of a range in one pass, in four or in three directions.

Diagnoses the spacing dependence of the obs4_read_gpu.py correlator: one pass of n steps records, at each
checkpoint n in [nmin, nmax] (stride every), the zero-momentum slice sums of the spatial-plaquette action density
(observer_step.slice_sums) and the lattice averages of the four-dimensional and spatial plaquette energy
densities, so the correlator and the observer's own scale come from the same configurations.

  mode 4d: observer_step.step (BlockSU2.blockLink, ApeLattice.apeConf, all four directions, six staples);
  mode 3d: the same step on the spatial links only, V = U_mu + c * (the four spatial staples), temporal links
           untouched (c = 0.25 is lattice_generator.ape_smear at alpha = 0.5).

    python leanstep_scan_gpu.py CAMPAIGN_DIR c mode nmin nmax every OUT_DIR [maxshards] [chains_per_batch]
Output per shard: OUT_DIR/<shard>_<mode>_c<c>.npz with n (k,), S (k, chain, T), e4 (k, chain), e3 (k, chain).
"""
import os
import sys

import numpy as np

import observer_step as O
from lattice_generator import _Backend, _qconj, _qmul, _sax


def step3(bg, q, c):
    out = bg.clone(q)
    for mu in range(3):
        U = q[..., mu, :]
        V = bg.clone(U)
        for nu in range(3):  # NOT A READ: the four spatial staples
            if nu == mu:
                continue
            Un = q[..., nu, :]
            up = _qmul(bg, _qmul(bg, Un, bg.roll(U, -1, _sax(nu, 1))), _qconj(bg, bg.roll(Un, -1, _sax(mu, 1))))
            Unm = bg.roll(Un, 1, _sax(nu, 1))
            dn = _qmul(bg, _qmul(bg, _qconj(bg, Unm), bg.roll(U, 1, _sax(nu, 1))), bg.roll(Unm, -1, _sax(mu, 1)))
            V = V + c * (up + dn)
        out[..., mu, :] = V / bg.norm(V, -1, True)
    return out


def emeans(bg, q):
    """Per chain: the lattice averages of the four-dimensional and spatial plaquette energy densities."""
    e4 = sum(e.mean(dim=(-4, -3, -2, -1)) for e in O.planes(bg, q))
    e3 = sum(e.mean(dim=(-4, -3, -2, -1)) for e in O.planes(bg, q, spatial=True))
    return bg.to_numpy(e4), bg.to_numpy(e3)


if __name__ == "__main__":
    camp, cw, mode = sys.argv[1], float(sys.argv[2]), sys.argv[3]
    nmin, nmax, every, out = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7]
    maxsh = O.opt(8, 10 ** 9)
    bat = O.opt(9, 8)
    stepf = {"4d": O.step, "3d": step3}[mode]
    chk = list(range(nmin, nmax + 1, every))
    bg = _Backend("cuda", fp="32")
    os.makedirs(out, exist_ok=True)
    for name in O.shards(camp, maxsh):
        dst = os.path.join(out, name.replace(".npy", f"_{mode}_c{cw:g}.npz"))
        if os.path.exists(dst):
            continue
        links = np.load(os.path.join(camp, name), mmap_mode="r")
        S, E4, E3 = [], [], []
        for c0 in range(0, links.shape[0], bat):  # NOT A READ: bat chains at a time bound the memory
            q = bg.t.as_tensor(np.array(links[c0:c0 + bat], dtype=np.float32), dtype=bg.f, device=bg.dev)
            s, e4, e3 = [], [], []
            for n in range(1, nmax + 1):
                q = stepf(bg, q, cw)
                if n in chk:
                    s.append(O.slice_sums(bg, q))
                    a, b = emeans(bg, q)
                    e4.append(a)
                    e3.append(b)
            S.append(np.stack(s))      # (k, bat, T)
            E4.append(np.stack(e4))    # (k, bat)
            E3.append(np.stack(e3))
            del q
        tmp = dst + ".tmp.npz"
        np.savez(tmp, n=np.array(chk), S=np.concatenate(S, 1), e4=np.concatenate(E4, 1), e3=np.concatenate(E3, 1))
        os.replace(tmp, dst)
        print(name, flush=True)
