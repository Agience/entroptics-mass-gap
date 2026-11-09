"""Checks for `MassGap.NoTransitionFlow`: which readings are monotone along the zoom-out?

Exact linear algebra, quadrature and closed forms only; no Monte Carlo. Run time under 10 seconds
(asserted).

1. The Lean statements on numbers. `chunkTension` doubling (sigma (2l)^2 = 4 sigma l^2); `kpCost`
   and the count condition 4 z e^{1 + kappa - tau} <= 1 of `MatchAt.matchAt_of_count`; the step at
   which a units-covariant edge cost passes it (`matchAt_of_tension_flow`); one length for every
   zoom under a floor (`uniform_length_of_floor`); the `fade` line, confined at every zoom, failing
   at every length on fine enough zooms (`fade_confined_no_uniform`); `U(1)` at sigma = 0
   (`u1_flow`).
2. Data processing on finite reversible Markov slabs (`obs_rate_zoomOut`, `fullRate_zoomOut`):
   rho(K^2) = rho(K)^2, every coarse reading's rate across n slabs <= rho(K)^n, and the swap control
   (`observer_rate_not_monotone`): the observer's rate 0 across one slab, 1 across two.
3. Migdal-Kadanoff recursion (b = 2, d = 4: bond moving f -> f^4, then decimation t_n -> t_n^4) on
   class functions of SU(2) and U(1), as in `match_checks.py`. A PROXY ONLY: an approximation, not a
   bound on the true RG, and not a statement about the 4D Wilson measure. Tracked per step:
   * s_k = -log t_F, the proxy's cost per renormalised plaquette (in MK a loop of A renormalised
     plaquettes reads t_F^A). It is NOT assumed to be a tension of the form sigma l^2: at the U(1)
     Coulomb fixed point it is a fixed positive number; its running coefficient
     (s_{k+1} - s_k)/s_k^2 (`RunsOneWay`) and, at the strong end, the law s' = 4 (s - log 4);
   * rho_k = max_{n >= 1} |t_n|, the maximal correlation of the class-function convolution kernel
     (the observer's relative rate per chunk);
   * D_k, the relative entropy of the normalised plaquette weight to Haar measure;
   * v_k = w(-1)/w(1) for SU(2) (the centre-vortex weight of one renormalised plaquette, a proxy for
     the 't Hooft flux free energy F = -log v), and w(pi)/w(0) for U(1);
   and, inside one step, whether decimation alone (a 4-fold convolution, a Markov operator fixing
   Haar measure) lowers D, as data processing requires (for rho this is automatic, t -> t^4), and
   whether bond moving raises D.
"""
from __future__ import annotations

import math
import time

import numpy as np
from entroptics_adapter import matrix_pencil
from scipy.special import iv

T0 = time.time()
E = math.e
# DERIVED: in 4D a plaquette has 4 links, each shared with 5 other plaquettes: 4 * 5 = 20 (match_checks.DELTA).
DELTA = 20
Z_ENT = E * DELTA          # connected-set entropy per plaquette, as in match_checks.py
# CHOSEN: no decay rate demanded beyond KP, the plain clustering threshold (match_checks.KAPPA); a
# positive kappa raises kpCost by kappa.
KAPPA = 0.0


# ---------------------------------------------------------------- 1. Lean statements on numbers
def kp_cost(z, kappa=KAPPA):
    return 1 + kappa + math.log(4 * z + 1)


def count_ok(z, tau, kappa=KAPPA):
    # DERIVED: the count condition 4 z e^{1 + kappa - tau} <= 1 of `MatchAt.matchAt_of_count`.
    return 4 * z * math.exp(1 + kappa - tau) <= 1


def section1():
    print("1. the Lean statements on numbers")
    for s, l in ((0.3, 1.0), (1.0, 2.5), (2.0, 0.7)):
        # CHOSEN: tolerance on the exact doubling identity sigma (2l)^2 = 4 sigma l^2 at O(1) sizes.
        assert abs(s * (2 * l) ** 2 - 4 * s * l ** 2) < 1e-12
    c = kp_cost(Z_ENT)
    print(f"   kpCost(z = e*20) = {c:.4f}; count condition holds at tau = kpCost: {count_ok(Z_ENT, c)}")
    assert count_ok(Z_ENT, c) and not count_ok(Z_ENT, c - 1.5)
    # units-covariant flow sigma f (2^k l0)^2 with sigma l0^2 = 0.25 (f = 1): step where it passes
    s0 = 0.25
    ks = [k for k in range(20) if count_ok(Z_ENT, s0 * 4 ** k)]
    print(f"   s_0 = sigma l0^2 = {s0}: s_k = 4^k s_0 passes the count condition from step {ks[0]}"
          f" (s = {s0 * 4 ** ks[0]:.2f}); every later step passes: {ks == list(range(ks[0], 20))}")
    assert ks == list(range(ks[0], 20))
    # uniform length under a floor: L0 = sqrt(kpCost / sigma0)
    for sig0 in (0.5, 1.0, 2.0):
        L0 = math.sqrt(c / sig0)
        sig = sig0 * (1 + np.abs(np.sin(np.arange(50))))      # a line with floor sig0
        ok = all(count_ok(Z_ENT, sj * L ** 2) for sj in sig for L in (L0, 1.5 * L0, 3 * L0))
        print(f"   floor sigma0 = {sig0}: one length L0 = {L0:.3f} serves all 50 zooms: {ok}")
        assert ok
    # fade line: sigma_j = 1/(j+1) > 0 at every zoom; at each L the condition fails for large j
    for L in (2.0, 10.0, 100.0):
        jfail = next(j for j in range(10 ** 7) if not count_ok(Z_ENT, L ** 2 / (j + 1)))
        print(f"   fade line, L = {L:6.1f}: count condition fails from zoom j = {jfail}"
              f" (sigma_j L^2 = {L ** 2 / (jfail + 1):.3f} < {c:.3f})")
        assert all(not count_ok(Z_ENT, L ** 2 / (j + 1)) for j in range(jfail, jfail + 1000))
    # U(1) at sigma = 0: the cost stays 0 and the condition fails for z >= 1/4
    for z in (0.25, 1.0, Z_ENT):
        assert not count_ok(z, 0.0)
    print("   U(1), sigma = 0: cost 0 at every step; 4 z e^(1+kappa) > 1 for z = 1/4, 1, e*20")


# ---------------------------------------------------------------- 2. data processing
def l2_basis(pi, vecs):
    """Orthonormal basis (in L^2(pi)) of the mean-zero part of span(vecs)."""
    one = np.ones(len(pi))
    cols = []
    for v in vecs:
        u = v - (pi @ v) * one
        for b in cols:
            u = u - (pi @ (u * b)) * b
        n = math.sqrt(max(pi @ (u * u), 0.0))
        # CHOSEN: Gram-Schmidt drop level; a residual norm below it is read as linear dependence
        # (a dependent residual is at rounding, ~1e-16; an independent one is O(1) for the vectors read).
        if n > 1e-10:
            cols.append(u / n)
    return cols


def rate_on(pi, K, basis):
    if not basis:
        return 0.0
    # the two-slice pair on the readings: zero-lag Gram <f, g>_pi, one-step <f, K g>_pi (symmetric:
    # every chain read here is reversible)
    G0 = np.array([[pi @ (f * g) for g in basis] for f in basis])
    B = np.array([[pi @ (f * (K @ g)) for g in basis] for f in basis])
    return float(np.abs(matrix_pencil(G0, B).evals).max())


def full_rate(pi, K):
    n = len(pi)
    return rate_on(pi, K, l2_basis(pi, [np.eye(n)[i] for i in range(n)]))


def section2():
    print("2. data processing on reversible Markov slabs")
    rng = np.random.default_rng(7)
    for trial in range(3):
        n = 12
        W = rng.random((n, n))
        W = W + W.T                                   # symmetric weights: reversible chain
        pi = W.sum(1) / W.sum()
        K = W / W.sum(1, keepdims=True)
        r1 = full_rate(pi, K)
        r2 = full_rate(pi, K @ K)
        c = rng.integers(0, 3, n)                     # a coarse reading with 3 values
        basis = l2_basis(pi, [(c == v).astype(float) for v in range(3)])
        obs = [rate_on(pi, np.linalg.matrix_power(K, m), basis) for m in (1, 2, 4)]
        print(f"   trial {trial}: rho(K) = {r1:.5f}, rho(K^2) = {r2:.5f} (rho(K)^2 = {r1 ** 2:.5f});"
              f" observer rate at n = 1, 2, 4: {obs[0]:.5f}, {obs[1]:.5f}, {obs[2]:.5f}"
              f" <= rho^n: {all(o <= r1 ** m + 1e-12 for o, m in zip(obs, (1, 2, 4)))}")
        # CHOSEN: tolerance on rho(K^2) = rho(K)^2, exact for a reversible K (`fullRate_zoomOut`).
        assert abs(r2 - r1 ** 2) < 1e-10
        assert all(o <= r1 ** m + 1e-12 for o, m in zip(obs, (1, 2, 4)))
    # swap control: states (a, b), K swaps, observer reads a
    states = [(a, b) for a in (0, 1) for b in (0, 1)]
    pi = np.full(4, 0.25)
    K = np.array([[1.0 if q == (p[1], p[0]) else 0.0 for q in states] for p in states])
    basis = l2_basis(pi, [np.array([1.0 if s[0] == v else 0.0 for s in states]) for v in (0, 1)])
    o1, o2 = rate_on(pi, K, basis), rate_on(pi, K @ K, basis)
    print(f"   swap control: observer rate across one slab {o1:.3f}, across two {o2:.3f};"
          f" full rate {full_rate(pi, K):.3f}")
    # CHOSEN: tolerances on the swap control's exact rates 0 (one slab) and 1 (two slabs).
    assert o1 < 1e-12 and abs(o2 - 1) < 1e-12


# ---------------------------------------------------------------- 3. Migdal-Kadanoff proxy
_TH = np.linspace(1e-6, np.pi - 1e-6, 4001)
_MU2 = (2 / np.pi) * np.sin(_TH) ** 2
_DTH = _TH[1] - _TH[0]
# CHOSEN: SU(2) representation cutoff 2j < 60, as match_checks.NREP on the same theta grid.
NREP = 60
_CHI2 = np.array([np.sin((n + 1) * _TH) / np.sin(_TH) for n in range(NREP)])
_PH = np.linspace(-np.pi, np.pi, 4001)[:-1]
# CHOSEN: U(1) charge cutoff n < 80, as match_checks.mk_u1 on the same 4000-point angle grid.
NU1 = 80
_COS = np.array([np.cos(n * _PH) for n in range(NU1)])


def su2_w(t):
    return 1 + sum((n + 1) * t[n] * _CHI2[n] for n in range(1, NREP))


def su2_read(t):
    w = np.clip(su2_w(t), 1e-300, None)
    D = float(np.sum(w * np.log(w) * _MU2) * _DTH)
    w1 = 1 + sum((n + 1) ** 2 * t[n] for n in range(1, NREP))
    wm1 = 1 + sum((-1) ** n * (n + 1) ** 2 * t[n] for n in range(1, NREP))
    return dict(s=-math.log(t[1]), rho=float(np.max(np.abs(t[1:]))), D=D, v=wm1 / w1)


def su2_step(t):
    F = np.clip(su2_w(t), 0, None) ** 4                       # bond moving
    Z0 = float(np.sum(F * _MU2) * _DTH)
    tm = np.array([float(np.sum(F * _CHI2[n] * _MU2) * _DTH) / ((n + 1) * Z0) for n in range(NREP)])
    tm[0] = 1.0
    t2 = tm ** 4                                              # decimation
    t2[0] = 1.0
    return tm, t2


def u1_w(t):
    return 1 + 2 * (t[1:] @ _COS[1:])


def u1_read(t):
    w = np.clip(u1_w(t), 1e-300, None)
    D = float(np.mean(w * np.log(w)))
    w0 = 1 + 2 * float(np.sum(t[1:]))
    wpi = 1 + 2 * float(np.sum(t[1:] * (-1.0) ** np.arange(1, NU1)))
    return dict(s=-math.log(t[1]), rho=float(np.max(np.abs(t[1:]))), D=D, v=wpi / w0)


def u1_step(t):
    F = np.clip(u1_w(t), 0, None) ** 4
    Z0 = float(F.mean())
    tm = (_COS @ F) / len(_PH) / Z0
    tm[0] = 1.0
    t2 = tm ** 4
    t2[0] = 1.0
    return tm, t2


# CHOSEN: track a flow only while t_F > 1e-12 (s < 27.6). Below it the quadrature of the moved
# weight (absolute error ~1e-16) sets t_F, so s is the noise floor, not the flow; every statement
# below is read on the tracked part. KP (s >= kpCost = 6.39) is reached well inside it.
T_FLOOR = 1e-12


def run_flow(t, step, read, steps):
    rows, dec_ok, bond_ok = [], True, True
    for _ in range(steps):
        if abs(t[1]) < T_FLOOR:
            break
        r = read(t)
        tm, t2 = step(t)
        if abs(tm[1]) < T_FLOOR:
            rows.append(r)
            break
        rm = read(tm)
        bond_ok &= rm["D"] >= r["D"] - 1e-9          # bond moving raises D
        if abs(t2[1]) >= T_FLOOR:
            r2 = read(t2)
            # decimation is a 4-fold convolution: data processing lowers D
            dec_ok &= r2["D"] <= rm["D"] + 1e-9
        rows.append(r)
        t = t2
    return rows, dec_ok, bond_ok


# DERIVED: start = 0 scans from the first tracked step; callers pass 1 for "from step 1 on".
def first_violation(xs, sign, start=0):
    for k in range(start, len(xs) - 1):
        if sign * (xs[k + 1] - xs[k]) < -1e-9:
            return k
    return None


def section3():
    print("3. Migdal-Kadanoff proxy (b = 2, d = 4); an approximation, not the 4D Wilson RG")
    out = {}
    for name, init, step, read, betas in (
            ("SU(2)", lambda b: np.array([iv(n + 1, b) / iv(1, b) for n in range(NREP)]),
             su2_step, su2_read, (1.0, 2.5, 4.0)),
            ("U(1)", lambda b: np.array([iv(n, b) / iv(0, b) for n in range(NU1)]),
             u1_step, u1_read, (0.5, 2.0, 4.0))):
        for b in betas:
            rows, dec_ok, bond_ok = run_flow(init(b), step, read, 40)
            s = [r["s"] for r in rows]
            rho = [r["rho"] for r in rows]
            D = [r["D"] for r in rows]
            v = [r["v"] for r in rows]
            n = len(s)
            kkp = next((k for k, x in enumerate(s) if x >= kp_cost(Z_ENT)), None)
            # running coefficient b_k = (s_{k+1} - s_k) / s_k^2 (RunsOneWay asks b_k >= b > 0)
            bk = [(s[k + 1] - s[k]) / s[k] ** 2 for k in range(n - 1)]
            # strong end of MK: bond moving adds log 4 of entropy, decimation multiplies by 4
            # CHOSEN: s > 4 marks the strong end where the law is read; its correction O(e^{-s}) is then
            # below e^{-4}, the scale the DERIVED cut on max(law) further down uses.
            law = [abs(s[k + 1] - 4 * (s[k] - math.log(4))) for k in range(n - 1) if s[k] > 4]
            # physical tension in units of the first lattice: s_k / 4^k
            sph = [s[k] / 4 ** k for k in range(n)]
            pts = [k for k in (0, 2, 4, 8, 12, 16) if k < n]
            print(f"   {name} beta={b:3.1f}: tracked {n} steps; s_k at k={pts}: "
                  + " ".join(f"{s[k]:.3f}" for k in pts) + f"; s_k >= kpCost at step {kkp}")
            print(f"        rho_k: " + " ".join(f"{rho[k]:.3f}" for k in pts)
                  + "; D_k: " + " ".join(f"{D[k]:.3f}" for k in pts)
                  + "; v_k: " + " ".join(f"{v[k]:.4f}" for k in pts))
            fv = {q: first_violation(x, sg) for q, x, sg in
                  (("s up", s, 1), ("rho down", rho, -1), ("D down", D, -1), ("v up", v, 1))}
            fv1 = {q: first_violation(x, sg, 1) for q, x, sg in
                   (("s up", s, 1), ("rho down", rho, -1), ("D down", D, -1), ("v up", v, 1))}
            print(f"        first step breaking monotonicity: {fv}; from step 1 on: {fv1}")
            print(f"        running coefficient b_k = (s_k+1 - s_k)/s_k^2: min over k>=1 "
                  # DERIVED: the guard against min of an empty bk[1:], not a magnitude.
                  f"{min(bk[1:]) if len(bk) > 1 else float('nan'):.4f}, at k=0 {bk[0]:.4f};"
                  f" last {bk[-1]:.4g}; s_k/4^k: " + " ".join(f"{sph[k]:.3g}" for k in pts)
                  + (f"; |s_k+1 - 4(s_k - log 4)| <= {max(law):.2e} where s_k > 4" if law else ""))
            print(f"        decimation lowers D at every tracked step: {dec_ok};"
                  f" bond moving raises D at every tracked step: {bond_ok}")
            out[(name, b)] = dict(s=s, rho=rho, D=D, v=v, bk=bk, kkp=kkp, dec=dec_ok, bond=bond_ok,
                                  fv1=fv1, law=law, sph=sph)
    # assertions on the proxy (MK only): SU(2) runs one way from step 1 on with b_k bounded below,
    # reaches the count condition, follows s' = 4(s - log 4) at the strong end, and every tracked
    # reading is monotone from step 1; U(1) at weak coupling settles at a fixed positive cost
    # (b_k -> 0, s settled) and never reaches the count condition; decimation lowers D and bond
    # moving raises it at every tracked step.
    for b in (1.0, 2.5, 4.0):
        r = out[("SU(2)", b)]
        # CHOSEN: a positive lower bound on b_k from step 1 (`RunsOneWay` asks b_k >= b > 0); the reads are
        # 0.263, 0.169, 0.156, so beta = 4 sits within a factor 1.6 of the cut.
        assert r["kkp"] is not None and r["dec"] and r["bond"] and min(r["bk"][1:]) > 0.1
        assert all(x is None for x in r["fv1"].values())
        # DERIVED: the non-emptiness guard for max(r["law"]) below, not a magnitude.
        assert len(r["law"]) >= 1
        # DERIVED: the law is exact up to the next character term, O(t_F) = O(e^{-s}) <= e^{-4}
        assert max(r["law"]) < 4 * math.exp(-4)
    for b in (2.0, 4.0):
        r = out[("U(1)", b)]
        assert r["kkp"] is None and r["dec"] and r["bond"]
        # CHOSEN: 1e-6 reads b_k -> 0 at the last step (reads 5.8e-11 and -5.4e-14).
        # DERIVED: bk[0] < 0 is the sign test "s first falls", not a magnitude.
        assert abs(r["bk"][-1]) < 1e-6 and r["bk"][0] < 0          # s first falls, then stops
        # CHOSEN: 1e-9 reads s settled; 0.1 reads it positive with margin. The settled s is 0.264 and
        # 0.128, so beta = 4 sits within a factor 1.3 of the 0.1 cut.
        assert abs(r["s"][-1] - r["s"][-2]) < 1e-9 and r["s"][-1] > 0.1   # settled, positive
    assert out[("U(1)", 0.5)]["kkp"] is not None                  # strong-coupling U(1) confines
    return out


def section4():
    print("4. one number of doublings for every zoom (uniform_steps_of_runsOneWay)")
    T = kp_cost(Z_ENT)
    for b, s0 in ((0.15, 0.4), (0.15, 0.7), (0.3, 0.4)):
        K = math.ceil((T - s0) / (b * s0 ** 2))
        # iterate the extremal sequence s_{k+1} = s_k + b s0^2 (the proof's lower bound) and the
        # quadratic one s_{k+1} = s_k + b s_k^2; both must pass T by step K
        x, y = s0, s0
        for _ in range(K):
            x, y = x + b * s0 ** 2, min(y + b * y ** 2, 1e6)     # cap: only y >= T is read
        assert x >= T - 1e-9 and y >= T
        kq = _quad_steps(s0, b, T)
        print(f"   b = {b}, s0 = {s0}: the proof's K = ceil((kpCost - s0)/(b s0^2)) = {K} doublings;"
              f" s_k+1 = s_k + b s_k^2 passes kpCost after {kq}")
        assert kq <= K


def _quad_steps(s0, b, T):
    k, y = 0, s0
    while y < T:
        k, y = k + 1, y + b * y ** 2
    return k


def main():
    section1()
    section2()
    section3()
    section4()
    dt = time.time() - T0
    print(f"time {dt:.2f} s")
    # CHOSEN: the 10 s run-time budget the module docstring states; the run takes under 1 s.
    assert dt < 10


if __name__ == "__main__":
    main()
