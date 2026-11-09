"""Checks for `MassGap.MKBound`: the Migdal-Kadanoff sandwich, upper and lower flows, and the window.

Exact recursions on character coefficients; quadrature on class-function grids; no Monte Carlo. Run time
under 10 seconds (asserted).

Conventions (as in `match_checks.py`). Wilson plaquette weight e^{beta_std Re tr U / N}, normalised
f = 1 + sum_{j != 0} d_j t_j Re chi_j, t_j = F_j / (d_j F_0) (for U(1): f = 1 + sum_{n != 0} t_n cos n theta).
Blocking b = 2 in d = 4. The upper decimation (Tomboulis 0707.2179 eqs. (2.19)-(2.22), (3.1)-(3.4) with
zeta = b^{d-2} = 4, r = 1): bond moving f -> f^zeta, then the exact 2-dimensional integration
t_j -> that_j^{b^2}, that_j = int f^zeta chi_j / (d_j int f^zeta); bulk factor per coarse plaquette
F0U = (int f^zeta)^{b^2}. The lower decimation: t^L = 0 with F0L = 1 (Tomboulis (3.9)), or t^L = t^6
(his (3.5)). The interpolated coefficients of Ito-Seiler 0711.4930 eq. (2.6b): t~ = alpha t^U.

1. Bond moving gives an upper bound (Jensen). int f^zeta >= 1 for every f >= 0 with int f = 1, so
   log F0U >= 0 at every step of every flow (asserted): the bulk factor of the upper bound is never below
   the lower bound's F0L = 1. This is `MKBound.pow_integral_ge_one` / `mkUpperF0_ge_one` evaluated.
2. Upper and lower flows for SU(2), SU(3), U(1). For each starting beta_std: u_n = sup |f - 1| along the
   upper flow, the first step in the direct-KP region of `match_checks.direct_kp_ok`, u at steps 10 and
   15, and the same for the lower flow (t^6). Cross-check: the SU(2) and U(1) upper flows equal
   `match_checks.mk_su2` / `mk_u1` (a second copy of the recursion is checked against the first).
   Results: SU(2) from beta_std = 1, 2, 4, 6 enters after 4, 8, 15, 23 steps; SU(3) from
   1, 2, 4, 6 after 2, 3, 7, 10; both stay. U(1) from beta = 1, 2, 4 does not enter in 40 steps.
3. Sampled interpolated flows stay below the upper flow. 6 seeded random alpha sequences in [0, 1]
   per beta (24 per group): u_n(alpha-flow) <= u_n(upper flow) at every step (asserted). At n = 1 this
   is linear (u_1(alpha) = alpha_0 u_1(upper), `abs_interp_dev_le`); from n = 2 on it tests the MK map
   under scaling, and the printed maximum ratio is taken over n >= 2. So, along the sampled orbits,
   once the upper flow meets the KP condition on u the interpolated flows meet it too. The KP condition
   on u is a necessary input of `StrongEnd` (the input `hreach` of `not_sandwichMatch_of_vortex`), not
   `StrongEnd` itself, which also needs the site-polymer representation with `MatchAt`; and the Lean
   pair (real w' with |w'| = |w|, Z+ = (Z + Z-)/2) models the Z_2 twist (SU(2), U(1) at angle pi),
   not the Z_3 twist of SU(3). The U(1) upper flow at beta >= 1 does not meet it in the steps run.
4. The window. Without `SandwichMatch` the sandwich only places Z and Z+ in intervals
   [Z~(0), Z~(1)]; with the lower bound t^L = 0, F0L = 1 of Tomboulis (3.9) (Z(0) = 1 <= Z(t^U), his
   (2.14)), `window_extensive` gives log Z~(1) - log Z~(0) >= N_p log F0U, N_p the number of coarse
   plaquettes. Printed: log F0U per coarse plaquette at the KP entry step, the log-width N_p log F0U on
   a coarse L^4 box (N_p = 6 L^4), against the vortex free energy scale at that step, L^2 t_F^{L^2}
   (a winding sheet of L^2 plaquettes at strong coupling). The log-width grows like L^4 and the scale
   it must resolve falls like exp(-O(L^2)): no bound-only computation can supply `SandwichMatch`; it is
   an exact identity whose tolerance (`vortex_of_sandwich`, the sum of epsilon_m) must sit below the
   vortex scale.
"""
from __future__ import annotations

import math
import os
import sys
import time

import numpy as np
from scipy.special import iv

T0 = time.time()
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import match_checks as mc  # noqa: E402

# DERIVED: zeta = b^{d-2} with blocking b = 2 in d = 4 (Tomboulis' bond-moving exponent, r = 1).
ZETA = 4          # b^{d-2}, b = 2, d = 4
# DERIVED: b^2 = 4 for b = 2, the number of fine plaquettes the 2-dimensional integration merges.
B2 = 4            # b^2 plaquettes merged by the 2-dimensional integration


# ------------------------------------------------------------------ class-function grids
class Group:
    """A class-function quadrature: points, Haar weights, Re chi_j on the points, dims, chi_j at the
    extremal points (where sup |f - 1| is attained but the torus grid may be degenerate)."""

    def __init__(self, name, weights, chis, dims, extremal):
        self.name = name
        self.w = weights / weights.sum()
        self.chi = chis                    # (reps, points), real parts
        self.d = dims                      # norm in t_j = int F chi_j / (d_j int F)
        self.ext = extremal                # (reps, k): Re chi_j at k extremal points

    def f(self, t):
        coef = self.d * t
        return 1.0 + coef @ self.chi, 1.0 + coef @ self.ext

    def u(self, t):
        fg, fe = self.f(t)
        return float(max(np.max(np.abs(fg - 1)), np.max(np.abs(fe - 1))))

    # DERIVED: alpha = 1 makes t~ = t^U, so the default step is the upper decimation itself.
    def step(self, t, alpha=1.0):
        """One upper decimation, then the interpolation t~ = alpha t^U.

        Returns (t~, log F0U, raw int f^zeta). log F0U is evaluated as b^2 log1p(int(6g^2 + 4g^3 + g^4)),
        g = f - 1 (int g = 0 for a normalised weight), so that it does not round to zero when the
        coefficients are small; the raw integral is returned for the Jensen check."""
        fg, _ = self.f(t)
        assert fg.min() > -1e-9, (self.name, fg.min())          # f >= 0: positivity of the weight
        F = np.clip(fg, 0.0, None) ** ZETA
        F0 = float(F @ self.w)
        g = fg - 1.0
        S = float((g * g * (6.0 + 4.0 * g + g * g)) @ self.w)
        that = (self.chi @ (F * self.w)) / (self.d * F0)
        return alpha * that ** B2, B2 * math.log1p(S), F0

    def tF(self, t):
        return float(t[0])


# CHOSEN: the representation cutoff (2j < 60) and theta grid of match_checks (NREP = 60, 4001 points),
# so the cross-check against mc.mk_su2 compares the same truncation; it does not test the truncation.
def su2_group(nrep=60, npts=4001):
    th = np.linspace(1e-6, np.pi - 1e-6, npts)
    w = np.sin(th) ** 2
    n = np.arange(1, nrep)                               # 2j = n, dimension n + 1
    chi = np.sin((n[:, None] + 1) * th[None, :]) / np.sin(th)[None, :]
    ext = np.stack([n + 1.0, (n + 1.0) * (-1.0) ** n], axis=1)          # U = 1, U = -1
    return Group("SU(2)", w, chi, n + 1.0, ext)


# DERIVED: equals su2_group's nrep, so the coefficient vector has one entry per character on the grid.
def su2_wilson(beta, nrep=60):
    n = np.arange(1, nrep)
    return iv(n + 1, beta) / iv(1, beta)


# CHOSEN: the charge cutoff |n| < 80 and 4000-point angle grid of match_checks.mk_u1, so the cross-check
# compares the same truncation; it does not test the truncation.
def u1_group(nmax=80, npts=4000):
    ph = np.linspace(-np.pi, np.pi, npts + 1)[:-1]
    n = np.concatenate([np.arange(1, nmax), -np.arange(1, nmax)])
    chi = np.cos(n[:, None] * ph[None, :])
    ext = np.stack([np.ones(len(n)), (-1.0) ** np.abs(n)], axis=1)
    return Group("U(1)", np.ones(npts), chi, np.ones(len(n)), ext)


# DERIVED: equals u1_group's nmax, so the coefficient vector has one entry per character on the grid.
def u1_wilson(beta, nmax=80):
    n = np.concatenate([np.arange(1, nmax), -np.arange(1, nmax)])
    return iv(np.abs(n), beta) / iv(0, beta)


def su3_reps(P):
    return [(p, q) for p in range(P + 1) for q in range(P + 1 - p) if (p, q) != (0, 0)]


# CHOSEN: truncation p + q <= 24 and a 128^2 torus grid; main() reruns at P = 30 and G = 160 and asserts
# the u_n change stays below 1e-6 (it reads 6.8e-14).
def su3_group(P=24, G=128):
    th = 2 * np.pi * (np.arange(G) + 0.5) / G
    T1, T2 = np.meshgrid(th, th, indexing="ij")
    z = np.stack([np.exp(1j * T1), np.exp(1j * T2), np.exp(-1j * (T1 + T2))]).reshape(3, -1)
    den = ((z[0] - z[1]) * (z[0] - z[2]) * (z[1] - z[2]))
    w = np.abs(den) ** 2
    # CHOSEN: separates the Weyl-denominator zeros (coincident eigenvalues, den = 0 up to rounding) from
    # the rest, a division guard; the Haar weight |den|^2 vanishes on the excluded points anyway.
    good = np.abs(den) > 1e-9
    inv = np.zeros_like(den)
    inv[good] = 1.0 / den[good]
    zp = np.ones((3, P + 3, z.shape[1]), dtype=complex)        # zp[i, k] = z_i^k
    for k in range(1, P + 3):
        zp[:, k] = zp[:, k - 1] * z
    reps = su3_reps(P)
    chi = np.zeros((len(reps), z.shape[1]))
    dims = np.zeros(len(reps))
    ext = np.zeros((len(reps), 3))
    om = np.exp(2j * np.pi / 3)
    for k, (p, q) in enumerate(reps):
        l0, l1 = p + q + 2, q + 1                             # Weyl: det[z_i^{l_j}] / det[z_i^{2,1,0}]
        num = (zp[0, l0] * (zp[1, l1] - zp[2, l1]) - zp[1, l0] * (zp[0, l1] - zp[2, l1])
               + zp[2, l0] * (zp[0, l1] - zp[1, l1]))
        chi[k] = (num * inv).real
        d = (p + 1) * (q + 1) * (p + q + 2) / 2
        dims[k] = d
        ext[k] = [d * (om ** ((p + 2 * q) * s)).real for s in range(3)]   # the three centre elements
    return Group("SU(3)", w, chi, dims, ext), reps


# DERIVED: equals su3_group's default G; the docstring requires the grid side the group was built on.
def su3_wilson_coeffs(grp, reps, beta, G=128):
    """Character coefficients of e^{beta Re tr U / 3}, by the same quadrature (G = the grid's side)."""
    th = 2 * np.pi * (np.arange(G) + 0.5) / G
    T1, T2 = np.meshgrid(th, th, indexing="ij")
    tr = (np.cos(T1) + np.cos(T2) + np.cos(T1 + T2)).ravel()
    F = np.exp(beta / 3.0 * tr)
    F0 = float(F @ grp.w)
    return (grp.chi @ (F * grp.w)) / (grp.d * F0)


# ------------------------------------------------------------------ flows
def flow(grp, t0, steps, alphas=None, lower=False):
    """u_n along a flow. alphas: per-step interpolation (None = 1, the upper flow). lower: t -> t^6."""
    t = t0.copy()
    us, lf0, tfs, raw = [], [], [], []
    for k in range(steps):
        us.append(grp.u(t))
        tfs.append(grp.tF(t))
        if lower:
            t, lf, F0 = t ** 6, 0.0, 1.0
        else:
            t, lf, F0 = grp.step(t, 1.0 if alphas is None else alphas[k])
        lf0.append(lf)
        raw.append(F0)
    return np.array(us), np.array(lf0), np.array(tfs), np.array(raw)


def first_in(us):
    for i, u in enumerate(us):
        if mc.direct_kp_ok(u):
            return i
    return None


def main():
    rng = np.random.default_rng(20071130)
    su2 = su2_group()
    u1 = u1_group()
    su3, reps = su3_group()

    # cross-checks against match_checks' own recursion (second copy checked against the first)
    for b in (1.0, 4.0):
        a = flow(su2, su2_wilson(b), 20)[0]
        m = np.array(mc.mk_su2(b, steps=20))
        assert np.allclose(a, m, rtol=1e-6, atol=1e-9), (b, a[:5], m[:5])
    a = flow(u1, u1_wilson(2.0), 20)[0]
    m = np.array(mc.mk_u1(2.0, steps=20))
    assert np.allclose(a, m, rtol=1e-6, atol=1e-9)
    # SU(3) quadrature: int (Re chi_F)^2 = 1/2 (complex rep), int chi_adj^2 = 1, t_F(beta -> 0) = beta/18
    iF, iA = reps.index((1, 0)), reps.index((1, 1))
    # CHOSEN: tolerance on the exact orthonormality value 1/2; the quadrature reads it to ~6e-17.
    assert abs(float((su3.chi[iF] ** 2) @ su3.w) - 0.5) < 1e-9
    # CHOSEN: tolerance on the exact orthonormality value 1; the quadrature reads it to ~1e-16.
    assert abs(float((su3.chi[iA] ** 2) @ su3.w) - 1.0) < 1e-9
    tF_small = su3_wilson_coeffs(su3, reps, 1e-3)[iF]
    # CHOSEN: tolerance of order beta = 1e-3 on t_F/beta -> 1/18, the size of the O(beta) correction it
    # must admit; the read is 4.6e-6.
    assert abs(tF_small / 1e-3 - 1 / 18) < 1e-3, tF_small
    # SU(3) truncation (P = 24 vs 30) and grid (G = 128 vs 160) at beta_std = 6, first 8 upper steps
    su3b, repsb = su3_group(P=30)
    su3c, repsc = su3_group(P=24, G=160)
    ua = flow(su3, su3_wilson_coeffs(su3, reps, 6.0), 8)[0]
    ub = flow(su3b, su3_wilson_coeffs(su3b, repsb, 6.0), 8)[0]
    uc = flow(su3c, su3_wilson_coeffs(su3c, repsc, 6.0, G=160), 8)[0]
    drift = float(max(np.max(np.abs(ua - ub) / ua), np.max(np.abs(ua - uc) / ua)))
    print(f"SU(3) beta_std=6, u_n for n < 8: {np.round(ua, 3)}; relative change P 24->30, G 128->160: {drift:.1e}")
    # CHOSEN: the relative change in u_n allowed under P 24->30 and G 128->160; the read is 6.8e-14.
    assert drift < 1e-6

    cases = [("SU(2)", su2, su2_wilson, (1.0, 2.0, 4.0, 6.0)),
             ("SU(3)", su3, lambda b: su3_wilson_coeffs(su3, reps, b), (1.0, 2.0, 4.0, 6.0)),
             ("U(1)", u1, u1_wilson, (0.5, 1.0, 2.0, 4.0))]
    steps = 40
    print("\n1-2. upper (zeta = 4, r = 1) and lower (t^6) flows; KP = match_checks.direct_kp_ok on u = sup|f-1|")
    summary = {}
    jensen_min = math.inf
    for name, grp, wil, betas in cases:
        for b in betas:
            t0 = wil(b)
            uU, lfU, tfU, raw = flow(grp, t0, steps)
            uL = flow(grp, t0, steps, lower=True)[0]
            iU, iL = first_in(uU), first_in(uL)
            jensen_min = min(jensen_min, float(raw.min()) - 1.0)
            assert raw.min() >= 1.0 - 1e-12, (name, b, raw.min())     # 1. Jensen: int f^zeta >= 1
            stay = iU is not None and all(mc.direct_kp_ok(x) for x in uU[iU:])
            summary[(name, b)] = (uU, lfU, tfU, iU)
            tail = ""
            if iU is None:
                tail = f"; u_{steps - 1}={uU[-1]:.4f}, mean decrease per step over the last 20: " \
                       f"{(uU[-21] - uU[-1]) / 20:.1e}"
            print(f"   {name} beta_std={b:3.1f}: u_0={uU[0]:7.3f}; upper enters KP at step {iU} (stays {stay});"
                  f" u_10={uU[10]:.2e} u_15={uU[15]:.2e}; lower enters at {iL}{tail}")
    print(f"   Jensen: min over all steps of int f^zeta - 1 = {jensen_min:.2e} (>= 0 up to rounding)")
    # CHOSEN: regression pins on the SU(2) KP entry steps this recursion gives at beta_std 4 and 6 (the
    # module docstring states them); a change to the recursion, grid or KP test moves them.
    assert summary[("SU(2)", 4.0)][3] == 15 and summary[("SU(2)", 6.0)][3] == 23   # as match_checks
    assert all(summary[(n, b)][3] is not None for n in ("SU(2)", "SU(3)") for b in (1.0, 2.0, 4.0, 6.0))
    assert all(summary[("U(1)", b)][3] is None for b in (1.0, 2.0, 4.0))

    print("\n3. interpolated flows (alpha_m uniform in [0,1], seeded) against the upper flow")
    for name, grp, wil, betas in cases:
        worst = 0.0
        for b in betas:
            uU = summary[(name, b)][0][:25]
            for _ in range(6):
                al = rng.uniform(0.0, 1.0, 25)
                ua = flow(grp, wil(b), 25, alphas=al)[0]
                assert np.all(ua <= uU * (1 + 1e-9) + 1e-300), (name, b)
                # n = 1 is linear (u_1(alpha) = alpha_0 u_1(upper), `abs_interp_dev_le`); n >= 2 tests the
                # monotonicity of the MK map itself, so the ratio is reported from n = 2 on
                # DERIVED: the division guard for the ratio ua / uU below, not a magnitude.
                pos = uU[2:] > 0
                if np.any(pos):
                    worst = max(worst, float(np.max(ua[2:][pos] / uU[2:][pos])))
        print(f"   {name}: max over n >= 2 of u_n(alpha) / u_n(upper) = {worst:.3e} ({6 * len(betas)} sequences)")

    print("\n4. the window against the vortex scale at the KP entry step n (coarse box L^4, N_p = 6 L^4)")
    for (name, b), (uU, lfU, tfU, iU) in summary.items():
        if iU is None:
            print(f"   {name} beta_std={b:3.1f}: upper flow not in KP within {steps} steps; no window to compare")
            continue
        eps = lfU[iU]
        tF = abs(tfU[iU])
        # DERIVED: the guard against log of zero in logw and logv below, not a magnitude.
        assert eps > 0 and tF > 0
        row = []
        for L in (8, 16, 32):
            logw = math.log(6 * L ** 4 * eps)
            logv = math.log(L ** 2) + L ** 2 * math.log(tF)
            row.append(f"L={L}: {logw:7.1f} vs {logv:9.1f}")
            assert logw > logv
        print(f"   {name} beta_std={b:3.1f} n={iU:2d}: log F0U/plaq={eps:.2e}, t_F={tF:.2e};"
              f" log(N_p log F0U) vs log(L^2 t_F^(L^2)): " + "; ".join(row))

    dt = time.time() - T0
    print(f"\ntime {dt:.2f} s")
    # CHOSEN: the 10 s run-time budget the module docstring states; the run takes about 5 s.
    assert dt < 10


if __name__ == "__main__":
    main()
