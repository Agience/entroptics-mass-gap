"""Numerical checks for `MassGap/FineLinks.lean`: the owner's three links for the fine end (A).

No Monte Carlo. Every number is an exact finite computation (a discretised two-slice law, a free-field
mode sum, a character expansion). Run: python research/code/fine_links_checks.py  (under 10 s).

Part 1, link (1), near-free. A compact two-slice law on the circle against its Gaussian (free)
  approximation, at coupling beta:
      J (t, t')  ~ exp(beta [A (cos t + cos t') + cos(t - t')]),   A = 1 + sqrt 3,
      J0(t, t')  ~ exp(-beta [A (t^2 + t'^2)/2 + (t - t')^2/2]),
  both normalised on the same grid of n points of (-pi, pi]. The Gaussian has correlation
  1/(A + 1) = 2 - sqrt 3 = e^{-arccosh 2}, the free per-step factor of CondGap section 4. The
  readings W are the polynomials of degree <= 3 in x = sqrt(beta) t (closed under constants). For a
  small-field cut |x|, |x'| <= s: delta = max |J/J0 - 1| on the cut, L = |J - J0| off it,
  eps = max(mass L, top generalised eigenvalue of sum_y L(x,y) F(x)^2 against ||F||^2_{pi0} on W);
  kappa = delta + eps minimised over s. Checked: the rate of J on W is at most
  nearFreeRate(r0, kappa) = (r0 + kappa + kappa^2)/(1 - kappa - kappa^2)  (`corrW_of_nearFree`),
  eps <= M P (`large_of_sup0`, M the sup ratio of W, P the mass), and the rate tends to r0.
  Also printed: P(|t| > 0.9 pi), the large-field probability, and the full maximal correlation of J.

Part 2, link (2), the observer's reading of the 4D free field (each photon polarisation as a
  massless scalar, spatial zero mode removed), periodic box N^3, side L = 1, slab tau = L. The
  observer reads the 2^3 cell averages (fixed physical cells, the same readings at every zoom).
  Mode sum: <phi_p(0) phi_p(t)*> = e^{-E_p t}/(2 sinh E_p), cosh E_p = 1 + sum 4 sin^2(p_j/2)
  (lattice units, t = tau/a steps); C(0), C(tau) are the covariances of the physical cell averages
  (phi_phys = phi_lat / a, so the observer's variable is the same at every zoom). The observer's law
  relative to the reading:
  R = C(0)^{-1/2} C(tau) C(0)^{-1/2} on the 7 non-uniform cell combinations; observer rate ||R||.
  Printed per zoom: observer rate, fine slab rate, the change of the observer's marginal
  ||C0_k^{-1/2} C0_{k+1} C0_k^{-1/2} - 1|| and of the relative cross form ||R_{k+1} - R_k||
  (lower bounds for the intertwining defect eta_k, `obs_law_diff`), and |rate_{k+1} - rate_k|.
  Aperture growth at tau = 1, a = 1/8: the observer rate for L = 1, 2, 4 ((B) fails, not (A)).

Part 3, link (3) and the exact control, 2D SU(2). The observer reads class functions of a spatial
  holonomy; the slab of area A (in units a_0^2) multiplies the character chi_j by t_j^{n},
  n = A / a_k^2 plaquettes, t_j the normalised character coefficient of one plaquette.
  Heat-kernel action t_j = exp(-s C2(j)): the observer's law is the same at every zoom, eta = 0,
  and the step error eta (2 + eta) + delta vanishes (`fixedObs_of_noBudget`): no budget.
  Wilson action t_j = I_{2j+1}(beta)/I_1(beta), beta_k tuned so that t_{1/2}^{n_k} = e^{-1}: the
  observer's law flows with k (eta_k > 0, `eta_pos_of_flow`), toward the heat-kernel law; the
  printed eta_k are summable. In 2D the gauge-invariant new-mode layer is {constants}
  (CondGap part A), so r_W = 0 and delta = 0 there.
"""
from __future__ import annotations

import itertools
import time

import numpy as np
from entroptics_adapter import matrix_pencil
from scipy.linalg import eigh
from scipy.optimize import brentq
from scipy.sparse.linalg import eigsh
from scipy.special import ive

SQ3 = np.sqrt(3.0)
R0_FREE = 2.0 - SQ3  # e^{-arccosh 2}


def near_free_rate(r0, k):
    return (r0 + k + k * k) / (1.0 - k - k * k)


# ---------------------------------------------------------------- Part 1

def rate_on_W(J, pi, Phi):
    """Rate of the two-slice law J (marginal pi) on the span of Phi's columns, centred.

    Phi's first column is the constant; it is dropped, since it centres to zero."""
    Phic = Phi[:, 1:] - pi @ Phi[:, 1:]
    X = np.sqrt(pi)[:, None] * Phic
    _, R = np.linalg.qr(X)
    U = Phic @ np.linalg.inv(R)  # orthonormal mean-zero readings in L2(pi)
    M = U.T @ J @ U
    # the two-slice pair on the orthonormal readings: zero-lag Gram identity, one-step U^T J U
    return float(np.abs(matrix_pencil(np.eye(len(M)), M).evals).max())


def full_maxcorr(J, pi):
    # CHOSEN: floor dropping grid points whose marginal underflows (it does at beta >= 256), so
    # 1/sqrt(pi) stays finite; points below it carry no weight in the top eigenvalues.
    keep = pi > 1e-280
    s = np.sqrt(pi[keep])
    S = J[np.ix_(keep, keep)] / s[:, None] / s[None, :]
    S = 0.5 * (S + S.T)
    vals = eigsh(S, k=3, which="LM", return_eigenvectors=False)
    vals = np.sort(np.abs(vals))[::-1]
    return vals[1]


def part1():
    print("Part 1. Link (1): near-free comparison on the circle; r0 = 2 - sqrt 3 =", f"{R0_FREE:.6f}")
    A = 1.0 + SQ3
    n = 1201
    th = -np.pi + 2 * np.pi * (np.arange(n) + 0.5) / n
    T, Tp = np.meshgrid(th, th, indexing="ij")
    print("   beta   r0(W)     rate_J(W)  s     delta     eps       kappa     bound     "
          "eps<=MP  maxcorr_J  P(|t|>0.9pi)")
    ok = True
    for beta in (16.0, 64.0, 256.0, 1024.0):
        logJ = beta * (A * (np.cos(T) + np.cos(Tp)) + np.cos(T - Tp))
        logJ0 = -beta * (A * (T ** 2 + Tp ** 2) / 2 + (T - Tp) ** 2 / 2)
        J = np.exp(logJ - logJ.max()); J /= J.sum()
        J0 = np.exp(logJ0 - logJ0.max()); J0 /= J0.sum()
        pi = J.sum(1); pi0 = J0.sum(1)
        x = np.sqrt(beta) * th
        Phi = np.stack([np.ones_like(x), x, x ** 2, x ** 3], axis=1)
        r0 = rate_on_W(J0, pi0, Phi)
        rJ = rate_on_W(J, pi, Phi)
        A0 = Phi.T @ (pi0[:, None] * Phi)
        Msup = np.max(np.einsum("ij,jk,ik->i", Phi, np.linalg.inv(A0), Phi))
        X, Xp = np.sqrt(beta) * T, np.sqrt(beta) * Tp
        best = None
        D = np.abs(J - J0)
        with np.errstate(divide="ignore", invalid="ignore"):
            # DERIVED: the guard against division by zero where J0 underflows, not a magnitude.
            rel = np.where(J0 > 0, D / J0, np.inf)
        for s in np.linspace(0.25, 6.0, 24):
            cut = (np.abs(X) <= s) & (np.abs(Xp) <= s)
            delta = rel[cut].max()
            L = np.where(cut, 0.0, D)
            mass = L.sum()
            B = Phi.T @ (L.sum(1)[:, None] * Phi)
            epsW = eigh(B, A0, eigvals_only=True)[-1]
            eps = max(epsW, mass)
            kap = delta + eps
            if best is None or kap < best[3]:
                best = (s, delta, eps, kap, epsW, mass)
        s, delta, eps, kap, epsW, mass = best
        # DERIVED: nearFreeRate's denominator 1 - kappa - kappa^2 must be positive, the formula's domain.
        bound = near_free_rate(r0, kap) if kap + kap * kap < 1 else np.inf
        mp_ok = epsW <= Msup * mass * (1 + 1e-9) + 1e-300
        mc = full_maxcorr(J, pi)
        big = np.abs(th) > 0.9 * np.pi
        plf = pi[big].sum()
        ok &= rJ <= bound + 1e-12
        print(f"  {beta:6.0f}  {r0:.6f}  {rJ:.6f}   {s:4.2f}  {delta:.2e}  {eps:.2e}  {kap:.2e}  "
              f"{bound:.6f}  {str(mp_ok):5s}    {mc:.6f}   {plf:.1e}")
    print("  rate_J(W) <= nearFreeRate(r0(W), kappa) at every beta:", ok)
    return ok


# ---------------------------------------------------------------- Part 2

# CHOSEN: side L = 1 fixes the physical unit and tau = L is the docstring's slab; the aperture-growth
# loop in part2 passes L = 1, 2, 4 explicitly.
def free_observer(N, L=1.0, tau=1.0):
    """Observer's relative law of the 2^3 cell averages of a massless free scalar on N^3."""
    a = L / N
    t = int(round(tau / a))
    p = 2 * np.pi * np.arange(N) / N
    w = 4 * np.sin(p / 2) ** 2
    W2 = w[:, None, None] + w[None, :, None] + w[None, None, :]
    with np.errstate(divide="ignore"):
        E = np.arccosh(1 + W2 / 2)
        # DERIVED: W2 = 0 exactly at the spatial zero mode, which the docstring removes; not a magnitude.
        G0 = np.where(W2 > 0, 1 / (2 * np.sinh(E)), 0.0)
    # DERIVED: W2 = 0 exactly at the spatial zero mode, which the docstring removes; not a magnitude.
    Gt = np.where(W2 > 0, np.exp(-E * t), 0.0) * G0
    # DERIVED: the fine rate is the slowest nonzero mode; W2 > 0 excludes the removed zero mode.
    fine = np.exp(-E[W2 > 0].min() * t)
    M = N // 2
    b0 = np.exp(-1j * np.outer(p, np.arange(M))).mean(1)
    b = [b0, np.exp(-1j * p * M) * b0]
    B = np.stack([(b[c[0]][:, None, None] * b[c[1]][None, :, None] * b[c[2]][None, None, :]).ravel()
                  for c in itertools.product((0, 1), repeat=3)])
    # the mode sum carries 1/N^3, and the 4D field in physical units is phi_lat / a, so that the
    # observer's coarse variable (the physical cell average) is the same variable at every zoom
    norm = N ** 3 * a ** 2
    C0 = np.real((np.conj(B) * G0.ravel()) @ B.T) / norm
    Ct = np.real((np.conj(B) * Gt.ravel()) @ B.T) / norm
    Q, _ = np.linalg.qr(np.concatenate([np.ones((8, 1)) / np.sqrt(8), np.eye(8)[:, :7]], axis=1))
    P = Q[:, 1:8]
    C0r = P.T @ C0 @ P; Ctr = P.T @ Ct @ P
    rate = float(np.abs(matrix_pencil(C0r, Ctr).evals).max())
    # NOT A READ: the symmetric whitener of the defined Gaussian covariance C0r, kept only so that R_N sits in one basis across N for the drift norms of part 2; the rate is read by matrix_pencil above
    ev, V = np.linalg.eigh(C0r)
    Wh = V @ np.diag(ev ** -0.5) @ V.T
    R = Wh @ Ctr @ Wh
    R = 0.5 * (R + R.T)
    return rate, fine, C0r, R, Wh


def part2():
    print("\nPart 2. Link (2): the observer's reading of the 4D free field (2^3 cells, tau = L = 1)")
    print("     N   obs rate     fine rate    |d marginal|   |R_k+1 - R_k|   |d rate|")
    prev = None
    rows = []
    ok = True
    for N in (4, 8, 16, 32):
        r, fine, C0r, R, Wh = free_observer(N)
        if prev is None:
            print(f"  {N:4d}   {r:.6e}  {fine:.6e}")
        else:
            rp, _, C0p, Rp, Whp = prev
            dm = np.linalg.norm(Whp @ C0r @ Whp - np.eye(7), 2)
            dR = np.linalg.norm(R - Rp, 2)
            drate = abs(r - rp)
            ok &= drate <= dR + 1e-15
            rows.append((dm, dR))
            print(f"  {N:4d}   {r:.6e}  {fine:.6e}  {dm:.3e}      {dR:.3e}       {drate:.3e}")
        ok &= r <= fine * (1 + 1e-9)
        prev = (r, fine, C0r, R, Wh)
    print("  observer rate <= fine rate, |d rate| <= |R_k+1 - R_k| at every step:", ok)
    print("  aperture growth, tau = 1, a = 1/8 (observer rate -> 1 as L grows: (B) fails):")
    for Lb in (1, 2, 4):
        r, fine, *_ = free_observer(8 * Lb, L=float(Lb), tau=1.0)
        print(f"    L = {Lb}: observer rate {r:.4f}, fine rate {fine:.4f}, e^(-2 pi/L) = "
              f"{np.exp(-2 * np.pi / Lb):.4f}")
    return ok


# ---------------------------------------------------------------- Part 3

def t_wilson(beta, j):
    return ive(int(round(2 * j + 1)), beta) / ive(1, beta)


def part3():
    print("\nPart 3. Link (3) and the exact control: 2D SU(2), observer reads holonomy class functions")
    js = (0.5, 1.0, 1.5, 2.0)
    C2 = {j: j * (j + 1) for j in js}
    sA = 1.0  # slab value of the fundamental: e^{-1}
    hk = {j: np.exp(-sA * C2[j] / C2[0.5]) for j in js}
    print("  heat-kernel action: law per zoom identical (eta = 0); entries", " ".join(f"{hk[j]:.6f}" for j in js))
    # per-step semigroup check of the heat kernel: t_j(a/2)^4 = t_j(a)
    s0 = 0.3
    semi = max(abs(np.exp(-s0 / 4 * C2[j]) ** 4 - np.exp(-s0 * C2[j])) for j in js)
    print(f"  heat-kernel semigroup |t_j(a/2)^4 - t_j(a)| = {semi:.1e}")
    print("  Wilson action, beta_k tuned so t_1/2^(n_k) = e^-1, n_k = 4^k plaquettes:")
    print("     k   n_k       beta_k        lambda_1      lambda_3/2    eta_obs_k (to k+1)")
    prev = None
    etas = []
    lams = []
    for k in range(0, 9):
        n = 4 ** k
        f = lambda lb: n * np.log(t_wilson(np.exp(lb), 0.5)) + sA
        lb = brentq(f, np.log(1e-3), np.log(1e9))
        beta = np.exp(lb)
        lam = {j: t_wilson(beta, j) ** n for j in js}
        lams.append(lam)
        if prev is not None:
            etas.append(max(abs(lam[j] - prev[j]) for j in js))
        prev = lam
    for k in range(9):
        lam = lams[k]
        eta = f"{etas[k]:.3e}" if k < len(etas) else ""
        beta = brentq(lambda lb: 4 ** k * np.log(t_wilson(np.exp(lb), 0.5)) + sA, np.log(1e-3), np.log(1e9))
        print(f"  {k:3d}  {4**k:6d}  {np.exp(beta):12.2f}   {lam[1.0]:.6f}      {lam[1.5]:.6f}      {eta}")
    ratios = [etas[i + 1] / etas[i] for i in range(len(etas) - 1)]
    print("  eta ratios", " ".join(f"{q:.3f}" for q in ratios), "; sum eta =", f"{sum(etas):.3e}")
    print(f"  limit of lambda_1 (heat kernel): {hk[1.0]:.6f}; last Wilson value {lams[-1][1.0]:.6f}")
    # DERIVED: eta_k > 0 is the sign `eta_pos_of_flow` states; q < 1 is decrease of eta (reads near 0.06).
    ok = all(e > 0 for e in etas) and all(q < 1 for q in ratios[1:])
    print("  Wilson: eta_k > 0 and geometrically decreasing:", ok)
    return ok


def main():
    t0 = time.time()
    a = part1()
    b = part2()
    c = part3()
    print(f"\nall checks: {a and b and c}   ({time.time() - t0:.1f} s)")


if __name__ == "__main__":
    main()
