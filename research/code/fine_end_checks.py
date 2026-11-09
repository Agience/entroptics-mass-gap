"""Unit checks for `MassGap.FineEnd`: the fine end one block step at a time.

The step statement (`FineEndStep`): from one zoom K with a positive gap ratio f = gLat / rLat, one
block step (zoom k+1 finer, zoom k coarser) loses at most the fraction eps_k of the reading,
(1 - eps_k) f_k <= f_{k+1}, with 0 <= eps_k < 1 and sum eps_k finite. `noFadeAtFineEnd_of_fineEndStep`
gives NoFadeAtFineEnd from it. The per-step loss read below is eps_k = max(0, 1 - f_{k+1} / f_k), the
least loss that satisfies the step inequality.

1. The floor (`tail_lower`, `noFade_of_stepLoss`): on profiles built to lose exactly eps_k per step,
   f_k >= f_K exp(-2 sum eps) once every loss is <= 1/2.
2. 2D SU(2) Wilson action, exact (non-abelian, no transition; positive control). Observer reading
   sigma_{1/2} = -log(I_2(b)/I_1(b)), gap reading sigma_1 = -log(I_3(b)/I_1(b)), zoom line
   b = 4 / a^2 (g = 1), a_k = 2^-k. The ratio rises to C_1 / C_{1/2} = 8/3 from below, so every
   step loss is 0; its distance to 8/3 falls by about 16 per step (size a^4, inside
   `stepBudget_resolution` at every p <= 4).
3. 4D free massive scalar, mass fixed in physical units (gapped positive control): the lattice gap
   (2/a) asinh(m a / 2) in units of a fixed physical length; step losses of size a^2.
4. 4D free photon (the U(1) Coulomb-phase fine end; control that must fail). On an N^3 spatial torus
   the lowest transfer energy is 2 asinh(sin(pi/N)) in lattice units, so E_min * N -> 2 pi: the gap
   is set by the box, a fixed fraction of the aperture, and is 0 in infinite volume at every zoom.
   A line confining at the coarse end and photon-like at the fine end loses the whole reading in one
   step (eps = 1), outside every budget (`fineEndStep_fails_of_gap_zero`).
5. 4D Z_N deconfined phase (control): the observer's own reading (string tension) is 0 there; the
   ratio in Lean is 0 there (x/0 = 0) and the statement fails (`fineEndStep_fails_of_observer_zero`).
   That the phase exists is cited (Creutz-Jacobs-Rebbi 1979), not computed here.
6. Losses of the size of the coupling (`perturbative_budget_admits_fade`, `oneLoop_budget_admits_fade`):
   fade(k) = 1/(k+1) loses 1/(k+2) per step, within C g^2(a_k) on the one-loop SU(3) line, and the
   total loss diverges like log k; the squared coupling g^4 has a finite sum (`stepBudget_twoLoop`).
   A ratio approaching its limit like R (1 + c g^2(a_k)) loses O(g^4) per step: inside the g^4 budget.
7. A finite jump (the model of a large-N bulk transition; cited, not computed) has total loss 1/2
   (`jump_fineEndStep`); the alternating 2, 1 reading has a floor and total loss growing linearly
   (`osc_noFade`, `osc_not_fineEndStep`).

Not reached: the step statement for the 4D SU(N) Wilson line. No 10-second computation decides it.

Each section runs in under 10 seconds; the script asserts it. No Monte Carlo.
"""
import math
import time

import numpy as np
from scipy.special import ive

# CHOSEN: a run-time budget in seconds, not a result; it decides only whether a section is too slow.
BUDGET = 10.0  # CHOSEN: the per-section wall-clock ceiling from the task brief, in seconds.


def timed(name, fn):
    t0 = time.perf_counter()
    fn()
    dt = time.perf_counter() - t0
    print(f"   [{name}: {dt:.2f} s]")
    assert dt < BUDGET, f"{name} took {dt:.1f} s"


def step_losses(f):
    f = np.asarray(f, dtype=float)
    return np.maximum(0.0, 1.0 - f[1:] / f[:-1])


def section_floor():
    print("1. the floor from a summable budget")
    rng = np.random.default_rng(0)  # CHOSEN: fixed seed; the profile is deterministic given it.
    K = 200  # CHOSEN: number of steps.
    eps = 0.5 * rng.random(K) * 0.7 ** np.arange(K)  # CHOSEN: losses <= 1/2, geometric envelope.
    f = np.empty(K + 1)
    f[0] = 1.0
    for k in range(K):
        f[k + 1] = (1.0 - eps[k]) * f[k]
    bound = f[0] * np.exp(-2.0 * np.concatenate([[0.0], np.cumsum(eps)]))
    assert np.all(bound <= f + 1e-15), "tail_lower bound violated"
    floor = f[0] * math.exp(-2.0 * eps.sum())
    print(f"   total loss {eps.sum():.4f}; min f {f.min():.4f} >= floor {floor:.4f}")
    assert f.min() >= floor


def section_su2_2d():
    print("2. 2D SU(2) Wilson, exact: sigma_1 / sigma_1/2 along b = 4/a^2")
    ks = np.arange(0, 11)  # CHOSEN: a = 1 .. 2^-10.
    a = 2.0 ** -ks
    b = 4.0 / a ** 2  # DERIVED: b = 4/(g^2 a^2) at g = 1 for SU(2).
    s_half = -np.log(ive(2, b) / ive(1, b))
    s_one = -np.log(ive(3, b) / ive(1, b))
    f = s_one / s_half
    eps = step_losses(f)
    dev = np.abs(f - 8.0 / 3.0)  # DERIVED: C_1 / C_1/2 = 2 / (3/4).
    for k in range(len(ks)):
        e = f"{eps[k]:.3e}" if k < len(eps) else "-"
        print(f"   a = 2^-{ks[k]:2d}  ratio {f[k]:.8f}  |ratio - 8/3| {dev[k]:.3e}  loss {e}")
    # DERIVED: selects the strictly positive losses; a sign test, not a magnitude.
    nz = eps[eps > 0]
    print(f"   total loss {eps.sum():.4e}")
    # CHOSEN: closeness to 8/3 at a = 2^-10 (read 1.6e-13); any cut from 1e-12 to 1e-5 passes the same.
    assert dev[-1] < 1e-5
    # The ratio rises toward 8/3 from below, so the least step loss is 0 here: inside every budget.
    # CHOSEN: a small total-loss ceiling; the read is exactly 0, so any positive value reads the same.
    assert eps.sum() < 1e-3
    # CHOSEN: steps 3..6, past the coarse end and before double rounding of -log(1 - x) sets in.
    shrink = dev[3:7] / dev[4:8]
    print(f"   |ratio - 8/3| shrinks per step by {shrink} (a^4: 16)")
    # DERIVED: 16 = 2^4, the shrink of an a^4 deviation under one halving of a. CHOSEN: the 0.2 band
    # (reads 16.003 to 16.118); an a^2 deviation (4) or a^6 one (64) lies far outside it.
    assert np.all(np.abs(shrink - 16.0) < 0.2)
    _ = nz


def section_massive_4d():
    print("3. 4D free massive scalar: lattice gap at fixed physical mass, observer length L = 1")
    m = 1.0  # CHOSEN: the physical mass, in units of the observer's length.
    ks = np.arange(0, 16)
    a = 2.0 ** -ks
    E = 2.0 / a * np.arcsinh(m * a / 2.0)  # DERIVED: transfer-matrix energy at p = 0, mass m.
    eps = np.abs(np.diff(E)) / E[:-1]
    print(f"   gap ratios {E[:4]} ... {E[-1]:.10f}")
    print(f"   per-step change {eps[:4]}; shrink {eps[-4:-1] / eps[-3:]}")
    # DERIVED: 4 = 2^2, the shrink of a change of size a^2 under one halving of a. CHOSEN: the 0.05 band
    # (reads 4.0000000); an a or a^4 change (2 or 16) lies far outside it.
    assert np.all(np.abs(eps[3:-1] / eps[4:] - 4.0) < 0.05), "per-step change must be of size a^2"
    D = np.max(eps / a[:-1] ** 2)
    print(f"   eps_k <= D a_k^2 with D = {D:.4f}; total change {eps.sum():.4e}")


def section_photon():
    print("4. 4D free photon: lowest transfer energy on an N^3 torus")
    for N in (8, 16, 32, 64, 128, 256, 512):  # CHOSEN: box sides in lattice units.
        E = 2.0 * np.arcsinh(np.sin(np.pi / N))  # DERIVED: lattice dispersion at |p| = 2 pi / N.
        print(f"   N = {N:4d}: E_min = {E:.6f}, E_min * N = {E * N:.6f}")
    # DERIVED: 2 pi is the limit of E_min * N; the remainder at N = 4096 is (2/3) pi^3 / N^2, about 1.2e-6.
    # CHOSEN: the 1e-5 band sits above that remainder.
    assert abs(2.0 * np.arcsinh(np.sin(np.pi / 4096)) * 4096 - 2 * np.pi) < 1e-5
    # At a fixed zoom the infinite-volume gap is the limit N -> infinity of E_min: zero.
    hi = 1.0  # CHOSEN: the coarse-end (confining) ratio of the model line.
    f = np.array([hi] * 5 + [0.0] * 5)
    # DERIVED: the guard against division by a zero reading (Lean's x / 0 = 0), not a magnitude.
    eps = np.maximum(0.0, 1.0 - np.divide(f[1:], f[:-1], out=np.zeros(9), where=f[:-1] > 0))
    print(f"   confining -> photon line: step losses {eps}")
    # DERIVED: a step from a positive reading to 0 loses exactly the whole reading, eps = 1.
    assert eps.max() == 1.0, "the transition step loses the whole reading"


def section_zn():
    print("5. 4D Z_N deconfined phase: observer reading 0 at fine zooms (cited)")
    g = np.ones(10)
    r = np.array([1.0] * 5 + [0.0] * 5)  # model: string tension vanishes from zoom 5 on.
    # DERIVED: the guard that implements Lean's x / 0 = 0, not a magnitude.
    ratio = np.divide(g, r, out=np.zeros_like(g), where=r > 0)  # Lean's x / 0 = 0.
    print(f"   ratio under x/0 = 0: {ratio}")
    # DERIVED: Lean's x / 0 = 0 makes the ratio exactly 0 where the observer reading is 0.
    assert np.all(ratio[5:] == 0.0)


def section_perturbative():
    print("6. losses of the size of g^2 do not suffice; g^4 does")
    b0 = 11 * 3 / (48 * math.pi ** 2)  # DERIVED: one-loop b0 = 11 N/(48 pi^2) at N = 3.
    us = 1.0  # CHOSEN: 1/g^2 at the observer's length L (coupling O(1) there).
    a0, L, s = 1.0, 1.0, 2.0  # CHOSEN: first spacing at the fixed length; block factor 2.
    ks = np.arange(0, 200000)
    inv = us - 2 * b0 * math.log(a0 / L) + 2 * b0 * math.log(s) * ks  # `invCoup_geometric`.
    g2 = 1.0 / inv
    loss = 1.0 / (ks + 2.0)
    C = (us - 2 * b0 * math.log(a0 / L)) + 2 * b0 * math.log(s)
    assert np.all(loss <= C * g2 + 1e-15), "fade's loss must be within C g^2"
    cs = np.cumsum(loss)
    g4 = np.cumsum(g2 ** 2)
    for n in (10, 1000, 100000, 199999):
        print(f"   n = {n:6d}: sum fade loss {cs[n]:.4f} (~ log n {math.log(n):.4f}),"
              f" sum g^4 {g4[n]:.6f}")
    # DERIVED: the fade's loss sum from 100000 to 199999 is about log 2 = 0.693 (a log-divergent sum).
    # CHOSEN: the cut 0.5 sits below log 2; a convergent loss sum would add almost nothing there.
    assert cs[199999] - cs[100000] > 0.5, "fade's total loss keeps growing"
    assert g4[199999] - g4[100000] < 1e-3 * g4[199999], "g^4 sum settles"
    R, c = 3.0, 0.7  # CHOSEN: a limit ratio and a coefficient of its g^2 deviation.
    f = R * (1.0 + c * g2)
    eps = step_losses(f)
    ratio = eps[1:2000] / g2[1:2000] ** 2
    print(f"   R (1 + c g^2): loss / g^4 in [{ratio.min():.4f}, {ratio.max():.4f}]"
          f" (expected c * 2 b0 log s = {c * 2 * b0 * math.log(s):.4f})")
    assert ratio.max() < 2 * c * 2 * b0 * math.log(s) + 1e-9


def section_jump_osc():
    print("7. a finite jump has a finite total loss; an alternating reading has none")
    f = np.array([2.0] * 6 + [1.0] * 6)
    eps = step_losses(f)
    print(f"   jump: total loss {eps.sum()}")
    # DERIVED: the jump 2 -> 1 loses exactly 1 - 1/2 = 1/2 (`jump_fineEndStep`), and the step statement
    # asks eps_k < 1.
    assert eps.sum() == 0.5 and eps.max() < 1
    # DERIVED: the parity test that alternates the reading 2, 1; not a magnitude.
    osc = np.array([2.0 if k % 2 == 0 else 1.0 for k in range(2000)])
    eo = step_losses(osc)
    print(f"   osc: floor {osc.min()}, total loss over 2000 zooms {eo.sum()}")
    # DERIVED: the floor of the 2, 1 reading is 1, and each of its 1000 falls 2 -> 1 loses exactly 1/2.
    assert osc.min() == 1.0 and eo.sum() == 0.5 * 1000


if __name__ == "__main__":
    timed("floor", section_floor)
    timed("su2_2d", section_su2_2d)
    timed("massive_4d", section_massive_4d)
    timed("photon", section_photon)
    timed("zn", section_zn)
    timed("perturbative", section_perturbative)
    timed("jump_osc", section_jump_osc)
    print("all checks passed")
