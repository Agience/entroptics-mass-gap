import Mathlib
import MassGap.WindowRead
import MassGap.CentreSectorSeedN

/-!
# MassGap.FractalTail — the dyadic shells of the action susceptibility, read through the doubling bootstrap

`PlaqSummable` leaves the tail `∑_{R < |z| ≤ L_k} |C_k(z)| ≤ κ' F_k` of the plaquette correlator along the tower,
uniformly in the number of dyadic scales between `R` and `L_k`. This module tests whether the doubling bootstrap
(`DoublingSharp.rec_sharp`), applied scale by scale, controls that tail in place of a renormalization group.
Declarations are in the namespace `MassGap.FractalTail`. Throughout, `D(β, w) = windowCoupling N β w`, `n = 2^w`,
`Var_L` the variance of the Wilson action on the cubic torus of side `L`, and `χ_L = Var_L / L⁴` its value per site
(`chi`), the zero-momentum action susceptibility of the torus.

## 1. The shell identity (proved)

* `curv_eq_shell`: `∂²_β D(w) = 16 Var_n − Var_{2n} = 16^{w+1} (χ_n − χ_{2n})` (`curv`; the second derivative is
  `WindowRead.deriv_windowCoupling`, `WindowRead.hasDerivAt_cutEnergy`). The doubling defect of the action variance is the change of the
  susceptibility per site between the two tori, times the volume of the larger one.
* `chi_double_sub`: `χ_{2n} − χ_n = (crossCut + blockShift)/(16 n⁴)` (`WindowRead.var_double_sub`): the covariances
  between distinct dyadic blocks of the `2n`-torus, plus the change of each block's variance between its own torus
  and its place in the larger one.

Argued, not formalized: with translation invariance `χ_L = ∑_{z ∈ T_L} C_L(z)` (orientations summed), and
`χ_{2n} − χ_n = ∑_{z ∈ T_{2n} ∖ B_n} C_{2n}(z) + ∑_{z ∈ B_n} (C_{2n}(z) − C_n(z))`, `B_n` the fundamental box of
`T_n` inside `T_{2n}`. The sum off `B_n` is the dyadic shell (some coordinate of `z` between `n/2` and `n`); the sum
on `B_n` is the finite-size term, where `C_n` already carries the images of every pair under the wrap of the smaller torus.
The identity reads the signed sum, at zero momentum, of the action density, in absolute units, on tori.

## 2. The telescope (proved)

* `shell_step`, `chi_telescope`: `χ_{2^{w+m}} = χ_{2^w} − ∑_{j<m} ∂²_β D(w+j) / 16^{w+j+1}`. Exact: the shell and the
  finite-size terms need no separation, the telescope reads the susceptibility of the largest torus.
* `chi_le_of_curv`: shell bounds `−∂²_β D(w+j) ≤ 16^{w+j+1} b_j` give `χ_{2^{w+m}} ≤ χ_{2^w} + ∑_{j<m} b_j`.
* `chi_le_of_curvFloor`: a window-uniform bound `|∂²_β D(w+j)| ≤ c` gives `χ_{2^{w+m}} ≤ χ_{2^w} + c/(15·16^w)`,
  uniformly in `m`. The volume factor `16^{w+j+1}` of §1 makes a bounded curvature a geometric series.

## 3. A second derivative from smallness on an interval (proved)

`second_deriv_le`: if `|f| ≤ ε` on `[x − s, x + s]` and `|f'''| ≤ M` everywhere, then `|f''(x)| ≤ 4ε/s² + 2Ms`
(the second difference `f(x+s) + f(x−s) − 2f(x)` against `s² f''(x)`, three mean value steps). This is the route that
works for step 2 of the test; analyticity and convexity do not (§6).

## 4. The third coupling derivative of `log Z` (proved)

* `hasDerivAt_varAction`: `∂_β Var_L = k3 = −(⟨S³⟩ − ⟨S²⟩⟨S⟩) + 2⟨S⟩ Var_L`, the negative third cumulant
  (`WilsonAnalytic.wilsonSystem_expect_hasDerivAt` at `O = S²`, and `WindowRead.hasDerivAt_meanAction`).
* `abs_k3_le`: `|k3| ≤ 6 M³` with `M = 2 |plaquettes|`, the sup of the action. Crude, polynomial in the side.
* `card_RPlaq`, `M3_eq`: `|∂³_β D(w)| ≤ M3 w = C₀ (16^w)³`, `C₀ = 96·32³ + 6·512³`.
* `curv_le_of_window`: `|D(·, w)| ≤ ε` on `[β − s, β + s]` gives `|∂²_β D(w)| ≤ 4ε/s² + 2 M3 w · s` at `β`.

## 5. The basin: shells beyond a seed window (proved)

* `seed_interval`: a strict seed `D(β, w₀) < 1/1000` at `β > 0` holds on some `[β − t, β + t] ⊆ [0, ∞)`
  (`CouplingTower.continuous_windowCoupling`).
* `window_sharp`: a seed at `y ≥ 0`, `w₀ ≥ 1`, gives `250 D(y, w₀ + k) ≤ (1/4)^{2^k}`
  (`CentreSectorSeedN.defectW_sharp`, from `DoublingSharp.iterate_sharp`).
* `curv_basin`: `|∂²_β D(w₀ + k)| ≤ 4 ε_k / s² + 2 M3 (w₀+k) s` for every `0 < s ≤ t`, `ε_k = (1/4)^{2^k}/250`.
* `summable_dexp`: `∑_k 256^k (1/2)^{2^k} < ∞` (ratio test): the doubly exponential decay beats the polynomial.
* `chi_bounded_of_seed`: at a strict seed, the torus susceptibility `χ_{2^{w₀+m}}(β)` is bounded uniformly in `m`.
  Choice `s_k = t (1/2)^{2^k}` (CHOSEN): the `1/s²` term becomes `4/(250 t²)`, killed by the volume `16^{w₀+k+1}`;
  the `s` term becomes `256^k (1/2)^{2^k}`, summable.

## 6. The paper test

Step 2, the three candidates.
* (a) Analyticity: the recursion is a positivity argument (`PowerFacts`: real non-negative spectrum of the
  transfer matrix); off the real axis the trace defect is not positive and `|p| small` no longer bounds the moduli
  of the excited weights. `|Z(β + iy)| ≤ Z(β)` bounds `Re log Z_n` from above, the wrong side for `−log Z_{2n}` in
  `D`. The complex extension of `D` is its cumulant expansion `∑_k (−iy)^k (16 κ_k(n) − κ_k(2n))/k!`, whose radius is
  of order `Var_{2n}^{−1/2} ~ n^{−2}` unless the cumulant defects are already controlled: circular. It also needs a
  zero-free disc for `Z_{2n}` uniform in the side, the analyticity of the free energy, which the tree does not give.
* (b) Convexity: `∂²D = 16 Var_n − Var_{2n}` has no sign; convexity of `log Z` reads only the per-site part
  (`MasslessExclude` §2).
* (c) A squaring bound for the variance defect: none in the tree; `rec_sharp` is an inequality between values at
  one coupling and does not differentiate.
* (d) What works: `second_deriv_le` with the crude third cumulant (§3–§5). It uses smallness on a coupling interval,
  available because a strict seed is open in `β`.

Step 3, against `PlaqSummable`'s tail. `chi_bounded_of_seed` is a fixed-`β` statement and does not discharge the tail:
1. Units. The bound is absolute. Its constant is `χ_{2^{w₀}} + ∑_k b_k` with `b_k` carrying `1/t²` and `16^{2w₀}`;
   the tail needs `κ' F_k` with `F_k ~ 1/β_k²` (the per-link floor, `PlaqShortDistance` §5), one `κ'` along the tower.
2. Scales. The bootstrap reads shells from the seed window `2^{w₀(β)}` up. The seed window is where `D` falls below
   `1/1000`, beyond the correlation length, which grows with `β`; the tail's shells from `R` to `L_k` (the screen box,
   of the order of the physical length `ρ` in lattice units `ρ/a_k`) lie mostly below it. Their whole contribution
   sits in `χ_{2^{w₀}}`, which this module does not bound. The bootstrap controls the region where decay has already
   set in, which is not the tail.
3. Signs. The telescope reads the signed sum `∑_z C(z)`; `PlaqSummable.opNorm_of_shortTail` reads `∑ |C(z)|`. The
   zero-momentum form of `PlaqShortDistance` is the signed one; the Schur bound is not.
4. Geometry. The telescope is on tori `T_{2^j}`; the tail is the infinite-volume periodic state on a box. The
   finite-size terms are inside `χ`, not separated.
5. Reading. The identity is for the action density; the tail is for the symmetrized class reading of the screen.

`U(1)` (argued). In the Coulomb phase `D(β, w) → D_∞ > 0` (`MasslessExclude.line_strictMono`, the rotor shape), so
no seed `D ≤ 1/1000` is reached at large `β` and `ε_k` does not decay. Then `second_deriv_le` gives nothing
summable: with `ε` fixed, `s` fixed leaves `2 M3 s / 16^{j+1} ~ 16^{2j}`, and `s ~ 16^{−j}` leaves
`ε 16^{2j}/16^{j+1}`. The route fails at step 2, exactly at the missing decay of `ε_k`. The target does not fail:
the free photon has `C(z) ~ |z|^{−8}`, summable in four dimensions, so the tail holds at `U(1)` with no gap. The
route uses the gap to prove a statement true without one.

Free field (argued). `log Z_L = −(dof_L/2) log β + const`, so `β² ∂²_β D(w) = (16 dof_n − dof_{2n})/2`, half the
zero-mode count difference, a constant in `w`. `chi_le_of_curvFloor` with `c ~ 1/β²` then gives `χ` bounded by a
fixed multiple of `1/β²`, the order of `C(0)`: relative and uniform. The free field satisfies the window-uniform
curvature bound, not a doubly exponential one.

## What does not follow

* `PlaqSummable`'s tail is not proved along any tower, nor `SplitRatio`.
* The exact missing inequality, after §2: eventually along the tower, with one `K`,
  `|16 Var_{2^j}(S) − Var_{2^{j+1}}(S)| ≤ K F_k` at `β_k` for every window `2^j ≤ L_k` (the action-variance doubling
  defect bounded in units of the local floor, window by window). `chi_le_of_curvFloor` turns it into
  `χ_{L_k} ≤ χ_{2^{w}} + K F_k/(15·16^w)`. Each instance compares two tori at one scale; the content is the
  uniformity over the `~k` windows at the same coupling, so it is a multiscale statement in one-scale form, the
  curvature counterpart of `DefectBound`'s bounded defect. The bootstrap gives it only for windows beyond the seed
  window and only in absolute units.
* Even with that inequality: the signed torus susceptibility is not the absolute box row sum (§6, items 3–5), and
  the base `χ_{2^w}` against `F_k`, `C_k(0) ≤ c/β_k²` and the per-link floor are not in the tree.
* (a)–(c) of §6 are argued; only (d) is formalized.

DERIVED (module-wide): `16 = 2⁴` the blocks and the volume ratio; `2` the doubling, the halves, the squares and the
second difference; `4` the dimension and the four values in the second difference; `15 = 16 − 1` the geometric sum;
`6 = 1 + 1 + 4` the third-cumulant bound; `32 = 2·16` and `512 = 2·16·16` the action sup per side; `256 = 16²`;
`3` the cube of the third cumulant; `8`, `96` and `1/16` as labelled at their theorems. Inherited: `1/1000`, `250`, `1/4` from `DoublingSharp` through
`CentreSectorSeedN.defectW_sharp`. CHOSEN: `s_k = t (1/2)^{2^k}` in `chi_bounded_of_seed` (any choice with the two
terms summable gives a bound), and `δ/2` in `seed_interval`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FractalTail

open Filter Topology Set
open MassGap MassGap.CompactGauge MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
  MassGap.WilsonReal

variable {N : ℕ}

/-! ## 1. The shell identity -/

/-- **The action susceptibility per site** on the cubic torus of side `n`: `Var_n(S)/n⁴`. DERIVED: `4` the
dimension. -/
def chi (N n : ℕ) (β : ℝ) : ℝ := WindowRead.varAction N (fun _ => n) β / (n : ℝ) ^ 4

/-- **The curvature of the window read**: `16 Var_n − Var_{2n}`, `n = 2^w`, which is `∂²_β D(w)`.
DERIVED: `16 = 2⁴`, `2` the doubling. -/
def curv (N w : ℕ) (β : ℝ) : ℝ :=
  16 * WindowRead.varAction N (fun _ => 2 ^ w) β - WindowRead.varAction N (fun _ => 2 * 2 ^ w) β

/-- **The curvature is the coupling derivative of the cut energy**, so the second derivative of `D`.
DERIVED: no numeral. -/
theorem hasDerivAt_cutEnergy_curv (hN : N ≠ 0) (w : ℕ) (β : ℝ) :
    HasDerivAt (fun x => WindowRead.cutEnergy N x w) (curv N w β) β :=
  WindowRead.hasDerivAt_cutEnergy hN w β

/-- `16^w = (2^w)⁴`. DERIVED: `16 = 2⁴`. -/
theorem sixteen_pow (w : ℕ) : (16 : ℝ) ^ w = ((2 : ℝ) ^ w) ^ 4 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- **The shell identity**: `∂²_β D(w) = 16^{w+1} (χ_n − χ_{2n})`. DERIVED: `16 = 2⁴`, `2` the doubling. -/
theorem curv_eq_shell (N w : ℕ) (β : ℝ) :
    curv N w β = 16 ^ (w + 1) * (chi N (2 ^ w) β - chi N (2 * 2 ^ w) β) := by
  unfold curv chi
  push_cast
  have h2 : (2 : ℝ) ^ w ≠ 0 := by positivity
  rw [pow_succ, sixteen_pow]
  field_simp
  ring

/-- **The doubling of the susceptibility is the cross-cut plus the block shift**, per site of the larger torus.
DERIVED: `16 = 2⁴`, `2` the doubling. -/
theorem chi_double_sub (hN : N ≠ 0) (β : ℝ) {n : ℕ} (hn : n ≠ 0) :
    chi N (2 * n) β - chi N n β
      = (WindowRead.crossCut N β n + WindowRead.blockShift N β n) / (16 * (n : ℝ) ^ 4) := by
  rw [← WindowRead.var_double_sub hN β n]
  unfold chi
  push_cast
  have h : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

/-! ## 2. The telescope -/

/-- **One shell**: `χ_{2n} = χ_n − ∂²_β D(w)/16^{w+1}`. DERIVED: `16`, `2` as in `curv_eq_shell`. -/
theorem shell_step (N v : ℕ) (β : ℝ) :
    chi N (2 * 2 ^ v) β = chi N (2 ^ v) β - curv N v β / 16 ^ (v + 1) := by
  rw [curv_eq_shell]
  have h : (16 : ℝ) ^ (v + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **The telescope**: `χ_{2^{w+m}} = χ_{2^w} − ∑_{j<m} ∂²_β D(w+j)/16^{w+j+1}`. DERIVED: `16`, `2` as above. -/
theorem chi_telescope (N w m : ℕ) (β : ℝ) :
    chi N (2 ^ (w + m)) β
      = chi N (2 ^ w) β - ∑ j ∈ Finset.range m, curv N (w + j) β / 16 ^ (w + j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show w + (m + 1) = (w + m) + 1 by ring, pow_succ', shell_step, ih, Finset.sum_range_succ]
    ring

/-- **Shell bounds give a susceptibility bound**: `−∂²_β D(w+j) ≤ 16^{w+j+1} b_j` for `j < m` gives
`χ_{2^{w+m}} ≤ χ_{2^w} + ∑_{j<m} b_j`. DERIVED: `16`, `2` as above. -/
theorem chi_le_of_curv {w m : ℕ} {β : ℝ} (b : ℕ → ℝ)
    (hb : ∀ j < m, -curv N (w + j) β ≤ 16 ^ (w + j + 1) * b j) :
    chi N (2 ^ (w + m)) β ≤ chi N (2 ^ w) β + ∑ j ∈ Finset.range m, b j := by
  rw [chi_telescope]
  have hs : ∑ j ∈ Finset.range m, (-(curv N (w + j) β / 16 ^ (w + j + 1))) ≤ ∑ j ∈ Finset.range m, b j :=
    Finset.sum_le_sum fun j hj => by
      have hp : (0 : ℝ) < 16 ^ (w + j + 1) := by positivity
      rw [← neg_div, div_le_iff₀ hp, mul_comm]
      exact hb j (Finset.mem_range.mp hj)
  rw [Finset.sum_neg_distrib] at hs
  linarith

/-- **A window-uniform curvature bound is a geometric series**: `|∂²_β D(w+j)| ≤ c` for `j < m` gives
`χ_{2^{w+m}} ≤ χ_{2^w} + c/(15·16^w)`, uniformly in `m`. DERIVED: `16 = 2⁴`, `15 = 16 − 1`. -/
theorem chi_le_of_curvFloor {w m : ℕ} {β c : ℝ} (hc : 0 ≤ c) (h : ∀ j < m, |curv N (w + j) β| ≤ c) :
    chi N (2 ^ (w + m)) β ≤ chi N (2 ^ w) β + c / (15 * 16 ^ w) := by
  let b : ℕ → ℝ := fun j => c / 16 ^ (w + 1) * (1 / 16) ^ j
  have key := chi_le_of_curv (N := N) (w := w) (m := m) (β := β) b (fun j hj => by
    have e : (16 : ℝ) ^ (w + j + 1) * b j = c := by
      show (16 : ℝ) ^ (w + j + 1) * (c / 16 ^ (w + 1) * (1 / 16) ^ j) = c
      rw [show w + j + 1 = (w + 1) + j by ring, pow_add, one_div_pow]
      have : (16 : ℝ) ^ j ≠ 0 := by positivity
      have : (16 : ℝ) ^ (w + 1) ≠ 0 := by positivity
      field_simp
    rw [e]
    exact (neg_le_abs _).trans (h j hj))
  have hgeom : ∑ j ∈ Finset.range m, (1 / 16 : ℝ) ^ j ≤ (1 - 1 / 16)⁻¹ := by
    rw [← tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    exact (summable_geometric_of_lt_one (r := 1 / 16) (by norm_num) (by norm_num)).sum_le_tsum _
      (fun j _ => by positivity)
  have hsum : ∑ j ∈ Finset.range m, b j ≤ c / (15 * 16 ^ w) := by
    show ∑ j ∈ Finset.range m, c / 16 ^ (w + 1) * (1 / 16 : ℝ) ^ j ≤ c / (15 * 16 ^ w)
    rw [← Finset.mul_sum]
    have hc' : 0 ≤ c / 16 ^ (w + 1) := by positivity
    have e15 : (1 - 1 / 16 : ℝ)⁻¹ = 16 / 15 := by norm_num
    calc c / 16 ^ (w + 1) * ∑ j ∈ Finset.range m, (1 / 16 : ℝ) ^ j
        ≤ c / 16 ^ (w + 1) * (1 - 1 / 16)⁻¹ := mul_le_mul_of_nonneg_left hgeom hc'
      _ = c / (15 * 16 ^ w) := by
        have : (16 : ℝ) ^ w ≠ 0 := by positivity
        rw [e15, pow_succ]
        field_simp
  linarith

/-! ## 3. A second derivative from smallness on an interval -/

/-- **The second derivative from the function and the third derivative**: if `|f| ≤ ε` on `[x − s, x + s]`,
`s > 0`, and `|f'''| ≤ M` everywhere, then `|f''(x)| ≤ 4ε/s² + 2Ms`. DERIVED: `2` the second difference and the
three mean value steps, `4` the four values `f(x ± s)`, `2 f(x)`, `3` the cube `s³`. -/
theorem second_deriv_le {f f1 f2 f3 : ℝ → ℝ} {x s ε M : ℝ} (hs : 0 < s)
    (h1 : ∀ y, HasDerivAt f (f1 y) y) (h2 : ∀ y, HasDerivAt f1 (f2 y) y)
    (h3 : ∀ y, HasDerivAt f2 (f3 y) y) (hM : ∀ y, |f3 y| ≤ M)
    (hf : ∀ y ∈ Icc (x - s) (x + s), |f y| ≤ ε) :
    |f2 x| ≤ 4 * ε / s ^ 2 + 2 * M * s := by
  have lip : ∀ a b, |f2 b - f2 a| ≤ M * |b - a| := fun a b => by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f2) (f' := f3) (s := univ)
      (fun y _ => (h3 y).hasDerivWithinAt) (fun y _ => by rw [Real.norm_eq_abs]; exact hM y) convex_univ
      (mem_univ a) (mem_univ b)
    simpa only [Real.norm_eq_abs] using this
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  let g : ℝ → ℝ := fun u => f (x + u) + f (x - u) - 2 * f x - u ^ 2 * f2 x
  let g1 : ℝ → ℝ := fun u => f1 (x + u) - f1 (x - u) - 2 * u * f2 x
  let g2 : ℝ → ℝ := fun u => f2 (x + u) + f2 (x - u) - 2 * f2 x
  have dg : ∀ u, HasDerivAt g (g1 u) u := fun u => by
    have ha := HasDerivAt.comp_const_add x u (h1 (x + u))
    have hb := HasDerivAt.comp_const_sub x u (h1 (x - u))
    have hq : HasDerivAt (fun u : ℝ => u ^ 2 * f2 x) (2 * u * f2 x) u := by
      simpa using (hasDerivAt_pow 2 u).mul_const (f2 x)
    have := ((ha.add hb).sub_const (2 * f x)).sub hq
    refine this.congr_deriv ?_
    show f1 (x + u) + -f1 (x - u) - 2 * u * f2 x = f1 (x + u) - f1 (x - u) - 2 * u * f2 x
    ring
  have dg1 : ∀ u, HasDerivAt g1 (g2 u) u := fun u => by
    have ha := HasDerivAt.comp_const_add x u (h2 (x + u))
    have hb := HasDerivAt.comp_const_sub x u (h2 (x - u))
    have hq : HasDerivAt (fun u : ℝ => 2 * u * f2 x) (2 * 1 * f2 x) u :=
      ((hasDerivAt_id' u).const_mul 2).mul_const (f2 x)
    have := (ha.sub hb).sub hq
    refine this.congr_deriv ?_
    show f2 (x + u) - -f2 (x - u) - 2 * 1 * f2 x = f2 (x + u) + f2 (x - u) - 2 * f2 x
    ring
  have hg2 : ∀ u ∈ Icc 0 s, ‖g2 u‖ ≤ 2 * M * s := fun u hu => by
    rw [Real.norm_eq_abs]
    have ea := lip x (x + u)
    have eb := lip x (x - u)
    rw [show x + u - x = u by ring, abs_of_nonneg hu.1] at ea
    rw [show x - u - x = -u by ring, abs_neg, abs_of_nonneg hu.1] at eb
    have hMu : M * u ≤ M * s := mul_le_mul_of_nonneg_left hu.2 hM0
    have e : g2 u = (f2 (x + u) - f2 x) + (f2 (x - u) - f2 x) := by
      show f2 (x + u) + f2 (x - u) - 2 * f2 x = (f2 (x + u) - f2 x) + (f2 (x - u) - f2 x)
      ring
    rw [e]
    calc |(f2 (x + u) - f2 x) + (f2 (x - u) - f2 x)| ≤ |f2 (x + u) - f2 x| + |f2 (x - u) - f2 x| :=
          abs_add_le _ _
      _ ≤ 2 * M * s := by linarith
  have h0s : (0 : ℝ) ∈ Icc 0 s := ⟨le_refl _, hs.le⟩
  have hg1 : ∀ u ∈ Icc 0 s, ‖g1 u‖ ≤ 2 * M * s * s := fun u hu => by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g1) (f' := g2) (s := Icc 0 s)
      (fun y _ => (dg1 y).hasDerivWithinAt) hg2 (convex_Icc 0 s) h0s hu
    have e0 : g1 0 = 0 := by
      show f1 (x + 0) - f1 (x - 0) - 2 * 0 * f2 x = 0
      rw [add_zero, sub_zero]
      ring
    rw [e0, sub_zero, sub_zero, Real.norm_eq_abs u, abs_of_nonneg hu.1] at this
    have : 2 * M * s * u ≤ 2 * M * s * s := mul_le_mul_of_nonneg_left hu.2 (by positivity)
    linarith
  have hgs := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := g1) (s := Icc 0 s)
    (fun y _ => (dg y).hasDerivWithinAt) hg1 (convex_Icc 0 s) h0s ⟨hs.le, le_refl _⟩
  have e0 : g 0 = 0 := by
    show f (x + 0) + f (x - 0) - 2 * f x - 0 ^ 2 * f2 x = 0
    rw [add_zero, sub_zero]
    ring
  rw [e0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs] at hgs
  have fa := abs_le.mp (hf (x + s) ⟨by linarith, le_refl _⟩)
  have fb := abs_le.mp (hf (x - s) ⟨le_refl _, by linarith⟩)
  have fc := abs_le.mp (hf x ⟨by linarith, by linarith⟩)
  have gs := abs_le.mp hgs
  have hgv : g s = f (x + s) + f (x - s) - 2 * f x - s ^ 2 * f2 x := rfl
  rw [hgv] at gs
  have hs2 : 0 < s ^ 2 := by positivity
  have key : |f2 x| * s ^ 2 ≤ 4 * ε + 2 * M * s ^ 3 := by
    have hcs : |f2 x * s ^ 2| ≤ 4 * ε + 2 * M * s ^ 3 := by
      rw [abs_le]
      constructor <;> linarith [fa.1, fa.2, fb.1, fb.2, fc.1, fc.2, gs.1, gs.2]
    rwa [abs_mul, abs_of_pos hs2] at hcs
  have e : 4 * ε / s ^ 2 + 2 * M * s = (4 * ε + 2 * M * s ^ 3) / s ^ 2 := by
    field_simp
  rw [e, le_div_iff₀ hs2]
  exact key

/-! ## 4. The third coupling derivative of `log Z` -/

/-- **The negative third cumulant of the action**: `−(⟨S³⟩ − ⟨S²⟩⟨S⟩) + 2⟨S⟩ Var(S)`. DERIVED: `2` the product
rule on `⟨S⟩²`. -/
def k3 (N : ℕ) (L : Fin 4 → ℕ) (β : ℝ) : ℝ :=
  -((RectWilson.sysR L N).expect (probHaar (SUN.SU N)) β
        (fun U => (RectWilson.sysR L N).action U * (RectWilson.sysR L N).action U
          * (RectWilson.sysR L N).action U)
      - (RectWilson.sysR L N).expect (probHaar (SUN.SU N)) β
          (fun U => (RectWilson.sysR L N).action U * (RectWilson.sysR L N).action U)
        * EffectiveCoupling.meanAction N L β)
    + 2 * EffectiveCoupling.meanAction N L β * WindowRead.varAction N L β

/-- **`∂_β Var_L(S) = k3`.** DERIVED: `2` the product rule. -/
theorem hasDerivAt_varAction (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) :
    HasDerivAt (fun x => WindowRead.varAction N L x) (k3 N L β) β := by
  have hS : Measurable (RectWilson.sysR L N).action :=
    measurable_wilsonSystem_action (N := N) (RectWilson.rbd L)
  have hb := WindowRead.action_abs_le hN L
  have hM0 : (0 : ℝ) ≤ 2 * (Fintype.card (RectWilson.RPlaq L) : ℝ) := by positivity
  have hSS : ∀ U, |(RectWilson.sysR L N).action U * (RectWilson.sysR L N).action U|
      ≤ 2 * (Fintype.card (RectWilson.RPlaq L) : ℝ) * (2 * (Fintype.card (RectWilson.RPlaq L) : ℝ)) :=
    fun U => by
      rw [abs_mul]
      exact mul_le_mul (hb U) (hb U) (abs_nonneg _) hM0
  have d2 := WilsonAnalytic.wilsonSystem_expect_hasDerivAt hN (RectWilson.rbd L) β
    (fun U => (RectWilson.sysR L N).action U * (RectWilson.sysR L N).action U) (hS.mul hS) _ hSS
  have d1 := WindowRead.hasDerivAt_meanAction hN L β
  have h := d2.sub (d1.mul d1)
  have h' : HasDerivAt (fun x => WindowRead.varAction N L x)
      (-((RectWilson.sysR L N).expect (probHaar (SUN.SU N)) β
          (fun U => (RectWilson.sysR L N).action U * (RectWilson.sysR L N).action U
            * (RectWilson.sysR L N).action U)
        - (RectWilson.sysR L N).expect (probHaar (SUN.SU N)) β
            (fun U => (RectWilson.sysR L N).action U * (RectWilson.sysR L N).action U)
          * EffectiveCoupling.meanAction N L β)
        - (-WindowRead.varAction N L β * EffectiveCoupling.meanAction N L β
          + EffectiveCoupling.meanAction N L β * -WindowRead.varAction N L β)) β := h
  refine h'.congr_deriv ?_
  unfold k3
  ring

/-- **The cumulant algebra**: `|−(E₃ − E₂ m) + 2 m (E₂ − m²)| ≤ 6 M³` when `|E₃| ≤ M³`, `|E₂| ≤ M²`, `|m| ≤ M`.
DERIVED: `6 = 1 + 1 + 4`, `2` the product rule, `3` the cube. -/
theorem k3_alg {E3 E2 m M : ℝ} (hM0 : 0 ≤ M) (h3 : |E3| ≤ M * M * M) (h2 : |E2| ≤ M * M)
    (h1 : |m| ≤ M) : |-(E3 - E2 * m) + 2 * m * (E2 - m * m)| ≤ 6 * M ^ 3 := by
  have hmm : |m| * |m| ≤ M * M := mul_le_mul h1 h1 (abs_nonneg _) hM0
  have eV : |E2 - m * m| ≤ 2 * (M * M) := by
    have hmm' : |m * m| ≤ M * M := by rw [abs_mul]; exact hmm
    calc |E2 - m * m| = |E2 + -(m * m)| := by rw [sub_eq_add_neg]
      _ ≤ |E2| + |-(m * m)| := abs_add_le _ _
      _ = |E2| + |m * m| := by rw [abs_neg]
      _ ≤ 2 * (M * M) := by linarith
  have p2 : |E2 * m| ≤ M * M * M := by
    rw [abs_mul]; exact mul_le_mul h2 h1 (abs_nonneg _) (mul_nonneg hM0 hM0)
  have p3 : |m * (E2 - m * m)| ≤ M * (2 * (M * M)) := by
    rw [abs_mul]; exact mul_le_mul h1 eV (abs_nonneg _) hM0
  have a3 := abs_le.mp h3
  have a2 := abs_le.mp p2
  have a1 := abs_le.mp p3
  rw [abs_le]
  constructor <;> linarith [a3.1, a3.2, a2.1, a2.2, a1.1, a1.2]

/-- **The third cumulant is at most `6 M³`** for any bound `M` on the action. DERIVED: `6`, `3` from `k3_alg`. -/
theorem abs_k3_le' (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hb : ∀ U, |(RectWilson.sysR L N).action U| ≤ M) : |k3 N L β| ≤ 6 * M ^ 3 := by
  have hS : Measurable (RectWilson.sysR L N).action :=
    measurable_wilsonSystem_action (N := N) (RectWilson.rbd L)
  have hSS : ∀ U, |(RectWilson.sysR L N).action U * (RectWilson.sysR L N).action U| ≤ M * M := fun U => by
    rw [abs_mul]; exact mul_le_mul (hb U) (hb U) (abs_nonneg _) hM0
  have hSSS : ∀ U, |(RectWilson.sysR L N).action U * (RectWilson.sysR L N).action U
      * (RectWilson.sysR L N).action U| ≤ M * M * M := fun U => by
    rw [abs_mul]; exact mul_le_mul (hSS U) (hb U) (abs_nonneg _) (mul_nonneg hM0 hM0)
  have e3 := wilsonSystem_expect_abs_le hN (RectWilson.rbd L) β
    (fun U => (RectWilson.sysR L N).action U * (RectWilson.sysR L N).action U
      * (RectWilson.sysR L N).action U) ((hS.mul hS).mul hS) _ hSSS
  have e2 := wilsonSystem_expect_abs_le hN (RectWilson.rbd L) β
    (fun U => (RectWilson.sysR L N).action U * (RectWilson.sysR L N).action U) (hS.mul hS) _ hSS
  have e1 : |EffectiveCoupling.meanAction N L β| ≤ M :=
    wilsonSystem_expect_abs_le hN (RectWilson.rbd L) β _ hS _ hb
  exact k3_alg hM0 e3 e2 e1

/-- **The third cumulant is at most `6 M³`**, `M = 2 |plaquettes|`. DERIVED: `2` the action bound, inherited
from `WindowRead.action_abs_le`. -/
theorem abs_k3_le (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) :
    |k3 N L β| ≤ 6 * (2 * (Fintype.card (RectWilson.RPlaq L) : ℝ)) ^ 3 :=
  abs_k3_le' hN L β (by positivity) (WindowRead.action_abs_le hN L)

/-- **The plaquettes of the cubic torus of side `n`**: `16 n⁴` (ordered direction pairs times sites).
DERIVED: `16 = 4·4`, `4` the dimension. -/
theorem card_RPlaq (n : ℕ) : Fintype.card (RectWilson.RPlaq (fun _ : Fin 4 => n)) = 16 * n ^ 4 := by
  simp only [RectWilson.RPlaq, RectWilson.RSite, Fintype.card_prod, Fintype.card_fin, Fintype.card_pi,
    Finset.prod_const, Finset.card_univ]

/-- **The sup of the third derivative of `D(w)`**: `16 · 6 M_n³ + 6 M_{2n}³`. DERIVED: `16`, `6`, `2`, `3` as
above. -/
def M3 (w : ℕ) : ℝ :=
  16 * (6 * (2 * (Fintype.card (RectWilson.RPlaq (fun _ : Fin 4 => 2 ^ w)) : ℝ)) ^ 3)
    + 6 * (2 * (Fintype.card (RectWilson.RPlaq (fun _ : Fin 4 => 2 * 2 ^ w)) : ℝ)) ^ 3

/-- **`M3 w = C₀ (16^w)³`**, `C₀ = 96·32³ + 6·512³`. DERIVED: `32 = 2·16`, `512 = 2·16·16`, `96 = 16·6`, `3` the cube. -/
theorem M3_eq (w : ℕ) : M3 w = (96 * 32 ^ 3 + 6 * 512 ^ 3) * ((16 : ℝ) ^ w) ^ 3 := by
  unfold M3
  rw [card_RPlaq, card_RPlaq, sixteen_pow]
  push_cast
  ring

/-- **`∂_β` of the curvature**, the third derivative of `D(w)`. DERIVED: `16`, `2` as in `curv`. -/
theorem hasDerivAt_curv (hN : N ≠ 0) (w : ℕ) (β : ℝ) :
    HasDerivAt (fun x => curv N w x)
      (16 * k3 N (fun _ => 2 ^ w) β - k3 N (fun _ => 2 * 2 ^ w) β) β :=
  ((hasDerivAt_varAction hN (fun _ => 2 ^ w) β).const_mul 16).sub
    (hasDerivAt_varAction hN (fun _ => 2 * 2 ^ w) β)

/-- **The third derivative of `D(w)` is at most `M3 w`.** DERIVED: `16` as in `curv`. -/
theorem abs_curv_deriv_le (hN : N ≠ 0) (w : ℕ) (β : ℝ) :
    |16 * k3 N (fun _ => 2 ^ w) β - k3 N (fun _ => 2 * 2 ^ w) β| ≤ M3 w := by
  have a := abs_le.mp (abs_k3_le hN (fun _ => 2 ^ w) β)
  have b := abs_le.mp (abs_k3_le hN (fun _ => 2 * 2 ^ w) β)
  unfold M3
  rw [abs_le]
  constructor <;> linarith [a.1, a.2, b.1, b.2]

/-- **The curvature of a window from the window read on a coupling interval**: `|D(·, w)| ≤ ε` on
`[β − s, β + s]` gives `|∂²_β D(w)| ≤ 4ε/s² + 2 M3 w · s`. DERIVED: `4`, `2` from `second_deriv_le`. -/
theorem curv_le_of_window (hN : N ≠ 0) {w : ℕ} {β s ε : ℝ} (hs : 0 < s)
    (hD : ∀ y ∈ Icc (β - s) (β + s), |CouplingTower.windowCoupling N y w| ≤ ε) :
    |curv N w β| ≤ 4 * ε / s ^ 2 + 2 * M3 w * s :=
  second_deriv_le (f := fun x => CouplingTower.windowCoupling N x w)
    (f1 := fun x => WindowRead.cutEnergy N x w) (f2 := fun x => curv N w x)
    (f3 := fun x => 16 * k3 N (fun _ => 2 ^ w) x - k3 N (fun _ => 2 * 2 ^ w) x) hs
    (fun y => CouplingTower.hasDerivAt_windowCoupling hN w y)
    (fun y => hasDerivAt_cutEnergy_curv hN w y) (fun y => hasDerivAt_curv hN w y)
    (fun y => abs_curv_deriv_le hN w y) hD

/-! ## 5. The basin -/

/-- **A strict seed holds on a coupling interval**: `D(β, w₀) < 1/1000` at `β > 0` gives `t ∈ (0, β]` with the
seed on `[β − t, β + t]`. CHOSEN: `δ/2`. DERIVED: `1000` inherited from `DoublingSharp.rec_sharp`. -/
theorem seed_interval (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β) {w₀ : ℕ}
    (h : CouplingTower.windowCoupling N β w₀ < 1 / 1000) :
    ∃ t : ℝ, 0 < t ∧ t ≤ β ∧ ∀ y ∈ Icc (β - t) (β + t), CouplingTower.windowCoupling N y w₀ < 1 / 1000 := by
  have hc := (CouplingTower.continuous_windowCoupling hN w₀).continuousAt (x := β)
  have hev : ∀ᶠ y in 𝓝 β, CouplingTower.windowCoupling N y w₀ < 1 / 1000 :=
    hc.tendsto.eventually (eventually_lt_nhds h)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (δ / 2) β, lt_min (by linarith) hβ, min_le_right _ _, fun y hy => hball ?_⟩
  have hm := min_le_left (δ / 2) β
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

/-- **Sharp squarings of the window read**: a seed `D(y, w₀) ≤ 1/1000` at `y ≥ 0`, `w₀ ≥ 1`, gives
`250 D(y, w₀ + k) ≤ (1/4)^{2^k}`. Inherited: `1/1000`, `250`, `1/4` from `DoublingSharp`. -/
theorem window_sharp [NeZero N] {y : ℝ} (hy : 0 ≤ y) {w₀ : ℕ} (hw : 1 ≤ w₀)
    (h : CouplingTower.windowCoupling N y w₀ ≤ 1 / 1000) (k : ℕ) :
    250 * CouplingTower.windowCoupling N y (w₀ + k) ≤ (1 / 4) ^ (2 ^ k) := by
  have := CentreSectorSeedN.defectW_sharp (N := N) hy (DeltaLengthTower.two_le_two_pow hw)
    (DeltaLengthTower.even_two_pow hw) h k
  unfold CouplingTower.windowCoupling
  rw [show 2 ^ (w₀ + k) = 2 ^ k * 2 ^ w₀ by rw [pow_add, mul_comm]]
  exact this

/-- **The curvature of the windows beyond a strict seed**: some `t > 0` such that for every `k` and `0 < s ≤ t`,
`|∂²_β D(w₀ + k)| ≤ 4 ε_k/s² + 2 M3 (w₀+k) s`, `ε_k = (1/4)^{2^k}/250`. Inherited: `1/1000`, `250`, `1/4`. -/
theorem curv_basin [NeZero N] {β : ℝ} (hβ : 0 < β) {w₀ : ℕ} (hw : 1 ≤ w₀)
    (h : CouplingTower.windowCoupling N β w₀ < 1 / 1000) :
    ∃ t : ℝ, 0 < t ∧ ∀ (k : ℕ) (s : ℝ), 0 < s → s ≤ t →
      |curv N (w₀ + k) β| ≤ 4 * ((1 / 4) ^ (2 ^ k) / 250) / s ^ 2 + 2 * M3 (w₀ + k) * s := by
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨t, ht, htβ, hseed⟩ := seed_interval hN hβ h
  refine ⟨t, ht, fun k s hs hst => curv_le_of_window hN hs fun y hy => ?_⟩
  have hy' : y ∈ Icc (β - t) (β + t) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hy0 : 0 ≤ y := by linarith [hy'.1]
  have hD0 := CouplingTower.windowCoupling_nonneg hN hy0 (show 1 ≤ w₀ + k by omega)
  have hD := window_sharp hy0 hw (hseed y hy').le k
  rw [abs_of_nonneg hD0]
  linarith

/-- **Doubly exponential decay beats an exponential**: `∑_k 256^k (1/2)^{2^k} < ∞`. DERIVED: `256 = 16²`,
`2` the doubling. -/
theorem summable_dexp : Summable (fun k : ℕ => (256 : ℝ) ^ k * (1 / 2) ^ (2 ^ k)) := by
  refine summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
    (Eventually.of_forall fun k => by positivity) ?_
  have hr : ∀ k : ℕ, ‖(256 : ℝ) ^ (k + 1) * (1 / 2) ^ (2 ^ (k + 1))‖ / ‖(256 : ℝ) ^ k * (1 / 2) ^ (2 ^ k)‖
      = 256 * (1 / 2 : ℝ) ^ (2 ^ k) := fun k => by
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), pow_succ 2 k, pow_mul]
    have h1 : (0 : ℝ) < 256 ^ k := by positivity
    have h2 : (0 : ℝ) < (1 / 2) ^ (2 ^ k) := by positivity
    field_simp
    ring
  have ht : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (2 ^ k)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
  have ht' := ht.const_mul 256
  rw [mul_zero] at ht'
  exact (tendsto_congr hr).mpr ht'

/-- **Beyond a strict seed the torus susceptibility is bounded uniformly in the side**: at `β > 0` with
`D(β, w₀) < 1/1000`, `w₀ ≥ 1`, some `B` bounds `χ_{2^{w₀+m}}(β)` for every `m`. The bound is absolute and at one
coupling. Inherited: `1/1000`, `250`, `1/4`. CHOSEN: `s_k = t (1/2)^{2^k}`. DERIVED: `16`, `256 = 16²`, `8 = 16/2`
the volume factor against the `2` of `second_deriv_le`, `C₀` from `M3_eq`; `1000` inherited from `DoublingSharp.rec_sharp`. -/
theorem chi_bounded_of_seed [NeZero N] {β : ℝ} (hβ : 0 < β) {w₀ : ℕ} (hw : 1 ≤ w₀)
    (h : CouplingTower.windowCoupling N β w₀ < 1 / 1000) :
    ∃ B : ℝ, ∀ m : ℕ, chi N (2 ^ (w₀ + m)) β ≤ B := by
  obtain ⟨t, ht, hcurv⟩ := curv_basin hβ hw h
  let b : ℕ → ℝ := fun k => 4 / (250 * t ^ 2 * (16 * 16 ^ w₀)) * (1 / 16) ^ k
    + (96 * 32 ^ 3 + 6 * 512 ^ 3) * ((16 : ℝ) ^ w₀) ^ 2 * t / 8 * ((256 : ℝ) ^ k * (1 / 2) ^ (2 ^ k))
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    show 0 ≤ 4 / (250 * t ^ 2 * (16 * 16 ^ w₀)) * (1 / 16 : ℝ) ^ k
      + (96 * 32 ^ 3 + 6 * 512 ^ 3) * ((16 : ℝ) ^ w₀) ^ 2 * t / 8 * ((256 : ℝ) ^ k * (1 / 2) ^ (2 ^ k))
    positivity
  have hbs : Summable b :=
    ((summable_geometric_of_lt_one (r := 1 / 16) (by norm_num) (by norm_num)).mul_left
      (4 / (250 * t ^ 2 * (16 * 16 ^ w₀)))).add
      (summable_dexp.mul_left ((96 * 32 ^ 3 + 6 * 512 ^ 3) * ((16 : ℝ) ^ w₀) ^ 2 * t / 8))
  refine ⟨chi N (2 ^ w₀) β + ∑' k, b k, fun m => ?_⟩
  have key := chi_le_of_curv (N := N) (w := w₀) (m := m) (β := β) b (fun k _ => by
    have hQ0 : (0 : ℝ) < 16 ^ k := by positivity
    have hP0 : (0 : ℝ) < 16 ^ w₀ := by positivity
    have hr0 : (0 : ℝ) < (1 / 2) ^ (2 ^ k) := by positivity
    have hr1 : (1 / 2 : ℝ) ^ (2 ^ k) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hst : t * (1 / 2) ^ (2 ^ k) ≤ t := by nlinarith
    have hc := hcurv k (t * (1 / 2) ^ (2 ^ k)) (by positivity) hst
    have hε : (1 / 4 : ℝ) ^ (2 ^ k) = ((1 / 2) ^ (2 ^ k)) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h16 : (16 : ℝ) ^ (w₀ + k + 1) = 16 * 16 ^ w₀ * 16 ^ k := by rw [pow_succ, pow_add]; ring
    have hM3 : M3 (w₀ + k) = (96 * 32 ^ 3 + 6 * 512 ^ 3) * (16 ^ w₀ * 16 ^ k) ^ 3 := by
      rw [M3_eq, pow_add]
    have h256 : (256 : ℝ) ^ k = ((16 : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h1_16 : (1 / 16 : ℝ) ^ k = 1 / 16 ^ k := by rw [one_div_pow]
    have e : 4 * ((1 / 4) ^ (2 ^ k) / 250) / (t * (1 / 2) ^ (2 ^ k)) ^ 2
        + 2 * M3 (w₀ + k) * (t * (1 / 2) ^ (2 ^ k)) = 16 ^ (w₀ + k + 1) * b k := by
      show _ = 16 ^ (w₀ + k + 1) * (4 / (250 * t ^ 2 * (16 * 16 ^ w₀)) * (1 / 16 : ℝ) ^ k
        + (96 * 32 ^ 3 + 6 * 512 ^ 3) * ((16 : ℝ) ^ w₀) ^ 2 * t / 8 * ((256 : ℝ) ^ k * (1 / 2) ^ (2 ^ k)))
      rw [hε, h16, hM3, h256, h1_16]
      field_simp
      ring
    rw [← e]
    exact (neg_le_abs _).trans hc)
  have hsum := hbs.sum_le_tsum (Finset.range m) (fun k _ => hb0 k)
  linarith

end MassGap.FractalTail

end

#print axioms MassGap.FractalTail.hasDerivAt_cutEnergy_curv
#print axioms MassGap.FractalTail.sixteen_pow
#print axioms MassGap.FractalTail.curv_eq_shell
#print axioms MassGap.FractalTail.chi_double_sub
#print axioms MassGap.FractalTail.shell_step
#print axioms MassGap.FractalTail.chi_telescope
#print axioms MassGap.FractalTail.chi_le_of_curv
#print axioms MassGap.FractalTail.chi_le_of_curvFloor
#print axioms MassGap.FractalTail.second_deriv_le
#print axioms MassGap.FractalTail.hasDerivAt_varAction
#print axioms MassGap.FractalTail.k3_alg
#print axioms MassGap.FractalTail.abs_k3_le'
#print axioms MassGap.FractalTail.abs_k3_le
#print axioms MassGap.FractalTail.card_RPlaq
#print axioms MassGap.FractalTail.M3_eq
#print axioms MassGap.FractalTail.hasDerivAt_curv
#print axioms MassGap.FractalTail.abs_curv_deriv_le
#print axioms MassGap.FractalTail.curv_le_of_window
#print axioms MassGap.FractalTail.seed_interval
#print axioms MassGap.FractalTail.window_sharp
#print axioms MassGap.FractalTail.curv_basin
#print axioms MassGap.FractalTail.summable_dexp
#print axioms MassGap.FractalTail.chi_bounded_of_seed
