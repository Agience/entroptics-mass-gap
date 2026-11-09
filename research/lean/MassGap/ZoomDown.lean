import Mathlib
import MassGap.FractalTail
import MassGap.TwistedTraceBoundFull

/-!
# MassGap.ZoomDown — the dyadic shells read from the finest window inward, and what replaces the basin there

`FractalTail` runs the doubling bootstrap outward from the seed window, where `D(β, w) = windowCoupling N β w`
falls below `1/1000`, and leaves the windows below the seed open: the missing inequality is
`|16 Var_{2^j}(S) − Var_{2^{j+1}}(S)| ≤ K F_k` at `β_k` for every window `2^j` below the seed. This module tests the
downward reading (start where the field is near free, at the finest windows, and pass control inward) against the
tree, proves what holds, and states what stops it. Declarations are in the namespace `MassGap.ZoomDown`.
Throughout, `curv N w β = 16 Var_{2^w} − Var_{2^{w+1}} = ∂²_β D(w)` and `chi N n β = Var_n / n⁴` (`FractalTail`).

## 1. The basin recedes from the small windows (proved)

* `window_out_of_basin`: for `N ≥ 2` and every window `w ≥ 1`, eventually in `β`, `D(β, w) > 1/1000`
  (`defect_gt` of `TwistedTraceBoundFull` at side `2^w`). On a fixed torus the centre sectors keep the doubling defect of
  order one at weak coupling.
* `basin_recedes`: for every `W`, eventually in `β`, every window `1 ≤ w ≤ W` lies outside the basin.
* `seedWindow_tendsto`: any choice of seed window `w₀(β) ≥ 1` with `D(β, w₀(β)) ≤ 1/1000` tends to infinity.
* `out_of_basin_down`: `D(β, w + 1) > 1/4000` gives `D(β, w) > 1/1000` (contrapositive of
  `CouplingTower.basin_contracts`). Read downward, the squaring recursion carries the absence of control
  from a window to the windows below it, never control.

So the small-window end is not in the basin: `rec_sharp` is unavailable there at every large coupling, for every
`N ≥ 2`, and the downward route cannot start from a small `D`. Near-free does not mean small `D`: at Gaussian order
around the flat connections (argued) `D(β, w) = A_w − c log β + o(1)` with `−c = (15/2) z`, `z` the count of
non-Gaussian (moduli) directions of the torus, the same at every window; `D` grows at fixed `w`.

## 2. The relative-unit curvature (proved)

What the near-free regime does control is the coupling dependence of `D` in relative units, the second difference
over a relative step `θβ`, not `D` itself.

* `second_diff_le`: `|f''(x)| ≤ |f(x+s) + f(x−s) − 2f(x)|/s² + 2Ms`, with `|f'''| ≤ M` only on `[x − s, x + s]`.
  The interval form of `FractalTail.second_deriv_le`, reading the second difference in place of a sup of `|f|`.
* `secondDiff N w β θ = D(β + θβ, w) + D(β − θβ, w) − 2 D(β, w)`; `thirdDefect N w y = 16 k3_{2^w} − k3_{2^{w+1}}`,
  `∂³_β D(w)` (`FractalTail.hasDerivAt_curv`).
* `curv_rel_le`: `|secondDiff| ≤ E` and `|thirdDefect| ≤ M/β³` on `[β − θβ, β + θβ]` give
  `β² |curv N w β| ≤ E/θ² + 2Mθ`. The `1/β²` of the floor comes out of the relative step.
* `free_secondDiff` (the test at the unit): for `D = A − c log β`, `secondDiff = −c log(1 − θ²)`, independent of
  `β` and of the window. The free part passes the relative clause with one `E` along all windows.

## 3. The telescope tolerates growth (proved)

* `chi_le_of_curvGrowth`: `|curv N (w+j) β| ≤ c q^j` for `j < m`, `0 ≤ q < 16`, gives
  `χ_{2^{w+m}} ≤ χ_{2^w} + c/((16 − q) 16^w)`, uniformly in `m`. The volume factor `16^{j+1}` of the shell identity
  absorbs any growth slower than `16^j`, so the window-uniform form of `FractalTail`'s missing inequality is
  stronger than the telescope needs.
* `chi_le_of_rel`: the two relative inputs with growth `q^j` give
  `β² (χ_{2^{w+m}} − χ_{2^w}) ≤ (E/θ² + 2Mθ)/((16 − q) 16^w)`, uniformly in `m`.

## 4. The paper test

Step 1 (the finest box). The tree has no one-box statement uniform in relative units: no bound
`Var_{2}(S) ≤ c/β²` on the side-`2` torus, no `C_k(0) ≤ c/β_k²` (`PlaqShortDistance`, What does not follow), and
the per-link conditional variance `ν(cv_l A_l) ~ 1/β²` is argued at Gaussian order only (`PlaqShortDistance` §5).
On a fixed torus the statement is a Laplace asymptotic of a finite-dimensional integral over `SU(N)^{links}` with a
degenerate minimum set (the flat connections), equipartition `β² Var → (codim)/2`; it is true and not formalized.
The base `χ_{2^w}` of §3 at `w = 1` is that statement.

Step 2 (the step). The shell identity is exact and two-sided (`FractalTail.chi_telescope`), so the downward reading
from the finest window and the upward reading from it are one identity; only the base moves. There is no inward
recursion of the defect: `rec_sharp` holds only for `D ≤ 1/1000`, which §1 rules out at every small window. The
replacement is §2–§3: a relative second difference `|secondDiff N j β θ| ≤ E q^j` and a relative third cumulant
defect `|thirdDefect N j y| ≤ M q^j/β³`, `q < 16`, for every window `j` from `1` to the screen box. The free field
meets both with `q = 1` (`free_secondDiff` for the second difference of its form `A − c log β`; argued that
this is its form, with `β³ ∂³_β D = −2c`). Near the seed window (argued) `D`
falls from order `log β` to below `1/1000` across a coupling change of order one (one doubling of the correlation
length), so `secondDiff` at a relative step `θβ` is of order `log β` there; the growth `q^j` absorbs it, since the
seed window `j₀` has `q^{j₀}` exponential in `β` for any `q > 1`.

## What does not follow

* Neither relative input of §3 is proved at any window, any coupling, or along any tower. At the small windows
  they are the perturbative (Bałaban-type) content: the coupling dependence of the finite-size free energy of a
  torus of side `2^j`, in relative units, with the running coupling between `β` and `β_eff(2^j)`; the third
  cumulant defect is the same kind of statement one derivative up. The crude `FractalTail.abs_curv_deriv_le`
  (`|thirdDefect| ≤ M3 w ~ 16^{3w}`, absolute) does not give `M/β³` and does not have growth below `16^j`.
* The exact missing inequality, after `chi_le_of_rel`: one `θ ∈ (0, 1)`, `q < 16`, `E`, `M` with, eventually along
  the tower, at `β_k` and for every window `1 ≤ j ≤ log₂ L_k`,
  `|D(β_k(1+θ), j) + D(β_k(1−θ), j) − 2 D(β_k, j)| ≤ E q^j` and
  `|16 k3_{2^j} − k3_{2^{j+1}}| ≤ M q^j / β_k³` on `[β_k(1−θ), β_k(1+θ)]`; together with the base
  `χ_2(β_k) ≤ c/β_k²` (step 1). Restating `FractalTail`'s inequality in this form is not discharging it.
* Even with those: the signed torus susceptibility is not the absolute box row sum of `PlaqSummable`
  (`FractalTail` §6, items 3–5), and `F_k` against `1/β_k²` is not in the tree.
* §1 is proved for `N ≥ 2`; the Gaussian-order form of `D` and the crossover estimate of §4 are argued.
* `U(1)`: §1 holds there too (`TwistedTraceBoundFull`, Controls); the relative inputs are argued to hold
  (free photon), consistent with `FractalTail` §6 that the tail needs no gap.

DERIVED (module-wide): `16 = 2⁴` the blocks and the volume ratio; `2` the doubling, the squares and the second
difference; `4` the four values of the second difference; `3` the cube `s³` and `β³`; `1/4000 = (1/1000)/4` from the
division by `4` in `CouplingTower.basin_contracts`. Inherited: `1/1000` from `DoublingSharp` through
`CouplingTower.basin_contracts`. `θ`, `q`, `E`, `M`, `c`, `A` are hypotheses.
The constants `15/2` and `z` appear only in the argued text.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ZoomDown

open Filter Topology Set
open MassGap

variable {N : ℕ}

/-! ## 1. The basin recedes -/

/-- **A fixed window leaves the basin at weak coupling**: for `N ≥ 2` and `w ≥ 1`, eventually in `β`,
`D(β, w) > 1/1000`. DERIVED: `2` the doubling; `1000` inherited from `DoublingSharp.rec_sharp`. -/
theorem window_out_of_basin (hN : 2 ≤ N) {w : ℕ} (hw : 1 ≤ w) :
    ∀ᶠ β in atTop, 1 / 1000 < CouplingTower.windowCoupling N β w := by
  obtain ⟨c, rfl⟩ : ∃ c, w = c + 1 := ⟨w - 1, by omega⟩
  have h := TwistedTraceBoundN.defect_gt hN (2 ^ c) Nat.one_le_two_pow
  rw [show 2 * 2 ^ c = 2 ^ (c + 1) by ring] at h
  exact h

/-- **The basin recedes**: for every `W`, eventually in `β`, every window `1 ≤ w ≤ W` reads above `1/1000`.
Inherited: `1/1000`. -/
theorem basin_recedes (hN : 2 ≤ N) (W : ℕ) :
    ∀ᶠ β in atTop, ∀ w ∈ Finset.Icc 1 W, 1 / 1000 < CouplingTower.windowCoupling N β w :=
  (Filter.eventually_all_finset _).2 fun _ hw => window_out_of_basin hN (Finset.mem_Icc.mp hw).1

/-- **Every seed window tends to infinity**: a choice `w₀(β) ≥ 1` with `D(β, w₀(β)) ≤ 1/1000` eventually is
unbounded along `β → ∞`. Inherited: `1/1000`. -/
theorem seedWindow_tendsto (hN : 2 ≤ N) {w₀ : ℝ → ℕ}
    (h : ∀ᶠ β in atTop, 1 ≤ w₀ β ∧ CouplingTower.windowCoupling N β (w₀ β) ≤ 1 / 1000) :
    Tendsto w₀ atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [basin_recedes hN b, h] with β hB hs
  by_contra hlt
  push_neg at hlt
  have := hB (w₀ β) (Finset.mem_Icc.mpr ⟨hs.1, hlt.le⟩)
  linarith [hs.2]

/-- **Read downward, the recursion carries the absence of control**: `D(β, w + 1) > 1/4000` gives
`D(β, w) > 1/1000`. Inherited: `1/1000`. DERIVED: `1/4000 = (1/1000)/4`. -/
theorem out_of_basin_down (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w)
    (h : 1 / 4000 < CouplingTower.windowCoupling N β (w + 1)) :
    1 / 1000 < CouplingTower.windowCoupling N β w := by
  by_contra hle
  push_neg at hle
  have := CouplingTower.basin_contracts hN hβ hw hle
  linarith

/-! ## 2. The relative-unit curvature -/

/-- **The second derivative from the second difference**: with `|f'''| ≤ M` on `[x − s, x + s]`, `s > 0`,
`|f''(x)| ≤ |f(x+s) + f(x−s) − 2f(x)|/s² + 2Ms`. DERIVED: `2` the second difference and the mean value steps,
`3` the cube `s³`. -/
theorem second_diff_le {f f1 f2 f3 : ℝ → ℝ} {x s M : ℝ} (hs : 0 < s)
    (h1 : ∀ y, HasDerivAt f (f1 y) y) (h2 : ∀ y, HasDerivAt f1 (f2 y) y)
    (h3 : ∀ y, HasDerivAt f2 (f3 y) y) (hM : ∀ y ∈ Icc (x - s) (x + s), |f3 y| ≤ M) :
    |f2 x| ≤ |f (x + s) + f (x - s) - 2 * f x| / s ^ 2 + 2 * M * s := by
  have hx : x ∈ Icc (x - s) (x + s) := ⟨by linarith, by linarith⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hx)
  have lip : ∀ b ∈ Icc (x - s) (x + s), |f2 b - f2 x| ≤ M * |b - x| := fun b hb => by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f2) (f' := f3)
      (s := Icc (x - s) (x + s)) (fun y _ => (h3 y).hasDerivWithinAt)
      (fun y hy => by rw [Real.norm_eq_abs]; exact hM y hy) (convex_Icc _ _) hx hb
    simpa only [Real.norm_eq_abs] using this
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
    have ea := lip (x + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have eb := lip (x - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
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
  have gs := abs_le.mp hgs
  have hgv : g s = f (x + s) + f (x - s) - 2 * f x - s ^ 2 * f2 x := rfl
  rw [hgv] at gs
  have hs2 : 0 < s ^ 2 := by positivity
  set Δ := f (x + s) + f (x - s) - 2 * f x with hΔ
  have hd1 := le_abs_self Δ
  have hd2 := neg_abs_le Δ
  have key : |f2 x| * s ^ 2 ≤ |Δ| + 2 * M * s ^ 3 := by
    have hcs : |f2 x * s ^ 2| ≤ |Δ| + 2 * M * s ^ 3 := by
      rw [abs_le]
      constructor <;> nlinarith [gs.1, gs.2]
    rwa [abs_mul, abs_of_pos hs2] at hcs
  have hk : |f2 x| ≤ (|Δ| + 2 * M * s ^ 3) / s ^ 2 := by
    rw [le_div_iff₀ hs2]
    exact key
  have e3 : 2 * M * s ^ 3 / s ^ 2 = 2 * M * s := by
    rw [div_eq_iff (ne_of_gt hs2)]
    ring
  rw [add_div, e3] at hk
  exact hk

/-- **The second difference of the window read over a relative coupling step**:
`D(β + θβ, w) + D(β − θβ, w) − 2 D(β, w)`. DERIVED: `2` the second difference. -/
def secondDiff (N w : ℕ) (β θ : ℝ) : ℝ :=
  CouplingTower.windowCoupling N (β + θ * β) w + CouplingTower.windowCoupling N (β - θ * β) w
    - 2 * CouplingTower.windowCoupling N β w

/-- **The third cumulant defect** `16 k3_{2^w} − k3_{2^{w+1}}`, the third coupling derivative of `D(w)`.
DERIVED: `16 = 2⁴`, `2` the doubling. -/
def thirdDefect (N w : ℕ) (y : ℝ) : ℝ :=
  16 * FractalTail.k3 N (fun _ => 2 ^ w) y - FractalTail.k3 N (fun _ => 2 * 2 ^ w) y

/-- **The curvature in relative units**: `|secondDiff| ≤ E` and `|thirdDefect| ≤ M/β³` on `[β − θβ, β + θβ]`
give `β² |curv N w β| ≤ E/θ² + 2Mθ`. DERIVED: `2` and `3` as in `second_diff_le`. -/
theorem curv_rel_le (hN : N ≠ 0) {w : ℕ} {β θ E M : ℝ} (hβ : 0 < β) (hθ : 0 < θ)
    (hE : |secondDiff N w β θ| ≤ E)
    (hM : ∀ y ∈ Icc (β - θ * β) (β + θ * β), |thirdDefect N w y| ≤ M / β ^ 3) :
    β ^ 2 * |FractalTail.curv N w β| ≤ E / θ ^ 2 + 2 * M * θ := by
  have hs : 0 < θ * β := mul_pos hθ hβ
  have h := second_diff_le (f := fun x => CouplingTower.windowCoupling N x w)
    (f1 := fun x => WindowRead.cutEnergy N x w) (f2 := fun x => FractalTail.curv N w x)
    (f3 := fun x => thirdDefect N w x) (x := β) (M := M / β ^ 3) hs
    (fun y => CouplingTower.hasDerivAt_windowCoupling hN w y)
    (fun y => FractalTail.hasDerivAt_cutEnergy_curv hN w y) (fun y => FractalTail.hasDerivAt_curv hN w y)
    hM
  beta_reduce at h
  have hΔ : |CouplingTower.windowCoupling N (β + θ * β) w + CouplingTower.windowCoupling N (β - θ * β) w
      - 2 * CouplingTower.windowCoupling N β w| ≤ E := hE
  have hs2 : 0 < (θ * β) ^ 2 := by positivity
  have h' : |FractalTail.curv N w β| ≤ E / (θ * β) ^ 2 + 2 * (M / β ^ 3) * (θ * β) := by
    have := div_le_div_of_nonneg_right hΔ hs2.le
    linarith
  have hb2 : 0 ≤ β ^ 2 := sq_nonneg β
  have e : β ^ 2 * (E / (θ * β) ^ 2 + 2 * (M / β ^ 3) * (θ * β)) = E / θ ^ 2 + 2 * M * θ := by
    have hβ0 : β ≠ 0 := ne_of_gt hβ
    have hθ0 : θ ≠ 0 := ne_of_gt hθ
    field_simp
  calc β ^ 2 * |FractalTail.curv N w β|
      ≤ β ^ 2 * (E / (θ * β) ^ 2 + 2 * (M / β ^ 3) * (θ * β)) := mul_le_mul_of_nonneg_left h' hb2
    _ = E / θ ^ 2 + 2 * M * θ := e

/-- **The free part passes the relative clause**: for `D(y) = A − c log y`, the second difference over the step
`θβ` is `−c log(1 − θ²)`, independent of `β` and of the window. DERIVED: `2` the second difference and the
square. -/
theorem free_secondDiff {A c β θ : ℝ} (hβ : 0 < β) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (A - c * Real.log (β + θ * β)) + (A - c * Real.log (β - θ * β)) - 2 * (A - c * Real.log β)
      = -c * Real.log (1 - θ ^ 2) := by
  have h1 : (0 : ℝ) < 1 + θ := by linarith
  have h2 : (0 : ℝ) < 1 - θ := by linarith
  rw [show β + θ * β = β * (1 + θ) by ring, show β - θ * β = β * (1 - θ) by ring,
    show (1 : ℝ) - θ ^ 2 = (1 + θ) * (1 - θ) by ring,
    Real.log_mul (ne_of_gt hβ) (ne_of_gt h1), Real.log_mul (ne_of_gt hβ) (ne_of_gt h2),
    Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]
  ring

/-! ## 3. The telescope tolerates growth -/

/-- **Curvature growing slower than the volume is a geometric series**: `|curv N (w+j) β| ≤ c q^j` for `j < m`,
`0 ≤ q < 16`, gives `χ_{2^{w+m}} ≤ χ_{2^w} + c/((16 − q) 16^w)`, uniformly in `m`. DERIVED: `16 = 2⁴`. -/
theorem chi_le_of_curvGrowth {w m : ℕ} {β c q : ℝ} (hc : 0 ≤ c) (hq0 : 0 ≤ q) (hq : q < 16)
    (h : ∀ j < m, |FractalTail.curv N (w + j) β| ≤ c * q ^ j) :
    FractalTail.chi N (2 ^ (w + m)) β ≤ FractalTail.chi N (2 ^ w) β + c / ((16 - q) * 16 ^ w) := by
  let b : ℕ → ℝ := fun j => c / 16 ^ (w + 1) * (q / 16) ^ j
  have key := FractalTail.chi_le_of_curv (N := N) (w := w) (m := m) (β := β) b (fun j hj => by
    have e : (16 : ℝ) ^ (w + j + 1) * b j = c * q ^ j := by
      show (16 : ℝ) ^ (w + j + 1) * (c / 16 ^ (w + 1) * (q / 16) ^ j) = c * q ^ j
      rw [show w + j + 1 = (w + 1) + j by ring, pow_add, div_pow]
      have : (16 : ℝ) ^ j ≠ 0 := by positivity
      have : (16 : ℝ) ^ (w + 1) ≠ 0 := by positivity
      field_simp
    rw [e]
    exact (neg_le_abs _).trans (h j hj))
  have hr0 : 0 ≤ q / 16 := by positivity
  have hr1 : q / 16 < 1 := by rw [div_lt_one (by norm_num)]; exact hq
  have hgeom : ∑ j ∈ Finset.range m, (q / 16 : ℝ) ^ j ≤ (1 - q / 16)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun j _ => by positivity)
  have hsum : ∑ j ∈ Finset.range m, b j ≤ c / ((16 - q) * 16 ^ w) := by
    show ∑ j ∈ Finset.range m, c / 16 ^ (w + 1) * (q / 16 : ℝ) ^ j ≤ _
    rw [← Finset.mul_sum]
    have hc' : 0 ≤ c / 16 ^ (w + 1) := by positivity
    have h16 : (0 : ℝ) < 16 - q := by linarith
    have einv : (1 - q / 16 : ℝ)⁻¹ = 16 / (16 - q) := by
      rw [show (1 : ℝ) - q / 16 = (16 - q) / 16 by ring, inv_div]
    have e : c / 16 ^ (w + 1) * (16 / (16 - q)) = c / ((16 - q) * 16 ^ w) := by
      have : (16 : ℝ) ^ w ≠ 0 := by positivity
      have : (16 : ℝ) - q ≠ 0 := ne_of_gt h16
      rw [pow_succ]
      field_simp
    calc c / 16 ^ (w + 1) * ∑ j ∈ Finset.range m, (q / 16 : ℝ) ^ j
        ≤ c / 16 ^ (w + 1) * (1 - q / 16)⁻¹ := mul_le_mul_of_nonneg_left hgeom hc'
      _ = c / ((16 - q) * 16 ^ w) := by rw [einv, e]
  linarith

/-- **The relative inputs bound the susceptibility in units of the floor**: with `|secondDiff N (w+j) β θ| ≤ E q^j`
and `|thirdDefect N (w+j)| ≤ M q^j/β³` on `[β − θβ, β + θβ]` for `j < m`, `0 ≤ q < 16`,
`β² (χ_{2^{w+m}} − χ_{2^w}) ≤ (E/θ² + 2Mθ)/((16 − q) 16^w)`, uniformly in `m`. DERIVED: `16`, `2`, `3` as above. -/
theorem chi_le_of_rel (hN : N ≠ 0) {w m : ℕ} {β θ q E M : ℝ} (hβ : 0 < β) (hθ : 0 < θ)
    (hq0 : 0 ≤ q) (hq : q < 16) (hE0 : 0 ≤ E) (hM0 : 0 ≤ M)
    (hE : ∀ j < m, |secondDiff N (w + j) β θ| ≤ E * q ^ j)
    (hM : ∀ j < m, ∀ y ∈ Icc (β - θ * β) (β + θ * β), |thirdDefect N (w + j) y| ≤ M * q ^ j / β ^ 3) :
    β ^ 2 * (FractalTail.chi N (2 ^ (w + m)) β - FractalTail.chi N (2 ^ w) β)
      ≤ (E / θ ^ 2 + 2 * M * θ) / ((16 - q) * 16 ^ w) := by
  set X := E / θ ^ 2 + 2 * M * θ with hX
  have hX0 : 0 ≤ X := by positivity
  have hb2 : 0 < β ^ 2 := by positivity
  have hc : 0 ≤ X / β ^ 2 := by positivity
  have hcurv : ∀ j < m, |FractalTail.curv N (w + j) β| ≤ X / β ^ 2 * q ^ j := fun j hj => by
    have hr := curv_rel_le hN hβ hθ (hE j hj) (hM j hj)
    have e : E * q ^ j / θ ^ 2 + 2 * (M * q ^ j) * θ = X * q ^ j := by rw [hX]; ring
    rw [e] at hr
    rw [div_mul_eq_mul_div, le_div_iff₀ hb2, mul_comm]
    exact hr
  have hχ := chi_le_of_curvGrowth (N := N) hc hq0 hq hcurv
  have h16 : (0 : ℝ) < (16 - q) * 16 ^ w := by
    have : (0 : ℝ) < 16 - q := by linarith
    positivity
  have e : β ^ 2 * (X / β ^ 2 / ((16 - q) * 16 ^ w)) = X / ((16 - q) * 16 ^ w) := by
    field_simp
  calc β ^ 2 * (FractalTail.chi N (2 ^ (w + m)) β - FractalTail.chi N (2 ^ w) β)
      ≤ β ^ 2 * (X / β ^ 2 / ((16 - q) * 16 ^ w)) :=
        mul_le_mul_of_nonneg_left (by linarith) hb2.le
    _ = X / ((16 - q) * 16 ^ w) := e

end MassGap.ZoomDown

#print axioms MassGap.ZoomDown.window_out_of_basin
#print axioms MassGap.ZoomDown.basin_recedes
#print axioms MassGap.ZoomDown.seedWindow_tendsto
#print axioms MassGap.ZoomDown.out_of_basin_down
#print axioms MassGap.ZoomDown.second_diff_le
#print axioms MassGap.ZoomDown.curv_rel_le
#print axioms MassGap.ZoomDown.free_secondDiff
#print axioms MassGap.ZoomDown.chi_le_of_curvGrowth
#print axioms MassGap.ZoomDown.chi_le_of_rel
