import Mathlib
import MassGap.OpenAIBridgeCluster

/-!
# MassGap.OpenAIBridgeSides — the gap of the seed on the cubic torus of every even side `L ≥ 2n`

`DoublingSharp.wilson_gap_sharp` reads the gap on the slice of the torus at corner `k𝟙` of the
dyadic lattice, side `2^k n`. The slice transfer `kT 0 T N β` depends only on the spatial slice `T`
(`RectTransfer.ZR_eq_cyc`: every time extent is a cyclic power of the same kernel), so what is pinned
to `2^k n` is the slice, and it is pinned by the corner lattice, which doubles every side at every
step. The tori of the OpenAI schedule have side `period p · den m` with `den m` odd and
`4 ∣ period p`, which is `2^k n` with `n` of bounded physical size only when the period is a power
of two.

The trace facts do not need integer ratios, only even times. This module climbs the dyadic lattice
to the level `m0 = 2^a n` and then takes one step of real ratio `ρ = L / (2 m0) ∈ [1, 4]` on levels
`m0, 2 m0, L`:

* `pr x ρ μ v = ρ x(v) − x(v + e_μ)` is the defect of a ratio-`ρ` step;
* `Climb x ρ` holds the three facts the climb uses on `{0,1,2}^4`: `p ≥ 0` at level `0`, `pr ≥ 0`
  at level `1`, and `p ≤ 1/10 ⇒ pr(v + e_μ) ≤ 5 p(v)²`;
* `stepC` is the mixed corner identity
  `p_μ(c + 2e_ν) = ρ p_μ(c + e_ν) − 2 pr_ν(c + e_ν) + pr_ν(c + e_μ + e_ν)` turned into a bound;
* `climb` — six raisings, the chain of `DoublingSharp.rec_zero_sharp` with the coordinates
  reversed: `Δ x 0 ≤ 1/1000 ⇒ p_0(0,2,2,2) ≤ 70 Δ x 0`, the direction-`0` defect at time `m0` on the
  slice of sides `(L, L, L)`.

For Wilson `SU(N)`, `raised_nonneg` and `raised_sq` derive the two level-`1` facts from
`Tr K^L ≤ λ^{L − 2m} Tr K^{2m}` and `λ^L ≤ Tr K^L` (`seqFacts`, from `KernelPower.hs_iter_le` and
`KernelPower.hs_iter_decomp`); `climb_yW` assembles `Climb` for the corner function `yW`. Then:

* `gap_side` — from the seed `16 log Z(n) − log Z(2n) ≤ 1/1000`, on the slice of side `L` with
  `2^(a+1) n ≤ L ≤ 2^(a+3) n`, the transfer has a unit top eigenvector and
  `‖K^n f‖ ≤ ½ ‖K‖^n ‖f‖` off it;
* `gap_even_side` — the same at every even `L ≥ 2n`;
* `cluster_even_side`, `connTorus_even_side` — the clustering of Theorem 4.47 at every even
  `L ≥ 2n`;
* `familyGap_sides`, `familyCluster_sides` — Theorems 4.46 and 4.47 along a family whose sides are
  even and at least twice the seed side;
* `schedule_side` and `scheduleCluster` — the OpenAI schedule `period p · den m`, `4 ∣ period p`,
  with seed side `2 den m` and spacing `1 / den m`: every torus of the schedule, rate `log 2 / 2`.

The seed itself is untouched. Even sides `n < L < 2n` and odd sides are not reached.
-/

namespace MassGap.OpenAIBridgeSides

open Real MassGap.DoublingRecursion

/-! ## 1. The mixed-ratio climb -/

/-- The defect of a step of ratio `ρ` in direction `μ` at corner `v`:
`pr x ρ μ v = ρ x(v) − x(v + e_μ)`. At `ρ = 2` it is `DoublingRecursion.p`.

DERIVED: no numeral beyond the structural ones; `4` is the spacetime dimension. -/
def pr (x : Pt → ℝ) (ρ : ℝ) (μ : Fin 4) (v : Pt) : ℝ := ρ * x v - x (v + E μ)

/-- The three facts of the mixed-ratio climb on the corners `{0,1,2}^4`: steps out of level `0` have
ratio `2` and steps out of level `1` have ratio `ρ`. `nn0`: the level-`0` defect is nonnegative;
`nn1`: the level-`1` defect is nonnegative; `sq`: a level-`0` defect at most `1/10` bounds the
level-`1` defect after it by `5` times its square.

DERIVED: `10` is the threshold below which `raised_sq` gives the constant `5`; `5` bounds
`4 · (10/9)²`, the ratio bound `4` times the square of `exp d − 1 ≤ (10/9) d` at `d ≤ 1/10`. -/
structure Climb (x : Pt → ℝ) (ρ : ℝ) : Prop where
  nn0 : ∀ μ v, (∀ i, v i ≤ 2) → v μ = 0 → 0 ≤ p x μ v
  nn1 : ∀ μ v, (∀ i, v i ≤ 2) → v μ = 1 → 0 ≤ pr x ρ μ v
  sq : ∀ μ v, (∀ i, v i ≤ 2) → v μ = 0 → p x μ v ≤ 1 / 10 →
    pr x ρ μ (v + E μ) ≤ 5 * p x μ v ^ 2

variable {x : Pt → ℝ} {ρ : ℝ}

/-- **The mixed corner step.** With `μ` at level `0` and `ν` at level `1` at `c_ν`, the identity
`p_μ(c_ν + e_ν) = ρ p_μ(c_ν) − 2 pr_ν(c_ν) + pr_ν(c_ν + e_μ)` and the three facts of `Climb` give
`p_μ(c_ν + e_ν) ≤ 4A + 5B²` from `p_μ(c_ν) ≤ A` and `p_ν(c_μ) ≤ B ≤ 1/10`, at ratio `ρ ≤ 4`.

DERIVED: `10` is the threshold of `Climb.sq`; `5` its constant. -/
theorem stepC (hx : Climb x ρ) (hρ4 : ρ ≤ 4) (μ ν : Fin 4) (cμ cν cμν cνν cμνν : Pt)
    (bμ : ∀ i, cμ i ≤ 2) (bν : ∀ i, cν i ≤ 2) (e1 : cν μ = 0) (e2 : cν ν = 1) (e3 : cμ ν = 0)
    (h3 : cν + E μ = cμν) (h4 : cμ + E ν = cμν) (h5 : cν + E ν = cνν)
    (h6 : cμν + E ν = cμνν) (h7 : cνν + E μ = cμνν) {A B : ℝ} (hB : B ≤ 1 / 10)
    (hA : 2 * x cν - x cμν ≤ A) (hBb : 2 * x cμ - x cμν ≤ B) :
    2 * x cνν - x cμνν ≤ 4 * A + 5 * B ^ 2 := by
  have nA : 0 ≤ 2 * x cν - x cμν := by
    have := hx.nn0 μ cν bν e1; rwa [p, h3] at this
  have nB : 0 ≤ 2 * x cμ - x cμν := by
    have := hx.nn0 ν cμ bμ e3; rwa [p, h4] at this
  have n1 : 0 ≤ ρ * x cν - x cνν := by
    have := hx.nn1 ν cν bν e2; rwa [pr, h5] at this
  have s1 : ρ * x cμν - x cμνν ≤ 5 * (2 * x cμ - x cμν) ^ 2 := by
    have := hx.sq ν cμ bμ e3 (by rw [p, h4]; linarith)
    rwa [h4, pr, h6, p, h4] at this
  have _ := h7
  have key : 2 * x cνν - x cμνν
      = ρ * (2 * x cν - x cμν) - 2 * (ρ * x cν - x cνν) + (ρ * x cμν - x cμνν) := by ring
  have hsq : (2 * x cμ - x cμν) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ nB hBb 2
  have hm : ρ * (2 * x cν - x cμν) ≤ 4 * (2 * x cν - x cμν) := mul_le_mul_of_nonneg_right hρ4 nA
  rw [key]
  linarith

/-- **The mixed-ratio climb.** Under `Climb x ρ` with `ρ ≤ 4`, `Δ x 0 = 16 x(0) − x(𝟙) ≤ 1/1000`
gives `p_0(0,2,2,2) = 2 x(0,2,2,2) − x(1,2,2,2) ≤ 70 Δ x 0`: the direction-`0` defect at level `0`
with the three other coordinates at level `2`. Six raisings by `stepC` from the four one-direction
defects at the corners next to `𝟙`, each at most `Δ`, through the bounds `(401/100) Δ`, `17 Δ` and
`70 Δ`, each below `1/10`.

DERIVED: `16` is `2⁴`, the volume ratio of one doubling in four directions (`Δ`); `1000` is the seed
threshold of `DoublingSharp.wilson_gap_sharp`; `70` is the third raising bound,
`4 · 17 + 5 · 17² / 1000 ≤ 70`, after `4 · (401/100) + 5 · (401/100)² / 1000 ≤ 17` and
`4 + 5 / 1000 ≤ 401/100`. -/
theorem climb (hx : Climb x ρ) (hρ4 : ρ ≤ 4) (hD : Δ x ![0, 0, 0, 0] ≤ 1 / 1000) :
    p x 0 ![0, 2, 2, 2] ≤ 70 * Δ x ![0, 0, 0, 0] := by
  have e00 : (![0, 0, 0, 0] : Pt) + one = ![1, 1, 1, 1] := by decide
  have e0 : (![0, 2, 2, 2] : Pt) + E 0 = ![1, 2, 2, 2] := by decide
  rw [p, e0]
  simp only [Δ, e00] at hD ⊢
  set D := 16 * x ![0, 0, 0, 0] - x ![1, 1, 1, 1] with hDdef
  have nn : ∀ (μ : Fin 4) (v u : Pt), (∀ i, v i ≤ 2) → v μ = 0 → v + E μ = u →
      0 ≤ 2 * x v - x u := by
    intro μ v u hb h0 h
    have := hx.nn0 μ v hb h0
    rwa [p, h] at this
  have a1 := nn 0 ![0, 0, 0, 0] ![1, 0, 0, 0] (by decide) (by decide) (by decide)
  have a2 := nn 1 ![1, 0, 0, 0] ![1, 1, 0, 0] (by decide) (by decide) (by decide)
  have a3 := nn 2 ![1, 1, 0, 0] ![1, 1, 1, 0] (by decide) (by decide) (by decide)
  have a4 := nn 3 ![1, 1, 1, 0] ![1, 1, 1, 1] (by decide) (by decide) (by decide)
  have b3 := nn 3 ![1, 1, 0, 0] ![1, 1, 0, 1] (by decide) (by decide) (by decide)
  have b4 := nn 2 ![1, 1, 0, 1] ![1, 1, 1, 1] (by decide) (by decide) (by decide)
  have c2 := nn 2 ![1, 0, 0, 0] ![1, 0, 1, 0] (by decide) (by decide) (by decide)
  have c3 := nn 3 ![1, 0, 1, 0] ![1, 0, 1, 1] (by decide) (by decide) (by decide)
  have c4 := nn 1 ![1, 0, 1, 1] ![1, 1, 1, 1] (by decide) (by decide) (by decide)
  have d1 := nn 1 ![0, 0, 0, 0] ![0, 1, 0, 0] (by decide) (by decide) (by decide)
  have d2 := nn 2 ![0, 1, 0, 0] ![0, 1, 1, 0] (by decide) (by decide) (by decide)
  have d3 := nn 3 ![0, 1, 1, 0] ![0, 1, 1, 1] (by decide) (by decide) (by decide)
  have d4 := nn 0 ![0, 1, 1, 1] ![1, 1, 1, 1] (by decide) (by decide) (by decide)
  have hD0 : 0 ≤ D := by linarith
  have B1 : 2 * x ![1, 1, 1, 0] - x ![1, 1, 1, 1] ≤ D := by linarith
  have B2 : 2 * x ![1, 1, 0, 1] - x ![1, 1, 1, 1] ≤ D := by linarith
  have B3 : 2 * x ![1, 0, 1, 1] - x ![1, 1, 1, 1] ≤ D := by linarith
  have B4 : 2 * x ![0, 1, 1, 1] - x ![1, 1, 1, 1] ≤ D := by linarith
  have k1 : 4 * D + 5 * D ^ 2 ≤ 401 / 100 * D := by nlinarith
  have S1 : 2 * x ![1, 1, 0, 2] - x ![1, 1, 1, 2] ≤ 401 / 100 * D :=
    (stepC hx hρ4 2 3 ![1, 1, 1, 0] ![1, 1, 0, 1] ![1, 1, 1, 1] ![1, 1, 0, 2] ![1, 1, 1, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by linarith) B2 B1).trans k1
  have S2 : 2 * x ![1, 0, 1, 2] - x ![1, 1, 1, 2] ≤ 401 / 100 * D :=
    (stepC hx hρ4 1 3 ![1, 1, 1, 0] ![1, 0, 1, 1] ![1, 1, 1, 1] ![1, 0, 1, 2] ![1, 1, 1, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by linarith) B3 B1).trans k1
  have S4 : 2 * x ![0, 1, 1, 2] - x ![1, 1, 1, 2] ≤ 401 / 100 * D :=
    (stepC hx hρ4 0 3 ![1, 1, 1, 0] ![0, 1, 1, 1] ![1, 1, 1, 1] ![0, 1, 1, 2] ![1, 1, 1, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by linarith) B4 B1).trans k1
  have k2 : 4 * (401 / 100 * D) + 5 * (401 / 100 * D) ^ 2 ≤ 17 * D := by nlinarith
  have S3 : 2 * x ![1, 0, 2, 2] - x ![1, 1, 2, 2] ≤ 17 * D :=
    (stepC hx hρ4 1 2 ![1, 1, 0, 2] ![1, 0, 1, 2] ![1, 1, 1, 2] ![1, 0, 2, 2] ![1, 1, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by linarith) S2 S1).trans k2
  have S6 : 2 * x ![0, 1, 2, 2] - x ![1, 1, 2, 2] ≤ 17 * D :=
    (stepC hx hρ4 0 2 ![1, 1, 0, 2] ![0, 1, 1, 2] ![1, 1, 1, 2] ![0, 1, 2, 2] ![1, 1, 2, 2]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by linarith) S4 S1).trans k2
  have k3 : 4 * (17 * D) + 5 * (17 * D) ^ 2 ≤ 70 * D := by nlinarith
  exact (stepC hx hρ4 0 1 ![1, 0, 2, 2] ![0, 1, 2, 2] ![1, 1, 2, 2] ![0, 2, 2, 2] ![1, 2, 2, 2]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by linarith) S6 S3).trans k3

/-! ## 2. The level-one facts from the trace sequence -/

/-- **Level-one nonnegativity.** For a trace sequence with the four trace facts at `m`
(`PowerFacts a λ s m`), an even time `L ≥ 2m` with `a L ≤ λ^{L−2m} a(2m)` and `λ^L ≤ a L`, and the
ratio `ρ = L / 2m ≥ 1`: `ρ log a(2m) − log a(L) ≥ (ρ − 1)(log a(2m) − 2m log λ) ≥ 0`.

DERIVED: no numeral beyond the structural ones; `2` is the doubled time of the trace facts. -/
theorem raised_nonneg {a : ℕ → ℝ} {lam s : ℝ} {m L : ℕ}
    (h : DoublingPower.PowerFacts a lam s m) (hL : 2 * m ≤ L) (hup : a L ≤ lam ^ (L - 2 * m) * a (2 * m)) (hlow : lam ^ L ≤ a L)
    (hρ : ρ * (2 * (m : ℝ)) = L) (hρ1 : 1 ≤ ρ) :
    0 ≤ ρ * log (a (2 * m)) - log (a L) := by
  have hl := h.lam_pos
  have hA := h.a2_pos
  have hB : 0 < a L := lt_of_lt_of_le (pow_pos hl L) hlow
  have h1 : log (a L) ≤ ((L - 2 * m : ℕ) : ℝ) * log lam + log (a (2 * m)) := by
    have := log_le_log hB hup
    rwa [log_mul (pow_pos hl _).ne' hA.ne', log_pow] at this
  have h2 : ((2 * m : ℕ) : ℝ) * log lam ≤ log (a (2 * m)) := by
    have := log_le_log (pow_pos hl _) h.dbl_ge
    rwa [log_pow] at this
  have hc : ((L - 2 * m : ℕ) : ℝ) = ρ * (2 * (m : ℝ)) - 2 * m := by
    rw [Nat.cast_sub hL, hρ]; norm_num
  push_cast at h2
  rw [hc] at h1
  have hprod := mul_nonneg (sub_nonneg.2 hρ1) (sub_nonneg.2 h2)
  have e : (ρ - 1) * (log (a (2 * m)) - 2 * (m : ℝ) * log lam)
      = ρ * log (a (2 * m)) - ((ρ * (2 * (m : ℝ)) - 2 * m) * log lam + log (a (2 * m))) := by
    ring
  rw [e] at hprod
  linarith

/-- **Level-zero squaring into a ratio-`ρ` step.** Under `PowerFacts a λ s m`, `λ^L ≤ a L`,
`ρ = L / 2m ∈ [0, 4]` and `defect a m ≤ 1/10`: `ρ log a(2m) − log a(L) ≤ ρ s² ≤ 5 · (defect a m)²`,
by `a(2m) ≤ λ^{2m}(1 + s²)` and `s ≤ exp(defect) − 1 ≤ (10/9) defect`.

DERIVED: `10` is the threshold at which `exp d ≤ 1/(1 − d) ≤ 10/9`; `5` bounds `4 · (10/9)² = 400/81`,
with `4` the largest ratio. -/
theorem raised_sq {a : ℕ → ℝ} {lam s : ℝ} {m L : ℕ}
    (h : DoublingPower.PowerFacts a lam s m) (hlow : lam ^ L ≤ a L) (hρ : ρ * (2 * (m : ℝ)) = L) (hρ0 : 0 ≤ ρ) (hρ4 : ρ ≤ 4)
    (hd : DoublingPower.defect a m ≤ 1 / 10) :
    ρ * log (a (2 * m)) - log (a L) ≤ 5 * DoublingPower.defect a m ^ 2 := by
  have hl := h.lam_pos
  have hs0 := h.s_nonneg
  have h1 : (L : ℝ) * log lam ≤ log (a L) := by
    have := log_le_log (pow_pos hl _) hlow
    rwa [log_pow] at this
  have h2 : log (a (2 * m)) ≤ ((2 * m : ℕ) : ℝ) * log lam + s ^ 2 := by
    have := log_le_log h.a2_pos h.dbl_le_sq
    rw [log_mul (pow_pos hl _).ne' (by positivity), log_pow] at this
    have := log_le_sub_one_of_pos (show 0 < 1 + s ^ 2 by positivity)
    linarith
  push_cast at h2
  have h3 : ρ * log (a (2 * m)) ≤ ρ * (2 * (m : ℝ)) * log lam + ρ * s ^ 2 := by
    calc ρ * log (a (2 * m)) ≤ ρ * (2 * (m : ℝ) * log lam + s ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hρ0
      _ = ρ * (2 * (m : ℝ)) * log lam + ρ * s ^ 2 := by ring
  rw [hρ] at h3
  set d := DoublingPower.defect a m
  have hd0 : 0 ≤ d := DoublingPower.defect_nonneg h
  have hex := DoublingPower.excited_le h
  have hexp : Real.exp d ≤ 10 / 9 := by
    have := exp_bound_div_one_sub_of_interval hd0 (by linarith)
    calc Real.exp d ≤ 1 / (1 - d) := this
      _ ≤ 10 / 9 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hm : Real.exp d - 1 ≤ d * Real.exp d := by
    have e1 := Real.add_one_le_exp (-d)
    have e2 : Real.exp (-d) * Real.exp d = 1 := by rw [← Real.exp_add]; simp
    have e3 := Real.exp_pos d
    nlinarith
  have hs : s ≤ d * (10 / 9) := by
    calc s ≤ Real.exp d - 1 := hex
      _ ≤ d * Real.exp d := hm
      _ ≤ d * (10 / 9) := mul_le_mul_of_nonneg_left hexp hd0
  have hs2 : s ^ 2 ≤ (d * (10 / 9)) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have hρs : ρ * s ^ 2 ≤ 4 * s ^ 2 := mul_le_mul_of_nonneg_right hρ4 (sq_nonneg s)
  nlinarith [sq_nonneg d]

/-! ## 3. Wilson `SU(N)`: the corner function on the levels `m0, 2 m0, L` -/

open MeasureTheory MassGap.RectWilson MassGap.RectTransfer MassGap.KernelPower
  MassGap.DoublingWilson MassGap.SlabKernelOperator

/-- The side at level `j`: `m0` at level `0`, `2 m0` at level `1`, `L` above.

DERIVED: no numeral beyond the structural ones; `2` is the doubling from level `0` to level `1`. -/
def lev (m0 L j : ℕ) : ℕ := if j = 0 then m0 else if j = 1 then 2 * m0 else L

/-- The extents of the torus at corner `v`: side `lev m0 L (v i)` in direction `i`.

DERIVED: `4` is the spacetime dimension. -/
def sides (m0 L : ℕ) (v : Pt) : Fin 4 → ℕ := fun i => lev m0 L (v i)

/-- The corner function: `log ZR` of the Wilson torus at corner `v`.

DERIVED: no numeral. -/
noncomputable def yW (N m0 L : ℕ) (β : ℝ) (v : Pt) : ℝ := Real.log (ZR (sides m0 L v) N β)

/-- A step in direction `μ` leaves the slice transverse to `μ` unchanged.

DERIVED: `4` is the spacetime dimension. -/
theorem tr_sides_add (m0 L : ℕ) (v : Pt) (μ : Fin 4) :
    tr (sides m0 L (v + E μ)) μ = tr (sides m0 L v) μ := by
  funext j
  simp only [tr, sides, Pi.add_apply, E_apply, if_neg (Ne.symm j.2), add_zero]

/-- A step in direction `μ` raises the level of direction `μ` by one.

DERIVED: `1` is the step; `4` the spacetime dimension. -/
theorem add_E_self (v : Pt) (μ : Fin 4) : (v + E μ) μ = v μ + 1 := by
  simp only [Pi.add_apply, E_apply, if_true]

variable {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)

include hN hβ in
/-- **The trace facts on one slice, at the times `2j`, `4j` and `L`.** For the transfer kernel of
the slice `T`, `j ≥ 1` and an even `L ≥ 4j`: the four trace facts at `2j` with `λ = ‖K‖`, and
`F L ≤ λ^{L − 4j} F(4j)` (`hs_iter_le`), `λ^L ≤ F L` (`hs_iter_decomp`).

DERIVED: no numeral beyond the structural ones; `2` is the even time and its doubling, and the
`L²` exponent of `hs`. -/
theorem seqFacts (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (j : ℕ) (hj : 1 ≤ j) (L : ℕ)
    (hLe : Even L) (hL : 2 * (2 * j) ≤ L) :
    ∃ lam s : ℝ, DoublingPower.PowerFacts (F N β μ T) lam s (2 * j) ∧
      F N β μ T L ≤ lam ^ (L - 2 * (2 * j)) * F N β μ T (2 * (2 * j)) ∧ lam ^ L ≤ F N β μ T L := by
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hS μ T N) (continuous_kT β) zero_le_one (abs_kT_le hN hβ)
      (kT_symm β) (K_pos hN hβ μ T)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_pos hN hβ μ T]
  have hpf := powerFacts (μ := hS μ T N) (continuous_kT β).measurable zero_le_one
    (abs_kT_le hN hβ) (kT_symm β) hφm hφb hφ1 heig hc hc0 j hj
  refine ⟨|c|, _, hpf, ?_, ?_⟩
  · obtain ⟨L', rfl⟩ := hLe
    unfold F traceSeq
    have e1 : (L' + L') / 2 - 1 = (2 * j - 1) + (L' - 2 * j) := by omega
    have e2 : 2 * (2 * j) / 2 - 1 = 2 * j - 1 := by omega
    have e3 : L' + L' - 2 * (2 * j) = 2 * (L' - 2 * j) := by omega
    rw [e1, e2, e3, hc]
    exact hs_iter_le (μ := hS μ T N) (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
      (2 * j - 1) (L' - 2 * j)
  · obtain ⟨L', rfl⟩ := hLe
    unfold F traceSeq
    rw [hs_iter_decomp (μ := hS μ T N) (bdd_kT hN hβ) (kT_symm β) hφm hφb hφ1 heig
      ((L' + L') / 2 - 1)]
    have e : (L' + L') / 2 - 1 + 1 = L' := by omega
    rw [e]
    have hpow : c ^ (2 * L') = |c| ^ (L' + L') := by
      rw [pow_mul, ← sq_abs, ← pow_mul]; ring_nf
    rw [hpow]
    linarith [hs_nonneg (μ := hS μ T N) (iter (hS μ T N) (rem (kT μ T N β) c φ) ((L' + L') / 2 - 1))]

include hN hβ in
/-- At every corner and in every direction `μ`, `yW` is the logarithm of the trace sequence of the
slice transverse to `μ` at the level of `μ`, when the three levels are even and positive.

DERIVED: no numeral beyond the structural ones; `2` is the even side. -/
theorem yW_at {j0 L : ℕ} (hj0 : 1 ≤ j0) (hLe : Even L) (hL2 : 2 ≤ L) (v : Pt) (μ : Fin 4) :
    yW N (2 * j0) L β v
      = Real.log (F N β μ (tr (sides (2 * j0) L v) μ) (lev (2 * j0) L (v μ))) := by
  have hev : ∃ i, 1 ≤ i ∧ sides (2 * j0) L v μ = 2 * i := by
    show ∃ i, 1 ≤ i ∧ lev (2 * j0) L (v μ) = 2 * i
    unfold lev
    split_ifs
    · exact ⟨j0, hj0, rfl⟩
    · exact ⟨2 * j0, by omega, rfl⟩
    · obtain ⟨L', hL'⟩ := hLe; exact ⟨L', by omega, by omega⟩
  obtain ⟨i, hi, hiL⟩ := hev
  unfold yW F
  rw [ZR_eq_traceSeq (μ := μ) hN hβ i hi hiL]
  rfl

include hN hβ in
/-- One step in direction `μ` from `v`: the same slice at the next level.

DERIVED: `2` is the even side; `1` the step. -/
theorem yW_next {j0 L : ℕ} (hj0 : 1 ≤ j0) (hLe : Even L) (hL2 : 2 ≤ L) (v : Pt) (μ : Fin 4) :
    yW N (2 * j0) L β (v + E μ)
      = Real.log (F N β μ (tr (sides (2 * j0) L v) μ) (lev (2 * j0) L (v μ + 1))) := by
  rw [yW_at hN hβ hj0 hLe hL2 (v + E μ) μ, tr_sides_add, add_E_self]

include hN hβ in
/-- **`Climb` for the Wilson corner function.** With levels `2j0`, `4j0`, `L` (`j0 ≥ 1`, `L` even,
`L ≥ 4j0`) and the ratio `ρ = L / 4j0 ∈ [1, 4]`, `yW N (2j0) L β` satisfies the three facts of
`Climb`: level-`0` nonnegativity is `DoublingPower.defect_nonneg`, level-`1` nonnegativity is
`raised_nonneg`, and the squaring is `raised_sq`, each on the trace sequence of the slice of
`seqFacts`.

DERIVED: no numeral beyond the structural ones; `2` is the doubled side and `4` the largest
ratio. -/
theorem climb_yW {j0 L : ℕ} (hj0 : 1 ≤ j0) (hLe : Even L) (hL4 : 2 * (2 * j0) ≤ L)
    (hρ : ρ * (2 * ((2 * j0 : ℕ) : ℝ)) = L) (hρ1 : 1 ≤ ρ) (hρ4 : ρ ≤ 4) :
    Climb (yW N (2 * j0) L β) ρ := by
  have hL2 : 2 ≤ L := by omega
  have l0 : lev (2 * j0) L 0 = 2 * j0 := by simp [lev]
  have l1 : lev (2 * j0) L (0 + 1) = 2 * (2 * j0) := by simp [lev]
  have l1' : lev (2 * j0) L 1 = 2 * (2 * j0) := by simp [lev]
  have l2 : lev (2 * j0) L (1 + 1) = L := by simp [lev]
  refine ⟨fun μ v _ h0 => ?_, fun μ v _ h1 => ?_, fun μ v _ h0 hd => ?_⟩
  · obtain ⟨lam, s, hpf, -, -⟩ := seqFacts hN hβ μ (tr (sides (2 * j0) L v) μ) j0 hj0 L hLe hL4
    have := DoublingPower.defect_nonneg hpf
    rw [p, yW_at hN hβ hj0 hLe hL2 v μ, yW_next hN hβ hj0 hLe hL2 v μ, h0, l0, l1]
    exact this
  · obtain ⟨lam, s, hpf, hup, hlow⟩ :=
      seqFacts hN hβ μ (tr (sides (2 * j0) L v) μ) j0 hj0 L hLe hL4
    rw [pr, yW_at hN hβ hj0 hLe hL2 v μ, yW_next hN hβ hj0 hLe hL2 v μ, h1, l1', l2]
    exact raised_nonneg hpf hL4 hup hlow hρ hρ1
  · obtain ⟨lam, s, hpf, -, hlow⟩ :=
      seqFacts hN hβ μ (tr (sides (2 * j0) L v) μ) j0 hj0 L hLe hL4
    have hpd : p (yW N (2 * j0) L β) μ v
        = DoublingPower.defect (F N β μ (tr (sides (2 * j0) L v) μ)) (2 * j0) := by
      rw [p, yW_at hN hβ hj0 hLe hL2 v μ, yW_next hN hβ hj0 hLe hL2 v μ, h0, l0, l1]; rfl
    rw [hpd] at hd ⊢
    have hv1 : (v + E μ) μ = 1 := by rw [add_E_self, h0]
    rw [pr, yW_at hN hβ hj0 hLe hL2 (v + E μ) μ, yW_next hN hβ hj0 hLe hL2 (v + E μ) μ,
      tr_sides_add, hv1, l1', l2]
    exact raised_sq hpf hlow hρ (by linarith) hρ4 hd

/-! ## 4. The gap on every even side -/

variable {n : ℕ} (hn : 2 ≤ n) (he : Even n)

/-- The slice of the cubic torus of side `L` is the slice of corner `(0,2,2,2)`.

DERIVED: `0` is the time direction; `2` the top level; `4` the spacetime dimension. -/
theorem tr_sides_top (m0 L : ℕ) :
    tr (sides m0 L ![0, 2, 2, 2]) 0 = tr (fun _ : Fin 4 => L) 0 := by
  funext j
  obtain ⟨j, hj⟩ := j
  fin_cases j
  · exact absurd rfl hj
  all_goals simp [tr, sides, lev]

/-- The base of the mixed corner lattice is the dyadic corner `a`.

DERIVED: `2` is the dyadic doubling; `0` the base level. -/
theorem sides_base (n a L : ℕ) {j0 : ℕ} (hm0 : 2 * j0 = 2 ^ a * n) :
    sides (2 * j0) L ![0, 0, 0, 0] = ext n (corner a) ∧
      sides (2 * j0) L (![0, 0, 0, 0] + one) = ext n (corner a + one) := by
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · have hv : (![0, 0, 0, 0] : Pt) i = 0 := by fin_cases i <;> rfl
    show lev (2 * j0) L ((![0, 0, 0, 0] : Pt) i) = 2 ^ (corner a i) * n
    rw [hv]
    show (if (0 : ℕ) = 0 then 2 * j0 else if (0 : ℕ) = 1 then 2 * (2 * j0) else L) = 2 ^ a * n
    rw [if_pos rfl, hm0]
  · have hv : ((![0, 0, 0, 0] : Pt) + one) i = 1 := by fin_cases i <;> rfl
    have hc : (corner a + one) i = a + 1 := by
      rw [Pi.add_apply]; show a + one i = a + 1; congr 1; fin_cases i <;> rfl
    show lev (2 * j0) L (((![0, 0, 0, 0] : Pt) + one) i) = 2 ^ ((corner a + one) i) * n
    rw [hv, hc]
    show (if (1 : ℕ) = 0 then 2 * j0 else if (1 : ℕ) = 1 then 2 * (2 * j0) else L)
      = 2 ^ (a + 1) * n
    rw [if_neg one_ne_zero, if_pos rfl, hm0, pow_succ]
    ring

include hN hβ hn he in
/-- **The gap of the seed on the slice of side `L`, `2^(a+1) n ≤ L ≤ 2^(a+3) n`.** If one torus of
even side `n ≥ 2` has `16 log Z(n⁴) − log Z((2n)⁴) ≤ 1/1000` at `β ≥ 0`, then for every `a` and
every even `L` with `2^(a+1) n ≤ L ≤ 2^(a+3) n`, the transfer operator `K` in direction `0` of the
cubic torus of side `L` (on `L²` of the spatial links of one slice, sides `(L, L, L)`, axis links
integrated out) has a unit eigenvector `ψ` with eigenvalue of modulus `‖K‖`, and every `f ⊥ ψ`
satisfies `‖K^n f‖ ≤ ½ ‖K‖^n ‖f‖`.

`iterate_sharp` bounds `250 Δ` at the dyadic corner `a` by `(1/4)^(2^a)`; that corner is the base of
the mixed lattice on levels `2^a n`, `2^(a+1) n`, `L` (`sides_base`); `climb` at the ratio
`ρ = L / 2^(a+1) n ∈ [1, 4]` bounds the direction-`0` defect at time `2^a n` on the slice of side
`L` by `70 Δ`; the excited weight there is at most `2 · 70 (1/4)^(2^a) / 250 ≤ (1/2)^(2^a)`, and
`KernelGap.gap_of_excited` at `q = a` gives the gap.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `3` is the exponent of the largest
ratio `4 = 2^(3−1)` above the level `2^(a+1) n`; `2` the doubled side, the least seed side, the `L²`
exponent and the contraction `1/2`; `0` the time direction of the slice and the sign of the coupling;
`1` the unit norm, the kernel bound and the first level. -/
theorem gap_side
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (a L : ℕ) (hLe : Even L) (hlo : 2 ^ (a + 1) * n ≤ L) (hhi : L ≤ 2 ^ (a + 3) * n) :
    ∃ ψ : Lp ℝ 2 (hS 0 (tr (fun _ : Fin 4 => L) 0) N), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, |c| = ‖kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1
          (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
          (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)‖ ∧
      kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1 (continuous_kT β).measurable zero_le_one
          (abs_kT_le hN hβ) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)
          (hS 0 (tr (fun _ : Fin 4 => L) 0) N) ψ = c • ψ ∧
      ∀ f : Lp ℝ 2 (hS 0 (tr (fun _ : Fin 4 => L) 0) N), inner ℝ f ψ = 0 →
        ‖((kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)
          (hS 0 (tr (fun _ : Fin 4 => L) 0) N)) ^ n) f‖
          ≤ 1 / 2 * ‖kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1
            (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
            (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)‖ ^ n
            * ‖f‖ := by
  set T := tr (fun _ : Fin 4 => L) 0 with hTdef
  -- the dyadic climb to corner `a`
  have hfr := factRep hN hβ hn he
  have hp := DoublingPower.positive_of_facts hfr
  have hxs := DoublingSharp.positiveS_of_facts hfr
  have hΔ0 : Δ (xW N n β) (corner 0) ≤ 1 / 1000 := by rw [Δ_corner0]; exact h0
  have hit := DoublingSharp.iterate_sharp hxs hp (by linarith) a
  have hq1 : ((1 : ℝ) / 4) ^ (2 ^ a) ≤ 1 / 4 := by
    have := pow_le_pow_of_le_one (a := (1 : ℝ) / 4) (by norm_num) (by norm_num)
      (Nat.one_le_two_pow (n := a))
    simpa using this
  have hq0 : 0 ≤ ((1 : ℝ) / 4) ^ (2 ^ a) := by positivity
  -- the levels
  obtain ⟨n', hn'⟩ := he
  set j0 := 2 ^ a * n' with hj0def
  have hj0 : 1 ≤ j0 := by
    have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have h2 : 1 ≤ n' := by omega
    rw [hj0def]; exact Nat.mul_le_mul h1 h2
  have hm0 : 2 * j0 = 2 ^ a * n := by rw [hj0def, hn']; ring
  have hL4 : 2 * (2 * j0) ≤ L := by
    have : 2 * (2 * j0) = 2 ^ (a + 1) * n := by rw [hm0, pow_succ]; ring
    omega
  have hL8 : L ≤ 4 * (2 * (2 * j0)) := by
    have : 4 * (2 * (2 * j0)) = 2 ^ (a + 3) * n := by rw [hm0, pow_add]; ring
    omega
  have hM : (0 : ℝ) < 2 * ((2 * j0 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((2 * j0 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * j0)
    linarith
  set ρ : ℝ := (L : ℝ) / (2 * ((2 * j0 : ℕ) : ℝ)) with hρdef
  have hρ : ρ * (2 * ((2 * j0 : ℕ) : ℝ)) = L := by rw [hρdef]; field_simp
  have hρ1 : 1 ≤ ρ := by
    rw [hρdef, le_div_iff₀ hM, one_mul]
    exact_mod_cast hL4
  have hρ4 : ρ ≤ 4 := by
    rw [hρdef, div_le_iff₀ hM]
    exact_mod_cast hL8
  have hx := climb_yW hN hβ hj0 hLe hL4 hρ hρ1 hρ4
  -- the base of the mixed lattice is the dyadic corner `a`
  have hbase : Δ (yW N (2 * j0) L β) ![0, 0, 0, 0] = Δ (xW N n β) (corner a) := by
    obtain ⟨s0, s1⟩ := sides_base n a L hm0
    unfold Δ yW xW
    rw [s0, s1]
  have hD : Δ (yW N (2 * j0) L β) ![0, 0, 0, 0] ≤ 1 / 1000 := by rw [hbase]; linarith
  have hcl := climb hx hρ4 hD
  rw [hbase] at hcl
  -- the eigenvector on the slice of side `L`
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hS 0 T N) (continuous_kT β) zero_le_one (abs_kT_le hN hβ)
      (kT_symm β) (K_pos hN hβ 0 T)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_pos hN hβ 0 T]
  have hpf : DoublingPower.PowerFacts (F N β 0 T) |c|
      (excited (hS 0 T N) (kT 0 T N β) c φ j0) (2 * j0) :=
    powerFacts (μ := hS 0 T N) (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
      (kT_symm β) hφm hφb hφ1 heig hc hc0 j0 hj0
  have hL2 : 2 ≤ L := by omega
  have hpd : p (yW N (2 * j0) L β) 0 ![0, 2, 2, 2] = DoublingPower.defect (F N β 0 T) (2 * j0) := by
    have hv : (![0, 2, 2, 2] : Pt) 0 = 0 := rfl
    have l0 : lev (2 * j0) L 0 = 2 * j0 := by simp [lev]
    have l1 : lev (2 * j0) L (0 + 1) = 2 * (2 * j0) := by simp [lev]
    rw [p, yW_at hN hβ hj0 hLe hL2 ![0, 2, 2, 2] 0, yW_next hN hβ hj0 hLe hL2 ![0, 2, 2, 2] 0,
      tr_sides_top, hv, l0, l1]
    rfl
  rw [hpd] at hcl
  have hd14 : DoublingPower.defect (F N β 0 T) (2 * j0) ≤ 1 / 4 := by nlinarith
  have hexc0 := DoublingPower.excited_le_two_defect hpf hd14
  have hhalf : ((1 : ℝ) / 4) ^ (2 ^ a) ≤ (1 / 2) ^ (2 ^ a) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hexc : excited (hS 0 T N) (kT 0 T N β) c φ j0 ≤ (1 / 2) ^ (2 ^ a) := by nlinarith
  have hidx : 2 ^ a * n / 2 = j0 := by rw [← hm0]; omega
  refine ⟨KernelGap.vac (μ := hS 0 T N) hφm hφb, KernelGap.norm_vac hφm hφb hφ1, c, hc,
    KernelGap.K_vac _ _ _ hφm hφb heig, fun f hf => ?_⟩
  exact KernelGap.gap_of_excited (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
    (kT_symm β) hφm hφb hφ1 heig hc hc0 a n (by omega) ⟨n', hn'⟩ (by rw [hidx]; exact hexc) f hf

/-- Every `L ≥ 2n` lies in a window `2^(a+1) n ≤ L ≤ 2^(a+3) n`, at `a = ⌊log₂ (L / 2n)⌋`.

DERIVED: `3` is the exponent of `gap_side`'s upper end; `2` the base of the logarithm and the
doubled side. -/
theorem exists_window {n L : ℕ} (hn : 1 ≤ n) (hL : 2 * n ≤ L) :
    ∃ a : ℕ, 2 ^ (a + 1) * n ≤ L ∧ L ≤ 2 ^ (a + 3) * n := by
  set r := L / (2 * n) with hr
  have h2n : 0 < 2 * n := by omega
  have hr1 : 1 ≤ r := (Nat.le_div_iff_mul_le h2n).2 (by omega)
  refine ⟨Nat.log 2 r, ?_, ?_⟩
  · have h1 := Nat.pow_log_le_self 2 (show r ≠ 0 by omega)
    have h3 : 2 ^ Nat.log 2 r * (2 * n) ≤ r * (2 * n) := Nat.mul_le_mul_right _ h1
    have h4 : r * (2 * n) ≤ L := Nat.div_mul_le_self L (2 * n)
    have e : 2 ^ (Nat.log 2 r + 1) * n = 2 ^ Nat.log 2 r * (2 * n) := by rw [pow_succ]; ring
    omega
  · have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) r
    have hdm := Nat.div_add_mod L (2 * n)
    have hmod := Nat.mod_lt L h2n
    have h5 : r + 1 ≤ 2 ^ (Nat.log 2 r + 1) := h1
    have h6 : (r + 1) * (2 * n) ≤ 2 ^ (Nat.log 2 r + 1) * (2 * n) := Nat.mul_le_mul_right _ h5
    have e : 2 ^ (Nat.log 2 r + 3) * n = 2 * (2 ^ (Nat.log 2 r + 1) * (2 * n)) := by
      rw [pow_add, pow_succ]; ring
    nlinarith

include hN hβ hn he in
/-- **The gap of the seed on the cubic torus of every even side `L ≥ 2n`.** If one torus of even
side `n ≥ 2` has `16 log Z(n⁴) − log Z((2n)⁴) ≤ 1/1000` at `β ≥ 0`, then for every even `L ≥ 2n`
the transfer operator `K` in direction `0` of the cubic torus of side `L` has a unit eigenvector `ψ`
with eigenvalue of modulus `‖K‖`, and `‖K^n f‖ ≤ ½ ‖K‖^n ‖f‖` for every `f ⊥ ψ`: the rate
`log 2 / n` per step of `DoublingSharp.wilson_gap_sharp`, now on every even side `L ≥ 2n` and not only
on `2^k n`. It is `gap_side` at the window of `exists_window`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `2` the doubled side, the least seed
side, the least ratio `L / n`, the `L²` exponent and the contraction `1/2`; `0` the time direction of
the slice and the sign of the coupling; `1` the unit norm and the kernel bound. -/
theorem gap_even_side
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L) :
    ∃ ψ : Lp ℝ 2 (hS 0 (tr (fun _ : Fin 4 => L) 0) N), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, |c| = ‖kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1
          (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
          (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)‖ ∧
      kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1 (continuous_kT β).measurable zero_le_one
          (abs_kT_le hN hβ) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)
          (hS 0 (tr (fun _ : Fin 4 => L) 0) N) ψ = c • ψ ∧
      ∀ f : Lp ℝ 2 (hS 0 (tr (fun _ : Fin 4 => L) 0) N), inner ℝ f ψ = 0 →
        ‖((kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)
          (hS 0 (tr (fun _ : Fin 4 => L) 0) N)) ^ n) f‖
          ≤ 1 / 2 * ‖kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1
            (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
            (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)‖ ^ n
            * ‖f‖ := by
  obtain ⟨a, hlo, hhi⟩ := exists_window (by omega : 1 ≤ n) hL
  exact gap_side hN hβ hn he h0 a L hLe hlo hhi

/-! ## 5. Clustering on every even side (Theorem 4.47) -/

open MassGap.OpenAIBridgeCluster

include hN hβ hn he in
/-- **Uniform exponential clustering of the transfer state on the cubic torus of every even side
`L ≥ 2n`, from the seed.** The slice transfer `K` of the torus of side `L` has a unit eigenvector
`ψ` with eigenvalue `c ≠ 0`, `|c| = ‖K‖`, and for every `t` and all `u`, `w`,
`|⟨u, K^t w⟩/c^t − ⟨u,ψ⟩⟨w,ψ⟩| ≤ 2 e^{−(log 2/n) t} ‖u‖ ‖w‖`. It is
`OpenAIBridgeCluster.inner_pow_div_sub_le` and `half_pow_div_le_exp` at the gap of
`gap_even_side`, as `wilson_cluster_uniform` is at the gap of `wilson_gap_sharp`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `2` the inverse of the contraction
`1/2` (the logarithm of which is the rate), the doubled side, the least seed side, the least ratio
`L / n` and the `L²` exponent; `0` the time direction of the slice, the sign of the coupling and the
excluded eigenvalue; `1` the kernel bound and the unit norm. -/
theorem cluster_even_side
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L) :
    ∃ ψ : Lp ℝ 2 (hS 0 (tr (fun _ : Fin 4 => L) 0) N), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, c ≠ 0 ∧ |c| = ‖kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1
          (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
          (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)‖ ∧
      kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1 (continuous_kT β).measurable zero_le_one
          (abs_kT_le hN hβ) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)
          (hS 0 (tr (fun _ : Fin 4 => L) 0) N) ψ = c • ψ ∧
      ∀ (t : ℕ) (u w : Lp ℝ 2 (hS 0 (tr (fun _ : Fin 4 => L) 0) N)),
        |inner ℝ u (((kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1
          (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
          (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)) ^ t) w)
            / c ^ t - inner ℝ u ψ * inner ℝ w ψ|
          ≤ 2 * Real.exp (-(Real.log 2 / n) * t) * ‖u‖ * ‖w‖ := by
  obtain ⟨ψ, hψ1, c, hc, hKψ, hgap⟩ := gap_even_side hN hβ hn he h0 L hLe hL
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_pos hN hβ 0 (tr (fun _ : Fin 4 => L) 0)]
  have hTs := fun u w => (MassGap.SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm
    (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1 (continuous_kT β).measurable zero_le_one
    (abs_kT_le hN hβ) (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT_symm β)).isSymmetric u w
  refine ⟨ψ, hψ1, c, hc0, hc, hKψ, fun t u w => ?_⟩
  have h1 := inner_pow_div_sub_le hTs hKψ hgap hψ1 hc hc0 t u w
  have h2 := half_pow_div_le_exp (n := n) (by omega) t
  calc _ ≤ _ := h1
    _ ≤ 2 * Real.exp (-(Real.log 2 / n) * t) * ‖u‖ * ‖w‖ := by
        gcongr

include hN hβ hn he in
/-- **The connected periodic trace ratio on the cubic torus of every even side `L ≥ 2n`, from the
seed.** There are a normalized bounded eigenfunction `φ` of the slice kernel `kT` of the torus of
side `L` and its eigenvalue `c ≠ 0` such that for all bounded measurable `a`, `b` of the slice
(`|a| ≤ A`, `|b| ≤ B`) and all `p + q + 2 = L`, at time separation `t = p + 1`,
`|connTorus a b p q| ≤ A B (1 + 9 σ_1) ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋)`,
`σ_1 = excited … c φ 1`. It is `OpenAIBridgeCluster.connTorus_decay` at the gap of
`gap_even_side`, as `wilson_connTorus_decay` is at the gap of `wilson_gap_sharp`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `1/2` its contraction; `9` the constant
of `connTorus_decay`; `2` the doubled side, the least seed side, the least ratio `L / n`, the square
and the offset of `iter` on the torus of `p + q + 2` steps; `0` the time direction of the slice, the
sign of the coupling and the excluded eigenvalue; `1` the offset of `iter`, the unit norm and the
one-step weight `σ_1`. -/
theorem connTorus_even_side
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L) :
    ∃ φ : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → SUN.SU N) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hS 0 (tr (fun _ : Fin 4 => L) 0) N) = 1 ∧
      (∀ z, ∫ y, kT 0 (tr (fun _ : Fin 4 => L) 0) N β z y * φ y
        ∂(hS 0 (tr (fun _ : Fin 4 => L) 0) N) = c * φ z) ∧
      ∀ (a b : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → SUN.SU N) → ℝ), Measurable a → Measurable b →
      ∀ A B : ℝ, (∀ x, |a x| ≤ A) → (∀ x, |b x| ≤ B) →
      ∀ p q : ℕ, p + q + 2 = L →
        |connTorus (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β)
            a b p q|
          ≤ A * B * (1 + 9 * excited (hS 0 (tr (fun _ : Fin 4 => L) 0) N)
              (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ 1)
            * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  obtain ⟨ψ, hψ1, c, hc, hKψ, hgap⟩ := gap_even_side hN hβ hn he h0 L hLe hL
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_pos hN hβ 0 (tr (fun _ : Fin 4 => L) 0)]
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, heig, hvac⟩ :=
    exists_eigenfun (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ) hψ1 hc0 hKψ
  refine ⟨φ, c, hc0, hφ1, heig, fun a b ham hbm A B hab hbb p q hpq => ?_⟩
  have hev : Even (p + q) := by
    obtain ⟨L', hL'⟩ := hLe
    exact ⟨L' - 1, by omega⟩
  refine connTorus_decay (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ) (kT_symm β)
    hφm hφb hφ1 heig hc (fun f hf => ?_) (by omega) hc0 ham hbm hab hbb p q hev
  rw [hvac] at hf
  exact hgap f hf

/-! ## 6. Theorems 4.46 and 4.47 along a family, and on the OpenAI schedule -/

/-- **A uniform gap along a family of tori of any even sides at least twice the seed side**
(Theorem 4.46 without the dyadic side condition). Couplings `β m p` in the normalization of the
OpenAI construction, seed sides `n m` and torus sides `Ls m p`: if `β m p ≥ 0`, and for all large `m`
the side `n m` is even and at least `2`, every `Ls m p` is even and at least `2 n m`, and the seed
holds at `(n m, β m p / 2)` for every `p`, then for all large `m` and all `p` the transfer operator
of the cubic torus of side `Ls m p` at coupling `β m p / 2` has a unit top eigenvector and its
`n m`-th power contracts the orthogonal complement by `1/2` relative to `‖K‖^(n m)`. It is
`gap_even_side` at each `(m, p)`; `OpenAIDictionary.familyGap_of_seed` is the dyadic case.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `2` is the halving of the coupling
(`action_eq_two_mul_wilsonEnergy`), the doubled side, the least seed side, the least ratio, the `L²`
exponent and the contraction `1/2`; `0` the sign of the coupling and the time direction of the slice;
`1` the unit norm and the kernel bound. -/
theorem familyGap_sides {N : ℕ} (hN : N ≠ 0) (β : ℕ → ℕ → ℝ) (n : ℕ → ℕ) (Ls : ℕ → ℕ → ℕ)
    (hβ : ∀ m p, 0 ≤ β m p)
    (hfam : ∀ᶠ m in Filter.atTop, 2 ≤ n m ∧ Even (n m) ∧ ∀ p,
      Even (Ls m p) ∧ 2 * n m ≤ Ls m p ∧
      16 * Real.log (ZR (fun _ => n m) N (β m p / 2))
        - Real.log (ZR (fun _ => 2 * n m) N (β m p / 2)) ≤ 1 / 1000) :
    ∀ᶠ m in Filter.atTop, ∀ p,
    ∃ ψ : Lp ℝ 2 (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, |c| = ‖kernelCLM (kT 0 (tr (fun _ : Fin 4 => Ls m p) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N) (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N)‖ ∧
      kernelCLM (kT 0 (tr (fun _ : Fin 4 => Ls m p) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N) (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N) ψ
        = c • ψ ∧
      ∀ f : Lp ℝ 2 (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N), inner ℝ f ψ = 0 →
        ‖((kernelCLM (kT 0 (tr (fun _ : Fin 4 => Ls m p) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N)
          (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N)) ^ n m) f‖
          ≤ 1 / 2 * ‖kernelCLM (kT 0 (tr (fun _ : Fin 4 => Ls m p) 0) N (β m p / 2)) 1
            (continuous_kT (β m p / 2)).measurable zero_le_one
            (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
            (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N)
            (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N)‖ ^ n m * ‖f‖ := by
  filter_upwards [hfam] with m hm p
  obtain ⟨hn, he, h⟩ := hm
  obtain ⟨hLe, hL, h0⟩ := h p
  exact gap_even_side hN (div_nonneg (hβ m p) zero_le_two) hn he h0 (Ls m p) hLe hL

/-- **Uniform exponential clustering along a family of tori of any even sides at least twice the
seed side, in physical units** (Theorem 4.47 without the dyadic side condition). Under the
hypotheses of `familyGap_sides` and spacings `a m > 0` with `n m · a m ≤ ℓ`: for all large `m` and
all `p`, the transfer operator `K` of the cubic torus of side `Ls m p` at coupling `β m p / 2` has a
unit eigenvector `ψ`, eigenvalue `c ≠ 0`, `|c| = ‖K‖`, and for every lag `t` and all `u`, `w`,
`|⟨u, K^t w⟩/c^t − ⟨u,ψ⟩⟨w,ψ⟩| ≤ 2 e^{−(log 2/ℓ) · t a_m} ‖u‖ ‖w‖`, uniform in `m` and `p`. It is
`cluster_even_side` with `OpenAIDictionary.physRate_le`, as `familyCluster_of_seed` is in the dyadic
case.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `2` the inverse of its contraction
(the logarithm of which is the rate), the halving of the coupling (`action_eq_two_mul_wilsonEnergy`),
the doubled side, the least seed side, the least ratio and the `L²` exponent; `0` the signs and the
time direction of the slice; `1` the kernel bound and the unit norm. -/
theorem familyCluster_sides {N : ℕ} (hN : N ≠ 0) (β : ℕ → ℕ → ℝ) (n : ℕ → ℕ) (Ls : ℕ → ℕ → ℕ)
    (hβ : ∀ m p, 0 ≤ β m p)
    (hfam : ∀ᶠ m in Filter.atTop, 2 ≤ n m ∧ Even (n m) ∧ ∀ p,
      Even (Ls m p) ∧ 2 * n m ≤ Ls m p ∧
      16 * Real.log (ZR (fun _ => n m) N (β m p / 2))
        - Real.log (ZR (fun _ => 2 * n m) N (β m p / 2)) ≤ 1 / 1000)
    (a : ℕ → ℝ) {ℓ : ℝ} (ha : ∀ m, 0 < a m) (hℓ : ∀ m, (n m : ℝ) * a m ≤ ℓ) :
    ∀ᶠ m in Filter.atTop, ∀ p,
    ∃ ψ : Lp ℝ 2 (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, c ≠ 0 ∧ |c| = ‖kernelCLM (kT 0 (tr (fun _ : Fin 4 => Ls m p) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N) (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N)‖ ∧
      kernelCLM (kT 0 (tr (fun _ : Fin 4 => Ls m p) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N) (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N) ψ
        = c • ψ ∧
      ∀ (t : ℕ) (u w : Lp ℝ 2 (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N)),
        |inner ℝ u (((kernelCLM (kT 0 (tr (fun _ : Fin 4 => Ls m p) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N)
          (hS 0 (tr (fun _ : Fin 4 => Ls m p) 0) N)) ^ t) w)
            / c ^ t - inner ℝ u ψ * inner ℝ w ψ|
          ≤ 2 * Real.exp (-(Real.log 2 / ℓ) * (t * a m)) * ‖u‖ * ‖w‖ := by
  filter_upwards [hfam] with m hm p
  obtain ⟨hn, he, h⟩ := hm
  obtain ⟨hLe, hL, h0⟩ := h p
  obtain ⟨ψ, hψ1, c, hc0, hc, hKψ, hcl⟩ :=
    cluster_even_side hN (div_nonneg (hβ m p) zero_le_two) hn he h0 (Ls m p) hLe hL
  refine ⟨ψ, hψ1, c, hc0, hc, hKψ, fun t u w => (hcl t u w).trans ?_⟩
  have hn1 : 1 ≤ n m := by omega
  have hr := OpenAIDictionary.physRate_le hn1 (ha m) (hℓ m)
  have hn0 : (0 : ℝ) < n m := by exact_mod_cast hn1
  have hrate : Real.log 2 / ℓ * (t * a m) ≤ Real.log 2 / n m * t := by
    have ht : (0 : ℝ) ≤ t * a m := mul_nonneg (Nat.cast_nonneg t) (ha m).le
    calc Real.log 2 / ℓ * (t * a m) ≤ Real.log 2 / (n m * a m) * (t * a m) :=
          mul_le_mul_of_nonneg_right hr ht
      _ = Real.log 2 / n m * t := by field_simp [(ha m).ne', hn0.ne']
  have hexp : Real.exp (-(Real.log 2 / n m) * t) ≤ Real.exp (-(Real.log 2 / ℓ) * (t * a m)) := by
    rw [Real.exp_le_exp]; linarith
  gcongr

/-- **The sides of the OpenAI schedule meet the side condition of `familyGap_sides`.** Their torus
at spacing index `m` and period index `p` has side `period p · den m` (`YM/Lattice/Scale.lean`,
`Schedule.side`), with `4 ∣ period p` (`period_four`) and `period p, den m > 0` (`Side` is `ℕ+`).
At the seed side `2 · den m`: the seed side is even and at least `2`, and the torus side is even and at
least twice the seed side, because `period p ≥ 4`.

DERIVED: `4` is the divisor of the period (`Schedule.period_four`); `2` the seed side per unit of
`den m`, the least seed side and the least ratio. -/
theorem schedule_side {P d : ℕ} (hP : 4 ∣ P) (hP0 : 0 < P) (hd : 0 < d) :
    2 ≤ 2 * d ∧ Even (2 * d) ∧ Even (P * d) ∧ 2 * (2 * d) ≤ P * d := by
  obtain ⟨r, rfl⟩ := hP
  have hr : 1 ≤ r := by omega
  refine ⟨by omega, ⟨d, by ring⟩, ⟨2 * r * d, by ring⟩, ?_⟩
  have : 4 * d ≤ 4 * r * d := by nlinarith
  linarith

/-- **Theorem 4.47 on every torus of the OpenAI schedule.** Couplings `β m p ≥ 0` in the normalization
of the OpenAI construction on the schedule `side m p = period p · den m` (`P p = period p`,
`d m = den m`; `4 ∣ P p`, `P p > 0`, `d m > 0`), spacing `a m = 1 / d m`, and the seed at the side
`2 d m` for all large `m` and every `p`. Then for all large `m` and all `p`, the transfer operator of
their torus at `β m p / 2` has a unit eigenvector `ψ`, eigenvalue `c ≠ 0`, `|c| = ‖K‖`, and
`|⟨u, K^t w⟩/c^t − ⟨u,ψ⟩⟨w,ψ⟩| ≤ 2 e^{−(log 2/2) · t a_m} ‖u‖ ‖w‖`: clustering at rate `log 2 / 2`
in physical units, uniform in the spacing and the volume, with no condition on the periods. It is
`familyCluster_sides` at `n m = 2 d m`, `ℓ = 2`, with `schedule_side`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `4` the divisor of the period
(`Schedule.period_four`); `2` the seed side per unit of `den m` and so the physical size `ℓ = 2` of
the seed torus, the inverse of the contraction, the halving of the coupling and the doubled side;
`0` the signs and the time direction of the slice; `1` the kernel bound, the unit norm and the
numerator of the spacing. -/
theorem scheduleCluster {N : ℕ} (hN : N ≠ 0) (β : ℕ → ℕ → ℝ) (P d : ℕ → ℕ)
    (hβ : ∀ m p, 0 ≤ β m p) (hP : ∀ p, 4 ∣ P p) (hP0 : ∀ p, 0 < P p) (hd : ∀ m, 0 < d m)
    (hseed : ∀ᶠ m in Filter.atTop, ∀ p,
      16 * Real.log (ZR (fun _ => 2 * d m) N (β m p / 2))
        - Real.log (ZR (fun _ => 2 * (2 * d m)) N (β m p / 2)) ≤ 1 / 1000) :
    ∀ᶠ m in Filter.atTop, ∀ p,
    ∃ ψ : Lp ℝ 2 (hS 0 (tr (fun _ : Fin 4 => P p * d m) 0) N), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, c ≠ 0 ∧ |c| = ‖kernelCLM (kT 0 (tr (fun _ : Fin 4 => P p * d m) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (fun _ : Fin 4 => P p * d m) 0) N)
          (hS 0 (tr (fun _ : Fin 4 => P p * d m) 0) N)‖ ∧
      kernelCLM (kT 0 (tr (fun _ : Fin 4 => P p * d m) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (fun _ : Fin 4 => P p * d m) 0) N)
          (hS 0 (tr (fun _ : Fin 4 => P p * d m) 0) N) ψ = c • ψ ∧
      ∀ (t : ℕ) (u w : Lp ℝ 2 (hS 0 (tr (fun _ : Fin 4 => P p * d m) 0) N)),
        |inner ℝ u (((kernelCLM (kT 0 (tr (fun _ : Fin 4 => P p * d m) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (fun _ : Fin 4 => P p * d m) 0) N)
          (hS 0 (tr (fun _ : Fin 4 => P p * d m) 0) N)) ^ t) w)
            / c ^ t - inner ℝ u ψ * inner ℝ w ψ|
          ≤ 2 * Real.exp (-(Real.log 2 / 2) * (t * (1 / (d m : ℝ)))) * ‖u‖ * ‖w‖ := by
  have hfam : ∀ᶠ m in Filter.atTop, 2 ≤ 2 * d m ∧ Even (2 * d m) ∧ ∀ p,
      Even (P p * d m) ∧ 2 * (2 * d m) ≤ P p * d m ∧
      16 * Real.log (ZR (fun _ => 2 * d m) N (β m p / 2))
        - Real.log (ZR (fun _ => 2 * (2 * d m)) N (β m p / 2)) ≤ 1 / 1000 := by
    filter_upwards [hseed] with m hm
    obtain ⟨h1, h2, -, -⟩ := schedule_side (hP 0) (hP0 0) (hd m)
    refine ⟨h1, h2, fun p => ?_⟩
    obtain ⟨-, -, h3, h4⟩ := schedule_side (hP p) (hP0 p) (hd m)
    exact ⟨h3, h4, hm p⟩
  have ha : ∀ m, 0 < 1 / (d m : ℝ) := fun m => by
    have : (0 : ℝ) < d m := by exact_mod_cast hd m
    exact one_div_pos.mpr this
  have hℓ : ∀ m, ((2 * d m : ℕ) : ℝ) * (1 / (d m : ℝ)) ≤ 2 := fun m => by
    have h0 : (d m : ℝ) ≠ 0 := by exact_mod_cast (hd m).ne'
    refine le_of_eq ?_
    push_cast
    rw [mul_assoc, mul_one_div_cancel h0, mul_one]
  exact familyCluster_sides hN β (fun m => 2 * d m) (fun m p => P p * d m) hβ hfam
    (fun m => 1 / (d m : ℝ)) ha hℓ

end MassGap.OpenAIBridgeSides

#print axioms MassGap.OpenAIBridgeSides.stepC
#print axioms MassGap.OpenAIBridgeSides.climb
#print axioms MassGap.OpenAIBridgeSides.raised_nonneg
#print axioms MassGap.OpenAIBridgeSides.raised_sq
#print axioms MassGap.OpenAIBridgeSides.tr_sides_add
#print axioms MassGap.OpenAIBridgeSides.add_E_self
#print axioms MassGap.OpenAIBridgeSides.seqFacts
#print axioms MassGap.OpenAIBridgeSides.yW_at
#print axioms MassGap.OpenAIBridgeSides.yW_next
#print axioms MassGap.OpenAIBridgeSides.climb_yW
#print axioms MassGap.OpenAIBridgeSides.tr_sides_top
#print axioms MassGap.OpenAIBridgeSides.sides_base
#print axioms MassGap.OpenAIBridgeSides.gap_side
#print axioms MassGap.OpenAIBridgeSides.exists_window
#print axioms MassGap.OpenAIBridgeSides.gap_even_side
#print axioms MassGap.OpenAIBridgeSides.cluster_even_side
#print axioms MassGap.OpenAIBridgeSides.connTorus_even_side
#print axioms MassGap.OpenAIBridgeSides.familyGap_sides
#print axioms MassGap.OpenAIBridgeSides.familyCluster_sides
#print axioms MassGap.OpenAIBridgeSides.schedule_side
#print axioms MassGap.OpenAIBridgeSides.scheduleCluster
