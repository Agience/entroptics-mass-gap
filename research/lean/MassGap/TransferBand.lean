import Mathlib
import MassGap.StallRigid
import MassGap.MassBand

/-!
# MassGap.TransferBand — what a held defect says about the transfer gap, and what it says about the tensor mass

Along a coupling tower the doubling defect is held at `u₀ > 0` at window side `2^k`. A positive defect is excited
spectral weight of the transfer operator at the window's own time (`StallRigid`, section 1:
`log(1+e) ≤ d ≤ 2 log(1+e)`). This module settles whether that weight bounds the transfer gap above by `C(u₀)/2^k`,
and what such a bound gives for the measured tensor mass `m′`. Declarations are in the namespace
`MassGap.TransferBand`.

Notation on a finite spectrum `w` with top `w i₀` (`DoublingRecursion.Top`): at time `m`, `y_i = (w_i/w_{i₀})^m`, the
excited weight `e = ∑_{i ≠ i₀} y_i` (`excited`), and the rate of a level `R_i = m log(w_{i₀}/w_i)`, so `y_i = e^{−R_i}`.
The transfer gap at time `m` is the least `R_i`; a bound `R_i ≤ C` at one level bounds it.

## 1. The test: one window does not bound the gap (proved)

* `flat_stall`: for every `u₀ > 0`, time `m ≥ 1` and `C`, a spectrum with top `1` and `n` equal excited levels has
  defect exactly `u₀` at time `m` and every excited rate `R_i ≥ C`. The excited weight, close to `e^{u₀} − 1` when the levels are small, is spread over
  `n ≈ e^{u₀+|C|}` levels of weight `e/n` each. So `d(m) = u₀` gives no bound `m_T ≤ C(u₀)/m`.
* The count is the point. `StallRigid.level_count` bounds the levels with `y_i ≥ c` by `(e^d − 1)/c`; nothing bounds
  the total number, and the Wilson slice transfer operator on `L²(G^{links})` has infinitely many levels.
* The flat stall is invisible one window later: its defect at time `2m` is at most `2 e^{−C} (e^{u₀} − 1)`
  (`flat_stall`, last clause, from `StallRigid.defect_double_le_level`). A held defect at window `k` with a vanishing
  defect at window `k + 1` is exactly this shape.

## 2. What restores the bound (proved)

* `rate_le_of_two_windows`: a defect at least `t > 0` at time `2m` and at most `A` at time `m` give a level with
  `R_i ≤ log(2(e^A − 1)/t)` (`StallRigid.exists_level`).
* `rate_le_of_count`: `R_i ≤ log n − log e` with `n` the number of excited levels.
* `rate_le_of_entropy`: `R_i ≤ H − log e`, `H = ∑ −p_i log p_i` the Shannon entropy of `p_i = y_i/e`
  (`levelEntropy`). The largest `p_i` is at least `e^{−H}`.
* `rate_le_of_entropy_growth`: if `H ≤ α log R_i + β` at every level (`α > 0`), some level has
  `R_i ≤ max 0 (2(α log(2α) − α + β − log e))`. This is the shape of a massive particle in a box of side `L`: its
  momentum levels below rate `R` number about `R^{3/2}`, so `H` grows like `(3/2) log R`, and the held weight then
  fixes `R` up to a constant. The count, not the weight, decides.

## 3. The Wilson window (proved, every `β ≥ 0`; `Yw_ge_of_next`, `slice_rate_le` for every compact group, the tower results for `SU(N)`)

* `Yw_ge_of_next`: at one window `w ≥ 1`, `t ≤ D(β, w+1)` and `8 D(β, w) + 2 D(β, w+1) ≤ A` give
  `t / (30 (e^A − 1)) ≤ Y(w)` (`StallRigid.fork_quant` at a single window; `StallRigid.level_floor` is its
  eventual form at fixed `β`).
* `slice_rate_le`: the same gives a step slice `i` with `2^w · (−log(λ₁/λ₀)) ≤ log(30 (e^A − 1)/t)`: the slice
  transfer gap at most `C/2^w`.
* `transfer_window_le`: along a coupling tower at `u₀`, a next-window floor `t ≤ D(βs k, k+1) ≤ B` gives,
  eventually, a step slice of side `2^k` with transfer gap at most `log(30 (e^{8u₀+2B} − 1)/t) / 2^k`.

## 4. The tensor mass (proved conditional)

`m′(β) ≥ −log r` for every periodic Clay gap `r` (`GapReadsTensorProved.gapReadsTensor`): the transfer gap bounds
`m′` below. It bounds `m′` above only if the tensor reading sees the low level. In a spectral representation
`Cov(n) = ∑ b_i r_i^n` with `b_i ≥ 0`, a level with `b_i = 0` does not enter, and the covariance decays at the rate of
the lowest level the tensor channel does reach; `spectral_floor` is the converse, `Cov(n) ≥ b_i r_i^n`.

* `WindowOverlap N β w a`: along separations `‖z_j‖∞ → ∞`, the tensor covariance of the periodic state at `β` is at
  least `a · Y(w)^{‖z_j‖∞/2^w}`, the window read of the step slices taken to the separation in window units. This is
  the overlap of the tensor channel with the window level at weight `a`; the rate is the transfer read, not a given
  number.
* `windowUpper_of_overlap`: along a coupling tower, a next-window floor `t ≤ D(βs k, k+1) ≤ B` and an overlap at some
  `a > 0`, eventually, give `WindowUpper N βs (log(30 (e^{8u₀+2B} − 1)/t))`: the upper half of (M), with the mass
  finite.
* `measTowerG_of_overlap_deep`: at depth `i ≥ 1`, `u₀ ≤ (1/2)^{2^i}/250`, with
  `log(30 (e^{8u₀+2B} − 1)/t) ≤ 2 · 2^i log 2`, the tower is a measured tower `MeasTowerG (SU N) βs`
  (`MassBand.measTowerG_of_windowUpper_deep`).

## What does not follow

* (M) stays open. Its lower half is proved (`ReflFloor.mass_floor_deep`); this module reduces its upper half to two
  unproved inputs, the next-window floor and the overlap, and no route to either is in the tree.
* The next-window floor `t ≤ D(βs k, k+1)` is not proved on any tower. `CouplingTower` fixes `D(βs k, k) = u₀` at the
  window `k` alone, and the squaring recursion (`DoublingSharp`, `ReflFloor.iterate_seed`) bounds `D(βs k, k+1)`
  above, near `(41/20) u₀²`, not below. `flat_stall` shows the floor is load-bearing: without it the gap is free.
* The bound `B` on `D(βs k, k+1)` is a hypothesis here; the squaring recursion is a candidate to discharge it and is
  not applied in this module.
* `slice_rate_le` bounds the transfer gap of a finite step slice of the torus (`StallRigid.topRatio`), not the periodic
  transfer gap of `PeriodicContent.PeriodicClayGapAt` that `gapReadsTensor` reads.
* `WindowOverlap` is proved at no coupling. It compares the infinite-volume periodic state's covariance with a finite
  torus slice's spectrum; no spectral representation of `FocusZoom.stateCov` of `periodicStateG` through the slice
  transfer is in the tree. It is a correlation floor at the transfer rate, and supplying it is the remaining content.
* The entropy inputs of section 2 are not read off the Wilson slice: the kernels carry no eigenvalue list.
* `measTowerG_of_overlap_deep` needs the constant `log(30 (e^{8u₀+2B} − 1)/t)` within twice the deep floor. With
  `t ≈ B ≈ u₀²` it is about `log(240/u₀)`, which sits within `2 · 2^i log 2` when `2^i log 2 ≥ log 60000`; no theorem
  here places `t` or `B` at that size.

DERIVED (module-wide): `0` the signs and the top index; `1` the least time, the least window and the top weight of
`flat_stall`; `2` the square in the purity, the doubled time, the window base, the band ratio and the factor in
`le_of_le_mul_log` (half of `x` absorbs the logarithm); `3/2` (in prose only) the momentum count of a box in three
space dimensions. Inherited: `30`, `8`, `2` of `StallRigid.fork_quant`; `250` and `(1/2)^{2^i}/250` the deep seed of
`ReflFloor.mass_floor_deep`; `41/20` the squaring constant of `DoublingSharp` (prose only). COMPUTED (prose only):
`240 = 30 · 8`, `60000 = 240 · 250`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.TransferBand

open Filter Topology
open scoped ENNReal
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayTreeG
open MassGap.MeasuredTower
open MassGap.MeasuredSpacing (mU measSpacing)
open MassGap.CouplingTower (StrongEnd CouplingTower windowCoupling)
open MassGap.BandUpper (WindowUpper)

/-! ## 0. Two real inequalities -/

/-- **A level read at time `n` is a rate bound.** `0 < c ≤ r^n`, `n ≥ 1`, `r ≥ 0` give `r > 0` and
`n · (−log r) ≤ −log c`. DERIVED: `1` the least time; `0` the sign. -/
theorem rate_of_pow {r c : ℝ} {n : ℕ} (hr : 0 ≤ r) (hn : 1 ≤ n) (hc : 0 < c) (h : c ≤ r ^ n) :
    0 < r ∧ (n : ℝ) * (-Real.log r) ≤ -Real.log c := by
  have hr0 : 0 < r := by
    rcases hr.lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_pow (by omega)] at h
      linarith
  refine ⟨hr0, ?_⟩
  have := Real.log_le_log hc h
  rw [Real.log_pow] at this
  linarith

/-- **A quantity at most a logarithm of itself is bounded.** `x ≤ α log x + β`, `α, x > 0`, give
`x ≤ 2 (α log(2α) − α + β)`, from `log(x/(2α)) ≤ x/(2α) − 1`. DERIVED: `2` half of `x` absorbs the logarithm;
`1` the tangent of `log` at `1`. -/
theorem le_of_le_mul_log {x α β : ℝ} (hα : 0 < α) (hx : 0 < x) (h : x ≤ α * Real.log x + β) :
    x ≤ 2 * (α * Real.log (2 * α) - α + β) := by
  have h2 : 0 < 2 * α := by positivity
  have h1 := Real.log_le_sub_one_of_pos (div_pos hx h2)
  rw [Real.log_div hx.ne' h2.ne'] at h1
  have h3 := mul_le_mul_of_nonneg_left h1 hα.le
  have e : α * (x / (2 * α) - 1) = x / 2 - α := by
    have := hα.ne'
    first
      | (field_simp; ring)
      | field_simp
  rw [e, mul_sub] at h3
  linarith

/-! ## 1. A finite spectrum: the test and its restorations -/

section Spectrum

open MassGap.DoublingRecursion

variable {ι : Type} [DecidableEq ι] {s : Finset ι} {w : ι → ℝ} {i₀ : ι}

/-- **A level in the window is a rate bound.** `c ≤ (w_i/w_{i₀})^m`, `c > 0`, `m ≥ 1`, give `w_i > 0` and
`m log(w_{i₀}/w_i) ≤ −log c`. DERIVED: `1` the least time. -/
theorem rate_of_level (h : Top s w i₀) {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 < c) {i : ι} (hi : i ∈ s)
    (hy : c ≤ (w i / w i₀) ^ m) : 0 < w i ∧ (m : ℝ) * Real.log (w i₀ / w i) ≤ -Real.log c := by
  obtain ⟨hr, hle⟩ := rate_of_pow (div_nonneg (h.nonneg i hi) h.pos.le) hm hc hy
  have hwi : 0 < w i := by
    rcases (h.nonneg i hi).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_div] at hr
      exact absurd hr (lt_irrefl 0)
  refine ⟨hwi, ?_⟩
  have e : Real.log (w i₀ / w i) = -Real.log (w i / w i₀) := by
    rw [Real.log_div h.pos.ne' hwi.ne', Real.log_div hwi.ne' h.pos.ne']
    ring
  rw [e]
  exact hle

/-- **A rate bound is a level bound.** `C ≤ m log(w_{i₀}/w_i)` gives `(w_i/w_{i₀})^m ≤ e^{−C}`. -/
theorem ratio_pow_le_of_rate (h : Top s w i₀) {m : ℕ} {C : ℝ} {i : ι} (hwi : 0 < w i)
    (hC : C ≤ (m : ℝ) * Real.log (w i₀ / w i)) : (w i / w i₀) ^ m ≤ Real.exp (-C) := by
  have hq : 0 < w i / w i₀ := div_pos hwi h.pos
  rw [← Real.exp_log (pow_pos hq m), Real.log_pow, Real.exp_le_exp]
  have e : Real.log (w i / w i₀) = -Real.log (w i₀ / w i) := by
    rw [Real.log_div h.pos.ne' hwi.ne', Real.log_div hwi.ne' h.pos.ne']
    ring
  rw [e]
  linarith

theorem erase_nonempty_of_excited (h : Top s w i₀) {m : ℕ} (he : 0 < excited s w i₀ m) :
    (s.erase i₀).Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  rw [StallRigid.excited_eq_sum h, hemp, Finset.sum_empty] at he
  exact lt_irrefl 0 he

/-- **The flat stall: one window does not bound the gap.** For every `u₀ > 0`, time `m ≥ 1` and `C`, the spectrum
with top `1` and `n` excited levels at one common ratio has defect exactly `u₀` at time `m`, every excited rate at
least `C`, and defect at most `2 e^{−C} (e^{u₀} − 1)` at time `2m`. The defect at one window holds the excited weight;
the number of levels it is spread over is free, and with it the gap. DERIVED: `1` the top weight and the least
time; `0` the top index; `2` the doubled time. -/
theorem flat_stall {u₀ : ℝ} (hu : 0 < u₀) {m : ℕ} (hm : 1 ≤ m) (C : ℝ) :
    ∃ (n : ℕ) (w : Fin (n + 1) → ℝ), Top Finset.univ w 0 ∧ defect Finset.univ w m = u₀ ∧
      (∀ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0,
        0 < w i ∧ C ≤ (m : ℝ) * Real.log (w 0 / w i)) ∧
      defect Finset.univ w (2 * m) ≤ 2 * Real.exp (-C) * (Real.exp u₀ - 1) := by
  set E := Real.exp u₀ - 1 with hE
  have hE0 : 0 < E := by
    have := Real.one_lt_exp_iff.mpr hu
    linarith
  set n : ℕ := ⌈E * Real.exp |C|⌉₊ + 1 with hn
  have hn0 : (0 : ℝ) < n := by rw [hn]; positivity
  have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
  have hnE : E * Real.exp |C| ≤ n := by
    rw [hn]
    push_cast
    have := Nat.le_ceil (E * Real.exp |C|)
    linarith
  have hexp1 : 1 ≤ Real.exp |C| := Real.one_le_exp (abs_nonneg C)
  have hEn : E ≤ n := by nlinarith
  have hb : (0 : ℝ) ≤ E / n := by positivity
  have hb1 : E / n ≤ 1 := (div_le_one hn0).mpr hEn
  have e1 : (n : ℝ) * (E / n) = E := mul_div_cancel₀ E hn0'
  have e2 : 1 + E = Real.exp u₀ := by rw [hE]; ring
  have hf1 : u₀ ≤ 2 * Real.log (1 + n * (E / n)) - Real.log (1 + n * (E / n) ^ 2) := by
    rw [e1, e2, Real.log_exp]
    have e3 : (n : ℝ) * (E / n) ^ 2 = E * (E / n) := by rw [sq, ← mul_assoc, e1]
    have h4 : 1 + (n : ℝ) * (E / n) ^ 2 ≤ Real.exp u₀ := by
      rw [e3, ← e2]
      have := mul_le_of_le_one_right hE0.le hb1
      linarith
    have h5 := Real.log_le_log (by positivity) h4
    rw [Real.log_exp] at h5
    linarith
  have hcont : ContinuousOn (fun y : ℝ => 2 * Real.log (1 + n * y) - Real.log (1 + n * y ^ 2))
      (Set.Icc 0 (E / n)) := by
    refine ContinuousOn.sub
      (continuousOn_const.mul (ContinuousOn.log (Continuous.continuousOn (by fun_prop)) ?_))
      (ContinuousOn.log (Continuous.continuousOn (by fun_prop)) ?_)
    · intro y hy
      have := mul_nonneg hn0.le hy.1
      exact ne_of_gt (by linarith)
    · intro y _
      have := mul_nonneg hn0.le (sq_nonneg y)
      exact ne_of_gt (by linarith)
  obtain ⟨y, hyI, hyf⟩ := intermediate_value_Icc hb hcont ⟨by simp [hu.le], hf1⟩
  have hyf' : 2 * Real.log (1 + n * y) - Real.log (1 + n * y ^ 2) = u₀ := hyf
  have hy0 : 0 < y := by
    rcases hyI.1.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hyf'
      simp at hyf'
      linarith
  have hy1 : y ≤ 1 := hyI.2.trans hb1
  set r : ℝ := y ^ ((m : ℝ)⁻¹) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hy0 _
  have hrm : r ^ m = y := Real.rpow_inv_natCast_pow hyI.1 (by omega)
  have hr1 : r ≤ 1 := Real.rpow_le_one hyI.1 hy1 (by positivity)
  set w : Fin (n + 1) → ℝ := fun i => if i = 0 then 1 else r with hw
  have hw0 : w 0 = 1 := by simp [hw]
  have hwi : ∀ i : Fin (n + 1), i ≠ 0 → w i = r := fun i hi => by simp [hw, hi]
  have htop : Top Finset.univ w 0 := by
    refine ⟨Finset.mem_univ _, by rw [hw0]; exact one_pos, fun i _ => ?_, fun i _ => ?_⟩
    · by_cases hi : i = 0
      · rw [hi, hw0]; exact zero_le_one
      · rw [hwi i hi]; exact hr0.le
    · rw [hw0]
      by_cases hi : i = 0
      · simp [hi, hw0]
      · rw [hwi i hi]; exact hr1
  have hps : ∀ k : ℕ, powSum Finset.univ w k = 1 + n * r ^ k := by
    intro k
    unfold powSum
    rw [Fin.sum_univ_succ, hw0, one_pow]
    have : ∀ i : Fin n, w i.succ ^ k = r ^ k := fun i => by rw [hwi _ (Fin.succ_ne_zero i)]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdef : defect Finset.univ w m = u₀ := by
    unfold defect
    rw [hps, hps, pow_mul', hrm]
    exact hyf'
  have hly : Real.log y ≤ Real.log E - Real.log n := by
    rw [← Real.log_div hE0.ne' hn0']
    exact Real.log_le_log hy0 hyI.2
  have hln : Real.log E + |C| ≤ Real.log n := by
    have := Real.log_le_log (by positivity) hnE
    rwa [Real.log_mul hE0.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  have hmr : (m : ℝ) * Real.log r = Real.log y := by rw [← Real.log_pow, hrm]
  have hlev : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0,
      0 < w i ∧ C ≤ (m : ℝ) * Real.log (w 0 / w i) := by
    intro i hi
    rw [hwi i (Finset.ne_of_mem_erase hi), hw0]
    refine ⟨hr0, ?_⟩
    rw [one_div, Real.log_inv]
    linarith [le_abs_self C]
  refine ⟨n, w, htop, hdef, hlev, ?_⟩
  have h2 := StallRigid.defect_double_le_level htop m (Real.exp_pos (-C)).le
    (fun i hi => ratio_pow_le_of_rate htop (hlev i hi).1 (hlev i hi).2)
  rw [hdef] at h2
  exact h2

/-- **Two windows bound the gap.** A defect at least `t > 0` at time `2m` and at most `A` at time `m` give an
excited level with `m log(w_{i₀}/w_i) ≤ log(2 (e^A − 1)/t)`. DERIVED: `2` the square in the purity; `1` the least
time. -/
theorem rate_le_of_two_windows (h : Top s w i₀) {m : ℕ} (hm : 1 ≤ m) {t A : ℝ} (ht : 0 < t)
    (hd : t ≤ defect s w (2 * m)) (hA : defect s w m ≤ A) :
    ∃ i ∈ s.erase i₀, 0 < w i ∧
      (m : ℝ) * Real.log (w i₀ / w i) ≤ Real.log (2 * (Real.exp A - 1) / t) := by
  obtain ⟨i, hi, hy⟩ := StallRigid.exists_level h m ht hd hA
  have h2 := StallRigid.defect_double_le_two h m
  have hA0 : 0 < A := by linarith
  have hE : 0 < Real.exp A - 1 := by
    have := Real.one_lt_exp_iff.mpr hA0
    linarith
  have hc : 0 < t / (2 * (Real.exp A - 1)) := div_pos ht (mul_pos two_pos hE)
  obtain ⟨hwi, hr⟩ := rate_of_level h hm hc (Finset.mem_of_mem_erase hi) hy
  refine ⟨i, hi, hwi, ?_⟩
  rw [show 2 * (Real.exp A - 1) / t = (t / (2 * (Real.exp A - 1)))⁻¹ from (inv_div _ _).symm,
    Real.log_inv]
  exact hr

/-- **The count bounds the gap.** With `n` excited levels and excited weight `e > 0`, some level has
`m log(w_{i₀}/w_i) ≤ log n − log e`. DERIVED: `1` the least time. -/
theorem rate_le_of_count (h : Top s w i₀) {m : ℕ} (hm : 1 ≤ m) (he : 0 < excited s w i₀ m) :
    ∃ i ∈ s.erase i₀, 0 < w i ∧ (m : ℝ) * Real.log (w i₀ / w i) ≤
      Real.log ((s.erase i₀).card : ℝ) - Real.log (excited s w i₀ m) := by
  have hne := erase_nonempty_of_excited h he
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image _ (fun i => (w i / w i₀) ^ m) hne
  have hsum : excited s w i₀ m ≤ (s.erase i₀).card * (w i / w i₀) ^ m := by
    rw [StallRigid.excited_eq_sum h, ← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ hmax
  have hcard : (0 : ℝ) < (s.erase i₀).card := by exact_mod_cast hne.card_pos
  have hc : 0 < excited s w i₀ m / (s.erase i₀).card := div_pos he hcard
  have hy : excited s w i₀ m / (s.erase i₀).card ≤ (w i / w i₀) ^ m := by
    rw [div_le_iff₀ hcard]
    linarith
  obtain ⟨hwi, hr⟩ := rate_of_level h hm hc (Finset.mem_of_mem_erase hi) hy
  refine ⟨i, hi, hwi, ?_⟩
  rw [Real.log_div he.ne' hcard.ne'] at hr
  linarith

/-- The Shannon entropy of the excited weights at time `m`, normalised to the excited weight:
`∑_{i ≠ i₀} −p_i log p_i`, `p_i = y_i / e`. -/
def levelEntropy (s : Finset ι) (w : ι → ℝ) (i₀ : ι) (m : ℕ) : ℝ :=
  ∑ i ∈ s.erase i₀, Real.negMulLog ((w i / w i₀) ^ m / excited s w i₀ m)

/-- **The entropy bounds the gap.** With excited weight `e > 0`, some level has
`m log(w_{i₀}/w_i) ≤ H − log e`, `H = levelEntropy`: the largest `p_i` is at least `e^{−H}`. DERIVED: `1` the
least time and the total of the `p_i`. -/
theorem rate_le_of_entropy (h : Top s w i₀) {m : ℕ} (hm : 1 ≤ m) (he : 0 < excited s w i₀ m) :
    ∃ i ∈ s.erase i₀, 0 < w i ∧
      (m : ℝ) * Real.log (w i₀ / w i) ≤ levelEntropy s w i₀ m - Real.log (excited s w i₀ m) := by
  have hne := erase_nonempty_of_excited h he
  set e := excited s w i₀ m with he_def
  set y : ι → ℝ := fun j => (w j / w i₀) ^ m with hy_def
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image _ y hne
  have hy0 : ∀ j ∈ s.erase i₀, 0 ≤ y j := fun j hj =>
    pow_nonneg (div_nonneg (h.nonneg j (Finset.mem_of_mem_erase hj)) h.pos.le) m
  have hsum : ∑ j ∈ s.erase i₀, y j = e := (StallRigid.excited_eq_sum h m).symm
  have hyi : 0 < y i := by
    by_contra hc
    push_neg at hc
    have : ∑ j ∈ s.erase i₀, y j ≤ 0 := Finset.sum_nonpos fun j hj => (hmax j hj).trans hc
    linarith
  have hterm : ∀ j ∈ s.erase i₀, -(y j / e) * Real.log (y i / e) ≤ Real.negMulLog (y j / e) := by
    intro j hj
    show _ ≤ -(y j / e) * Real.log (y j / e)
    rcases (div_nonneg (hy0 j hj) he.le).lt_or_eq with hp | hp
    · have hl := Real.log_le_log hp (div_le_div_of_nonneg_right (hmax j hj) he.le)
      have := mul_le_mul_of_nonneg_left hl hp.le
      linarith
    · rw [← hp]
      simp
  have hH : -Real.log (y i / e) ≤ levelEntropy s w i₀ m := by
    have h1 := Finset.sum_le_sum hterm
    have h2 : ∑ j ∈ s.erase i₀, -(y j / e) * Real.log (y i / e) = -Real.log (y i / e) := by
      rw [← Finset.sum_mul, show ∑ j ∈ s.erase i₀, -(y j / e) = -1 by
        rw [Finset.sum_neg_distrib, ← Finset.sum_div, hsum, div_self he.ne']]
      ring
    rw [h2] at h1
    exact h1
  obtain ⟨hwi, hr⟩ := rate_of_level h hm hyi (Finset.mem_of_mem_erase hi) le_rfl
  refine ⟨i, hi, hwi, ?_⟩
  rw [Real.log_div hyi.ne' he.ne'] at hH
  linarith

/-- **An entropy growing at most logarithmically in the rate bounds the gap.** If at every excited level
`H ≤ α log(m log(w_{i₀}/w_i)) + β`, `α > 0`, some level has
`m log(w_{i₀}/w_i) ≤ max 0 (2 (α log(2α) − α + β − log e))`. DERIVED: `0` the sign of a rate; `2` from
`le_of_le_mul_log`. -/
theorem rate_le_of_entropy_growth (h : Top s w i₀) {m : ℕ} (hm : 1 ≤ m) (he : 0 < excited s w i₀ m)
    {α β : ℝ} (hα : 0 < α)
    (hH : ∀ i ∈ s.erase i₀, 0 < w i →
      levelEntropy s w i₀ m ≤ α * Real.log ((m : ℝ) * Real.log (w i₀ / w i)) + β) :
    ∃ i ∈ s.erase i₀, 0 < w i ∧ (m : ℝ) * Real.log (w i₀ / w i) ≤
      max 0 (2 * (α * Real.log (2 * α) - α + (β - Real.log (excited s w i₀ m)))) := by
  obtain ⟨i, hi, hwi, hr⟩ := rate_le_of_entropy h hm he
  refine ⟨i, hi, hwi, ?_⟩
  rcases le_or_gt ((m : ℝ) * Real.log (w i₀ / w i)) 0 with h0 | h0
  · exact h0.trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    refine le_of_le_mul_log hα h0 ?_
    have := hH i hi hwi
    linarith

/-- **The overlap of a spectral sum.** With nonnegative weights `b` and ratios `r`, the sum `∑ b_j r_j^n` is at
least the term of any one level. A covariance with this representation is floored at the rate of every level it
reaches. -/
theorem spectral_floor {κ : Type} (S : Finset κ) {b r : κ → ℝ} (hb : ∀ j ∈ S, 0 ≤ b j)
    (hr : ∀ j ∈ S, 0 ≤ r j) {i : κ} (hi : i ∈ S) (n : ℕ) :
    b i * r i ^ n ≤ ∑ j ∈ S, b j * r j ^ n :=
  Finset.single_le_sum (f := fun j => b j * r j ^ n)
    (fun j hj => mul_nonneg (hb j hj) (pow_nonneg (hr j hj) n)) hi

end Spectrum

/-! ## 2. The Wilson window -/

section Wilson

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] {β : ℝ}

/-- **The next window forces a level at this one.** At `β ≥ 0`, `w ≥ 1`, `t ≤ D(β, w+1)` with `t > 0` and
`8 D(β, w) + 2 D(β, w+1) ≤ A` give `e^A > 1` and `t / (30 (e^A − 1)) ≤ Y(w)`. Inherited: `30`, `8`, `2` of
`StallRigid.fork_quant`. -/
theorem Yw_ge_of_next (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) {t A : ℝ} (ht : 0 < t)
    (hD : t ≤ StallRigid.Dw G β (w + 1))
    (hA : 8 * StallRigid.Dw G β w + 2 * StallRigid.Dw G β (w + 1) ≤ A) :
    0 < Real.exp A - 1 ∧ t / (30 * (Real.exp A - 1)) ≤ StallRigid.Yw G hβ w := by
  have hD0 := StallRigid.Dw_nonneg (G := G) hβ hw
  have hA0 : 0 < A := by linarith
  have hE : 0 < Real.exp A - 1 := by
    have := Real.one_lt_exp_iff.mpr hA0
    linarith
  refine ⟨hE, ?_⟩
  have hf := StallRigid.fork_quant (G := G) hβ hw
  have hle : Real.exp (8 * StallRigid.Dw G β w + 2 * StallRigid.Dw G β (w + 1)) ≤ Real.exp A :=
    Real.exp_le_exp.mpr hA
  have hY := StallRigid.Yw_nonneg (G := G) hβ w
  have h3 : 30 * StallRigid.Yw G hβ w *
        (Real.exp (8 * StallRigid.Dw G β w + 2 * StallRigid.Dw G β (w + 1)) - 1)
      ≤ 30 * StallRigid.Yw G hβ w * (Real.exp A - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  rw [div_le_iff₀ (mul_pos (by norm_num) hE)]
  nlinarith

/-- **The slice transfer gap at the window, from the next window.** Under the hypotheses of `Yw_ge_of_next`, a
step slice `i` of side `2^w` has `λ₁/λ₀ > 0` and `2^w · (−log(λ₁/λ₀)) ≤ log(30 (e^A − 1)/t)`. DERIVED: `2` the
window base; `1` the least window. Inherited: `30`. DERIVED: `30 = 2 · 15`, `8`, `2` of
`StallRigid.fork_quant` (`8`, `2` from `StallRigid.pred_le`). -/
theorem slice_rate_le (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) {t A : ℝ} (ht : 0 < t)
    (hD : t ≤ StallRigid.Dw G β (w + 1))
    (hA : 8 * StallRigid.Dw G β w + 2 * StallRigid.Dw G β (w + 1) ≤ A) :
    ∃ i : Fin 4, 0 < StallRigid.topRatio G hβ i (StallRigid.sliceT (2 ^ w) i) ∧
      (2 : ℝ) ^ w * (-Real.log (StallRigid.topRatio G hβ i (StallRigid.sliceT (2 ^ w) i))) ≤
        Real.log (30 * (Real.exp A - 1) / t) := by
  obtain ⟨hE, hY⟩ := Yw_ge_of_next hβ hw ht hD hA
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (StallRigid.winRead G hβ w)
  have hc : 0 < t / (30 * (Real.exp A - 1)) := div_pos ht (mul_pos (by norm_num) hE)
  have hYi : StallRigid.Yw G hβ w = StallRigid.winRead G hβ w i := hi
  have hy : t / (30 * (Real.exp A - 1)) ≤
      StallRigid.topRatio G hβ i (StallRigid.sliceT (2 ^ w) i) ^ 2 ^ w := by
    rw [hYi] at hY
    exact hY
  obtain ⟨hr, hle⟩ := rate_of_pow (StallRigid.topRatio_spec (G := G) hβ i
    (StallRigid.sliceT (2 ^ w) i)).1 Nat.one_le_two_pow hc hy
  refine ⟨i, hr, ?_⟩
  rw [show 30 * (Real.exp A - 1) / t = (t / (30 * (Real.exp A - 1)))⁻¹ from (inv_div _ _).symm,
    Real.log_inv]
  push_cast at hle
  exact hle

end Wilson

/-! ## 3. Along a coupling tower, and the tensor mass -/

section Tower

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

/-- **The transfer gap along a tower, from a next-window floor.** On a coupling tower at `u₀`, if eventually
`t ≤ D(βs k, k+1) ≤ B` with `t > 0`, then eventually a step slice of side `2^k` at `βs k` has
`2^k · (−log(λ₁/λ₀)) ≤ log(30 (e^{8u₀+2B} − 1)/t)`. Inherited: `30`, `8`, `2` of `StallRigid.fork_quant`. -/
theorem transfer_window_le {u₀ t B : ℝ} (ht : 0 < t) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id)
    (hnext : ∀ᶠ k in atTop,
      t ≤ windowCoupling N (βs k) (k + 1) ∧ windowCoupling N (βs k) (k + 1) ≤ B) :
    ∀ᶠ k in atTop, ∃ hβ : 0 ≤ βs k, ∃ i : Fin 4,
      0 < StallRigid.topRatio (MassGap.SUN.SU N) hβ i (StallRigid.sliceT (2 ^ k) i) ∧
      (2 : ℝ) ^ k * (-Real.log (StallRigid.topRatio (MassGap.SUN.SU N) hβ i (StallRigid.sliceT (2 ^ k) i)))
        ≤ Real.log (30 * (Real.exp (8 * u₀ + 2 * B) - 1) / t) := by
  filter_upwards [hT.2.2, hnext] with k ⟨hk, hβ, hg⟩ ⟨h1, h2⟩
  have hg' : windowCoupling N (βs k) k = u₀ := hg
  have hk' : 1 ≤ k := hk
  refine ⟨hβ, slice_rate_le (G := MassGap.SUN.SU N) (w := k) hβ hk' ht ?_ ?_⟩
  · rw [StallRigid.Dw_SU]
    exact h1
  · rw [StallRigid.Dw_SU, StallRigid.Dw_SU, hg']
    linarith

variable (N) in
/-- **The tensor channel overlaps the window level at weight `a`.** At `β ≥ 0` and window `w`: along separations
`z_j` with `‖z_j‖∞ → ∞`, the tensor covariance of the periodic state at `β` is at least
`a · Y(w)^{‖z_j‖∞ / 2^w}`, `Y(w)` the window read of the step slices (`StallRigid.Yw`). The rate is the transfer read
of the window; in a spectral representation with nonnegative weights it is the weight of the window level
(`spectral_floor`). DERIVED: `2` the window base. -/
def WindowOverlap (β : ℝ) (w : ℕ) (a : ℝ) : Prop :=
  ∃ hβ : 0 ≤ β, ∃ (x : ISite) (z : ℕ → ISite), Tendsto (fun j => (snormG (z j) : ℝ)) atTop atTop ∧
    ∀ᶠ j in atTop, a * StallRigid.Yw (MassGap.SUN.SU N) hβ w ^ ((snormG (z j) : ℝ) / 2 ^ w) ≤
      |FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) β)
        (tensorEnergyG (MassGap.SUN.SU N) x) (tensorEnergyG (MassGap.SUN.SU N) (x + z j))|

/-- **An overlap and a next-window floor give the upper half of (M).** On a coupling tower at `u₀`, if eventually
`t ≤ D(βs k, k+1) ≤ B` (`t > 0`) and the tensor channel overlaps the window level at some weight `a > 0`, then
`WindowUpper N βs (log(30 (e^{8u₀+2B} − 1)/t))`: eventually `m′(βs k)` is finite and at most that constant over
`2^k`. Inherited: `30`, `8`, `2` of `StallRigid.fork_quant`. DERIVED: `2` the window base; `30 = 2 · 15`,
`8`, `2` of `StallRigid.fork_quant` (`8`, `2` from `StallRigid.pred_le`). -/
theorem windowUpper_of_overlap {u₀ t B : ℝ} (ht : 0 < t) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id)
    (h : ∀ᶠ k in atTop, t ≤ windowCoupling N (βs k) (k + 1) ∧ windowCoupling N (βs k) (k + 1) ≤ B ∧
      ∃ a : ℝ, 0 < a ∧ WindowOverlap N (βs k) k a) :
    WindowUpper N βs (Real.log (30 * (Real.exp (8 * u₀ + 2 * B) - 1) / t)) := by
  refine BandUpper.windowUpper_of_corrFloor ?_
  filter_upwards [hT.2.2, h] with k hkk hkh
  obtain ⟨hk, -, hg⟩ := hkk
  obtain ⟨h1, h2, a, ha, hβ, x, z, hz, hfl⟩ := hkh
  have hg' : windowCoupling N (βs k) k = u₀ := hg
  have hk' : 1 ≤ k := hk
  obtain ⟨hE, hY⟩ := Yw_ge_of_next (G := MassGap.SUN.SU N) (w := k) (A := 8 * u₀ + 2 * B) hβ hk' ht
    (by rw [StallRigid.Dw_SU]; exact h1)
    (by rw [StallRigid.Dw_SU, StallRigid.Dw_SU, hg']; linarith)
  have hc : 0 < t / (30 * (Real.exp (8 * u₀ + 2 * B) - 1)) := div_pos ht (mul_pos (by norm_num) hE)
  set c := t / (30 * (Real.exp (8 * u₀ + 2 * B) - 1)) with hc_def
  have hU : Real.log (30 * (Real.exp (8 * u₀ + 2 * B) - 1) / t) = -Real.log c := by
    rw [hc_def, ← Real.log_inv, inv_div]
  refine ⟨a, ha, x, z, hz, ?_⟩
  filter_upwards [hfl] with j hj
  refine le_trans (mul_le_mul_of_nonneg_left ?_ ha.le) hj
  have hs : (0 : ℝ) ≤ (snormG (z j) : ℝ) / 2 ^ k := by positivity
  calc Real.exp (-(Real.log (30 * (Real.exp (8 * u₀ + 2 * B) - 1) / t) / 2 ^ k * (snormG (z j) : ℝ)))
      = c ^ ((snormG (z j) : ℝ) / 2 ^ k) := by
        rw [Real.rpow_def_of_pos hc, hU]
        congr 1
        ring
    _ ≤ StallRigid.Yw (MassGap.SUN.SU N) hβ k ^ ((snormG (z j) : ℝ) / 2 ^ k) :=
        Real.rpow_le_rpow hc.le hY hs

/-- **The measured tower from an overlap at the tower's depth.** A coupling tower at `u₀ ≤ (1/2)^{2^i}/250`,
`i ≥ 1`, with the next-window floor and the overlap of `windowUpper_of_overlap`, and with
`log(30 (e^{8u₀+2B} − 1)/t) ≤ 2 · 2^i log 2`, is a measured tower (`MassBand.measTowerG_of_windowUpper_deep`).
DERIVED: `1` the least depth; `2` the band ratio. Inherited: `250` and the deep seed; `30`, `8`, `2` of
`StallRigid.fork_quant`. -/
theorem measTowerG_of_overlap_deep {u₀ t B : ℝ} {i : ℕ} (hi : 1 ≤ i)
    (hu : u₀ ≤ (1 / 2 : ℝ) ^ (2 ^ i) / 250) (ht : 0 < t) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id)
    (h : ∀ᶠ k in atTop, t ≤ windowCoupling N (βs k) (k + 1) ∧ windowCoupling N (βs k) (k + 1) ≤ B ∧
      ∃ a : ℝ, 0 < a ∧ WindowOverlap N (βs k) k a)
    (hU : Real.log (30 * (Real.exp (8 * u₀ + 2 * B) - 1) / t) ≤ 2 * (2 ^ i * Real.log 2)) :
    MeasTowerG (MassGap.SUN.SU N) βs :=
  MassBand.measTowerG_of_windowUpper_deep hi hu hT
    (MassBand.windowUpper_mono hU (windowUpper_of_overlap ht hT h))

end Tower

end MassGap.TransferBand

end

#print axioms MassGap.TransferBand.rate_of_pow
#print axioms MassGap.TransferBand.le_of_le_mul_log
#print axioms MassGap.TransferBand.rate_of_level
#print axioms MassGap.TransferBand.ratio_pow_le_of_rate
#print axioms MassGap.TransferBand.erase_nonempty_of_excited
#print axioms MassGap.TransferBand.flat_stall
#print axioms MassGap.TransferBand.rate_le_of_two_windows
#print axioms MassGap.TransferBand.rate_le_of_count
#print axioms MassGap.TransferBand.rate_le_of_entropy
#print axioms MassGap.TransferBand.rate_le_of_entropy_growth
#print axioms MassGap.TransferBand.spectral_floor
#print axioms MassGap.TransferBand.Yw_ge_of_next
#print axioms MassGap.TransferBand.slice_rate_le
#print axioms MassGap.TransferBand.transfer_window_le
#print axioms MassGap.TransferBand.windowUpper_of_overlap
#print axioms MassGap.TransferBand.measTowerG_of_overlap_deep
