import Mathlib
import MassGap.PurityBound

/-!
# MassGap.PurityTaylor — the logarithmic gap bound and the expansions of the pressure form

Theorem 2.2, (2.4), and Lemma 2.4 (the second-order expansions of `F` and `B` and `F′(0) = 1/2`)
of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`).

* (2.3) and (2.4) from the excited-weight bound `x ^ T ≤ d p` (`x = λ₁/λ₀`): `gap_ratio_le`,
  `x ≤ d(p)^{1/T}`; `gap_log`, for `1/2 < p < 1`, `x > 0`, `T > 0`,
  `(1/T) log ((1 + √(2p − 1)) / (1 − √(2p − 1))) ≤ −log x`; `gap_log_sharp`: equality at
  `x = d(p)^{1/T}`.
* `F ε = −log ((√(2e^{−ε} − 1) + 1)/2)` and `B ε = e^{F ε} − 1` (paper, (2.5)).
  `B_eq`: `B ε = (1 − s)/(1 + s)` with `s = √(2e^{−ε} − 1)`; `B_eq_d`: `B ε = d (e^{−ε})`;
  `F_eq_log`: `F ε = log (1 + B ε)`; `s_zero`, `F_zero`, `B_zero`.
* `exp_neg_bound`: `|e^{−ε} − (1 − ε + ε²/2)| ≤ (2/9)|ε|³` for `|ε| ≤ 1`; `s_bound`:
  `|s ε − (1 − ε)| ≤ |ε|³` for `|ε| ≤ 1/4`. `B_bound`, `F_bound`: for `|ε| ≤ 1/4`,
  `|B ε − ε/2 − ε²/4| ≤ 2|ε|³` and `|F ε − ε/2 − ε²/8| ≤ 4|ε|³`.
  `B_taylor`, `F_taylor`: the same as `O(ε³)` at `0` (paper, Lemma 2.4).
  `hasDerivAt_F`, `hasDerivAt_B`: `F′(0) = B′(0) = 1/2` (via the generic `hasDerivAt_of_taylor`).
* `twoLevel_F` (`ε ≤ log 2`), `F_twoLevel` (on `[0, log 2]`): `F` and `PurityBound.twoLevel` are
  inverse; `exp_neg_F`, `F_mem`, `twoLevel_mem`.
* Lemma 2.4: `F_strictMonoOn`, `F_convexOn` on `[0, log 2]`, and the chord bound (2.6) `F_chord`:
  `F ε ≤ (F ε*/ε*) ε` for `0 < ε* ≤ log 2`, `0 ≤ ε ≤ ε*`.

DERIVED (module-wide): `1/2` the purity threshold; `1/4` the radius of the explicit bounds;
`2` and `4` their constants; `1/2`, `1/4`, `1/8` the Taylor coefficients.
-/

namespace MassGap.PurityTaylor

open Real Set Filter Asymptotics Topology MassGap.PurityBound

/-- **Theorem 2.2, (2.4).** A gap ratio `x = λ₁/λ₀` with `x ^ T ≤ d p` satisfies
`−log x ≥ (1/T) log ((1 + √(2p − 1)) / (1 − √(2p − 1)))`. DERIVED: `1/2`. -/
theorem gap_log {p x T : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hx : 0 < x) (hT : 0 < T)
    (hxT : x ^ T ≤ d p) :
    1 / T * log ((1 + √(2 * p - 1)) / (1 - √(2 * p - 1))) ≤ -log x := by
  set r := √(2 * p - 1)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hr1 : r < 1 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hdp : d p = ((1 + r) / (1 - r))⁻¹ := by
    simp only [d, inv_div]; rfl
  have hlog : T * log x ≤ -log ((1 + r) / (1 - r)) := by
    rw [← Real.log_rpow hx, ← Real.log_inv, ← hdp]
    exact Real.log_le_log (Real.rpow_pos_of_pos hx T) hxT
  rw [one_div_mul_eq_div, div_le_iff₀ hT]
  linarith

/-- **(2.4) is sharp.** At `x = d(p)^{1/T}` the bound holds with equality. DERIVED: `1/2`. -/
theorem gap_log_sharp {p T : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hT : 0 < T) :
    (d p ^ (1 / T)) ^ T = d p ∧
      -log (d p ^ (1 / T)) = 1 / T * log ((1 + √(2 * p - 1)) / (1 - √(2 * p - 1))) := by
  set r := √(2 * p - 1)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hr1 : r < 1 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hdpos : 0 < d p := div_pos (by linarith) (by linarith)
  have hdp : d p = ((1 + r) / (1 - r))⁻¹ := by
    simp only [d, inv_div]; rfl
  refine ⟨?_, ?_⟩
  · rw [← Real.rpow_mul hdpos.le, one_div_mul_cancel hT.ne', Real.rpow_one]
  · rw [Real.log_rpow hdpos, hdp, Real.log_inv]
    ring

/-- `s ε = √(2e^{−ε} − 1)`. -/
noncomputable def s (ε : ℝ) : ℝ := √(2 * exp (-ε) - 1)

/-- The paper's pressure form `F ε = −log ((√(2e^{−ε} − 1) + 1)/2)`, (2.5). -/
noncomputable def F (ε : ℝ) : ℝ := -log ((√(2 * exp (-ε) - 1) + 1) / 2)

/-- The paper's `B ε = e^{F ε} − 1`, (2.5). -/
noncomputable def B (ε : ℝ) : ℝ := exp (F ε) - 1

theorem s_nonneg (ε : ℝ) : 0 ≤ s ε := Real.sqrt_nonneg _

/-- `B ε = (1 − s)/(1 + s)`. -/
theorem B_eq (ε : ℝ) : B ε = (1 - s ε) / (1 + s ε) := by
  have h1 : 0 < 1 + s ε := by linarith [s_nonneg ε]
  have hpos : 0 < (s ε + 1) / 2 := by linarith [s_nonneg ε]
  have hF : F ε = -log ((s ε + 1) / 2) := rfl
  rw [B, hF, Real.exp_neg, Real.exp_log hpos, inv_div, div_sub_one (by linarith)]
  congr 1 <;> ring

/-- **(2.5).** `B ε = d (e^{−ε})`. -/
theorem B_eq_d (ε : ℝ) : B ε = d (exp (-ε)) := by
  rw [B_eq]; rfl

/-- `F ε = log (1 + B ε)`. -/
theorem F_eq_log (ε : ℝ) : F ε = log (1 + B ε) := by
  rw [B, add_sub_cancel, Real.log_exp]

theorem s_zero : s 0 = 1 := by simp [s]; norm_num

theorem F_zero : F 0 = 0 := by simp [F]; norm_num

theorem B_zero : B 0 = 0 := by simp [B, F_zero]

/-- The exponential to second order: `|e^{−ε} − (1 − ε + ε²/2)| ≤ (2/9)|ε|³` for `|ε| ≤ 1`. -/
theorem exp_neg_bound {ε : ℝ} (hε : |ε| ≤ 1) :
    |exp (-ε) - (1 - ε + ε ^ 2 / 2)| ≤ 2 / 9 * |ε| ^ 3 := by
  have h := Real.exp_bound (x := -ε) (by rwa [abs_neg]) (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg] at h
  norm_num [Nat.factorial] at h
  have e : exp (-ε) - (1 - ε + ε ^ 2 / 2) = exp (-ε) - (1 + -ε + ε ^ 2 / 2) := by ring
  rw [e]
  linarith

/-- **`s` to second order.** For `|ε| ≤ 1/4`, `|s ε − (1 − ε)| ≤ |ε|³`. -/
theorem s_bound {ε : ℝ} (hε : |ε| ≤ 1 / 4) : |s ε - (1 - ε)| ≤ |ε| ^ 3 := by
  have he0 := abs_nonneg ε
  have hlo : -ε ≤ |ε| := neg_le_abs ε
  have hhi : ε ≤ |ε| := le_abs_self ε
  have hexp : 1 - ε ≤ exp (-ε) := by linarith [Real.add_one_le_exp (-ε)]
  have hu : 0 ≤ 2 * exp (-ε) - 1 := by linarith
  have hsq : s ε ^ 2 = 2 * exp (-ε) - 1 := Real.sq_sqrt hu
  have hb := exp_neg_bound (ε := ε) (by linarith)
  have hst : 3 / 4 ≤ s ε + (1 - ε) := by linarith [s_nonneg ε]
  have hprod : (s ε - (1 - ε)) * (s ε + (1 - ε)) = 2 * (exp (-ε) - (1 - ε + ε ^ 2 / 2)) := by
    nlinarith [hsq]
  have habs : |s ε - (1 - ε)| * (s ε + (1 - ε)) ≤ 4 / 9 * |ε| ^ 3 := by
    rw [← abs_of_pos (by linarith : (0:ℝ) < s ε + (1 - ε)), ← abs_mul, hprod, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  have h3 : 0 ≤ |ε| ^ 3 := by positivity
  nlinarith [abs_nonneg (s ε - (1 - ε))]

/-- **`B` to second order.** For `|ε| ≤ 1/4`, `|B ε − ε/2 − ε²/4| ≤ 2|ε|³`. -/
theorem B_bound {ε : ℝ} (hε : |ε| ≤ 1 / 4) : |B ε - ε / 2 - ε ^ 2 / 4| ≤ 2 * |ε| ^ 3 := by
  have he0 := abs_nonneg ε
  have hlo : -ε ≤ |ε| := neg_le_abs ε
  have hhi : ε ≤ |ε| := le_abs_self ε
  have hs0 := s_nonneg ε
  have hst := s_bound hε
  have h2e : 7 / 4 ≤ 2 - ε := by linarith
  have h1s : 0 < 1 + s ε := by linarith
  have hid : B ε - ε / 2 - ε ^ 2 / 4 =
      2 * ((1 - ε) - s ε) / ((1 + s ε) * (2 - ε)) + ε ^ 3 / (4 * (2 - ε)) := by
    rw [B_eq]
    field_simp
    ring
  have hden : 7 / 4 ≤ (1 + s ε) * (2 - ε) := by nlinarith
  have h1 : |2 * ((1 - ε) - s ε) / ((1 + s ε) * (2 - ε))| ≤ 8 / 7 * |ε| ^ 3 := by
    rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < (1 + s ε) * (2 - ε)),
      div_le_iff₀ (by linarith), abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_sub_comm]
    have h3 : 0 ≤ |ε| ^ 3 := by positivity
    nlinarith
  have h2 : |ε ^ 3 / (4 * (2 - ε))| ≤ 1 / 7 * |ε| ^ 3 := by
    rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 4 * (2 - ε)), div_le_iff₀ (by linarith),
      abs_pow]
    have h3 : 0 ≤ |ε| ^ 3 := by positivity
    nlinarith
  rw [hid]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 8 / 7 * |ε| ^ 3 + 1 / 7 * |ε| ^ 3 := add_le_add h1 h2
    _ ≤ 2 * |ε| ^ 3 := by nlinarith [pow_nonneg he0 3]

/-- **`F` to second order.** For `|ε| ≤ 1/4`, `|F ε − ε/2 − ε²/8| ≤ 4|ε|³`. -/
theorem F_bound {ε : ℝ} (hε : |ε| ≤ 1 / 4) : |F ε - ε / 2 - ε ^ 2 / 8| ≤ 4 * |ε| ^ 3 := by
  set e := |ε| with he
  have he0 : 0 ≤ e := abs_nonneg ε
  have hE := B_bound hε
  set b := B ε
  have hsq : |ε ^ 2| = e ^ 2 := by rw [abs_pow]
  have he2 : e ^ 2 ≤ e / 4 := by nlinarith
  have he3 : e ^ 3 ≤ e ^ 2 / 4 := by nlinarith
  -- `|b − ε/2| ≤ (3/4) e²`
  have hbm : |b - ε / 2| ≤ 3 / 4 * e ^ 2 := by
    have : |b - ε / 2| ≤ |b - ε / 2 - ε ^ 2 / 4| + |ε ^ 2 / 4| := by
      calc |b - ε / 2| = |(b - ε / 2 - ε ^ 2 / 4) + ε ^ 2 / 4| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [abs_div, hsq, abs_of_pos (by norm_num : (0:ℝ) < 4)] at this
    linarith
  have hb : |b| ≤ e := by
    have : |b| ≤ |b - ε / 2| + |ε / 2| := by
      calc |b| = |(b - ε / 2) + ε / 2| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)] at this
    linarith
  have hbp : |b + ε / 2| ≤ 3 / 2 * e := by
    calc |b + ε / 2| ≤ |b| + |ε / 2| := abs_add_le _ _
      _ = |b| + e / 2 := by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      _ ≤ 3 / 2 * e := by linarith
  -- the logarithm to second order
  have hb1 : |-b| < 1 := by rw [abs_neg]; linarith
  have hlog := Real.abs_log_sub_add_sum_range_le hb1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at hlog
  have hL : |log (1 + b) - b + b ^ 2 / 2| ≤ 4 / 3 * e ^ 3 := by
    have hden : 3 / 4 ≤ 1 - |b| := by linarith
    have hb3 : |b| ^ 3 ≤ e ^ 3 := pow_le_pow_left₀ (abs_nonneg b) hb 3
    have hq : |b| ^ (2 + 1) / (1 - |b|) ≤ 4 / 3 * e ^ 3 := by
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ |b| ^ 3 := by positivity
      norm_num
      nlinarith
    have hlog' : |log (1 + b) - b + b ^ 2 / 2| ≤ |b| ^ (2 + 1) / (1 - |b|) := by
      convert hlog using 2
      push_cast
      ring
    exact hlog'.trans hq
  have hid : F ε - ε / 2 - ε ^ 2 / 8 =
      (log (1 + b) - b + b ^ 2 / 2) + (b - ε / 2 - ε ^ 2 / 4) - (b - ε / 2) * (b + ε / 2) / 2 := by
    rw [F_eq_log]; ring
  have hP : |(b - ε / 2) * (b + ε / 2) / 2| ≤ 9 / 16 * e ^ 3 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have := mul_le_mul hbm hbp (abs_nonneg _) (by positivity)
    nlinarith
  rw [hid]
  calc _ ≤ |(log (1 + b) - b + b ^ 2 / 2) + (b - ε / 2 - ε ^ 2 / 4)| +
        |(b - ε / 2) * (b + ε / 2) / 2| := abs_sub _ _
    _ ≤ (|log (1 + b) - b + b ^ 2 / 2| + |b - ε / 2 - ε ^ 2 / 4|) +
        |(b - ε / 2) * (b + ε / 2) / 2| := by gcongr; exact abs_add_le _ _
    _ ≤ (4 / 3 * e ^ 3 + 2 * e ^ 3) + 9 / 16 * e ^ 3 := by gcongr
    _ ≤ 4 * e ^ 3 := by nlinarith [pow_nonneg he0 3]

theorem eventually_small : ∀ᶠ ε in 𝓝 (0:ℝ), |ε| ≤ 1 / 4 := by
  have : Metric.ball (0:ℝ) (1 / 4) ∈ 𝓝 (0:ℝ) := Metric.ball_mem_nhds 0 (by norm_num)
  filter_upwards [this] with ε hε
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
  exact hε.le

/-- **Lemma 2.4.** `B ε = ε/2 + ε²/4 + O(ε³)` as `ε → 0`. -/
theorem B_taylor : (fun ε => B ε - ε / 2 - ε ^ 2 / 4) =O[𝓝 0] fun ε => ε ^ 3 := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_small] with ε hε
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  exact B_bound hε

/-- **Lemma 2.4.** `F ε = ε/2 + ε²/8 + O(ε³)` as `ε → 0`. -/
theorem F_taylor : (fun ε => F ε - ε / 2 - ε ^ 2 / 8) =O[𝓝 0] fun ε => ε ^ 3 := by
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_small] with ε hε
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  exact F_bound hε

/-- A second-order expansion `g ε = ε/2 + c ε² + O(ε³)` with `g 0 = 0` gives `g′(0) = 1/2`. -/
theorem hasDerivAt_of_taylor {g : ℝ → ℝ} {c : ℝ} (h0 : g 0 = 0)
    (h : (fun ε => g ε - ε / 2 - c * ε ^ 2) =O[𝓝 0] fun ε => ε ^ 3) :
    HasDerivAt g (1 / 2) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have h3 : (fun ε : ℝ => ε ^ 3) =o[𝓝 0] fun ε => ε := isLittleO_pow_id (by norm_num)
  have h2 : (fun ε : ℝ => c * ε ^ 2) =o[𝓝 0] fun ε => ε :=
    (isLittleO_pow_id (by norm_num : 1 < 2)).const_mul_left c
  have := (h.trans_isLittleO h3).add h2
  refine this.congr_left fun ε => ?_
  simp [h0]; ring

/-- **Lemma 2.4.** `F′(0) = 1/2`. -/
theorem hasDerivAt_F : HasDerivAt F (1 / 2) 0 :=
  hasDerivAt_of_taylor (c := 1 / 8) F_zero (F_taylor.congr_left fun ε => by ring)

/-- `B′(0) = 1/2`. -/
theorem hasDerivAt_B : HasDerivAt B (1 / 2) 0 :=
  hasDerivAt_of_taylor (c := 1 / 4) B_zero (B_taylor.congr_left fun ε => by ring)

/-- **Theorem 2.2, (2.3).** `x ^ T ≤ d p` gives `x ≤ d(p)^{1/T}`. -/
theorem gap_ratio_le {p x T : ℝ} (hx : 0 < x) (hT : 0 < T) (hxT : x ^ T ≤ d p) :
    x ≤ d p ^ (1 / T) := by
  have h := Real.rpow_le_rpow (Real.rpow_pos_of_pos hx T).le hxT
    (by positivity : (0:ℝ) ≤ 1 / T)
  rwa [← Real.rpow_mul hx.le, mul_one_div_cancel hT.ne', Real.rpow_one] at h

/-- `e^{−F ε} = (s ε + 1)/2`. -/
theorem exp_neg_F (ε : ℝ) : exp (-F ε) = (s ε + 1) / 2 := by
  have hpos : 0 < (s ε + 1) / 2 := by have := s_nonneg ε; positivity
  have hF : F ε = -log ((s ε + 1) / 2) := rfl
  rw [hF, neg_neg, exp_log hpos]

/-- **`twoLevel` inverts `F`.** `twoLevel (F ε) = ε` for `ε ≤ log 2`. DERIVED: `2`. -/
theorem twoLevel_F {ε : ℝ} (hε : ε ≤ log 2) : twoLevel (F ε) = ε := by
  have hw : exp (-log 2) ≤ exp (-ε) := exp_le_exp.mpr (by linarith)
  rw [exp_neg, exp_log two_pos] at hw
  have hs2 : s ε ^ 2 = 2 * exp (-ε) - 1 := Real.sq_sqrt (by linarith)
  have hp : pur (F ε) = exp (-ε) := by
    unfold pur
    rw [exp_neg_F]
    linear_combination (1 / 2 : ℝ) * hs2
  unfold twoLevel
  rw [hp, log_exp, neg_neg]

/-- **`F` inverts `twoLevel`** on `[0, log 2]`. DERIVED: `2`. -/
theorem F_twoLevel {u : ℝ} (hu : u ∈ Icc 0 (log 2)) : F (twoLevel u) = u := by
  have hw := exp_neg_mem hu
  have he : exp (-twoLevel u) = pur u := by
    unfold twoLevel
    rw [neg_neg, exp_log (pur_pos u)]
  have hsq : 2 * pur u - 1 = (2 * exp (-u) - 1) ^ 2 := by unfold pur; ring
  have hF : F (twoLevel u) = -log ((√(2 * exp (-twoLevel u) - 1) + 1) / 2) := rfl
  rw [hF, he, hsq, Real.sqrt_sq (by linarith [hw.1]),
    show (2 * exp (-u) - 1 + 1) / 2 = exp (-u) by ring, log_exp, neg_neg]

/-- `F` maps `[0, ∞)` into `[0, log 2]`. DERIVED: `2`. -/
theorem F_mem {ε : ℝ} (hε : 0 ≤ ε) : F ε ∈ Icc 0 (log 2) := by
  have hs0 := s_nonneg ε
  have hs1 : s ε ≤ 1 := by
    have h1 : 2 * exp (-ε) - 1 ≤ 1 := by
      linarith [exp_le_one_iff.mpr (by linarith : -ε ≤ 0)]
    calc s ε = √(2 * exp (-ε) - 1) := rfl
      _ ≤ √1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  have hF : F ε = -log ((s ε + 1) / 2) := rfl
  have hq : 0 < (s ε + 1) / 2 := by positivity
  constructor
  · rw [hF, neg_nonneg]
    exact log_nonpos hq.le (by linarith)
  · have h := log_le_log (by norm_num : (0:ℝ) < 1 / 2) (by linarith : (1 / 2 : ℝ) ≤ (s ε + 1) / 2)
    rw [one_div, log_inv] at h
    rw [hF]
    linarith

/-- `twoLevel` maps `[0, log 2]` into itself. DERIVED: `2`. -/
theorem twoLevel_mem {u : ℝ} (hu : u ∈ Icc 0 (log 2)) : twoLevel u ∈ Icc 0 (log 2) := by
  have h0 : (0:ℝ) ∈ Icc 0 (log 2) := ⟨le_rfl, (log_pos one_lt_two).le⟩
  have h2 : log 2 ∈ Icc 0 (log 2) := ⟨(log_pos one_lt_two).le, le_rfl⟩
  have hm := twoLevel_strictMonoOn.monotoneOn
  have a := hm h0 hu hu.1
  have b := hm hu h2 hu.2
  rw [twoLevel_zero] at a
  rw [twoLevel_log_two] at b
  exact ⟨a, b⟩

/-- **Lemma 2.4 (monotonicity).** `F` is strictly increasing on `[0, log 2]`. DERIVED: `2`. -/
theorem F_strictMonoOn : StrictMonoOn F (Icc 0 (log 2)) := by
  intro u hu v hv huv
  have hwv := exp_neg_mem hv
  have hlt : exp (-v) < exp (-u) := exp_lt_exp.mpr (by linarith)
  have hs : s v < s u := Real.sqrt_lt_sqrt (by linarith [hwv.1]) (by linarith)
  have hq : 0 < (s v + 1) / 2 := by have := s_nonneg v; positivity
  have hFu : F u = -log ((s u + 1) / 2) := rfl
  have hFv : F v = -log ((s v + 1) / 2) := rfl
  rw [hFu, hFv, neg_lt_neg_iff]
  exact log_lt_log hq (by linarith)

/-- **Lemma 2.4 (convexity).** `F` is convex on `[0, log 2]`: it is the increasing inverse of the
concave `twoLevel`. DERIVED: `2`. -/
theorem F_convexOn : ConvexOn ℝ (Icc 0 (log 2)) F := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hX := F_mem hx.1
  have hY := F_mem hy.1
  have hXY : a • F x + b • F y ∈ Icc 0 (log 2) := convex_Icc _ _ hX hY ha hb hab
  have hxy : a • x + b • y ∈ Icc 0 (log 2) := convex_Icc _ _ hx hy ha hb hab
  have hc := twoLevel_concaveOn.2 hX hY ha hb hab
  rw [twoLevel_F hx.2, twoLevel_F hy.2] at hc
  have h := F_strictMonoOn.monotoneOn hxy (twoLevel_mem hXY) hc
  rwa [F_twoLevel hXY] at h

/-- **Lemma 2.4, (2.6).** For `0 < ε* ≤ log 2` and `0 ≤ ε ≤ ε*`, `F ε ≤ (F ε*/ε*) ε`.
DERIVED: `2`. -/
theorem F_chord {ε ε' : ℝ} (h0 : 0 < ε') (h2 : ε' ≤ log 2) (hε : 0 ≤ ε) (hεε : ε ≤ ε') :
    F ε ≤ F ε' / ε' * ε := by
  have hz : (0:ℝ) ∈ Icc 0 (log 2) := ⟨le_rfl, (log_pos one_lt_two).le⟩
  have hθ0 : 0 ≤ ε / ε' := div_nonneg hε h0.le
  have hθ1 : ε / ε' ≤ 1 := (div_le_one h0).mpr hεε
  have h := F_convexOn.2 hz ⟨h0.le, h2⟩ (by linarith : 0 ≤ 1 - ε / ε') hθ0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, F_zero] at h
  have e1 : ε / ε' * ε' = ε := by field_simp
  have e2 : ε / ε' * F ε' = F ε' / ε' * ε := by ring
  rw [e1] at h
  linarith

end MassGap.PurityTaylor

#print axioms MassGap.PurityTaylor.gap_log
#print axioms MassGap.PurityTaylor.gap_log_sharp
#print axioms MassGap.PurityTaylor.s_nonneg
#print axioms MassGap.PurityTaylor.B_eq
#print axioms MassGap.PurityTaylor.B_eq_d
#print axioms MassGap.PurityTaylor.F_eq_log
#print axioms MassGap.PurityTaylor.s_zero
#print axioms MassGap.PurityTaylor.F_zero
#print axioms MassGap.PurityTaylor.B_zero
#print axioms MassGap.PurityTaylor.exp_neg_bound
#print axioms MassGap.PurityTaylor.s_bound
#print axioms MassGap.PurityTaylor.B_bound
#print axioms MassGap.PurityTaylor.F_bound
#print axioms MassGap.PurityTaylor.eventually_small
#print axioms MassGap.PurityTaylor.B_taylor
#print axioms MassGap.PurityTaylor.F_taylor
#print axioms MassGap.PurityTaylor.hasDerivAt_of_taylor
#print axioms MassGap.PurityTaylor.hasDerivAt_F
#print axioms MassGap.PurityTaylor.hasDerivAt_B
#print axioms MassGap.PurityTaylor.gap_ratio_le
#print axioms MassGap.PurityTaylor.exp_neg_F
#print axioms MassGap.PurityTaylor.twoLevel_F
#print axioms MassGap.PurityTaylor.F_twoLevel
#print axioms MassGap.PurityTaylor.F_mem
#print axioms MassGap.PurityTaylor.twoLevel_mem
#print axioms MassGap.PurityTaylor.F_strictMonoOn
#print axioms MassGap.PurityTaylor.F_convexOn
#print axioms MassGap.PurityTaylor.F_chord
