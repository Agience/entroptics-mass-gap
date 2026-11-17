import MassGap.PurityBesselK

/-!
# MassGap.PurityFreeFieldLimit — the change of variables (B.1) and the limit of `r⁸ log²(1/r) C(r)`

Proposition B.1 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510,
`Paper-2/Paper-2.pdf`). With `L = log(1/r)` and `q_r(u) = L² / log²(e + u²/r²)`,

  `∫₀^∞ u⁶ K₁(u) q_r(u) du → 384 · 1/4 = 96` as `r → 0⁺`,

and `r⁸ log²(1/r) C(r) = c/(2π²) ∫₀^∞ u⁶ K₁ q_r → 3d∗/π⁴` at `c = d∗/(16π²)`.

The integral splits at `u = √r`.

* `one_le_log`: `1 ≤ log(e + x)` at `x ≥ 0`.
* `q_nonneg`, `q_le_sq`: `0 ≤ q_r(u) ≤ L²`.
* `q_le_one`: `q_r(u) ≤ 1` at `0 < r < 1`, `u > √r`, from `u²/r² ≥ 1/r`.
* `integrableOn_moment_q`: `u⁶ K₁ q_r` is integrable on `(0, ∞)`, dominated by `L² u⁶ K₁`.
* `tail_le`: `∫_{(0, √r]} u⁶ K₁ q_r ≤ L² r³/6`, from `u⁶ K₁(u) ≤ u⁵` (`K1_le`);
  `tail_bound_tendsto`: `L² r³/6 → 0` (`tendsto_log_mul_rpow_nhdsGT_zero`).
* `head_tendsto`: `∫_{(√r, ∞)} u⁶ K₁ q_r → 96` by dominated convergence with bound `u⁶ K₁`
  (`integrableOn_moment_K1`) and pointwise limit `u⁶ K₁(u)/4`
  (`PurityFreeField.quotient_tendsto`).
* `moment_limit`: `∫₀^∞ u⁶ K₁ q_r → 96`.
* `limit_scaled`: `c/(2π²) ∫₀^∞ u⁶ K₁ q_r → 48c/π²`; `limit_scaled_constant`: `→ 3d∗/π⁴` at
  `c = d∗/(16π²)`.
* `rho`: `ρ(s) = c s²/log²(e + s)`; `integrand`: `ρ(s) √s K₁(r√s)/(4π² r)`; `C`:
  `C(r) = ∫₀^∞ integrand(s) ds`.
* `integral_comp_sq`: `∫₀^∞ f(s) ds = ∫₀^∞ 2v f(v²) dv`.
* `integrand_comp`: after `s = v²`, `v = u/r`, `2v · integrand(v²)` is
  `c/(2π²) r⁻⁷ u⁶ K₁(u)/log²(e + u²/r²)`.
* `integrableOn_moment_log`: `u⁶ K₁(u)/log²(e + u²/r²)` is integrable on `(0, ∞)`.
* `integrableOn_integrand`: the integrand of `C` is integrable on `(0, ∞)` at `r > 0`, through
  `integrableOn_Ioi_comp_rpow_iff` and `integrableOn_Ioi_comp_mul_left_iff`.
* `covariance_eq`: (B.1), `r⁸ L² C(r) = c/(2π²) ∫₀^∞ u⁶ K₁ q_r` at `r > 0` (`u = r√s`).
* `covariance_limit`: `r⁸ log²(1/r) C(r) → 3d∗/π⁴` at `c = d∗/(16π²)`.
-/

namespace MassGap.PurityFreeFieldLimit

open Real Filter Topology MeasureTheory Set
open MassGap.PurityBesselK (K1 K1_nonneg K1_le integrableOn_moment_K1 moment_K1)

/-- `1 ≤ log(e + x)` at `x ≥ 0`. -/
theorem one_le_log {x : ℝ} (hx : 0 ≤ x) : 1 ≤ log (exp 1 + x) :=
  calc (1 : ℝ) = log (exp 1) := (log_exp 1).symm
    _ ≤ log (exp 1 + x) := log_le_log (exp_pos 1) (by linarith)

/-- The quotient `q_r(u) = L² / log²(e + u²/r²)`, `L = log(1/r)`. -/
noncomputable def q (r u : ℝ) : ℝ := log (1 / r) ^ 2 / log (exp 1 + u ^ 2 / r ^ 2) ^ 2

theorem q_nonneg (r u : ℝ) : 0 ≤ q r u := by unfold q; positivity

/-- `q_r(u) ≤ L²`. -/
theorem q_le_sq (r u : ℝ) : q r u ≤ log (1 / r) ^ 2 := by
  have h := one_le_log (div_nonneg (sq_nonneg u) (sq_nonneg r))
  have h2 : 1 ≤ log (exp 1 + u ^ 2 / r ^ 2) ^ 2 := by nlinarith
  exact div_le_self (sq_nonneg _) h2

/-- `q_r(u) ≤ 1` at `0 < r < 1`, `u > √r`. -/
theorem q_le_one {r u : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hu : sqrt r < u) : q r u ≤ 1 := by
  have hur : r < u ^ 2 := by nlinarith [sq_sqrt hr0.le, sqrt_nonneg r]
  have hL : 0 < log (1 / r) := log_pos (one_lt_one_div hr0 hr1)
  have hx : 1 / r ≤ exp 1 + u ^ 2 / r ^ 2 := by
    have : 1 / r ≤ u ^ 2 / r ^ 2 := by
      rw [div_le_div_iff₀ hr0 (by positivity)]
      nlinarith
    linarith [exp_pos 1]
  have hle : log (1 / r) ≤ log (exp 1 + u ^ 2 / r ^ 2) := log_le_log (by positivity) hx
  unfold q
  rw [div_le_one (pow_pos (hL.trans_le hle) 2)]
  nlinarith

theorem measurable_q (r : ℝ) : Measurable (q r) := by
  unfold q
  fun_prop

/-- `u⁶ K₁ q_r` is integrable on `(0, ∞)`. -/
theorem integrableOn_moment_q (r : ℝ) :
    IntegrableOn (fun u => u ^ 6 * K1 u * q r u) (Ioi 0) := by
  have hI : Integrable (fun u => u ^ 6 * K1 u) (volume.restrict (Ioi 0)) := integrableOn_moment_K1
  refine Integrable.mono' (hI.mul_const (log (1 / r) ^ 2))
    (hI.aestronglyMeasurable.mul (measurable_q r).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_)
  have h0 : 0 ≤ u ^ 6 * K1 u := mul_nonneg (pow_nonneg (le_of_lt hu) 6) (K1_nonneg u)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (q_nonneg r u))]
  exact mul_le_mul_of_nonneg_left (q_le_sq r u) h0

/-- `u⁶ K₁(u) ≤ u⁵` at `u > 0`. -/
theorem moment_K1_le {u : ℝ} (hu : 0 < u) : u ^ 6 * K1 u ≤ u ^ 5 :=
  calc u ^ 6 * K1 u ≤ u ^ 6 * (1 / u) := mul_le_mul_of_nonneg_left (K1_le hu) (by positivity)
    _ = u ^ 5 := by rw [mul_one_div, pow_succ, mul_div_assoc, div_self hu.ne', mul_one]

/-- `∫_{(0, √r]} u⁶ K₁ q_r ≤ L² r³/6`. -/
theorem tail_le {r : ℝ} (hr0 : 0 < r) :
    ∫ u in Ioc 0 (sqrt r), u ^ 6 * K1 u * q r u ≤ log (1 / r) ^ 2 * r ^ 3 / 6 := by
  have hc : Continuous fun u : ℝ => log (1 / r) ^ 2 * u ^ 5 := by fun_prop
  have hpt : ∀ u ∈ Ioc 0 (sqrt r), u ^ 6 * K1 u * q r u ≤ log (1 / r) ^ 2 * u ^ 5 := by
    intro u hu
    calc u ^ 6 * K1 u * q r u ≤ u ^ 5 * log (1 / r) ^ 2 :=
          mul_le_mul (moment_K1_le hu.1) (q_le_sq r u) (q_nonneg r u) (pow_nonneg hu.1.le 5)
      _ = log (1 / r) ^ 2 * u ^ 5 := mul_comm _ _
  have hm := setIntegral_mono_on ((integrableOn_moment_q r).mono_set Ioc_subset_Ioi_self)
    (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc hpt
  have he : ∫ u in Ioc 0 (sqrt r), log (1 / r) ^ 2 * u ^ 5 = log (1 / r) ^ 2 * r ^ 3 / 6 := by
    rw [← intervalIntegral.integral_of_le (sqrt_nonneg r), intervalIntegral.integral_const_mul,
      integral_pow]
    have h6 : sqrt r ^ (5 + 1) = r ^ 3 := by
      rw [show 5 + 1 = 2 * 3 by rfl, pow_mul, sq_sqrt hr0.le]
    rw [h6]
    ring
  linarith

/-- `L² r³/6 → 0` as `r → 0⁺`. -/
theorem tail_bound_tendsto :
    Tendsto (fun r : ℝ => log (1 / r) ^ 2 * r ^ 3 / 6) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 3 / 2) (by norm_num)
  have h3 : Tendsto (fun x : ℝ => (log x * x ^ (3 / 2 : ℝ)) ^ 2 / 6) (𝓝[>] 0)
      (𝓝 ((0 : ℝ) ^ 2 / 6)) := (h.pow 2).div_const 6
  rw [show (0 : ℝ) ^ 2 / 6 = 0 by norm_num] at h3
  refine h3.congr' (eventually_mem_nhdsWithin.mono fun x hx => ?_)
  have hx' : (0 : ℝ) < x := hx
  have hp : (x ^ (3 / 2 : ℝ)) ^ 2 = x ^ 3 := by
    rw [← rpow_natCast, ← rpow_mul hx'.le,
      show (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast]
  dsimp only
  rw [mul_pow, hp, one_div, log_inv, neg_sq]

/-- `∫_{(√r, ∞)} u⁶ K₁ q_r → 96` as `r → 0⁺`, by dominated convergence. -/
theorem head_tendsto :
    Tendsto (fun r : ℝ => ∫ u in Ioi 0, (Ioi (sqrt r)).indicator (fun u => u ^ 6 * K1 u * q r u) u)
      (𝓝[>] 0) (𝓝 96) := by
  have hI : Integrable (fun u => u ^ 6 * K1 u) (volume.restrict (Ioi 0)) := integrableOn_moment_K1
  have h96 : ∫ u in Ioi 0, u ^ 6 * K1 u * (1 / 4) = 96 := by
    rw [integral_mul_const, moment_K1]
    norm_num
  rw [← h96]
  refine tendsto_integral_filter_of_dominated_convergence (fun u => u ^ 6 * K1 u) ?_ ?_ hI ?_
  · exact Eventually.of_forall fun r =>
      (hI.aestronglyMeasurable.mul (measurable_q r).aestronglyMeasurable).indicator measurableSet_Ioi
  · have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r < 1 :=
      (eventually_mem_nhdsWithin).and (nhdsWithin_le_nhds (gt_mem_nhds one_pos))
    refine hev.mono fun r hr => (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_)
    have h0 : 0 ≤ u ^ 6 * K1 u := mul_nonneg (pow_nonneg (le_of_lt hu) 6) (K1_nonneg u)
    by_cases hs : u ∈ Ioi (sqrt r)
    · rw [indicator_of_mem hs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (q_nonneg r u))]
      calc u ^ 6 * K1 u * q r u ≤ u ^ 6 * K1 u * 1 :=
            mul_le_mul_of_nonneg_left (q_le_one hr.1 hr.2 hs) h0
        _ = u ^ 6 * K1 u := mul_one _
    · rw [indicator_of_notMem hs, norm_zero]
      exact h0
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_)
    have hs : Tendsto sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := continuous_sqrt.tendsto 0
      rw [sqrt_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), sqrt r < u := hs.eventually (gt_mem_nhds hu)
    refine ((PurityFreeField.quotient_tendsto hu).const_mul (u ^ 6 * K1 u)).congr'
      (hev.mono fun r hr => ?_)
    dsimp only
    rw [indicator_of_mem (show u ∈ Ioi (sqrt r) from hr)]
    rfl

/-- `∫₀^∞ u⁶ K₁(u) L² / log²(e + u²/r²) du → 96` as `r → 0⁺`. -/
theorem moment_limit :
    Tendsto (fun r : ℝ => ∫ u in Ioi 0, u ^ 6 * K1 u * q r u) (𝓝[>] 0) (𝓝 96) := by
  have hsplit : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∫ u in Ioi 0, u ^ 6 * K1 u * q r u =
      (∫ u in Ioc 0 (sqrt r), u ^ 6 * K1 u * q r u) +
        ∫ u in Ioi 0, (Ioi (sqrt r)).indicator (fun u => u ^ 6 * K1 u * q r u) u := by
    refine Eventually.of_forall fun r => ?_
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.2 (Ioi_subset_Ioi (sqrt_nonneg r)),
      ← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        ((integrableOn_moment_q r).mono_set Ioc_subset_Ioi_self)
        ((integrableOn_moment_q r).mono_set (Ioi_subset_Ioi (sqrt_nonneg r))),
      Ioc_union_Ioi_eq_Ioi (sqrt_nonneg r)]
  have htail : Tendsto (fun r : ℝ => ∫ u in Ioc 0 (sqrt r), u ^ 6 * K1 u * q r u) (𝓝[>] 0)
      (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tail_bound_tendsto
      (Eventually.of_forall fun r => setIntegral_nonneg measurableSet_Ioc fun u hu =>
        mul_nonneg (mul_nonneg (pow_nonneg hu.1.le 6) (K1_nonneg u)) (q_nonneg r u))
      (eventually_mem_nhdsWithin.mono fun r hr => tail_le hr)
  have h := htail.add head_tendsto
  rw [zero_add] at h
  exact h.congr' (hsplit.mono fun r hr => hr.symm)

/-- `c/(2π²) ∫₀^∞ u⁶ K₁ q_r → 48c/π²` (`PurityFreeField.limit_coeff`). -/
theorem limit_scaled (c : ℝ) :
    Tendsto (fun r : ℝ => c / (2 * π ^ 2) * ∫ u in Ioi 0, u ^ 6 * K1 u * q r u) (𝓝[>] 0)
      (𝓝 (48 * c / π ^ 2)) := by
  have h := moment_limit.const_mul (c / (2 * π ^ 2))
  rwa [show c / (2 * π ^ 2) * 96 = 48 * c / π ^ 2 by rw [← PurityFreeField.limit_coeff]; ring]
    at h

/-- At `c = d∗/(16π²)` the limit is `3d∗/π⁴` (`PurityFreeField.limit_constant`). -/
theorem limit_scaled_constant (d : ℝ) :
    Tendsto (fun r : ℝ => d / (16 * π ^ 2) / (2 * π ^ 2) * ∫ u in Ioi 0, u ^ 6 * K1 u * q r u)
      (𝓝[>] 0) (𝓝 (3 * d / π ^ 4)) := by
  have h := limit_scaled (d / (16 * π ^ 2))
  rwa [show 48 * (d / (16 * π ^ 2)) / π ^ 2 = 3 * d / π ^ 4 by
    rw [← PurityFreeField.limit_constant]; ring] at h

/-- The squared-mass density `ρ(s) = c s² / log²(e + s)`. -/
noncomputable def rho (c s : ℝ) : ℝ := c * s ^ 2 / log (exp 1 + s) ^ 2

/-- The integrand `ρ(s) √s K₁(r√s) / (4π² r)` of `C`. -/
noncomputable def integrand (c r s : ℝ) : ℝ := rho c s * sqrt s / (4 * π ^ 2 * r) * K1 (r * sqrt s)

/-- The separated Euclidean-time covariance `C(r) = ∫₀^∞ ρ(s) √s K₁(r√s) / (4π² r) ds`. -/
noncomputable def C (c r : ℝ) : ℝ := ∫ s in Ioi 0, integrand c r s

/-- `s = v²`: `∫₀^∞ f(s) ds = ∫₀^∞ 2v f(v²) dv`. -/
theorem integral_comp_sq (f : ℝ → ℝ) :
    ∫ s in Ioi 0, f s = ∫ v in Ioi 0, 2 * v * f (v ^ 2) := by
  rw [← integral_comp_rpow_Ioi f (p := 2) two_ne_zero]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [smul_eq_mul, show (2 : ℝ) - 1 = 1 by norm_num, rpow_one, rpow_two, abs_two]

/-- The integrand after `s = v²`, `v = u/r`:
`2v · integrand(v²) = c/(2π²) r⁻⁷ u⁶ K₁(u) / log²(e + u²/r²)` at `r, u > 0`. -/
theorem integrand_comp {c r u : ℝ} (hr : 0 < r) (hu : 0 < u) :
    2 * (r⁻¹ * u) * integrand c r ((r⁻¹ * u) ^ 2) =
      c / (2 * π ^ 2) * r⁻¹ ^ 7 * (u ^ 6 * K1 u / log (exp 1 + u ^ 2 / r ^ 2) ^ 2) := by
  have hv : 0 ≤ r⁻¹ * u := mul_nonneg (inv_nonneg.2 hr.le) hu.le
  simp only [integrand, rho, sqrt_sq hv]
  rw [show r * (r⁻¹ * u) = u by rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul],
    show (r⁻¹ * u) ^ 2 = u ^ 2 / r ^ 2 by rw [mul_pow, inv_pow]; ring]
  ring

/-- `u⁶ K₁(u) / log²(e + u²/r²)` is integrable on `(0, ∞)`, dominated by `u⁶ K₁`. -/
theorem integrableOn_moment_log (r : ℝ) :
    IntegrableOn (fun u => u ^ 6 * K1 u / log (exp 1 + u ^ 2 / r ^ 2) ^ 2) (Ioi 0) := by
  have hI : Integrable (fun u => u ^ 6 * K1 u) (volume.restrict (Ioi 0)) := integrableOn_moment_K1
  have hm : Measurable fun u : ℝ => log (exp 1 + u ^ 2 / r ^ 2) ^ 2 := by fun_prop
  refine Integrable.mono' hI ((hI.aestronglyMeasurable.mul hm.inv.aestronglyMeasurable).congr
    (ae_of_all _ fun u => (div_eq_mul_inv _ _).symm)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_)
  have h0 : 0 ≤ u ^ 6 * K1 u := mul_nonneg (pow_nonneg (le_of_lt hu) 6) (K1_nonneg u)
  have h1 := one_le_log (div_nonneg (sq_nonneg u) (sq_nonneg r))
  have h2 : 1 ≤ log (exp 1 + u ^ 2 / r ^ 2) ^ 2 := by nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 (by positivity))]
  exact div_le_self h0 h2

/-- The integrand of `C` is integrable on `(0, ∞)` at `r > 0`. -/
theorem integrableOn_integrand (c : ℝ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (integrand c r) (Ioi 0) := by
  rw [← integrableOn_Ioi_comp_rpow_iff (integrand c r) (p := 2) two_ne_zero]
  have e : (fun x : ℝ => (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • integrand c r (x ^ (2 : ℝ))) =
      fun v => 2 * v * integrand c r (v ^ 2) := by
    funext v
    rw [smul_eq_mul, show (2 : ℝ) - 1 = 1 by norm_num, rpow_one, rpow_two, abs_two]
  rw [e]
  have hmul := integrableOn_Ioi_comp_mul_left_iff (fun v => 2 * v * integrand c r (v ^ 2)) 0
    (inv_pos.2 hr)
  rw [mul_zero] at hmul
  rw [← hmul]
  exact IntegrableOn.congr_fun ((integrableOn_moment_log r).const_mul (c / (2 * π ^ 2) * r⁻¹ ^ 7))
    (fun u hu => (integrand_comp hr hu).symm) measurableSet_Ioi

/-- (B.1): `r⁸ L² C(r) = c/(2π²) ∫₀^∞ u⁶ K₁(u) L² / log²(e + u²/r²) du` at `r > 0`
(`u = r√s`). -/
theorem covariance_eq (c : ℝ) {r : ℝ} (hr : 0 < r) :
    r ^ 8 * log (1 / r) ^ 2 * C c r = c / (2 * π ^ 2) * ∫ u in Ioi 0, u ^ 6 * K1 u * q r u := by
  set g : ℝ → ℝ := fun v => 2 * v * integrand c r (v ^ 2) with hg
  have h0 : C c r = ∫ v in Ioi 0, g v := integral_comp_sq (integrand c r)
  have h1 : ∫ v in Ioi 0, g v = r⁻¹ * ∫ u in Ioi 0, g (r⁻¹ * u) := by
    rw [integral_comp_mul_left_Ioi g 0 (inv_pos.2 hr), mul_zero, inv_inv, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have h2 : ∫ u in Ioi 0, g (r⁻¹ * u) = ∫ u in Ioi 0,
      c / (2 * π ^ 2) * r⁻¹ ^ 7 * (u ^ 6 * K1 u / log (exp 1 + u ^ 2 / r ^ 2) ^ 2) := by
    exact setIntegral_congr_fun measurableSet_Ioi fun u hu => integrand_comp hr hu
  have h3 : ∫ u in Ioi 0, u ^ 6 * K1 u * q r u =
      log (1 / r) ^ 2 * ∫ u in Ioi 0, u ^ 6 * K1 u / log (exp 1 + u ^ 2 / r ^ 2) ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [q]
    ring
  have e : r ^ 8 * r⁻¹ * r⁻¹ ^ 7 = 1 := by
    have := hr.ne'
    field_simp
  rw [h0, h1, h2, integral_const_mul, h3]
  linear_combination (c / (2 * π ^ 2) * log (1 / r) ^ 2 *
    ∫ u in Ioi 0, u ^ 6 * K1 u / log (exp 1 + u ^ 2 / r ^ 2) ^ 2) * e

/-- The limit of Proposition B.1: `r⁸ log²(1/r) C(r) → 3d∗/π⁴` as `r → 0⁺` at `c = d∗/(16π²)`. -/
theorem covariance_limit (d : ℝ) :
    Tendsto (fun r : ℝ => r ^ 8 * log (1 / r) ^ 2 * C (d / (16 * π ^ 2)) r) (𝓝[>] 0)
      (𝓝 (3 * d / π ^ 4)) :=
  (limit_scaled_constant d).congr'
    (eventually_mem_nhdsWithin.mono fun _ hr => (covariance_eq _ hr).symm)

end MassGap.PurityFreeFieldLimit

#print axioms MassGap.PurityFreeFieldLimit.one_le_log
#print axioms MassGap.PurityFreeFieldLimit.q_nonneg
#print axioms MassGap.PurityFreeFieldLimit.q_le_sq
#print axioms MassGap.PurityFreeFieldLimit.q_le_one
#print axioms MassGap.PurityFreeFieldLimit.measurable_q
#print axioms MassGap.PurityFreeFieldLimit.integrableOn_moment_q
#print axioms MassGap.PurityFreeFieldLimit.moment_K1_le
#print axioms MassGap.PurityFreeFieldLimit.tail_le
#print axioms MassGap.PurityFreeFieldLimit.tail_bound_tendsto
#print axioms MassGap.PurityFreeFieldLimit.head_tendsto
#print axioms MassGap.PurityFreeFieldLimit.moment_limit
#print axioms MassGap.PurityFreeFieldLimit.limit_scaled
#print axioms MassGap.PurityFreeFieldLimit.limit_scaled_constant
#print axioms MassGap.PurityFreeFieldLimit.integral_comp_sq
#print axioms MassGap.PurityFreeFieldLimit.integrand_comp
#print axioms MassGap.PurityFreeFieldLimit.integrableOn_moment_log
#print axioms MassGap.PurityFreeFieldLimit.integrableOn_integrand
#print axioms MassGap.PurityFreeFieldLimit.covariance_eq
#print axioms MassGap.PurityFreeFieldLimit.covariance_limit
