import Mathlib

/-!
# MassGap.PurityCancel — the analytic content of Theorem 8.1 and Corollary 8.2 of the purity paper

Theorem 8.1 (finite-order nonwrapping cancellation) and Corollary 8.2 (an actual Wilson window
subcase) of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`).

`Z_t(z) = ∫ e^{z A_t} dU` is Mathlib's `complexMGF A_t μ_t` for a probability measure `μ_t` and a
measurable action `A_t` (in the paper, product Haar measure on the links of `s × ℤ/tℤ` and
`A_t = (1/d) Σ_p Re Tr U_p`);
`Ψ_T = 2 log Z_T − log Z_{2T}` (`psi`) with the principal logarithm, and
`R = log(3/2)/(12VT)` (`radius`). The bounds `|A_T| ≤ 6VT` and `|A_{2T}| ≤ 12VT` and the
vanishing (8.1) `Ψ_T^{(n)}(0) = 0` for `n < T` enter as hypotheses.

* `cauchy_remainder`: a function holomorphic on `|z| < R`, continuous on `|z| ≤ R`, bounded by `M`
  on `|z| = R`, with vanishing derivatives of order `< T` at `0`, has
  `|f(z)| ≤ M (|z|/R)^T / (1 − |z|/R)` for `|z| < R` (Cauchy's estimate and the geometric tail).
* `differentiable_mgf`, `mgf_sub_one_le`, `mgf_near_one`: for `|A| ≤ a`, `Z` is entire and
  `|Z(w) − 1| ≤ e^{|w| a} − 1`, at most `1/2` when `|w| a ≤ log(3/2)`.
* `norm_log_le_log_two`: `|u| ≤ 1/2` gives `|log(1 + u)| ≤ log 2` (from the logarithm series).
* `psi_le`: `|Z₁ − 1|, |Z₂ − 1| ≤ 1/2` give `|2 log Z₁ − log Z₂| ≤ 3 log 2`.
* `mgf_ne_zero`: `Z_T` and `Z_{2T}` do not vanish on `|z| ≤ R`.
* `remainder`: (8.2), `|Ψ_T(z)| ≤ 3 log 2 (|z|/R)^T / (1 − |z|/R)` for `|z| < R`.
* `window_ratio`: (8.4) and `V < (48T)³` give `βW/R ≤ 1/1000`.
* `window_bound`: `T ≥ 3`, `(2T)³ ≤ V` and that ratio turn (8.2) into `|Ψ_T| ≤ V/(161 (48T)³)`.
* `corollary_window`: Corollary 8.2's bound `|Ψ_T(βW)| ≤ V/(161 (48T)³)` for `s ∈ W_T`.
* `psi_nonneg_trace`: `λ_i ≥ 0` give `0 ≤ 2 log Σ λ_i^T − log Σ λ_i^{2T}` (`Tr K^{2T} ≤ (Tr K^T)²`).

(8.1) for the Wilson action with product Haar measure is `PurityWilsonChain.hvan_wilson`, by
moment matching (`PurityMomentMatch`, `PurityTwoLift`) in place of the cumulant expansion (8.3); it
holds at every transverse extent, so the side condition `s_j ≥ 2T` is not needed for it.

Not formalized here: the identification of the principal logarithm with the analytic logarithm normalized at
`z = 0` (they agree on the disk, where `|Z − 1| ≤ 1/2`).

At odd `T = 2j + 1` the real counterpart `log Z(L′) ≤ 2 log Z(L)` (`L μ = T`, `L′ μ = 2T`) holds
for the Wilson partition function `RectWilsonG.ZRG` over a nontrivial gauge group at `β > 0`
with every spatial extent at least `2` (`PurityOddTimeLower.ZRG_defect_odd_nonneg`, from
positive semidefiniteness of the transfer operator, without the spectral sum), and
`Ψ_T(2β) ≥ 0` at odd `T` on the `SU(N)` Wilson lattice, `N ≥ 2`, is
`PurityOddTimeWilson.psi_nonneg_wilson_odd`.

`PurityMomentMatch` reduces (8.1) to moment matching, `E_{2T}[A^n] = Σ_{i ≤ n} C(n,i) E_T[A^i]
E_T[A^{n−i}]` for `n < T`, working with the principal logarithm directly.

`PurityPlaqCount` instantiates `μ_t` and `A_t` with the product Haar measure and the plaquette
action on the 4-torus, proves the bounds `|A_t| ≤ 6Vt`, `Ψ_T(2β)` real and equal to
`2 log Z_T − log Z_{2T}`, and `Ψ_T(2β) ≥ 0` at even `T` through the transfer-kernel trace
identity `RectTransfer.ZR_eq_traceSeq`.
-/

namespace MassGap.PurityCancel

open Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped Nat

/-- (8.2) for one function: Cauchy's estimate and the geometric tail from degree `T`. -/
theorem cauchy_remainder {f : ℂ → ℂ} {R M : ℝ} {T : ℕ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball 0 R)) (hM : ∀ w ∈ sphere (0 : ℂ) R, ‖f w‖ ≤ M)
    (hvan : ∀ n < T, iteratedDeriv n f 0 = 0) {z : ℂ} (hz : ‖z‖ < R) :
    ‖f z‖ ≤ M * (‖z‖ / R) ^ T / (1 - ‖z‖ / R) := by
  have hq0 : 0 ≤ ‖z‖ / R := div_nonneg (norm_nonneg _) hR.le
  have hq1 : ‖z‖ / R < 1 := (div_lt_one hR).2 hz
  have hzb : z ∈ ball (0 : ℂ) R := by simpa using hz
  have hS := Complex.hasSum_taylorSeries_on_ball hf.differentiableOn hzb
  simp only [sub_zero] at hS
  have hg : HasSum (fun n : ℕ => if n < T then 0 else M * (‖z‖ / R) ^ n)
      (M * (‖z‖ / R) ^ T / (1 - ‖z‖ / R)) := by
    rw [← hasSum_nat_add_iff' T]
    have hsum : ∑ i ∈ Finset.range T, (if i < T then (0 : ℝ) else M * (‖z‖ / R) ^ i) = 0 :=
      Finset.sum_eq_zero fun i hi => if_pos (Finset.mem_range.1 hi)
    rw [hsum, sub_zero]
    have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M * (‖z‖ / R) ^ T)
    have hfun : (fun n : ℕ => if n + T < T then (0 : ℝ) else M * (‖z‖ / R) ^ (n + T)) =
        fun i => M * (‖z‖ / R) ^ T * (‖z‖ / R) ^ i := by
      funext n
      rw [if_neg (by omega), pow_add]
      ring
    rw [hfun, div_eq_mul_inv]
    exact h
  rw [← hS.tsum_eq]
  refine tsum_of_norm_bounded hg fun n => ?_
  by_cases hn : n < T
  · simp [hn, hvan n hn]
  · rw [if_neg hn]
    have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf hM
    have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    rw [norm_smul, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
    calc (n ! : ℝ)⁻¹ * (‖z‖ ^ n * ‖iteratedDeriv n f 0‖)
        ≤ (n ! : ℝ)⁻¹ * (‖z‖ ^ n * (n ! * M / R ^ n)) := by gcongr
      _ = M * (‖z‖ / R) ^ n := by
        rw [div_pow]
        field_simp

/-- `‖e^w − 1‖ ≤ e^{‖w‖} − 1`. -/
theorem norm_exp_sub_one_le (w : ℂ) : ‖Complex.exp w - 1‖ ≤ Real.exp ‖w‖ - 1 := by
  simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum w 1

/-- `x ≤ log(3/2)` gives `e^x − 1 ≤ 1/2`. -/
theorem exp_sub_one_le_half {x : ℝ} (hx : x ≤ Real.log (3 / 2)) : Real.exp x - 1 ≤ 1 / 2 := by
  have := Real.exp_le_exp.2 hx
  rw [Real.exp_log (by norm_num)] at this
  linarith

section MGF

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Ω → ℝ}
  {a : ℝ}

/-- A bounded action has an entire moment generating function. -/
theorem differentiable_mgf (hA : AEMeasurable A μ) (hb : ∀ᵐ ω ∂μ, |A ω| ≤ a) :
    Differentiable ℂ (complexMGF A μ) := by
  have hset : integrableExpSet A μ = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    exact integrable_exp_mul_of_mem_Icc hA (hb.mono fun ω h => abs_le.1 h)
  have h := differentiableOn_complexMGF (X := A) (μ := μ)
  rw [hset, interior_univ] at h
  intro z
  exact h.differentiableAt (by simp)

/-- `|Z(w) − 1| ≤ e^{|w| a} − 1` for `|A| ≤ a`. -/
theorem mgf_sub_one_le (hA : AEMeasurable A μ) (hb : ∀ᵐ ω ∂μ, |A ω| ≤ a) (w : ℂ) :
    ‖complexMGF A μ w - 1‖ ≤ Real.exp (‖w‖ * a) - 1 := by
  have hpt : ∀ᵐ ω ∂μ, ‖Complex.exp (w * A ω) - 1‖ ≤ Real.exp (‖w‖ * a) - 1 := by
    filter_upwards [hb] with ω hω
    refine (norm_exp_sub_one_le _).trans ?_
    gcongr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hω (norm_nonneg _)
  have hmeas : AEStronglyMeasurable (fun ω => Complex.exp (w * A ω)) μ :=
    (Complex.measurable_exp.comp_aemeasurable
      ((Complex.measurable_ofReal.comp_aemeasurable hA).const_mul w)).aestronglyMeasurable
  have hint : Integrable (fun ω => Complex.exp (w * A ω)) μ := by
    refine Integrable.of_bound hmeas (Real.exp (‖w‖ * a)) ?_
    filter_upwards [hb] with ω hω
    refine (Complex.norm_exp_le_exp_norm _).trans ?_
    gcongr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hω (norm_nonneg _)
  have h1 : complexMGF A μ w - 1 = ∫ ω, (Complex.exp (w * A ω) - 1) ∂μ := by
    rw [integral_sub hint (integrable_const 1)]
    simp [complexMGF]
  rw [h1]
  calc ‖∫ ω, (Complex.exp (w * A ω) - 1) ∂μ‖ ≤ ∫ _ω, (Real.exp (‖w‖ * a) - 1) ∂μ :=
        norm_integral_le_of_norm_le (integrable_const _) hpt
    _ = Real.exp (‖w‖ * a) - 1 := by simp

/-- `|w| a ≤ log(3/2)` gives `|Z(w) − 1| ≤ 1/2`. -/
theorem mgf_near_one (hA : AEMeasurable A μ) (hb : ∀ᵐ ω ∂μ, |A ω| ≤ a) {w : ℂ}
    (hw : ‖w‖ * a ≤ Real.log (3 / 2)) : ‖complexMGF A μ w - 1‖ ≤ 1 / 2 :=
  (mgf_sub_one_le hA hb w).trans (exp_sub_one_le_half hw)

end MGF

/-- `|u| ≤ 1/2` gives `|log(1 + u)| ≤ log 2`. -/
theorem norm_log_le_log_two {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) : ‖Complex.log (1 + u)‖ ≤ Real.log 2 := by
  have hu1 : ‖-u‖ < 1 := by rw [norm_neg]; linarith
  have hS := Complex.hasSum_taylorSeries_neg_log hu1
  rw [sub_neg_eq_add] at hS
  have hR := Real.hasSum_pow_div_log_of_abs_lt_one (x := ‖u‖)
    (by rw [abs_of_nonneg (norm_nonneg _)]; linarith)
  have hg : HasSum (fun n : ℕ => ‖u‖ ^ n / n) (-Real.log (1 - ‖u‖)) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [Finset.sum_range_one] using hR
  have hb : ∀ n : ℕ, ‖(-u) ^ n / n‖ ≤ ‖u‖ ^ n / n := fun n => by
    simp [norm_pow, norm_neg]
  have h := tsum_of_norm_bounded hg hb
  rw [hS.tsum_eq, norm_neg] at h
  refine h.trans ?_
  rw [neg_le, ← Real.log_inv]
  exact Real.log_le_log (by norm_num) (by rw [inv_eq_one_div]; linarith)

/-- `|Z₁ − 1|, |Z₂ − 1| ≤ 1/2` give `|2 log Z₁ − log Z₂| ≤ 3 log 2`. -/
theorem psi_le {Z₁ Z₂ : ℂ} (h₁ : ‖Z₁ - 1‖ ≤ 1 / 2) (h₂ : ‖Z₂ - 1‖ ≤ 1 / 2) :
    ‖2 * Complex.log Z₁ - Complex.log Z₂‖ ≤ 3 * Real.log 2 := by
  have l₁ := norm_log_le_log_two h₁
  have l₂ := norm_log_le_log_two h₂
  rw [show 1 + (Z₁ - 1) = Z₁ by ring] at l₁
  rw [show 1 + (Z₂ - 1) = Z₂ by ring] at l₂
  have h := norm_sub_le (2 * Complex.log Z₁) (Complex.log Z₂)
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_mul, h2] at h
  linarith

/-- `|Z − 1| ≤ 1/2` puts `Z` in the slit plane. -/
theorem mem_slitPlane_of_near_one {Z : ℂ} (h : ‖Z - 1‖ ≤ 1 / 2) : Z ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have := Complex.re_le_norm (1 - Z)
  rw [norm_sub_rev] at this
  simp only [Complex.sub_re, Complex.one_re] at this
  linarith

/-- `R = log(3/2)/(12VT)`. DERIVED: `12VT` the bound `|A_{2T}| ≤ 12VT` (six plaquettes per site
on `V · 2T` sites); `3/2 = 1 + 1/2`, so `|w| A ≤ log(3/2)` gives `|e^{wA}| ≤ 3/2`. -/
noncomputable def radius (V : ℝ) (T : ℕ) : ℝ := Real.log (3 / 2) / (12 * V * T)

theorem radius_pos {V : ℝ} {T : ℕ} (hV : 0 < V) (hT : 0 < T) : 0 < radius V T := by
  unfold radius
  have : (0 : ℝ) < T := by exact_mod_cast hT
  exact div_pos (Real.log_pos (by norm_num)) (by positivity)

/-- `|w| ≤ R` and `a ≤ 12VT` give `|w| a ≤ log(3/2)`. -/
theorem radius_mul_le {V a : ℝ} {T : ℕ} (hV : 0 < V) (hT : 0 < T) (ha : a ≤ 12 * V * T)
    {w : ℂ} (hw : ‖w‖ ≤ radius V T) : ‖w‖ * a ≤ Real.log (3 / 2) := by
  have hc : (0 : ℝ) < 12 * V * T := by
    have : (0 : ℝ) < T := by exact_mod_cast hT
    positivity
  calc ‖w‖ * a ≤ ‖w‖ * (12 * V * T) := mul_le_mul_of_nonneg_left ha (norm_nonneg _)
    _ ≤ Real.log (3 / 2) := by rwa [radius, le_div_iff₀ hc] at hw

section Wilson

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {μ₁ : Measure Ω₁}
  {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] {A₁ : Ω₁ → ℝ}
  {A₂ : Ω₂ → ℝ}

/-- `Ψ_T(z) = 2 log Z_T(z) − log Z_{2T}(z)`. -/
noncomputable def psi (μ₁ : Measure Ω₁) (A₁ : Ω₁ → ℝ) (μ₂ : Measure Ω₂) (A₂ : Ω₂ → ℝ) (z : ℂ) :
    ℂ :=
  2 * Complex.log (complexMGF A₁ μ₁ z) - Complex.log (complexMGF A₂ μ₂ z)

/-- `|Z_T − 1|, |Z_{2T} − 1| ≤ 1/2` on `|w| ≤ R`. -/
theorem near_one_on_disk {V : ℝ} {T : ℕ} (hV : 0 < V) (hT : 0 < T)
    (h₁ : AEMeasurable A₁ μ₁) (h₂ : AEMeasurable A₂ μ₂) (hb₁ : ∀ᵐ ω ∂μ₁, |A₁ ω| ≤ 6 * V * T)
    (hb₂ : ∀ᵐ ω ∂μ₂, |A₂ ω| ≤ 12 * V * T) {w : ℂ} (hw : ‖w‖ ≤ radius V T) :
    ‖complexMGF A₁ μ₁ w - 1‖ ≤ 1 / 2 ∧ ‖complexMGF A₂ μ₂ w - 1‖ ≤ 1 / 2 := by
  have hT' : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  exact ⟨mgf_near_one h₁ hb₁ (radius_mul_le hV hT (by nlinarith) hw),
    mgf_near_one h₂ hb₂ (radius_mul_le hV hT le_rfl hw)⟩

/-- `Z_T` and `Z_{2T}` do not vanish on `|w| ≤ R`. -/
theorem mgf_ne_zero {V : ℝ} {T : ℕ} (hV : 0 < V) (hT : 0 < T)
    (h₁ : AEMeasurable A₁ μ₁) (h₂ : AEMeasurable A₂ μ₂) (hb₁ : ∀ᵐ ω ∂μ₁, |A₁ ω| ≤ 6 * V * T)
    (hb₂ : ∀ᵐ ω ∂μ₂, |A₂ ω| ≤ 12 * V * T) {w : ℂ} (hw : ‖w‖ ≤ radius V T) :
    complexMGF A₁ μ₁ w ≠ 0 ∧ complexMGF A₂ μ₂ w ≠ 0 := by
  obtain ⟨n₁, n₂⟩ := near_one_on_disk hV hT h₁ h₂ hb₁ hb₂ hw
  exact ⟨Complex.slitPlane_ne_zero (mem_slitPlane_of_near_one n₁),
    Complex.slitPlane_ne_zero (mem_slitPlane_of_near_one n₂)⟩

/-- (8.2): `|Ψ_T(z)| ≤ 3 log 2 (|z|/R)^T / (1 − |z|/R)` for `|z| < R`, given (8.1). -/
theorem remainder {V : ℝ} {T : ℕ} (hV : 0 < V) (hT : 0 < T)
    (h₁ : AEMeasurable A₁ μ₁) (h₂ : AEMeasurable A₂ μ₂) (hb₁ : ∀ᵐ ω ∂μ₁, |A₁ ω| ≤ 6 * V * T)
    (hb₂ : ∀ᵐ ω ∂μ₂, |A₂ ω| ≤ 12 * V * T)
    (hvan : ∀ n < T, iteratedDeriv n (psi μ₁ A₁ μ₂ A₂) 0 = 0) {z : ℂ} (hz : ‖z‖ < radius V T) :
    ‖psi μ₁ A₁ μ₂ A₂ z‖ ≤
      3 * Real.log 2 * (‖z‖ / radius V T) ^ T / (1 - ‖z‖ / radius V T) := by
  have hR := radius_pos hV hT
  have hd : DifferentiableOn ℂ (psi μ₁ A₁ μ₂ A₂) (closedBall 0 (radius V T)) := by
    intro w hw
    have hw' : ‖w‖ ≤ radius V T := by simpa using hw
    obtain ⟨n₁, n₂⟩ := near_one_on_disk hV hT h₁ h₂ hb₁ hb₂ hw'
    have d₁ := (differentiable_mgf h₁ hb₁ w).clog (mem_slitPlane_of_near_one n₁)
    have d₂ := (differentiable_mgf h₂ hb₂ w).clog (mem_slitPlane_of_near_one n₂)
    exact ((d₁.const_mul 2).sub d₂).differentiableWithinAt
  refine cauchy_remainder hR (hd.diffContOnCl_ball le_rfl) (fun w hw => ?_) hvan hz
  have hw' : ‖w‖ ≤ radius V T := by simp at hw; exact hw.le
  obtain ⟨n₁, n₂⟩ := near_one_on_disk hV hT h₁ h₂ hb₁ hb₂ hw'
  exact psi_le n₁ n₂

end Wilson

/-- (8.4) and `V < (48T)³` give `βW/R ≤ 1/1000`. -/
theorem window_ratio {V x : ℝ} {T : ℕ} (hT : 0 < T) (hV : 0 < V) (hVhi : V < (48 * T : ℝ) ^ 3)
    (hx : x ≤ Real.log (3 / 2) / (12000 * 48 ^ 3 * T ^ 4)) :
    x / radius V T ≤ 1 / 1000 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hL : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hx' : x * (12000 * 48 ^ 3 * T ^ 4) ≤ Real.log (3 / 2) := by
    rwa [le_div_iff₀ (by positivity)] at hx
  rw [div_le_iff₀ (radius_pos hV hT), radius, mul_div_assoc', le_div_iff₀ (by positivity)]
  have hc : (0 : ℝ) < (48 * T) ^ 3 := by positivity
  refine le_of_mul_le_mul_right ?_ hc
  have h1 := mul_le_mul_of_nonneg_right hx' hV.le
  have h2 := mul_le_mul_of_nonneg_left hVhi.le hL.le
  nlinarith

/-- `T ≥ 3`, `(2T)³ ≤ V` and `0 ≤ q ≤ 1/1000` turn (8.2) into `|Ψ| ≤ V/(161 (48T)³)`. -/
theorem window_bound {V q P : ℝ} {T : ℕ} (hT : 3 ≤ T) (hVlo : (2 * T : ℝ) ^ 3 ≤ V)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 1000) (hP : P ≤ 3 * Real.log 2 * q ^ T / (1 - q)) :
    P ≤ V / (161 * (48 * T) ^ 3) := by
  have hq3 : q ^ T ≤ (1 / 1000) ^ 3 :=
    (pow_le_pow_of_le_one hq0 (by linarith) hT).trans (pow_le_pow_left₀ hq0 hq 3)
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 : 3 * Real.log 2 * q ^ T / (1 - q) ≤ 1 / 333000000 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul hl2.le hq3 (pow_nonneg hq0 T) zero_le_one]
  have hT' : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have h2 : (1 : ℝ) / 333000000 < 1 / (161 * 13824) := by norm_num
  have h3 : (1 : ℝ) / (161 * 13824) ≤ V / (161 * (48 * T) ^ 3) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  linarith

/-- Corollary 8.2: for `T ≥ 3`, `s ∈ W_T` (`(2T)³ ≤ V < (48T)³`) and (8.4),
`|Ψ_T(βW)| ≤ V/(161 (48T)³)`, given (8.1). -/
theorem corollary_window {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {A₁ : Ω₁ → ℝ} {A₂ : Ω₂ → ℝ} {V x : ℝ} {T : ℕ} (hT : 3 ≤ T)
    (hVlo : (2 * T : ℝ) ^ 3 ≤ V) (hVhi : V < (48 * T : ℝ) ^ 3)
    (h₁ : AEMeasurable A₁ μ₁) (h₂ : AEMeasurable A₂ μ₂) (hb₁ : ∀ᵐ ω ∂μ₁, |A₁ ω| ≤ 6 * V * T)
    (hb₂ : ∀ᵐ ω ∂μ₂, |A₂ ω| ≤ 12 * V * T)
    (hvan : ∀ n < T, iteratedDeriv n (psi μ₁ A₁ μ₂ A₂) 0 = 0)
    (hx0 : 0 ≤ x) (hx : x ≤ Real.log (3 / 2) / (12000 * 48 ^ 3 * T ^ 4)) :
    ‖psi μ₁ A₁ μ₂ A₂ x‖ ≤ V / (161 * (48 * T) ^ 3) := by
  have hT0 : 0 < T := by omega
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
  have hV : 0 < V := lt_of_lt_of_le (by positivity) hVlo
  have hR := radius_pos hV hT0
  have hr := window_ratio hT0 hV hVhi hx
  have hxn : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  have hz : ‖(x : ℂ)‖ < radius V T := by
    rw [hxn]
    have := (div_le_iff₀ hR).1 hr
    nlinarith
  have h := remainder hV hT0 h₁ h₂ hb₁ hb₂ hvan hz
  rw [hxn] at h
  exact window_bound hT hVlo (div_nonneg hx0 hR.le) hr h

/-- `Tr K^{2T} ≤ (Tr K^T)²`: `λ_i ≥ 0` give `0 ≤ 2 log Σ λ_i^T − log Σ λ_i^{2T}`. -/
theorem psi_nonneg_trace {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (T : ℕ)
    (hl : ∀ i ∈ s, 0 ≤ lam i) (h2 : 0 < ∑ i ∈ s, lam i ^ (2 * T)) :
    0 ≤ 2 * Real.log (∑ i ∈ s, lam i ^ T) - Real.log (∑ i ∈ s, lam i ^ (2 * T)) := by
  have hsq : ∑ i ∈ s, lam i ^ (2 * T) ≤ (∑ i ∈ s, lam i ^ T) ^ 2 := by
    have := Finset.sum_sq_le_sq_sum_of_nonneg (s := s) (f := fun i => lam i ^ T)
      fun i hi => pow_nonneg (hl i hi) T
    simpa [← pow_mul, mul_comm] using this
  have := Real.log_le_log h2 hsq
  rw [Real.log_pow] at this
  push_cast at this
  linarith

end MassGap.PurityCancel

#print axioms MassGap.PurityCancel.cauchy_remainder
#print axioms MassGap.PurityCancel.norm_exp_sub_one_le
#print axioms MassGap.PurityCancel.exp_sub_one_le_half
#print axioms MassGap.PurityCancel.differentiable_mgf
#print axioms MassGap.PurityCancel.mgf_sub_one_le
#print axioms MassGap.PurityCancel.mgf_near_one
#print axioms MassGap.PurityCancel.norm_log_le_log_two
#print axioms MassGap.PurityCancel.psi_le
#print axioms MassGap.PurityCancel.mem_slitPlane_of_near_one
#print axioms MassGap.PurityCancel.radius_pos
#print axioms MassGap.PurityCancel.radius_mul_le
#print axioms MassGap.PurityCancel.near_one_on_disk
#print axioms MassGap.PurityCancel.mgf_ne_zero
#print axioms MassGap.PurityCancel.remainder
#print axioms MassGap.PurityCancel.window_ratio
#print axioms MassGap.PurityCancel.window_bound
#print axioms MassGap.PurityCancel.corollary_window
#print axioms MassGap.PurityCancel.psi_nonneg_trace
