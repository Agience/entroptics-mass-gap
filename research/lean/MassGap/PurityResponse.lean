import Mathlib

/-!
# MassGap.PurityResponse — the thermal response formula, Proposition 6.4 of the purity paper

Proposition 6.4 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`).

The setting is a probability measure `ν` and a bounded measurable action `S`, with
`mom ν g S b = ∫ g e^{−b S} dν`, partition function `Z_b = mom ν 1 S b` and Gibbs mean
`gibbs ν S b = ⟨S⟩_b = mom ν S S b / Z_b`. In the Wilson instance `ν₁, ν₂` are the product Haar
measures on the `T`- and `2T`-tori, `S_T = Σ_p (1 − Re Tr U_p / d)` over the `N = 6 V T`
plaquettes, each term in `[0, 2]`; the module takes `0 ≤ S₁ ≤ 2N`, `0 ≤ S₂ ≤ 4N` as hypotheses.
`e_T = ⟨S₁⟩/N`, `e_{2T} = ⟨S₂⟩/(2N)` and `ψ(b) = 2 log Z_b(T) − log Z_b(2T)`.

* `hasDerivAt_mom`, `integrable_mom`: differentiation under the finite integral,
  `d/db ∫ g e^{−bS} = −∫ g S e^{−bS}`.
* `Z_pos`, `Z_zero`, `hasDerivAt_log_Z`: `Z_b > 0`, `Z_0 = 1`, `(log Z_b)' = −⟨S⟩_b`.
* `gibbs_mem`, `eT_mem`: `0 ≤ S ≤ c` gives `0 ≤ ⟨S⟩_b ≤ c`, so `0 ≤ e_T(b) ≤ 2`.
* `hasDerivAt_psi`: paper, (6.6), `dψ/db = 2N (e_{2T} − e_T)`, which is `12 V T (e_{2T} − e_T)`
  at `N = 6 V T`.
* `continuous_response`: `ψ` is `C¹` in `b`; `PurityResponseSmooth.contDiff_psi` gives `C^∞`.
* `psi_eq_integral`: paper, (6.7), `ψ(b) = 2N ∫₀^b (e_{2T}(u) − e_T(u)) du`, with no sign
  condition on the integrand.
* `psi_lipschitz`: paper, (6.8), `|ψ(b) − ψ(b₀)| ≤ 4N |b − b₀|`, which is `24 V T |b − b₀|`.
* `certified`, `radius_eq`, `response_certified`: paper, (6.9). A margin
  `ψ(b₀)/V ≤ ε_T − δ` certifies `ψ(b)/V ≤ ε_T` for `|b − b₀| ≤ δ/(24T)`; at
  `ε_T = 1/(161 (48T)³)`, `δ = ε_T/2` the radius is `1/(7728 · 48³ T⁴)`.
-/

namespace MassGap.PurityResponse

open Real MeasureTheory Set Metric

variable {X : Type*} [MeasurableSpace X]

/-- The moment `∫ g e^{−b S} dν`. -/
noncomputable def mom (ν : Measure X) (g S : X → ℝ) (b : ℝ) : ℝ :=
  ∫ x, g x * exp (-(b * S x)) ∂ν

/-- The Gibbs mean `⟨S⟩_b = ∫ S e^{−bS} / ∫ e^{−bS}`. -/
noncomputable def gibbs (ν : Measure X) (S : X → ℝ) (b : ℝ) : ℝ :=
  mom ν S S b / mom ν (fun _ => 1) S b

omit [MeasurableSpace X] in
theorem abs_mul_le {S : X → ℝ} {M : ℝ} (hM : ∀ x, |S x| ≤ M) (b : ℝ) (x : X) :
    |b * S x| ≤ |b| * M := by
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg b)

omit [MeasurableSpace X] in
theorem exp_le {S : X → ℝ} {M : ℝ} (hM : ∀ x, |S x| ≤ M) (b : ℝ) (x : X) :
    exp (-(b * S x)) ≤ exp (|b| * M) := by
  apply exp_le_exp.2
  have := abs_le.1 (abs_mul_le hM b x)
  linarith [this.1]

theorem integrable_mom {ν : Measure X} [IsFiniteMeasure ν] {g S : X → ℝ} {K M : ℝ}
    (hg : Measurable g) (hS : Measurable S) (hgK : ∀ x, |g x| ≤ K) (hM : ∀ x, |S x| ≤ M)
    (b : ℝ) : Integrable (fun x => g x * exp (-(b * S x))) ν := by
  refine Integrable.of_bound (by fun_prop : Measurable fun x => g x * exp (-(b * S x))).aestronglyMeasurable
    (K * exp (|b| * M)) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  exact mul_le_mul (hgK x) (exp_le hM b x) (exp_pos _).le ((abs_nonneg _).trans (hgK x))

/-- Differentiation under the finite integral: `d/db ∫ g e^{−bS} = −∫ g S e^{−bS}`. -/
theorem hasDerivAt_mom {ν : Measure X} [IsFiniteMeasure ν] {g S : X → ℝ} {K M : ℝ}
    (hg : Measurable g) (hS : Measurable S) (hgK : ∀ x, |g x| ≤ K) (hM : ∀ x, |S x| ≤ M)
    (b₀ : ℝ) : HasDerivAt (mom ν g S) (-mom ν (fun x => g x * S x) S b₀) b₀ := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun b x => g x * exp (-(b * S x))) (F' := fun b x => -(g x * S x * exp (-(b * S x))))
    (x₀ := b₀) (s := ball b₀ 1) (bound := fun _ => K * M * exp ((|b₀| + 1) * M))
    (ball_mem_nhds b₀ zero_lt_one)
    (Filter.Eventually.of_forall fun b =>
      (by fun_prop : Measurable fun x => g x * exp (-(b * S x))).aestronglyMeasurable)
    (integrable_mom hg hS hgK hM b₀)
    (by fun_prop : Measurable fun x => -(g x * S x * exp (-(b₀ * S x)))).aestronglyMeasurable
    (ae_of_all _ fun x b hb => by
      have hb' : |b| ≤ |b₀| + 1 := by
        have := abs_sub_abs_le_abs_sub b b₀
        rw [Metric.mem_ball, Real.dist_eq] at hb
        linarith
      have hK : 0 ≤ K := (abs_nonneg _).trans (hgK x)
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x)
      have he : exp (-(b * S x)) ≤ exp ((|b₀| + 1) * M) :=
        (exp_le hM b x).trans (exp_le_exp.2 (mul_le_mul_of_nonneg_right hb' hM0))
      simp only [norm_neg, Real.norm_eq_abs, abs_mul, Real.abs_exp]
      exact mul_le_mul (mul_le_mul (hgK x) (hM x) (abs_nonneg _) hK) he (exp_pos _).le
        (mul_nonneg hK hM0))
    (integrable_const _)
    (ae_of_all _ fun x b _ => by
      have h1 : HasDerivAt (fun y => -(y * S x)) (-S x) b := (hasDerivAt_mul_const (S x)).neg
      have h := h1.exp.const_mul (g x)
      exact h.congr_deriv (by ring))
  show HasDerivAt (fun b => ∫ x, g x * exp (-(b * S x)) ∂ν)
    (-∫ x, g x * S x * exp (-(b₀ * S x)) ∂ν) b₀
  rw [← integral_neg]
  exact key.2

/-- `Z_b > 0`. -/
theorem Z_pos {ν : Measure X} [IsProbabilityMeasure ν] {S : X → ℝ} {M : ℝ} (hS : Measurable S)
    (hM : ∀ x, |S x| ≤ M) (b : ℝ) : 0 < mom ν (fun _ => 1) S b := by
  have hlow : ∀ x, exp (-(|b| * M)) ≤ (fun _ => (1 : ℝ)) x * exp (-(b * S x)) := by
    intro x
    rw [one_mul]
    apply exp_le_exp.2
    have := abs_le.1 (abs_mul_le hM b x)
    linarith [this.2]
  have h0 : ∫ _x, exp (-(|b| * M)) ∂ν = exp (-(|b| * M)) := by simp
  calc (0 : ℝ) < exp (-(|b| * M)) := exp_pos _
    _ = ∫ _x, exp (-(|b| * M)) ∂ν := h0.symm
    _ ≤ mom ν (fun _ => 1) S b :=
        integral_mono (integrable_const _)
          (integrable_mom (g := fun _ => 1) (K := 1) measurable_const hS (fun _ => by simp) hM b) hlow

/-- `Z_0 = 1`. -/
theorem Z_zero {ν : Measure X} [IsProbabilityMeasure ν] (S : X → ℝ) :
    mom ν (fun _ => 1) S 0 = 1 := by
  simp [mom]

/-- `(log Z_b)' = −⟨S⟩_b`. -/
theorem hasDerivAt_log_Z {ν : Measure X} [IsProbabilityMeasure ν] {S : X → ℝ} {M : ℝ}
    (hS : Measurable S) (hM : ∀ x, |S x| ≤ M) (b : ℝ) :
    HasDerivAt (fun b => log (mom ν (fun _ => 1) S b)) (-gibbs ν S b) b := by
  have h := (hasDerivAt_mom (ν := ν) (g := fun _ => 1) (K := 1) measurable_const hS (fun _ => by simp) hM b).log
    (Z_pos hS hM b).ne'
  have hfun : (fun x => (fun _ => (1 : ℝ)) x * S x) = S := funext fun x => one_mul _
  rw [hfun] at h
  convert h using 1
  rw [gibbs, neg_div]

/-- `0 ≤ S ≤ c` gives `0 ≤ ⟨S⟩_b ≤ c`. -/
theorem gibbs_mem {ν : Measure X} [IsProbabilityMeasure ν] {S : X → ℝ} {c : ℝ}
    (hS : Measurable S) (h0 : ∀ x, 0 ≤ S x) (hc : ∀ x, S x ≤ c) (b : ℝ) :
    0 ≤ gibbs ν S b ∧ gibbs ν S b ≤ c := by
  have hM : ∀ x, |S x| ≤ c := fun x => by rw [abs_of_nonneg (h0 x)]; exact hc x
  have hZ := Z_pos (ν := ν) hS hM b
  have hW0 : 0 ≤ mom ν S S b :=
    integral_nonneg fun x => mul_nonneg (h0 x) (exp_pos _).le
  have hWc : mom ν S S b ≤ c * mom ν (fun _ => 1) S b := by
    have hi1 := integrable_mom (ν := ν) hS hS hM hM b
    have hi2 := (integrable_mom (ν := ν) (g := fun _ => 1) (K := 1) measurable_const hS (fun _ => by simp) hM b).const_mul c
    have := integral_mono hi1 hi2 fun x => by
      simp only [one_mul]
      exact mul_le_mul_of_nonneg_right (hc x) (exp_pos _).le
    rw [integral_const_mul] at this
    exact this
  refine ⟨div_nonneg hW0 hZ.le, ?_⟩
  rw [gibbs, div_le_iff₀ hZ]
  exact hWc

/-- `⟨S⟩_b` is continuous in `b`. -/
theorem continuous_gibbs {ν : Measure X} [IsProbabilityMeasure ν] {S : X → ℝ} {M : ℝ}
    (hS : Measurable S) (hM : ∀ x, |S x| ≤ M) : Continuous (gibbs ν S) := by
  have hZ : Continuous (mom ν (fun _ => 1) S) := continuous_iff_continuousAt.2 fun b =>
    (hasDerivAt_mom (ν := ν) (g := fun _ => 1) (K := 1) measurable_const hS (fun _ => by simp) hM b).continuousAt
  have hW : Continuous (mom ν S S) := continuous_iff_continuousAt.2 fun b =>
    (hasDerivAt_mom (ν := ν) hS hS hM hM b).continuousAt
  exact hW.div hZ fun b => (Z_pos hS hM b).ne'

/-- The energy density `e = ⟨S⟩/N`. -/
noncomputable def eT (N : ℝ) (ν : Measure X) (S : X → ℝ) (b : ℝ) : ℝ := gibbs ν S b / N

/-- `0 ≤ S ≤ 2N` gives `0 ≤ e(b) ≤ 2`. -/
theorem eT_mem {ν : Measure X} [IsProbabilityMeasure ν] {S : X → ℝ} {N : ℝ} (hN : 0 < N)
    (hS : Measurable S) (h0 : ∀ x, 0 ≤ S x) (hc : ∀ x, S x ≤ 2 * N) (b : ℝ) :
    0 ≤ eT N ν S b ∧ eT N ν S b ≤ 2 := by
  obtain ⟨g0, gc⟩ := gibbs_mem (ν := ν) hS h0 hc b
  refine ⟨div_nonneg g0 hN.le, ?_⟩
  rw [eT, div_le_iff₀ hN]
  linarith

variable {Y : Type*} [MeasurableSpace Y]

/-- The pressure defect `ψ(b) = 2 log Z_b(T) − log Z_b(2T)`. -/
noncomputable def psi (ν₁ : Measure X) (ν₂ : Measure Y) (S₁ : X → ℝ) (S₂ : Y → ℝ) (b : ℝ) : ℝ :=
  2 * log (mom ν₁ (fun _ => 1) S₁ b) - log (mom ν₂ (fun _ => 1) S₂ b)

section Response

variable {ν₁ : Measure X} [IsProbabilityMeasure ν₁] {ν₂ : Measure Y} [IsProbabilityMeasure ν₂]
  {S₁ : X → ℝ} {S₂ : Y → ℝ} {N : ℝ}

/-- Paper, (6.6): `dψ/db = 2N (e_{2T} − e_T)`. -/
theorem hasDerivAt_psi (hN : 0 < N) (hS₁ : Measurable S₁) (hS₂ : Measurable S₂)
    (h₁0 : ∀ x, 0 ≤ S₁ x) (h₁c : ∀ x, S₁ x ≤ 2 * N) (h₂0 : ∀ y, 0 ≤ S₂ y)
    (h₂c : ∀ y, S₂ y ≤ 2 * (2 * N)) (b : ℝ) :
    HasDerivAt (psi ν₁ ν₂ S₁ S₂) (2 * N * (eT (2 * N) ν₂ S₂ b - eT N ν₁ S₁ b)) b := by
  have hM₁ : ∀ x, |S₁ x| ≤ 2 * N := fun x => by rw [abs_of_nonneg (h₁0 x)]; exact h₁c x
  have hM₂ : ∀ y, |S₂ y| ≤ 2 * (2 * N) := fun y => by rw [abs_of_nonneg (h₂0 y)]; exact h₂c y
  have h := ((hasDerivAt_log_Z (ν := ν₁) hS₁ hM₁ b).const_mul 2).sub
    (hasDerivAt_log_Z (ν := ν₂) hS₂ hM₂ b)
  refine h.congr_deriv ?_
  have hN' := hN.ne'
  unfold eT
  field_simp
  ring

/-- The response integrand is continuous. -/
theorem continuous_response (hS₁ : Measurable S₁) (hS₂ : Measurable S₂)
    (h₁0 : ∀ x, 0 ≤ S₁ x) (h₁c : ∀ x, S₁ x ≤ 2 * N) (h₂0 : ∀ y, 0 ≤ S₂ y)
    (h₂c : ∀ y, S₂ y ≤ 2 * (2 * N)) :
    Continuous fun u => 2 * N * (eT (2 * N) ν₂ S₂ u - eT N ν₁ S₁ u) := by
  have hM₁ : ∀ x, |S₁ x| ≤ 2 * N := fun x => by rw [abs_of_nonneg (h₁0 x)]; exact h₁c x
  have hM₂ : ∀ y, |S₂ y| ≤ 2 * (2 * N) := fun y => by rw [abs_of_nonneg (h₂0 y)]; exact h₂c y
  have c₁ := continuous_gibbs (ν := ν₁) hS₁ hM₁
  have c₂ := continuous_gibbs (ν := ν₂) hS₂ hM₂
  unfold eT
  fun_prop

/-- Paper, (6.7): `ψ(b) = 2N ∫₀^b (e_{2T}(u) − e_T(u)) du`. No sign of the integrand is used. -/
theorem psi_eq_integral (hN : 0 < N) (hS₁ : Measurable S₁) (hS₂ : Measurable S₂)
    (h₁0 : ∀ x, 0 ≤ S₁ x) (h₁c : ∀ x, S₁ x ≤ 2 * N) (h₂0 : ∀ y, 0 ≤ S₂ y)
    (h₂c : ∀ y, S₂ y ≤ 2 * (2 * N)) (b : ℝ) :
    psi ν₁ ν₂ S₁ S₂ b = 2 * N * ∫ u in (0 : ℝ)..b, (eT (2 * N) ν₂ S₂ u - eT N ν₁ S₁ u) := by
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_psi (ν₁ := ν₁) (ν₂ := ν₂) hN hS₁ hS₂ h₁0 h₁c h₂0 h₂c u)
    ((continuous_response (ν₁ := ν₁) (ν₂ := ν₂) hS₁ hS₂ h₁0 h₁c h₂0 h₂c).intervalIntegrable 0 b)
  have h0 : psi ν₁ ν₂ S₁ S₂ 0 = 0 := by simp [psi, Z_zero]
  rw [intervalIntegral.integral_const_mul, h0, sub_zero] at hI
  exact hI.symm

/-- Paper, (6.8): `|ψ(b) − ψ(b₀)| ≤ 4N |b − b₀|`. -/
theorem psi_lipschitz (hN : 0 < N) (hS₁ : Measurable S₁) (hS₂ : Measurable S₂)
    (h₁0 : ∀ x, 0 ≤ S₁ x) (h₁c : ∀ x, S₁ x ≤ 2 * N) (h₂0 : ∀ y, 0 ≤ S₂ y)
    (h₂c : ∀ y, S₂ y ≤ 2 * (2 * N)) (b b₀ : ℝ) :
    |psi ν₁ ν₂ S₁ S₂ b - psi ν₁ ν₂ S₁ S₂ b₀| ≤ 4 * N * |b - b₀| := by
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_psi (ν₁ := ν₁) (ν₂ := ν₂) hN hS₁ hS₂ h₁0 h₁c h₂0 h₂c u)
    ((continuous_response (ν₁ := ν₁) (ν₂ := ν₂) hS₁ hS₂ h₁0 h₁c h₂0 h₂c).intervalIntegrable b₀ b)
  rw [← hI, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => ?_
  obtain ⟨a0, a2⟩ := eT_mem (ν := ν₁) hN hS₁ h₁0 h₁c u
  obtain ⟨c0, c2⟩ := eT_mem (ν := ν₂) (by linarith : (0 : ℝ) < 2 * N) hS₂ h₂0 h₂c u
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * N)]
  have : |eT (2 * N) ν₂ S₂ u - eT N ν₁ S₁ u| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
  nlinarith

end Response

/-- Paper, (6.9): a margin `ψ(b₀)/V ≤ ε − δ` and the bound `24 V T |b − b₀|` certify
`ψ(b)/V ≤ ε` for `|b − b₀| ≤ δ/(24T)`. -/
theorem certified {ψb ψ₀ V T ε δ b b₀ : ℝ} (hV : 0 < V) (hT : 0 < T)
    (hL : |ψb - ψ₀| ≤ 24 * V * T * |b - b₀|) (hm : ψ₀ / V ≤ ε - δ) (hr : |b - b₀| ≤ δ / (24 * T)) :
    ψb / V ≤ ε := by
  rw [div_le_iff₀ hV] at hm ⊢
  rw [le_div_iff₀ (by positivity)] at hr
  have h1 : ψb - ψ₀ ≤ 24 * V * T * |b - b₀| := (le_abs_self _).trans hL
  have h2 : 24 * V * T * |b - b₀| ≤ δ * V := by nlinarith
  linarith

/-- The radius at `ε_T = 1/(161 (48T)³)`, `δ = ε_T/2`: `δ/(24T) = 1/(7728 · 48³ T⁴)`. -/
theorem radius_eq {T : ℝ} (hT : 0 < T) :
    1 / (161 * (48 * T) ^ 3) / 2 / (24 * T) = 1 / (7728 * 48 ^ 3 * T ^ 4) := by
  field_simp
  ring

/-- Paper, (6.9) on the Wilson response: with `N = 6 V T`, a margin
`ψ(b₀)/V ≤ ε_T/2` at `ε_T = 1/(161 (48T)³)` certifies `ψ(b)/V ≤ ε_T` for
`|b − b₀| ≤ 1/(7728 · 48³ T⁴)`. -/
theorem response_certified {ν₁ : Measure X} [IsProbabilityMeasure ν₁] {ν₂ : Measure Y}
    [IsProbabilityMeasure ν₂] {S₁ : X → ℝ} {S₂ : Y → ℝ} {V T : ℝ} (hV : 0 < V) (hT : 0 < T)
    (hS₁ : Measurable S₁) (hS₂ : Measurable S₂)
    (h₁0 : ∀ x, 0 ≤ S₁ x) (h₁c : ∀ x, S₁ x ≤ 2 * (6 * V * T)) (h₂0 : ∀ y, 0 ≤ S₂ y)
    (h₂c : ∀ y, S₂ y ≤ 2 * (2 * (6 * V * T))) {b b₀ : ℝ}
    (hm : psi ν₁ ν₂ S₁ S₂ b₀ / V ≤ 1 / (161 * (48 * T) ^ 3) / 2)
    (hr : |b - b₀| ≤ 1 / (7728 * 48 ^ 3 * T ^ 4)) :
    psi ν₁ ν₂ S₁ S₂ b / V ≤ 1 / (161 * (48 * T) ^ 3) := by
  have hN : (0 : ℝ) < 6 * V * T := by positivity
  have hL := psi_lipschitz (ν₁ := ν₁) (ν₂ := ν₂) hN hS₁ hS₂ h₁0 h₁c h₂0 h₂c b b₀
  refine certified (δ := 1 / (161 * (48 * T) ^ 3) / 2) hV hT (hL.trans_eq (by ring)) ?_ ?_
  · linarith
  · rw [radius_eq hT]; exact hr

end MassGap.PurityResponse

#print axioms MassGap.PurityResponse.abs_mul_le
#print axioms MassGap.PurityResponse.exp_le
#print axioms MassGap.PurityResponse.integrable_mom
#print axioms MassGap.PurityResponse.hasDerivAt_mom
#print axioms MassGap.PurityResponse.Z_pos
#print axioms MassGap.PurityResponse.Z_zero
#print axioms MassGap.PurityResponse.hasDerivAt_log_Z
#print axioms MassGap.PurityResponse.gibbs_mem
#print axioms MassGap.PurityResponse.continuous_gibbs
#print axioms MassGap.PurityResponse.eT_mem
#print axioms MassGap.PurityResponse.hasDerivAt_psi
#print axioms MassGap.PurityResponse.continuous_response
#print axioms MassGap.PurityResponse.psi_eq_integral
#print axioms MassGap.PurityResponse.psi_lipschitz
#print axioms MassGap.PurityResponse.certified
#print axioms MassGap.PurityResponse.radius_eq
#print axioms MassGap.PurityResponse.response_certified
