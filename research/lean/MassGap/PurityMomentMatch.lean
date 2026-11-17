import MassGap.PurityCancel

/-!
# MassGap.PurityMomentMatch — (8.1) of the purity paper from `Z_{2T} − Z_T²`

Section 8 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`).

The vanishing (8.1) `Ψ_T^{(n)}(0) = 0` for `n < T`, the hypothesis `hvan` of
`PurityCancel.remainder` and `PurityCancel.corollary_window`, follows from the vanishing of the
same derivatives of `Z_{2T} − Z_T²`.

* `order_psi`: for `f, g` analytic at `0` with `f 0 = g 0 = 1`, the analytic order of
  `2 log f − log g` at `0` is at least that of `g − f²`. Near `0`,
  `(2 log f − log g)' = (2 f' (g − f²) − (g − f²)' f) / (f g)`.
* `vanish_psi`: the same statement for derivatives, `∀ n < T, (g − f²)^{(n)}(0) = 0` gives
  `∀ n < T, (2 log f − log g)^{(n)}(0) = 0`.
* `hvan_of_mgf`: for bounded measurable actions under probability measures,
  `∀ n < T, (Z_{2T} − Z_T²)^{(n)}(0) = 0` gives `hvan` for `PurityCancel.psi`.
* `iteratedDeriv_mgf_zero`: `Z^{(n)}(0) = E[A^n]`.
* `iteratedDeriv_mgf_sub_sq`: `(Z_{2T} − Z_T²)^{(n)}(0) = E_{2T}[A^n] − Σ_{i ≤ n} C(n,i) E_T[A^i]
  E_T[A^{n−i}]` (Leibniz).
* `hvan_of_moments`: moment matching, `E_{2T}[A^n] = Σ_{i ≤ n} C(n,i) E_T[A^i] E_T[A^{n−i}]` for
  `n < T` (the moments of order `< T` of `A_{2T}` are those of a sum of two independent copies of
  `A_T`), gives `hvan`.

The moment matching and `hvan` for a nearest-neighbour chain are `PurityTwoLift.moment_cover`
and `PurityTwoLift.hvan_cover`. The Wilson action at circumference `T` is such a chain
(`PurityWilsonChain`), which gives `hvan` for it (`PurityWilsonChain.hvan_wilson`).
-/

namespace MassGap.PurityMomentMatch

open Filter Topology MeasureTheory ProbabilityTheory

/-- The analytic order of `2 log f − log g` at `0` is at least that of `g − f²`, for `f, g`
analytic at `0` with `f 0 = g 0 = 1`. -/
theorem order_psi {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hf0 : f 0 = 1) (hg0 : g 0 = 1) {T : ℕ}
    (h : (T : ℕ∞) ≤ analyticOrderAt (fun z => g z - f z ^ 2) 0) :
    (T : ℕ∞) ≤ analyticOrderAt (fun z => 2 * Complex.log (f z) - Complex.log (g z)) 0 := by
  set H : ℂ → ℂ := fun z => g z - f z ^ 2 with hHdef
  have hfs : f 0 ∈ Complex.slitPlane := by rw [hf0]; exact Complex.one_mem_slitPlane
  have hgs : g 0 ∈ Complex.slitPlane := by rw [hg0]; exact Complex.one_mem_slitPlane
  have hP : AnalyticAt ℂ (fun z => 2 * Complex.log (f z) - Complex.log (g z)) 0 :=
    (analyticAt_const.mul (hf.clog hfs)).sub (hg.clog hgs)
  have hP0 : (fun z => 2 * Complex.log (f z) - Complex.log (g z)) 0 = 0 := by
    simp [hf0, hg0]
  have hH : AnalyticAt ℂ H 0 := hg.sub (hf.pow 2)
  have hH0 : H 0 = 0 := by simp [hHdef, hf0, hg0]
  cases T with
  | zero => exact bot_le
  | succ n =>
    refine (analyticOrderAt_deriv_ge_iff hP hP0).mp ?_
    -- near `0`, `P' = (2 f' H − H' f) (f g)⁻¹`
    have hfn : ∀ᶠ z in 𝓝 (0 : ℂ), f z ∈ Complex.slitPlane :=
      hf.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hfs)
    have hgn : ∀ᶠ z in 𝓝 (0 : ℂ), g z ∈ Complex.slitPlane :=
      hg.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hgs)
    have hcongr : deriv (fun z => 2 * Complex.log (f z) - Complex.log (g z)) =ᶠ[𝓝 0]
        (((fun z => 2 * deriv f z) * H - deriv H * f) * (f * g)⁻¹) := by
      filter_upwards [hfn, hgn, hf.eventually_analyticAt, hg.eventually_analyticAt]
        with z hfz hgz haf hag
      have h1 := (haf.differentiableAt.hasDerivAt).clog hfz
      have h2 := (hag.differentiableAt.hasDerivAt).clog hgz
      have hPd : deriv (fun z => 2 * Complex.log (f z) - Complex.log (g z)) z = _ :=
        ((h1.const_mul 2).sub h2).deriv
      have hHd : deriv H z = _ :=
        (hag.differentiableAt.hasDerivAt.sub (haf.differentiableAt.hasDerivAt.pow 2)).deriv
      have hf' := Complex.slitPlane_ne_zero hfz
      have hg' := Complex.slitPlane_ne_zero hgz
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.inv_apply]
      rw [hPd, hHd]
      simp only [hHdef]
      norm_num
      field_simp
      ring
    rw [analyticOrderAt_congr hcongr]
    have hfg : AnalyticAt ℂ (f * g)⁻¹ 0 :=
      (hf.mul hg).inv (by simp [hf0, hg0])
    have hc : AnalyticAt ℂ (fun z => 2 * deriv f z) 0 := analyticAt_const.mul hf.deriv
    have hN : AnalyticAt ℂ ((fun z => 2 * deriv f z) * H - deriv H * f) 0 :=
      (hc.mul hH).sub (hH.deriv.mul hf)
    rw [analyticOrderAt_mul hN hfg]
    refine le_trans ?_ (le_self_add)
    refine le_trans (le_min ?_ ?_) le_analyticOrderAt_sub
    · rw [analyticOrderAt_mul hc hH]
      exact le_add_left (le_trans (by exact_mod_cast Nat.le_succ n) h)
    · rw [analyticOrderAt_mul hH.deriv hf]
      exact le_add_right ((analyticOrderAt_deriv_ge_iff hH hH0).mpr (by exact_mod_cast h))

/-- `∀ n < T, (g − f²)^{(n)}(0) = 0` gives `∀ n < T, (2 log f − log g)^{(n)}(0) = 0`, for `f, g`
analytic at `0` with `f 0 = g 0 = 1`. -/
theorem vanish_psi {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hf0 : f 0 = 1) (hg0 : g 0 = 1) {T : ℕ}
    (h : ∀ n < T, iteratedDeriv n (fun z => g z - f z ^ 2) 0 = 0) :
    ∀ n < T, iteratedDeriv n (fun z => 2 * Complex.log (f z) - Complex.log (g z)) 0 = 0 := by
  have hfs : f 0 ∈ Complex.slitPlane := by rw [hf0]; exact Complex.one_mem_slitPlane
  have hgs : g 0 ∈ Complex.slitPlane := by rw [hg0]; exact Complex.one_mem_slitPlane
  have hP : AnalyticAt ℂ (fun z => 2 * Complex.log (f z) - Complex.log (g z)) 0 :=
    (analyticAt_const.mul (hf.clog hfs)).sub (hg.clog hgs)
  have hH : AnalyticAt ℂ (fun z => g z - f z ^ 2) 0 := hg.sub (hf.pow 2)
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hP).mp
    (order_psi hf hg hf0 hg0 ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hH).mpr h))

section MGF

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {μ₁ : Measure Ω₁}
  {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] {A₁ : Ω₁ → ℝ}
  {A₂ : Ω₂ → ℝ} {a₁ a₂ : ℝ}

/-- (8.1) for `PurityCancel.psi` from the vanishing of the derivatives of order `< T` of
`Z_{2T} − Z_T²` at `0`. -/
theorem hvan_of_mgf (hA₁ : AEMeasurable A₁ μ₁) (hb₁ : ∀ᵐ ω ∂μ₁, |A₁ ω| ≤ a₁)
    (hA₂ : AEMeasurable A₂ μ₂) (hb₂ : ∀ᵐ ω ∂μ₂, |A₂ ω| ≤ a₂) {T : ℕ}
    (h : ∀ n < T,
      iteratedDeriv n (fun z => complexMGF A₂ μ₂ z - complexMGF A₁ μ₁ z ^ 2) 0 = 0) :
    ∀ n < T, iteratedDeriv n (PurityCancel.psi μ₁ A₁ μ₂ A₂) 0 = 0 :=
  vanish_psi ((PurityCancel.differentiable_mgf hA₁ hb₁).analyticAt 0)
    ((PurityCancel.differentiable_mgf hA₂ hb₂).analyticAt 0)
    (by simp [complexMGF]) (by simp [complexMGF]) h

/-- `Z^{(n)}(0) = E[A^n]` for a bounded measurable action. -/
theorem iteratedDeriv_mgf_zero (hA₁ : AEMeasurable A₁ μ₁) (hb₁ : ∀ᵐ ω ∂μ₁, |A₁ ω| ≤ a₁) (n : ℕ) :
    iteratedDeriv n (complexMGF A₁ μ₁) 0 = μ₁[fun ω => (A₁ ω : ℂ) ^ n] := by
  have hset : integrableExpSet A₁ μ₁ = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    exact integrable_exp_mul_of_mem_Icc hA₁ (hb₁.mono fun ω h => abs_le.1 h)
  rw [iteratedDeriv_complexMGF (by simp [hset]) n]
  simp

/-- `(Z_{2T} − Z_T²)^{(n)}(0) = E_{2T}[A^n] − Σ_{i ≤ n} C(n,i) E_T[A^i] E_T[A^{n−i}]`. -/
theorem iteratedDeriv_mgf_sub_sq (hA₁ : AEMeasurable A₁ μ₁) (hb₁ : ∀ᵐ ω ∂μ₁, |A₁ ω| ≤ a₁)
    (hA₂ : AEMeasurable A₂ μ₂) (hb₂ : ∀ᵐ ω ∂μ₂, |A₂ ω| ≤ a₂) (n : ℕ) :
    iteratedDeriv n (fun z => complexMGF A₂ μ₂ z - complexMGF A₁ μ₁ z ^ 2) 0
      = μ₂[fun ω => (A₂ ω : ℂ) ^ n] - ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) * μ₁[fun ω => (A₁ ω : ℂ) ^ i] * μ₁[fun ω => (A₁ ω : ℂ) ^ (n - i)] := by
  have hZ₁ : ContDiffAt ℂ n (complexMGF A₁ μ₁) 0 :=
    ((PurityCancel.differentiable_mgf hA₁ hb₁).analyticAt 0).contDiffAt
  have hZ₂ : ContDiffAt ℂ n (complexMGF A₂ μ₂) 0 :=
    ((PurityCancel.differentiable_mgf hA₂ hb₂).analyticAt 0).contDiffAt
  have hsq : (fun z => complexMGF A₂ μ₂ z - complexMGF A₁ μ₁ z ^ 2)
      = complexMGF A₂ μ₂ - complexMGF A₁ μ₁ * complexMGF A₁ μ₁ := by
    funext z
    simp [sq]
  have hZZ : ContDiffAt ℂ n (complexMGF A₁ μ₁ * complexMGF A₁ μ₁) 0 := hZ₁.mul hZ₁
  rw [hsq, iteratedDeriv_sub hZ₂ hZZ, iteratedDeriv_mul hZ₁ hZ₁,
    iteratedDeriv_mgf_zero hA₂ hb₂]
  simp only [iteratedDeriv_mgf_zero hA₁ hb₁]

/-- (8.1) for `PurityCancel.psi` from moment matching: `E_{2T}[A^n] = Σ_{i ≤ n} C(n,i) E_T[A^i]
E_T[A^{n−i}]` for `n < T`, the moments of `A_{2T}` equal those of a sum of two independent copies
of `A_T`. -/
theorem hvan_of_moments (hA₁ : AEMeasurable A₁ μ₁) (hb₁ : ∀ᵐ ω ∂μ₁, |A₁ ω| ≤ a₁)
    (hA₂ : AEMeasurable A₂ μ₂) (hb₂ : ∀ᵐ ω ∂μ₂, |A₂ ω| ≤ a₂) {T : ℕ}
    (h : ∀ n < T, μ₂[fun ω => (A₂ ω : ℂ) ^ n] = ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℂ) * μ₁[fun ω => (A₁ ω : ℂ) ^ i] * μ₁[fun ω => (A₁ ω : ℂ) ^ (n - i)]) :
    ∀ n < T, iteratedDeriv n (PurityCancel.psi μ₁ A₁ μ₂ A₂) 0 = 0 :=
  hvan_of_mgf hA₁ hb₁ hA₂ hb₂ fun n hn => by
    rw [iteratedDeriv_mgf_sub_sq hA₁ hb₁ hA₂ hb₂, h n hn, sub_self]

end MGF

end MassGap.PurityMomentMatch

#print axioms MassGap.PurityMomentMatch.order_psi
#print axioms MassGap.PurityMomentMatch.vanish_psi
#print axioms MassGap.PurityMomentMatch.hvan_of_mgf
#print axioms MassGap.PurityMomentMatch.iteratedDeriv_mgf_zero
#print axioms MassGap.PurityMomentMatch.iteratedDeriv_mgf_sub_sq
#print axioms MassGap.PurityMomentMatch.hvan_of_moments
