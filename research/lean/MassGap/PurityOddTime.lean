import Mathlib
import MassGap.CyclicKernel
import MassGap.SectorDefect
import MassGap.PurityThermal
import MassGap.PurityRectWilsonFixed

/-!
# MassGap.PurityOddTime — (6.2) and (6.3) of the purity paper at odd times

Proposition 6.1 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`),
at the time `T = 2j + 1`, `j ≥ 1`. The trace at `T` is the cyclic integral
`cyc μ k T = ∫ ∏_t k(W_t, W_{t+1})` (`CyclicKernel.cyc`); at even `T` it is `traceSeq μ k T`
(`CyclicKernel.cyc_even`), which is the setting of `PurityThermal`.

`k` is a bounded, jointly measurable, symmetric kernel on a probability space with a bounded
eigenfunction `φ`, `∫ φ² = 1`, eigenvalue `c > 0` and `c = ‖K‖`; `rem k c φ = k − c φ ⊗ φ` and `R`
is its operator on `L²`.

* `trace_iter_le`: for a bounded measurable kernel `r` with operator `R`,
  `|∫ r^{∗(2j+1)}(x, x) dx| ≤ ‖R‖^{2j−1} ‖r‖²_HS`, by Cauchy–Schwarz on
  `r^{∗(2j+1)} = r^{∗j} ∗ r^{∗(j+1)}` and `‖R^i S‖_HS ≤ ‖R‖^i ‖S‖_HS` (`KernelPower.hs_iter_le`).
* `cyc_odd`: `cyc μ k (2j+1) = c^{2j+1} + ∫ r^{∗(2j+1)}(x, x) dx`.
* `cyc_succ_ge`, `cyc_succ_pos`: a bounded measurable kernel bounded below by `m > 0` has
  `cyc μ a (n+1) ≥ m^{n+1} > 0`.
* `trace_excess_odd_le`, `defect_odd_le`: with `‖R‖ ≤ τ c` and `‖K‖²_HS/‖K‖² − 1 ≤ U`,
  `cyc(T)/‖K‖^T − 1 ≤ τ^{T−2} U` and, for `cyc(T) > 0`,
  `ψ_T = 2 log cyc(T) − log cyc(2T) ≤ 2 log (1 + τ^{T−2} U)`.
* `trace_excess_odd`, `defect_odd`, `ZRG_defect_odd`: the same for the Wilson transfer kernel
  `kTG` of a nontrivial gauge group, spatial extents at least `2` and `β > 0`, with
  `τ = tanh(β tpMax (1 − q/d)/2)`: `cyc(T)/‖K‖^T − 1 ≤ τ^T/(1 − τ²)`,
  `ψ_T ≤ 2 log (1 + τ^T/(1 − τ²))`, and `2 log Z(L) − log Z(L') ≤ 2 log (1 + τ^T/(1 − τ²))` for
  time extents `L μ = T`, `L' μ = 2T` and the same spatial extents.

With `PurityRectWilsonFixed.trace_excess` and `PurityRectWilsonFixed.defect` at `T = 2j`, (6.2)
and (6.3) for `kTG` hold at every integer `T ≥ 2`.
-/

namespace MassGap.PurityOddTime

open MeasureTheory Real MassGap.SlabKernelOperator MassGap.KernelPower MassGap.CyclicKernel

section General

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- `|∫ r^{∗(2j+1)}(x, x) dx| ≤ ‖R‖^{2j−1} ‖r‖²_HS` for a bounded measurable kernel, `j ≥ 1`. -/
theorem trace_iter_le {r : X → X → ℝ} {Cr : ℝ} (hrm : Measurable (Function.uncurry r))
    (hCr0 : 0 ≤ Cr) (hrb : ∀ x y, |r x y| ≤ Cr) (j : ℕ) (hj : 1 ≤ j) :
    |∫ x, iter μ r (2 * j) x x ∂μ| ≤
      ‖kernelCLM r Cr hrm hCr0 hrb μ μ‖ ^ (2 * j - 1) * hs μ r := by
  have hr : Bdd r := ⟨hrm, Cr, hrb⟩
  have hA := hr.iter (μ := μ) (j - 1)
  have hB := hr.iter (μ := μ) j
  obtain ⟨CA, hCA⟩ := hA.bdd
  obtain ⟨CB, hCB⟩ := hB.bdd
  have e : iter μ r (2 * j) = conv μ (iter μ r (j - 1)) (iter μ r j) := by
    have h := iter_add (μ := μ) hr (j - 1) j
    rwa [show j - 1 + j + 1 = 2 * j by omega] at h
  have hf : Measurable (fun p : X × X => iter μ r (j - 1) p.1 p.2) := hA.meas
  have hg : Measurable (fun p : X × X => iter μ r j p.2 p.1) := hB.meas.comp measurable_swap
  have hfg : Integrable (fun p : X × X => iter μ r (j - 1) p.1 p.2 * iter μ r j p.2 p.1)
      (μ.prod μ) :=
    integrable_of_bdd (hf.mul hg) (C := CA * CB) (fun p => by
      rw [abs_mul]
      exact mul_le_mul (hCA _ _) (hCB _ _) (abs_nonneg _) ((abs_nonneg _).trans (hCA p.1 p.2)))
  have hf2 : Integrable (fun p : X × X => iter μ r (j - 1) p.1 p.2 ^ 2) (μ.prod μ) :=
    integrable_of_bdd (hf.pow_const 2) (C := CA ^ 2) (fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCA _ _) 2)
  have hg2 : Integrable (fun p : X × X => iter μ r j p.2 p.1 ^ 2) (μ.prod μ) :=
    integrable_of_bdd (hg.pow_const 2) (C := CB ^ 2) (fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCB _ _) 2)
  have et : ∫ x, iter μ r (2 * j) x x ∂μ =
      ∫ p, iter μ r (j - 1) p.1 p.2 * iter μ r j p.2 p.1 ∂(μ.prod μ) := by
    rw [integral_prod _ hfg, e]; rfl
  have ef : ∫ p, iter μ r (j - 1) p.1 p.2 ^ 2 ∂(μ.prod μ) = hs μ (iter μ r (j - 1)) :=
    integral_prod _ hf2
  have eg : ∫ p, iter μ r j p.2 p.1 ^ 2 ∂(μ.prod μ) = hs μ (iter μ r j) := by
    rw [integral_prod _ hg2]
    exact hs_swap hB
  have hcs := sq_integral_mul_le hf2 hg2 hfg
  rw [ef, eg] at hcs
  have h1 := hs_iter_le (μ := μ) hrm hCr0 hrb 0 (j - 1)
  rw [zero_add] at h1
  change hs μ (iter μ r (j - 1)) ≤ _ * hs μ r at h1
  have h2 := hs_iter_le (μ := μ) hrm hCr0 hrb (j - 1) 1
  rw [show j - 1 + 1 = j by omega, mul_one] at h2
  set R := ‖kernelCLM r Cr hrm hCr0 hrb μ μ‖ with hR
  have hR0 : 0 ≤ R := norm_nonneg _
  have hsA0 := hs_nonneg (μ := μ) (iter μ r (j - 1))
  rw [et]
  have hsq : (∫ p, iter μ r (j - 1) p.1 p.2 * iter μ r j p.2 p.1 ∂(μ.prod μ)) ^ 2 ≤
      (R * hs μ (iter μ r (j - 1))) ^ 2 :=
    calc _ ≤ hs μ (iter μ r (j - 1)) * hs μ (iter μ r j) := hcs
      _ ≤ hs μ (iter μ r (j - 1)) * (R ^ 2 * hs μ (iter μ r (j - 1))) :=
          mul_le_mul_of_nonneg_left h2 hsA0
      _ = (R * hs μ (iter μ r (j - 1))) ^ 2 := by ring
  have habs : |∫ p, iter μ r (j - 1) p.1 p.2 * iter μ r j p.2 p.1 ∂(μ.prod μ)| ≤
      R * hs μ (iter μ r (j - 1)) :=
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hR0 hsA0)).1 (by rw [sq_abs]; exact hsq)
  calc |∫ p, iter μ r (j - 1) p.1 p.2 * iter μ r j p.2 p.1 ∂(μ.prod μ)|
      ≤ R * hs μ (iter μ r (j - 1)) := habs
    _ ≤ R * (R ^ (2 * (j - 1)) * hs μ r) := mul_le_mul_of_nonneg_left h1 hR0
    _ = R ^ (2 * j - 1) * hs μ r := by
        rw [show 2 * j - 1 = 2 * (j - 1) + 1 by omega, pow_succ]; ring

/-- A bounded measurable kernel bounded below by `m ≥ 0` has `cyc μ a (n+1) ≥ m^{n+1}`. -/
theorem cyc_succ_ge {a : X → X → ℝ} (ha : Bdd a) {m : ℝ} (hm : 0 ≤ m) (hlow : ∀ x y, m ≤ a x y)
    (n : ℕ) : m ^ (n + 1) ≤ cyc μ a (n + 1) := by
  rw [cyc_succ ha]
  have hi := ha.iter (μ := μ) n
  obtain ⟨Ci, hCi⟩ := hi.bdd
  have hd : Measurable fun x => iter μ a n x x :=
    hi.meas.comp (measurable_id.prodMk measurable_id)
  have hl : ∀ x, m ^ (n + 1) ≤ iter μ a n x x := fun x =>
    SectorDefect.iter_low (μ := μ) ha hm hlow n x x
  calc m ^ (n + 1) = ∫ _x, m ^ (n + 1) ∂μ := by simp
    _ ≤ ∫ x, iter μ a n x x ∂μ :=
        integral_mono (integrable_const _) (integrable_of_bdd hd (C := Ci) fun x => hCi x x) hl

/-- A bounded measurable kernel bounded below by `m > 0` has `cyc μ a (n+1) > 0`. -/
theorem cyc_succ_pos {a : X → X → ℝ} (ha : Bdd a) {m : ℝ} (hm : 0 < m) (hlow : ∀ x y, m ≤ a x y)
    (n : ℕ) : 0 < cyc μ a (n + 1) :=
  (pow_pos hm _).trans_le (cyc_succ_ge ha hm.le hlow n)

/-- `cyc μ k (2j+1) = c^{2j+1} + ∫ r^{∗(2j+1)}(x, x) dx`, `r = k − c φ ⊗ φ`. -/
theorem cyc_odd {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x y, k x y = k y x) {φ : X → ℝ}
    (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B) (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ}
    (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z) (j : ℕ) :
    cyc μ k (2 * j + 1) = c ^ (2 * j + 1) + ∫ x, iter μ (rem k c φ) (2 * j) x x ∂μ := by
  rw [cyc_succ hk]
  have hr := (Bdd.rem hk hφm hφb (c := c)).iter (μ := μ) (2 * j)
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have hd : Measurable fun x => iter μ (rem k c φ) (2 * j) x x :=
    hr.meas.comp (measurable_id.prodMk measurable_id)
  have hφ2 : Integrable (fun x => φ x ^ 2) μ :=
    integrable_of_bdd (hφm.pow_const 2) (C := B ^ 2) (fun x => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb x) 2)
  have e : ∀ x, iter μ k (2 * j) x x =
      c ^ (2 * j + 1) * φ x ^ 2 + iter μ (rem k c φ) (2 * j) x x := fun x => by
    rw [iter_decomp hk hsym hφm hφb hφ1 heig (2 * j) x x]; ring
  simp_rw [e]
  rw [integral_add (hφ2.const_mul _) (integrable_of_bdd hd (C := Cr) fun x => hCr x x),
    integral_const_mul, hφ1, mul_one]

variable {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)
  (hnorm : |c| = ‖kernelCLM k C hkm hC0 hkb μ μ‖) (hcpos : 0 < c)
  {Cr : ℝ} (hrm : Measurable (Function.uncurry (rem k c φ))) (hCr0 : 0 ≤ Cr)
  (hrb : ∀ x y, |rem k c φ x y| ≤ Cr) {τ : ℝ}
  (hτ : ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ ≤ τ * |c|)

include hkm hkb hsym hφm hφb hφ1 heig hnorm hcpos hτ in
/-- **(6.2) at odd time, operator form.** With `‖R‖ ≤ τ c` and `‖K‖²_HS/‖K‖² − 1 ≤ U`,
`cyc(T)/‖K‖^T − 1 ≤ τ^{T−2} U` at `T = 2j + 1`. -/
theorem trace_excess_odd_le {U : ℝ} (hU : hs μ k / ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ 2 - 1 ≤ U)
    (j : ℕ) (hj : 1 ≤ j) :
    cyc μ k (2 * j + 1) / ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (2 * j + 1) - 1 ≤
      τ ^ (2 * j - 1) * U := by
  have hc0 : c ≠ 0 := hcpos.ne'
  have hτ0 : 0 ≤ τ := (mul_nonneg_iff_of_pos_right (abs_pos.mpr hc0)).1 ((norm_nonneg _).trans hτ)
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hratio := PurityThermal.hs_rem_ratio hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hc0
  rw [← hnorm, abs_of_pos hcpos] at hratio hU ⊢
  have hrU : hs μ (rem k c φ) / c ^ 2 ≤ U := hratio ▸ hU
  have hτ' : ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ ≤ τ * c :=
    hτ.trans_eq (by rw [abs_of_pos hcpos])
  have htr := trace_iter_le (μ := μ) hrm hCr0 hrb j hj
  rw [cyc_odd hk hsym hφm hφb hφ1 heig j]
  have hcp : 0 < c ^ (2 * j + 1) := pow_pos hcpos _
  rw [add_div, div_self hcp.ne', add_sub_cancel_left, div_le_iff₀ hcp]
  have hp : ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ ^ (2 * j - 1) ≤ (τ * c) ^ (2 * j - 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hτ' _
  have hsr0 := hs_nonneg (μ := μ) (rem k c φ)
  have e2 : 2 * j + 1 = 2 * j - 1 + 2 := by omega
  calc ∫ x, iter μ (rem k c φ) (2 * j) x x ∂μ
      ≤ |∫ x, iter μ (rem k c φ) (2 * j) x x ∂μ| := le_abs_self _
    _ ≤ ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ ^ (2 * j - 1) * hs μ (rem k c φ) := htr
    _ ≤ (τ * c) ^ (2 * j - 1) * hs μ (rem k c φ) := mul_le_mul_of_nonneg_right hp hsr0
    _ = τ ^ (2 * j - 1) * (hs μ (rem k c φ) / c ^ 2) * c ^ (2 * j + 1) := by
        rw [e2, pow_add, mul_pow,
          show τ ^ (2 * j - 1) * (hs μ (rem k c φ) / c ^ 2) * (c ^ (2 * j - 1) * c ^ 2) =
            τ ^ (2 * j - 1) * c ^ (2 * j - 1) * (hs μ (rem k c φ) / c ^ 2 * c ^ 2) by ring,
          div_mul_cancel₀ _ (pow_ne_zero 2 hc0)]
    _ ≤ τ ^ (2 * j - 1) * U * c ^ (2 * j + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrU (pow_nonneg hτ0 _)) hcp.le

include hkm hkb hsym hφm hφb hφ1 heig hnorm hcpos hτ in
/-- **(6.3) at odd time for kernels.** With `‖R‖ ≤ τ c`, `‖K‖²_HS/‖K‖² − 1 ≤ U` and
`cyc(T) > 0`, `ψ_T = 2 log cyc(T) − log cyc(2T) ≤ 2 log (1 + τ^{T−2} U)` at `T = 2j + 1`. -/
theorem defect_odd_le {U : ℝ} (hU : hs μ k / ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ 2 - 1 ≤ U)
    (j : ℕ) (hj : 1 ≤ j) (hX : 0 < cyc μ k (2 * j + 1)) :
    DoublingPower.defect (cyc μ k) (2 * j + 1) ≤ 2 * log (1 + τ ^ (2 * j - 1) * U) := by
  have hc0 : c ≠ 0 := hcpos.ne'
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hf := powerFacts (μ := μ) hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hc0 (2 * j + 1) (by omega)
  have hb := hf.base
  have hs0 := hf.s_nonneg
  rw [abs_of_pos hcpos] at hb
  have hev := cyc_even (μ := μ) hk hsym (2 * j + 1) (by omega)
  have hE := trace_excess_odd_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hcpos hrm hCr0 hrb hτ
    hU j hj
  rw [← hnorm, abs_of_pos hcpos] at hE
  have hp1 : 0 < c ^ (2 * j + 1) := pow_pos hcpos _
  have hp2 : 0 < c ^ (2 * (2 * j + 1)) := pow_pos hcpos _
  have hY : 1 ≤ cyc μ k (2 * (2 * j + 1)) / c ^ (2 * (2 * j + 1)) := by
    rw [hev, hb, mul_div_cancel_left₀ _ hp2.ne']; linarith
  have hcyc2 : 0 < cyc μ k (2 * (2 * j + 1)) := by
    rw [hev, hb]; exact mul_pos hp2 (by linarith)
  have h := PurityTrace.psi_le (U := τ ^ (2 * j - 1) * U) (div_pos hX hp1) (by linarith) hY
  unfold DoublingPower.defect
  rw [log_div hX.ne' hp1.ne', log_div hcyc2.ne' hp2.ne', log_pow, log_pow] at h
  push_cast at h
  linarith

end General

/-- `τ^{2j−1} · τ²/(1 − τ²) = τ^{2j+1}/(1 − τ²)`. -/
theorem pow_tail_odd (τ : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    τ ^ (2 * j - 1) * (τ ^ 2 / (1 - τ ^ 2)) = τ ^ (2 * j + 1) / (1 - τ ^ 2) := by
  rw [show 2 * j + 1 = 2 * j - 1 + 2 by omega, pow_add, mul_div_assoc]

section Wilson

open MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.GaugeGroup MassGap.PurityHaarProjection

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- **(6.2) at odd time for the Wilson transfer kernel**, `τ = tanh(β tpMax (1 − q/d)/2)`,
`T = 2j + 1`, `j ≥ 1`. -/
theorem trace_excess_odd [Nontrivial G] {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 2 ≤ T j) (j : ℕ)
    (hj : 1 ≤ j) :
    cyc (hSG G μ T) (kTG G μ T β) (2 * j + 1) /
        ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ.le)
          (hSG G μ T) (hSG G μ T)‖ ^ (2 * j + 1) - 1
      ≤ tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) ^ (2 * j + 1) /
        (1 - tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) ^ 2) := by
  obtain ⟨hpos, φ, hφc, -, hφb, hφ1, heig, hR⟩ :=
    PurityRectWilsonFixed.norm_rem_le (G := G) (μ := μ) (T := T) hβ hT
  have hk : Bdd (kTG G μ T β) := bdd_kTG hβ.le
  have hφm := hφc.measurable
  have hr := hk.rem (c := ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
    (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖) hφm hφb
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have hCr0 : 0 ≤ Cr := (abs_nonneg _).trans (hCr (fun _ => 1) (fun _ => 1))
  have hτ := (hR Cr hr.meas hCr0 hCr).trans_eq (congrArg (HMul.hMul _) (abs_norm _).symm)
  have hU := PurityRectWilsonFixed.trace_excess (G := G) (μ := μ) (T := T) hβ hT 1 le_rfl
  rw [mul_one, PurityRayleigh.traceSeq_two] at hU
  have h := trace_excess_odd_le (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ.le)
    (kTG_symm β) hφm hφb hφ1 heig (abs_norm _) hpos hr.meas hCr0 hCr hτ hU j hj
  rwa [pow_tail_odd _ j hj] at h

/-- **(6.3) at odd time for the Wilson transfer kernel**, `ψ_T ≤ 2 log (1 + τ^T/(1 − τ²))`,
`τ = tanh(β tpMax (1 − q/d)/2)`, `T = 2j + 1`, `j ≥ 1`. -/
theorem defect_odd [Nontrivial G] {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 2 ≤ T j) (j : ℕ) (hj : 1 ≤ j) :
    DoublingPower.defect (cyc (hSG G μ T) (kTG G μ T β)) (2 * j + 1) ≤
      2 * log (1 +
        tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) ^ (2 * j + 1) /
        (1 - tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) ^ 2)) := by
  obtain ⟨hpos, φ, hφc, -, hφb, hφ1, heig, hR⟩ :=
    PurityRectWilsonFixed.norm_rem_le (G := G) (μ := μ) (T := T) hβ hT
  have hk : Bdd (kTG G μ T β) := bdd_kTG hβ.le
  have hφm := hφc.measurable
  have hr := hk.rem (c := ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
    (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖) hφm hφb
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have hCr0 : 0 ≤ Cr := (abs_nonneg _).trans (hCr (fun _ => 1) (fun _ => 1))
  have hτ := (hR Cr hr.meas hCr0 hCr).trans_eq (congrArg (HMul.hMul _) (abs_norm _).symm)
  have hU := PurityRectWilsonFixed.trace_excess (G := G) (μ := μ) (T := T) hβ hT 1 le_rfl
  rw [mul_one, PurityRayleigh.traceSeq_two] at hU
  have hX : 0 < cyc (hSG G μ T) (kTG G μ T β) (2 * j + 1) :=
    cyc_succ_pos hk (RectTransfer.kTmin_pos (μ := μ) (T := T) β) (kTG_lower hβ.le) (2 * j)
  have h := defect_odd_le (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ.le)
    (kTG_symm β) hφm hφb hφ1 heig (abs_norm _) hpos hr.meas hCr0 hCr hτ hU j hj hX
  rwa [pow_tail_odd _ j hj] at h

/-- **(6.3) at odd time for the Wilson partition function.** For a nontrivial gauge group, time
extents `L μ = 2j + 1` and `L' μ = 2(2j + 1)`, `j ≥ 1`, the same spatial extents, each at least
`2`, and `β > 0`, `2 log Z(L) − log Z(L') ≤ 2 log (1 + τ^{2j+1}/(1 − τ²))`,
`τ = tanh(β tpMax (1 − q/d)/2)`. -/
theorem ZRG_defect_odd [Nontrivial G] {β : ℝ} (hβ : 0 < β) {L L' : Fin 4 → ℕ}
    (hT : ∀ ν : {j : Fin 4 // j ≠ μ}, 2 ≤ L ν.1) (htr : tr L' μ = tr L μ) (j : ℕ) (hj : 1 ≤ j)
    (hL : L μ = 2 * j + 1) (hL' : L' μ = 2 * (2 * j + 1)) :
    2 * log (ZRG G L β) - log (ZRG G L' β) ≤
      2 * log (1 +
        tanh (β * RectTransfer.tpMax μ (tr L μ) * (1 - (fixedRank G : ℝ) / dim G) / 2) ^
          (2 * j + 1) /
        (1 - tanh (β * RectTransfer.tpMax μ (tr L μ) * (1 - (fixedRank G : ℝ) / dim G) / 2) ^ 2)) := by
  have h := defect_odd (G := G) (T := tr L μ) hβ hT j hj
  have h1 := ZRG_eq_cyc (G := G) (μ := μ) (L := L) β
  have h2 := ZRG_eq_cyc (G := G) (μ := μ) (L := L') β
  rw [htr, hL'] at h2
  rw [hL] at h1
  unfold DoublingPower.defect at h
  rw [h1, h2]
  exact h

end Wilson

end MassGap.PurityOddTime

#print axioms MassGap.PurityOddTime.trace_iter_le
#print axioms MassGap.PurityOddTime.cyc_succ_ge
#print axioms MassGap.PurityOddTime.cyc_succ_pos
#print axioms MassGap.PurityOddTime.cyc_odd
#print axioms MassGap.PurityOddTime.trace_excess_odd_le
#print axioms MassGap.PurityOddTime.defect_odd_le
#print axioms MassGap.PurityOddTime.pow_tail_odd
#print axioms MassGap.PurityOddTime.trace_excess_odd
#print axioms MassGap.PurityOddTime.defect_odd
#print axioms MassGap.PurityOddTime.ZRG_defect_odd
