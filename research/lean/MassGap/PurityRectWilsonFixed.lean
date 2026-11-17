import Mathlib
import MassGap.PurityHaarProjection
import MassGap.PurityRectWilson

/-!
# MassGap.PurityRectWilsonFixed — Theorem 5.2 for the Wilson transfer kernel at the ratio `tanh(β tpMax (1 − q/d)/2)` of Theorem 5.4

Theorem 5.2 and (6.2), (6.3) of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov,
I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling*
(research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510,
`Paper-2/Paper-2.pdf`), at the ratio of Lemma 5.3 and Theorem 5.4, for the gauge-projected
transfer kernel `RectTransferG.kTG` of the rectangular torus over a nontrivial gauge group `G`,
with `β > 0` and every spatial extent at least `2`.

The exponent `F = −2β tp(A, V, V')` of `gkG` has `∫ F dA = −β tpMax (1 − q/d)`
(`PurityHaarProjection.integral_exponent`), with `q = fixedRank G < d = dim G`
(`PurityHaarProjection.fixedRank_lt`). `PurityRectWilson.norm_rem_le_of` and its companions apply
with `cl = −β tpMax (1 − q/d)`, and the ratio is `τ = tanh(β tpMax (1 − q/d)/2)`.

* `hlt`, `ratio_eq`: `cl < 0` and `(1 − e^{cl})/(1 + e^{cl}) = τ`.
* `norm_rem_le`, `trace_excess`, `defect`: Theorem 5.2 as `‖R‖ ≤ τ‖K‖`, (6.2) and (6.3) at
  `T = 2j`, `j ≥ 1`, for `kTG`.
* `ZRG_defect`: (6.3) for the Wilson partition function: for time extents `L μ = 2j` and
  `L' μ = 4j` with the same spatial extents,
  `2 log Z(L) − log Z(L') ≤ 2 log (1 + τ^{2j}/(1 − τ²))`.
-/

namespace MassGap.PurityRectWilsonFixed

open MeasureTheory Real MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectWilsonG
  MassGap.RectTransferG MassGap.SlabKernelOperator MassGap.KernelPower MassGap.GaugeGroup
  MassGap.PurityHaarProjection

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- `cl = −β tpMax (1 − q/d) < 0` for a nontrivial gauge group, `β > 0` and spatial extents at
least `2`. -/
theorem hlt [Nontrivial G] {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 2 ≤ T j) :
    -β * (RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G)) < 0 := by
  have hd : (0 : ℝ) < dim G := Nat.cast_pos.2 dim_pos
  have hq : (fixedRank G : ℝ) / dim G < 1 :=
    (div_lt_one hd).2 (Nat.cast_lt.2 fixedRank_lt)
  have h1 : 0 < 1 - (fixedRank G : ℝ) / dim G := by linarith
  have h2 := PurityRectWilson.tpMax_pos (μ := μ) fun j => (by have := hT j; omega : 0 < T j)
  have := mul_pos hβ (mul_pos h2 h1)
  linarith

theorem ratio_eq (β : ℝ) :
    (exp 0 - exp (-β * (RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G)))) /
        (exp 0 + exp (-β * (RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G)))) =
      tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) := by
  rw [PurityWilson.ratio_tanh (exp_pos _) (exp_pos _), ← exp_sub, log_exp]
  congr 1
  ring

/-! ## Theorem 5.2, (6.2), (6.3) for `kTG` at `cl = −β tpMax (1 − q/d)` -/

/-- **Theorem 5.2 for the Wilson transfer kernel, ratio of Theorem 5.4.** `‖K‖ > 0`, the top
eigenfunction is continuous and bounded below, and the deflated operator satisfies
`‖R‖ ≤ tanh(β tpMax (1 − q/d)/2)‖K‖`. -/
theorem norm_rem_le [Nontrivial G] {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 2 ≤ T j) :
    0 < ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ.le)
        (hSG G μ T) (hSG G μ T)‖ ∧
      ∃ φ : (SpT μ T → G) → ℝ, Continuous φ ∧ (∃ m, 0 < m ∧ ∀ x, m ≤ φ x) ∧
        (∀ x, |φ x| ≤ 1 / ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
          (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖) ∧
        ∫ x, φ x ^ 2 ∂(hSG G μ T) = 1 ∧
        (∀ z, ∫ y, kTG G μ T β z y * φ y ∂(hSG G μ T) =
          ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
            (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ * φ z) ∧
        ∀ (Cr : ℝ)
          (hrm : Measurable (Function.uncurry (rem (kTG G μ T β)
            ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
              (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ φ)))
          (hCr0 : 0 ≤ Cr)
          (hrb : ∀ x y, |rem (kTG G μ T β)
            ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
              (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ φ x y| ≤ Cr),
          ‖kernelCLM (rem (kTG G μ T β)
            ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
              (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ φ) Cr hrm hCr0 hrb
              (hSG G μ T) (hSG G μ T)‖
            ≤ tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) *
              ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
                (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ :=
  PurityRectWilson.norm_rem_le_of hβ.le (fun V V' => (integral_exponent hT β V V').ge)
    (hlt hβ hT) (ratio_eq β)

/-- **(6.2) for the Wilson transfer kernel**, `τ = tanh(β tpMax (1 − q/d)/2)`, `T = 2j`, `j ≥ 1`. -/
theorem trace_excess [Nontrivial G] {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 2 ≤ T j) (j : ℕ)
    (hj : 1 ≤ j) :
    traceSeq (hSG G μ T) (kTG G μ T β) (2 * j) /
        ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ.le)
          (hSG G μ T) (hSG G μ T)‖ ^ (2 * j) - 1
      ≤ tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) ^ (2 * j) /
        (1 - tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) ^ 2) :=
  PurityRectWilson.trace_excess_of hβ.le (fun V V' => (integral_exponent hT β V V').ge)
    (hlt hβ hT) (ratio_eq β) j hj

/-- **(6.3) for the Wilson transfer kernel**, `ψ_T ≤ 2 log (1 + τ^T/(1 − τ²))`,
`τ = tanh(β tpMax (1 − q/d)/2)`, `T = 2j`, `j ≥ 1`. -/
theorem defect [Nontrivial G] {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 2 ≤ T j) (j : ℕ) (hj : 1 ≤ j) :
    DoublingPower.defect (traceSeq (hSG G μ T) (kTG G μ T β)) (2 * j) ≤
      2 * Real.log (1 +
        tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) ^ (2 * j) /
        (1 - tanh (β * RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G) / 2) ^ 2)) :=
  PurityRectWilson.defect_of hβ.le (fun V V' => (integral_exponent hT β V V').ge)
    (hlt hβ hT) (ratio_eq β) j hj

/-! ## (6.3) for the Wilson partition function -/

/-- **(6.3) for the Wilson partition function.** For a nontrivial gauge group, time extents
`L μ = 2j` and `L' μ = 4j`, `j ≥ 1`, the same spatial extents, each at least `2`, and `β > 0`,
`2 log Z(L) − log Z(L') ≤ 2 log (1 + τ^{2j}/(1 − τ²))`, `τ = tanh(β tpMax (1 − q/d)/2)`. -/
theorem ZRG_defect [Nontrivial G] {β : ℝ} (hβ : 0 < β) {L L' : Fin 4 → ℕ}
    (hT : ∀ ν : {j : Fin 4 // j ≠ μ}, 2 ≤ L ν.1) (htr : tr L' μ = tr L μ) (j : ℕ) (hj : 1 ≤ j)
    (hL : L μ = 2 * j) (hL' : L' μ = 2 * (2 * j)) :
    2 * Real.log (ZRG G L β) - Real.log (ZRG G L' β) ≤
      2 * Real.log (1 +
        tanh (β * RectTransfer.tpMax μ (tr L μ) * (1 - (fixedRank G : ℝ) / dim G) / 2) ^ (2 * j) /
        (1 - tanh (β * RectTransfer.tpMax μ (tr L μ) * (1 - (fixedRank G : ℝ) / dim G) / 2) ^ 2)) :=
  PurityRectWilson.ZRG_defect_of hβ.le htr j hj hL hL'
    (defect (G := G) (T := tr L μ) hβ hT j hj)

end MassGap.PurityRectWilsonFixed

#print axioms MassGap.PurityRectWilsonFixed.hlt
#print axioms MassGap.PurityRectWilsonFixed.ratio_eq
#print axioms MassGap.PurityRectWilsonFixed.norm_rem_le
#print axioms MassGap.PurityRectWilsonFixed.trace_excess
#print axioms MassGap.PurityRectWilsonFixed.defect
#print axioms MassGap.PurityRectWilsonFixed.ZRG_defect
