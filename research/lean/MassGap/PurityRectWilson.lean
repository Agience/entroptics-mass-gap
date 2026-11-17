import Mathlib
import MassGap.RectTransferG
import MassGap.PurityWilsonCompact

/-!
# MassGap.PurityRectWilson — Theorem 5.2 and (6.2), (6.3) for the Wilson transfer kernel

Theorem 5.2 and (6.2), (6.3) of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood,
T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak
Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>,
commit 8e01510, `Paper-2/Paper-2.pdf`), for the gauge-projected transfer kernel
`RectTransferG.kTG` of the rectangular torus over a gauge group `G`, with `β > 0` and positive
spatial extents `T`.

The kernel is `k = D · A · D` with `D V = exp(−β sp(V)/2)` and
`A V V' = ∫ exp(−2β tp(A, V, V')) dA` over Haar measure on the axis links. The exponent lies in
`[−2β tpMax, 0]` pointwise (`RectTransferG.tpG_nonneg`, `RectTransferG.tpG_le`), and inverting the
axis links swaps `V` and `V'` (`RectTransferG.tpG_inv`), so `PurityWilsonCompact` applies with
`cl = −2β tpMax`, `cu = 0`, and the ratio is `τ = tanh(β tpMax)`.

* `tpMax_pos`: `0 < tpMax` for positive spatial extents.
* `ratio_eq`: `(1 − e^{−2β tpMax})/(1 + e^{−2β tpMax}) = tanh(β tpMax)`.
* `norm_rem_le_of`, `trace_excess_of`, `defect_of`: Theorem 5.2 as `‖R‖ ≤ τ‖K‖`, (6.2) and
  (6.3) at `T = 2j`, `j ≥ 1`, for `kTG`, at any lower bound `cl < 0` of `∫ −2β tp dA`,
  `τ = (1 − e^{cl})/(1 + e^{cl})`. `ZRG_defect_of`: a bound on the doubling defect of `kTG` at
  `T = 2j` bounds `2 log Z(L) − log Z(L')` for `L μ = 2j`, `L' μ = 4j`.
* `norm_rem_le`, `trace_excess`, `defect`: the same at `cl = −2β tpMax`, `τ = tanh(β tpMax)`.
* `ZRG_defect`: (6.3) for the Wilson partition function: for time extents `L μ = 2j` and
  `L' μ = 4j` with the same spatial extents,
  `2 log Z(L) − log Z(L') ≤ 2 log (1 + τ^{2j}/(1 − τ²))`.
-/

namespace MassGap.PurityRectWilson

open MeasureTheory Real MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectWilsonG
  MassGap.RectTransferG MassGap.SlabKernelOperator MassGap.KernelPower MassGap.GaugeGroup

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

omit [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
theorem tpMax_pos (hT : ∀ j, 0 < T j) : 0 < RectTransfer.tpMax μ T := by
  unfold RectTransfer.tpMax
  have h1 : 0 < Fintype.card {j : Fin 4 // j ≠ μ} :=
    Fintype.card_pos_iff.2
      ⟨if h : μ = 0 then ⟨1, by rw [h]; decide⟩ else ⟨0, fun e => h e.symm⟩⟩
  have h2 : 0 < Fintype.card (TT μ T) := Fintype.card_pos_iff.2 ⟨fun j => ⟨0, hT j⟩⟩
  have h1' : (0 : ℝ) < Fintype.card {j : Fin 4 // j ≠ μ} := Nat.cast_pos.2 h1
  have h2' : (0 : ℝ) < Fintype.card (TT μ T) := Nat.cast_pos.2 h2
  positivity

omit [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
theorem ratio_eq (β : ℝ) :
    (exp 0 - exp (-β * (2 * RectTransfer.tpMax μ T))) /
        (exp 0 + exp (-β * (2 * RectTransfer.tpMax μ T))) = tanh (β * RectTransfer.tpMax μ T) := by
  rw [PurityWilson.ratio_tanh (exp_pos _) (exp_pos _), ← exp_sub, log_exp]
  congr 1
  ring

/-! ## The hypotheses of `PurityWilsonCompact` for `kTG` -/

theorem hF (β : ℝ) :
    Continuous fun p : ((SpT μ T → G) × (SpT μ T → G)) × (TT μ T → G) =>
      -β * (2 * tpTG G μ T p.2 p.1.1 p.1.2) :=
  continuous_const.mul
    (continuous_const.mul (continuous_tpG continuous_snd continuous_fst.fst continuous_fst.snd))

theorem hFs (β : ℝ) (V V' : SpT μ T → G) (A : TT μ T → G) :
    -β * (2 * tpTG G μ T A V' V) =
      -β * (2 * tpTG G μ T
        (MeasurableEquiv.piCongrRight (fun _ : TT μ T => MeasurableEquiv.inv G) A) V V') := by
  have h := tpG_inv (fun y => (A y)⁻¹) V V'
  simp only [inv_inv] at h
  exact congrArg (fun t => -β * (2 * t)) h

theorem hcl {β : ℝ} (hβ : 0 ≤ β) (V V' : SpT μ T → G) :
    -β * (2 * RectTransfer.tpMax μ T) ≤
      ∫ A, -β * (2 * tpTG G μ T A V V') ∂(hAG G μ T) := by
  have hc : Continuous fun A : TT μ T → G => -β * (2 * tpTG G μ T A V V') :=
    continuous_const.mul
      (continuous_const.mul (continuous_tpG continuous_id continuous_const continuous_const))
  calc -β * (2 * RectTransfer.tpMax μ T)
      = ∫ _A, -β * (2 * RectTransfer.tpMax μ T) ∂(hAG G μ T) := by simp
    _ ≤ _ := integral_mono (integrable_const _) (PurityWilsonCompact.integrable_cont hc)
        fun A => by have := tpG_le A V V'; nlinarith

theorem hcu {β : ℝ} (hβ : 0 ≤ β) (V V' : SpT μ T → G) (A : TT μ T → G) :
    -β * (2 * tpTG G μ T A V V') ≤ 0 := by
  have := tpG_nonneg A V V'; nlinarith

omit [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
theorem hlt {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 0 < T j) :
    -β * (2 * RectTransfer.tpMax μ T) < 0 := by
  have := tpMax_pos hT; nlinarith

theorem hDc (β : ℝ) : Continuous fun V : SpT μ T → G => exp (-β * spTG G μ T V / 2) :=
  continuous_exp.comp ((continuous_const.mul (continuous_spG continuous_id)).div_const 2)

theorem hDl {β : ℝ} (hβ : 0 ≤ β) (V : SpT μ T → G) :
    exp (-β * RectTransfer.spMax μ T / 2) ≤ exp (-β * spTG G μ T V / 2) := by
  have := spG_le V
  exact exp_le_exp.2 (by nlinarith)

theorem hDu {β : ℝ} (hβ : 0 ≤ β) (V : SpT μ T → G) : exp (-β * spTG G μ T V / 2) ≤ 1 := by
  have := spG_nonneg V
  exact exp_le_one_iff.2 (by nlinarith)

/-! ## Theorem 5.2, (6.2), (6.3) for `kTG` at a lower bound `cl` -/

/-- **Theorem 5.2 for the Wilson transfer kernel at a lower bound `cl`.** For `β ≥ 0` and any
`cl < 0` below `∫ −2β tp dA`, `‖K‖ > 0`, the top eigenfunction is continuous and bounded below,
and the deflated operator satisfies `‖R‖ ≤ τ‖K‖`, `τ = (1 − e^{cl})/(1 + e^{cl})`. -/
theorem norm_rem_le_of {β : ℝ} (hβ : 0 ≤ β) {cl τ : ℝ}
    (hcl : ∀ V V' : SpT μ T → G, cl ≤ ∫ A, -β * (2 * tpTG G μ T A V V') ∂(hAG G μ T))
    (hlt : cl < 0) (hτ : (exp 0 - exp cl) / (exp 0 + exp cl) = τ) :
    0 < ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
        (hSG G μ T) (hSG G μ T)‖ ∧
      ∃ φ : (SpT μ T → G) → ℝ, Continuous φ ∧ (∃ m, 0 < m ∧ ∀ x, m ≤ φ x) ∧
        (∀ x, |φ x| ≤ 1 / ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
          (abs_kTG_le hβ) (hSG G μ T) (hSG G μ T)‖) ∧
        ∫ x, φ x ^ 2 ∂(hSG G μ T) = 1 ∧
        (∀ z, ∫ y, kTG G μ T β z y * φ y ∂(hSG G μ T) =
          ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
            (abs_kTG_le hβ) (hSG G μ T) (hSG G μ T)‖ * φ z) ∧
        ∀ (Cr : ℝ)
          (hrm : Measurable (Function.uncurry (rem (kTG G μ T β)
            ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
              (abs_kTG_le hβ) (hSG G μ T) (hSG G μ T)‖ φ)))
          (hCr0 : 0 ≤ Cr)
          (hrb : ∀ x y, |rem (kTG G μ T β)
            ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
              (abs_kTG_le hβ) (hSG G μ T) (hSG G μ T)‖ φ x y| ≤ Cr),
          ‖kernelCLM (rem (kTG G μ T β)
            ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
              (abs_kTG_le hβ) (hSG G μ T) (hSG G μ T)‖ φ) Cr hrm hCr0 hrb
              (hSG G μ T) (hSG G μ T)‖
            ≤ τ * ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
                (abs_kTG_le hβ) (hSG G μ T) (hSG G μ T)‖ := by
  have h := PurityWilsonCompact.norm_rem_le (μ := hSG G μ T) (ν := hAG G μ T)
    (D := fun V => exp (-β * spTG G μ T V / 2)) (dl := exp (-β * RectTransfer.spMax μ T / 2))
    (du := 1) (F := fun V V' A => -β * (2 * tpTG G μ T A V V'))
    (σ := MeasurableEquiv.piCongrRight (fun _ : TT μ T => MeasurableEquiv.inv G))
    (cl := cl) (cu := 0) (A := gkG G μ T β) (k := kTG G μ T β)
    (C := 1) (hDc β) (exp_pos _) (hDl hβ) (hDu hβ) (hF β) measurePreserving_invAxG
    (hFs β) hcl (hcu hβ) hlt (fun _ _ => rfl) (fun _ _ => rfl)
    (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
  rw [hτ] at h
  exact h

/-- **(6.2) for the Wilson transfer kernel at a lower bound `cl`**, `τ = (1 − e^{cl})/(1 + e^{cl})`,
`T = 2j`, `j ≥ 1`. -/
theorem trace_excess_of {β : ℝ} (hβ : 0 ≤ β) {cl τ : ℝ}
    (hcl : ∀ V V' : SpT μ T → G, cl ≤ ∫ A, -β * (2 * tpTG G μ T A V V') ∂(hAG G μ T))
    (hlt : cl < 0) (hτ : (exp 0 - exp cl) / (exp 0 + exp cl) = τ) (j : ℕ) (hj : 1 ≤ j) :
    traceSeq (hSG G μ T) (kTG G μ T β) (2 * j) /
        ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
          (hSG G μ T) (hSG G μ T)‖ ^ (2 * j) - 1
      ≤ τ ^ (2 * j) / (1 - τ ^ 2) := by
  have h := PurityWilsonCompact.trace_excess (μ := hSG G μ T) (ν := hAG G μ T)
    (D := fun V => exp (-β * spTG G μ T V / 2)) (dl := exp (-β * RectTransfer.spMax μ T / 2))
    (du := 1) (F := fun V V' A => -β * (2 * tpTG G μ T A V V'))
    (σ := MeasurableEquiv.piCongrRight (fun _ : TT μ T => MeasurableEquiv.inv G))
    (cl := cl) (cu := 0) (A := gkG G μ T β) (k := kTG G μ T β)
    (C := 1) (hDc β) (exp_pos _) (hDl hβ) (hDu hβ) (hF β) measurePreserving_invAxG
    (hFs β) hcl (hcu hβ) hlt (fun _ _ => rfl) (fun _ _ => rfl)
    (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ) j hj
  simp only at h
  rwa [hτ] at h

/-- **(6.3) for the Wilson transfer kernel at a lower bound `cl`**,
`ψ_T ≤ 2 log (1 + τ^T/(1 − τ²))`, `τ = (1 − e^{cl})/(1 + e^{cl})`, `T = 2j`, `j ≥ 1`. -/
theorem defect_of {β : ℝ} (hβ : 0 ≤ β) {cl τ : ℝ}
    (hcl : ∀ V V' : SpT μ T → G, cl ≤ ∫ A, -β * (2 * tpTG G μ T A V V') ∂(hAG G μ T))
    (hlt : cl < 0) (hτ : (exp 0 - exp cl) / (exp 0 + exp cl) = τ) (j : ℕ) (hj : 1 ≤ j) :
    DoublingPower.defect (traceSeq (hSG G μ T) (kTG G μ T β)) (2 * j) ≤
      2 * Real.log (1 + τ ^ (2 * j) / (1 - τ ^ 2)) := by
  have h := PurityWilsonCompact.defect (μ := hSG G μ T) (ν := hAG G μ T)
    (D := fun V => exp (-β * spTG G μ T V / 2)) (dl := exp (-β * RectTransfer.spMax μ T / 2))
    (du := 1) (F := fun V V' A => -β * (2 * tpTG G μ T A V V'))
    (σ := MeasurableEquiv.piCongrRight (fun _ : TT μ T => MeasurableEquiv.inv G))
    (cl := cl) (cu := 0) (A := gkG G μ T β) (k := kTG G μ T β)
    (C := 1) (hDc β) (exp_pos _) (hDl hβ) (hDu hβ) (hF β) measurePreserving_invAxG
    (hFs β) hcl (hcu hβ) hlt (fun _ _ => rfl) (fun _ _ => rfl)
    (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ) j hj
  simp only at h
  rwa [hτ] at h

/-- **(6.3) for the Wilson partition function from (6.3) for `kTG`.** For time extents `L μ = 2j`
and `L' μ = 4j` with the same spatial extents and `β ≥ 0`, any bound `b` on the doubling defect of
`kTG` at `T = 2j` bounds `2 log Z(L) − log Z(L')`. -/
theorem ZRG_defect_of {β : ℝ} (hβ : 0 ≤ β) {L L' : Fin 4 → ℕ} (htr : tr L' μ = tr L μ) (j : ℕ)
    (hj : 1 ≤ j) (hL : L μ = 2 * j) (hL' : L' μ = 2 * (2 * j)) {b : ℝ}
    (h : DoublingPower.defect (traceSeq (hSG G μ (tr L μ)) (kTG G μ (tr L μ) β)) (2 * j) ≤ b) :
    2 * Real.log (ZRG G L β) - Real.log (ZRG G L' β) ≤ b := by
  have h1 := ZRG_eq_traceSeq (G := G) (μ := μ) (L := L) hβ j hj hL
  have h2 := ZRG_eq_traceSeq (G := G) (μ := μ) (L := L') hβ (2 * j) (by omega) hL'
  rw [htr, hL'] at h2
  rw [hL] at h1
  unfold DoublingPower.defect at h
  rw [h1, h2]
  exact h

/-! ## Theorem 5.2, (6.2), (6.3) for `kTG` at `cl = −2β tpMax` -/

/-- **Theorem 5.2 for the Wilson transfer kernel.** `‖K‖ > 0`, the top eigenfunction is
continuous and bounded below, and the deflated operator satisfies `‖R‖ ≤ tanh(β tpMax)‖K‖`. -/
theorem norm_rem_le {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 0 < T j) :
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
            ≤ tanh (β * RectTransfer.tpMax μ T) *
              ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
                (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖ :=
  norm_rem_le_of hβ.le (hcl hβ.le) (hlt hβ hT) (ratio_eq β)

/-- **(6.2) for the Wilson transfer kernel**, `τ = tanh(β tpMax)`, `T = 2j`, `j ≥ 1`. -/
theorem trace_excess {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 0 < T j) (j : ℕ) (hj : 1 ≤ j) :
    traceSeq (hSG G μ T) (kTG G μ T β) (2 * j) /
        ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ.le)
          (hSG G μ T) (hSG G μ T)‖ ^ (2 * j) - 1
      ≤ tanh (β * RectTransfer.tpMax μ T) ^ (2 * j) /
        (1 - tanh (β * RectTransfer.tpMax μ T) ^ 2) :=
  trace_excess_of hβ.le (hcl hβ.le) (hlt hβ hT) (ratio_eq β) j hj

/-- **(6.3) for the Wilson transfer kernel**, `ψ_T ≤ 2 log (1 + τ^T/(1 − τ²))`,
`τ = tanh(β tpMax)`, `T = 2j`, `j ≥ 1`. -/
theorem defect {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 0 < T j) (j : ℕ) (hj : 1 ≤ j) :
    DoublingPower.defect (traceSeq (hSG G μ T) (kTG G μ T β)) (2 * j) ≤
      2 * Real.log (1 + tanh (β * RectTransfer.tpMax μ T) ^ (2 * j) /
        (1 - tanh (β * RectTransfer.tpMax μ T) ^ 2)) :=
  defect_of hβ.le (hcl hβ.le) (hlt hβ hT) (ratio_eq β) j hj

/-! ## (6.3) for the Wilson partition function -/

/-- **(6.3) for the Wilson partition function.** For time extents `L μ = 2j` and `L' μ = 4j`,
`j ≥ 1`, the same positive spatial extents, and `β > 0`,
`2 log Z(L) − log Z(L') ≤ 2 log (1 + τ^{2j}/(1 − τ²))`, `τ = tanh(β tpMax)`. -/
theorem ZRG_defect {β : ℝ} (hβ : 0 < β) {L L' : Fin 4 → ℕ}
    (hT : ∀ ν : {j : Fin 4 // j ≠ μ}, 0 < L ν.1) (htr : tr L' μ = tr L μ) (j : ℕ) (hj : 1 ≤ j)
    (hL : L μ = 2 * j) (hL' : L' μ = 2 * (2 * j)) :
    2 * Real.log (ZRG G L β) - Real.log (ZRG G L' β) ≤
      2 * Real.log (1 + tanh (β * RectTransfer.tpMax μ (tr L μ)) ^ (2 * j) /
        (1 - tanh (β * RectTransfer.tpMax μ (tr L μ)) ^ 2)) :=
  ZRG_defect_of hβ.le htr j hj hL hL' (defect (G := G) (T := tr L μ) hβ hT j hj)

end MassGap.PurityRectWilson

#print axioms MassGap.PurityRectWilson.tpMax_pos
#print axioms MassGap.PurityRectWilson.ratio_eq
#print axioms MassGap.PurityRectWilson.hF
#print axioms MassGap.PurityRectWilson.hFs
#print axioms MassGap.PurityRectWilson.hcl
#print axioms MassGap.PurityRectWilson.hcu
#print axioms MassGap.PurityRectWilson.hlt
#print axioms MassGap.PurityRectWilson.hDc
#print axioms MassGap.PurityRectWilson.hDl
#print axioms MassGap.PurityRectWilson.hDu
#print axioms MassGap.PurityRectWilson.norm_rem_le_of
#print axioms MassGap.PurityRectWilson.trace_excess_of
#print axioms MassGap.PurityRectWilson.defect_of
#print axioms MassGap.PurityRectWilson.ZRG_defect_of
#print axioms MassGap.PurityRectWilson.norm_rem_le
#print axioms MassGap.PurityRectWilson.trace_excess
#print axioms MassGap.PurityRectWilson.defect
#print axioms MassGap.PurityRectWilson.ZRG_defect
