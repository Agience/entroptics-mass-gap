import Mathlib
import MassGap.OpenAIBridgeCubic

/-!
# MassGap.OpenAIBridgeThermal — the thermal remainder decays with the separation

`OpenAIBridgeCubic.thermRem μ k c φ F w a b = ‖R^{b+1} F R^{a+1}‖²_HS / |c|^L` with
`L = 2w + (2a+2) + (2b+2)`. Splitting `R^{a+1} = R^{p+1} R^{q+1}` and `R^{b+1} = R^{q'+1} R^{p'+1}`
and applying the gap bound in Hilbert–Schmidt form (`OpenAIBridgeRP.hs_conv_rem_le`) on each side
removes `q + 1` and `q' + 1` steps from each separation at the price of the contraction:

    D_L(f; a, b) ≤ (1/2)^{2⌊(q+1)/n⌋} (1/2)^{2⌊(q'+1)/n⌋} D_{L'}(f; p, p'),

`a = p + q + 1`, `b = p' + q' + 1`, `L' = L − 2(q+1) − 2(q'+1)` (`thermRem_shorten`). With
`OpenAIBridgeCubic.parts_le_moment` the shorter remainder is below the reflected moment on the torus
of `L'` steps (`thermRem_shorten_moment`). No sup bound of the insertion and no positivity of the
transfer operator enter.

* `hs_rem_conv_le` — the gap bound with the remainder on the left, by transposition.
* `thermRem_shorten` — the shortening inequality.
* `thermRem_shorten_moment` — the thermal remainder below the contraction times the reflected moment
  at the shorter separations.
* `thermalRemainderVanishes_of_bound` — a remainder below a vanishing factor times an eventually
  bounded moment satisfies `OpenAIBridgeCubic.ThermalRemainderVanishes`.
-/

namespace MassGap.OpenAIBridgeThermal

open MeasureTheory Real Filter
open MassGap.KernelPower MassGap.SlabKernelOperator MassGap.OpenAIBridgeCluster
  MassGap.OpenAIBridgeSlab MassGap.OpenAIBridgeRP MassGap.OpenAIBridgeCubic

section Shorten

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

variable {φ : X → ℝ} (hφm : Measurable φ) {Bφ : ℝ} (hφb : ∀ x, |φ x| ≤ Bφ)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1)

variable {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
  {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)

variable (hnorm : |c| = ‖kernelCLM k C hkm hC0 hkb μ μ‖) {n : ℕ}
  (hgap : ∀ f : Lp ℝ 2 μ, inner ℝ f (KernelGap.vac (μ := μ) hφm hφb) = 0 →
    ‖((kernelCLM k C hkm hC0 hkb μ μ) ^ n) f‖
      ≤ 1 / 2 * ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ n * ‖f‖)

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The gap bound with the remainder on the left**:
`hs(R^{m+1} ∗ P) ≤ ((1/2)^⌊(m+1)/n⌋ |c|^{m+1})² hs(P)`. Transpose (`hs_tp`, `tp_conv`), use the
symmetry of `R^{m+1}` (`tp_iter`) and `OpenAIBridgeRP.hs_conv_rem_le`.

DERIVED: `1/2` is the contraction of the gap hypothesis; `1` the offset of `iter`; `2` the squares. -/
theorem hs_rem_conv_le {P : X → X → ℝ} (hP : Bdd P) (m : ℕ) :
    hs μ (conv μ (iter μ (rem k c φ) m) P)
      ≤ ((1 / 2) ^ ((m + 1) / n) * |c| ^ (m + 1)) ^ 2 * hs μ P := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hJ : Bdd (iter μ (rem k c φ) m) := hr.iter m
  have hJP : Bdd (conv μ (iter μ (rem k c φ) m) P) := Bdd.conv (μ := μ) hJ hP
  rw [← hs_tp hJP, tp_conv, tp_iter hr (rem_symm hsym) m, ← hs_tp hP]
  exact hs_conv_rem_le hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap (bdd_tp hP) m

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The thermal remainder decays with the separation**: for `a = p + q + 1`, `b = p' + q' + 1`,

    D_L(f; a, b) ≤ (1/2)^{2⌊(q+1)/n⌋} (1/2)^{2⌊(q'+1)/n⌋} D_{L'}(f; p, p'),

`L' = L − 2(q+1) − 2(q'+1)`. `iter_add` splits both powers of `R`, `conv_assoc` regroups,
`hs_rem_conv_le` strips `R^{q'+1}` on the left and `hs_conv_rem_le` strips `R^{q+1}` on the right;
the powers `|c|^{2(q+1)}`, `|c|^{2(q'+1)}` cancel against the normalisation.

DERIVED: `1/2` is the contraction of the gap hypothesis; `1` the offset of `iter`; `2` the squares
and the doubled separations. -/
theorem thermRem_shorten (hc0 : c ≠ 0) {F : X → X → ℝ} (hF : Bdd F) (w p q p' q' : ℕ) :
    thermRem μ k c φ F w (p + q + 1) (p' + q' + 1)
      ≤ ((1 / 2) ^ ((q + 1) / n)) ^ 2 * ((1 / 2) ^ ((q' + 1) / n)) ^ 2
        * thermRem μ k c φ F w p p' := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hIp := hr.iter (μ := μ) p
  have hIq := hr.iter (μ := μ) q
  have hIp' := hr.iter (μ := μ) p'
  have hIq' := hr.iter (μ := μ) q'
  have hY : Bdd (conv μ F (iter μ (rem k c φ) p)) := Bdd.conv (μ := μ) hF hIp
  have hZ : Bdd (conv μ (iter μ (rem k c φ) p') (conv μ F (iter μ (rem k c φ) p))) :=
    Bdd.conv (μ := μ) hIp' hY
  have hZq : Bdd (conv μ (conv μ (iter μ (rem k c φ) p') (conv μ F (iter μ (rem k c φ) p)))
      (iter μ (rem k c φ) q)) := Bdd.conv (μ := μ) hZ hIq
  have ea : iter μ (rem k c φ) (p + q + 1)
      = conv μ (iter μ (rem k c φ) p) (iter μ (rem k c φ) q) := iter_add hr p q
  have eb : iter μ (rem k c φ) (p' + q' + 1)
      = conv μ (iter μ (rem k c φ) q') (iter μ (rem k c φ) p') := by
    rw [show p' + q' + 1 = q' + p' + 1 by ring]; exact iter_add hr q' p'
  have ek : conv μ (iter μ (rem k c φ) (p' + q' + 1)) (conv μ F (iter μ (rem k c φ) (p + q + 1)))
      = conv μ (iter μ (rem k c φ) q')
          (conv μ (conv μ (iter μ (rem k c φ) p') (conv μ F (iter μ (rem k c φ) p)))
            (iter μ (rem k c φ) q)) := by
    rw [ea, eb, conv_assoc hF hIp hIq, ← conv_assoc hIq' hIp' (Bdd.conv (μ := μ) hY hIq),
      conv_assoc hIp' hY hIq]
  have h1 := hs_rem_conv_le hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hZq q'
  have h2 := hs_conv_rem_le hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hZ q
  set u : ℝ := (1 / 2) ^ ((q + 1) / n)
  set v : ℝ := (1 / 2) ^ ((q' + 1) / n)
  set s : ℝ := |c| ^ (q + 1)
  set t : ℝ := |c| ^ (q' + 1)
  set N0 : ℝ := hs μ (conv μ (iter μ (rem k c φ) p') (conv μ F (iter μ (rem k c φ) p)))
  set P0 : ℝ := |c| ^ (w + w + (p + p + 2) + (p' + p' + 2))
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hP0 : 0 < P0 := pow_pos hc _
  have hs0 : 0 < s := pow_pos hc _
  have ht0 : 0 < t := pow_pos hc _
  have hN0 : 0 ≤ N0 := hs_nonneg _
  have hNq := hs_nonneg (μ := μ) (conv μ (conv μ (iter μ (rem k c φ) p')
    (conv μ F (iter μ (rem k c φ) p))) (iter μ (rem k c φ) q))
  have eL : |c| ^ (w + w + (p + q + 1 + (p + q + 1) + 2) + (p' + q' + 1 + (p' + q' + 1) + 2))
      = P0 * s ^ 2 * t ^ 2 := by
    simp only [P0, s, t]; ring
  have hnum : hs μ (conv μ (iter μ (rem k c φ) (p' + q' + 1))
        (conv μ F (iter μ (rem k c φ) (p + q + 1))))
      ≤ (v * t) ^ 2 * ((u * s) ^ 2 * N0) := by
    rw [ek]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
  unfold thermRem
  rw [eL, div_le_iff₀ (by positivity)]
  have e : u ^ 2 * v ^ 2 * (N0 / P0) * (P0 * s ^ 2 * t ^ 2) = (v * t) ^ 2 * ((u * s) ^ 2 * N0) := by
    field_simp
  rw [e]
  exact hnum

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The thermal remainder below the reflected moment at the shorter separations**: for
`a = p + q + 1`, `b = p' + q' + 1`,

    D_L(f; a, b) ≤ (1/2)^{2⌊(q+1)/n⌋} (1/2)^{2⌊(q'+1)/n⌋} (1 + σ₀') E_{L'}[f · θf],

`σ₀' = excited (w + p + p' + 2)`, `E_{L'}` the reflected moment at separations `2p + 2`, `2p' + 2`
on the torus of `L' = 2(w + p + p' + 2)` steps (`thermRem_shorten`,
`OpenAIBridgeCubic.parts_le_moment`).

DERIVED: `1/2` is the contraction; `1` the vacuum's own weight and the offset of `iter`; `2` the
squares and the offset of the excited weight. -/
theorem thermRem_shorten_moment (hc0 : c ≠ 0) {F : X → X → ℝ} (hF : Bdd F) (w p q p' q' : ℕ) :
    thermRem μ k c φ F w (p + q + 1) (p' + q' + 1)
      ≤ ((1 / 2) ^ ((q + 1) / n)) ^ 2 * ((1 / 2) ^ ((q' + 1) / n)) ^ 2
        * ((1 + excited μ k c φ (w + p + p' + 2)) * torusMom μ k F p p' (w + p + p' + 1)) :=
  (thermRem_shorten hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hF w p q p' q').trans
    (mul_le_mul_of_nonneg_left
      (parts_le_moment hφm hφb hφ1 hkm hkb hsym heig hc0 hF w p p').1 (by positivity))

end Shorten

/-! ## Vanishing from a vanishing factor -/

/-- **A remainder below a vanishing factor times a bounded moment vanishes**: if eventually along
the order `D p N ≤ s p N · M p N`, the factor `s ≥ 0` is eventually below every `ε > 0` and the
moment `M` is eventually at most `M₀`, then `ThermalRemainderVanishes D`. With
`thermRem_shorten_moment`, `s` is the contraction `(1/2)^{2⌊(q+1)/n⌋} (1/2)^{2⌊(q'+1)/n⌋}` and `M`
the reflected moment at the shorter separations.

DERIVED: `0` is the sign of the factor and the limit. -/
theorem thermalRemainderVanishes_of_bound {D s M : ℕ → ℕ → ℝ} {M₀ : ℝ}
    (hD : ∀ᶠ p in atTop, ∀ᶠ N in atTop, D p N ≤ s p N * M p N)
    (hs : ∀ ε : ℝ, 0 < ε → ∀ᶠ p in atTop, ∀ᶠ N in atTop, 0 ≤ s p N ∧ s p N ≤ ε)
    (hM : ∀ᶠ p in atTop, ∀ᶠ N in atTop, M p N ≤ M₀) :
    ThermalRemainderVanishes D := by
  intro ε hε
  set B : ℝ := max M₀ 0 + 1
  have hB : 0 < B := by positivity
  filter_upwards [hD, hs (ε / B) (div_pos hε hB), hM] with p h1 h2 h3
  filter_upwards [h1, h2, h3] with N e1 e2 e3
  have hMB : M p N ≤ B := e3.trans ((le_max_left _ _).trans (by linarith))
  calc D p N ≤ s p N * M p N := e1
    _ ≤ s p N * B := mul_le_mul_of_nonneg_left hMB e2.1
    _ ≤ ε / B * B := mul_le_mul_of_nonneg_right e2.2 hB.le
    _ = ε := div_mul_cancel₀ ε hB.ne'

end MassGap.OpenAIBridgeThermal

#print axioms MassGap.OpenAIBridgeThermal.hs_rem_conv_le
#print axioms MassGap.OpenAIBridgeThermal.thermRem_shorten
#print axioms MassGap.OpenAIBridgeThermal.thermRem_shorten_moment
#print axioms MassGap.OpenAIBridgeThermal.thermalRemainderVanishes_of_bound
