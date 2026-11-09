import Mathlib
import MassGap.RectTransferG
import MassGap.DoublingWilson
import MassGap.DoublingSharp

/-!
# MassGap.DoublingWilsonG — the four-dimensional doubling facts for the Wilson model of `G`

`DoublingWilson` with `SUN.SU N` replaced by a `GaugeGroup G`.
`xWG G n β v = log ZRG G (ext n v) β`, the logarithm of the partition function on the 4-torus with
sides `2^{v_μ} n`.

* `factRepG`: at `β ≥ 0` and even `n ≥ 2`, in every direction and at every corner, `ZRG` is the trace
  sequence of the symmetric, continuous, strictly positive kernel `RectTransferG.kTG`, which has a top
  eigenfunction (`KernelEigen.exists_eigen`), so the four trace facts hold.
* `positiveG`: `DoublingRecursion.Positive (xWG G n β)`.
* `Δ_corner0G`: `Δ (xWG G n β) (corner 0) = defectWG G 4 (wilsonDensityG G) β n`.
* `Δ_cornerG`: the corner function at `k𝟙` is the defect at side `2ᵏ n`.
* `defectWG_pow_le`: at `β ≥ 0`, a seed `defectWG ≤ 1/1000` at an even side `n ≥ 2` gives the seed at
  every side `2ᵏ n`.

DERIVED (module-wide): `4` the dimension; `2` the doubling; `16 = 2⁴` the number of side-`n` tori in
the side-`2n` torus; `1/1000`, `250`, `1/4` the constants of `DoublingSharp`.
-/

namespace MassGap.DoublingWilsonG

open MeasureTheory Real MassGap MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.KernelPower MassGap.DoublingRecursion MassGap.SlabKernelOperator MassGap.DoublingWilson
  MassGap.GaugeGroup

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- The corner function. -/
noncomputable def xWG (n : ℕ) (β : ℝ) (v : Pt) : ℝ := Real.log (ZRG G (ext n v) β)

/-- The trace sequence of the transverse transfer kernel. -/
noncomputable def FG (β : ℝ) (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (m : ℕ) : ℝ :=
  traceSeq (hSG G μ T) (kTG G μ T β) m

variable {G} {β : ℝ} (hβ : 0 ≤ β)

include hβ in
theorem K_posG (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) :
    0 < ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
      (hSG G μ T) (hSG G μ T)‖ :=
  norm_pos_iff.mpr (kernelCLM_ne_zero _ _ _ _ _ _ _ (RectTransfer.kTmin_pos β) (kTG_lower hβ))

include hβ in
/-- The four trace facts for the transverse transfer kernel, at every even `m = 2j ≥ 2`. -/
theorem factsG (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (j : ℕ) (hj : 1 ≤ j) :
    ∃ lam s : ℝ, DoublingPower.PowerFacts (FG G β μ T) lam s (2 * j) := by
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hSG G μ T) (continuous_kTG β) zero_le_one (abs_kTG_le hβ)
      (kTG_symm β) (K_posG hβ μ T)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_posG (G := G) hβ μ T]
  exact ⟨|c|, _, powerFacts (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
    (kTG_symm β) hφm hφb hφ1 heig hc hc0 j hj⟩

variable {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hβ hn he in
theorem xWG_eq (v : Pt) (μ : Fin 4) :
    xWG G n β v = Real.log (FG G β μ (tr (ext n v) μ) (ext n v μ)) := by
  obtain ⟨n', rfl⟩ := he
  have hj : 1 ≤ 2 ^ (v μ) * n' := by
    have : 1 ≤ 2 ^ (v μ) := Nat.one_le_two_pow; nlinarith
  unfold xWG FG
  rw [ZRG_eq_traceSeq (μ := μ) hβ (2 ^ (v μ) * n') hj (by simp only [ext]; ring)]

include hβ hn he in
/-- `ZRG` at every corner, in every direction, is realised by the four trace facts. -/
theorem factRepG : DoublingPower.FactRep (xWG G n β) := by
  intro μ v
  obtain ⟨n', rfl⟩ := he
  set j := 2 ^ (v μ) * n' with hjdef
  have hj : 1 ≤ j := by
    have : 1 ≤ 2 ^ (v μ) := Nat.one_le_two_pow; rw [hjdef]; nlinarith
  have hm : ext (n' + n') v μ = 2 * j := by simp only [ext, hjdef]; ring
  obtain ⟨lam, s, hf⟩ := factsG (G := G) hβ μ (tr (ext (n' + n') v) μ) j hj
  refine ⟨FG G β μ (tr (ext (n' + n') v) μ), lam, s, 2 * j, hf, ?_, ?_, ?_⟩
  · rw [xWG_eq hβ hn ⟨n', rfl⟩ v μ, hm]
  · rw [xWG_eq hβ hn ⟨n', rfl⟩ (v + E μ) μ, tr_ext_add, ext_add_self, hm]
  · rw [xWG_eq hβ hn ⟨n', rfl⟩ (v + E μ + E μ) μ, tr_ext_add, tr_ext_add, ext_add_self,
      ext_add_self, hm]

include hβ hn he in
/-- The doubling hypothesis `Positive` for the Wilson partition function of `G`. -/
theorem positiveG : Positive (xWG G n β) :=
  DoublingPower.positive_of_facts (factRepG hβ hn he)

variable (G) in
/-- The corner function at `corner 0` is the doubling defect of `TorusDoubling`. -/
theorem Δ_corner0G (n : ℕ) (β : ℝ) :
    Δ (xWG G n β) (corner 0) = TorusDoubling.defectWG G 4 (wilsonDensityG G) β n := by
  unfold Δ xWG TorusDoubling.defectWG
  rw [corner0, corner1, ← ZT_four_eqG, ← ZT_four_eqG]
  norm_num

variable (G) in
/-- The corner function at the diagonal corner `k𝟙` is the defect at side `2ᵏ n`. -/
theorem Δ_cornerG (n k : ℕ) (β : ℝ) :
    Δ (xWG G n β) (corner k) = TorusDoubling.defectWG G 4 (wilsonDensityG G) β (2 ^ k * n) := by
  have h1 : ext n (corner k) = fun _ => 2 ^ k * n := by funext i; rfl
  have h2 : ext n (corner k + one) = fun _ => 2 * (2 ^ k * n) := by
    rw [← corner_succ]; funext i
    show 2 ^ (k + 1) * n = 2 * (2 ^ k * n)
    ring
  unfold Δ xWG TorusDoubling.defectWG
  rw [h1, h2, ← ZT_four_eqG, ← ZT_four_eqG]
  norm_num

include hβ hn he in
/-- **The seed climbs the dyadic sides at one coupling.** -/
theorem defectWG_pow_le (h0 : TorusDoubling.defectWG G 4 (wilsonDensityG G) β n ≤ 1 / 1000)
    (k : ℕ) : TorusDoubling.defectWG G 4 (wilsonDensityG G) β (2 ^ k * n) ≤ 1 / 1000 := by
  have hfr := factRepG (G := G) hβ hn he
  have hp := DoublingPower.positive_of_facts hfr
  have hx := DoublingSharp.positiveS_of_facts hfr
  have hΔ : Δ (xWG G n β) (corner 0) ≤ 1 / 1000 := by rw [Δ_corner0G]; exact h0
  have hi := DoublingSharp.iterate_sharp hx hp (by linarith) k
  have hq : ((1 : ℝ) / 4) ^ (2 ^ k) ≤ 1 / 4 := by
    have := pow_le_pow_of_le_one (a := (1 : ℝ) / 4) (by norm_num) (by norm_num)
      (Nat.one_le_two_pow (n := k))
    simpa using this
  rw [← Δ_cornerG]
  linarith

end MassGap.DoublingWilsonG

#print axioms MassGap.DoublingWilsonG.factRepG
#print axioms MassGap.DoublingWilsonG.positiveG
#print axioms MassGap.DoublingWilsonG.Δ_corner0G
#print axioms MassGap.DoublingWilsonG.defectWG_pow_le
