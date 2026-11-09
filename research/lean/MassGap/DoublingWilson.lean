import Mathlib
import MassGap.RectTransfer
import MassGap.KernelEigen
import MassGap.KernelGap
import MassGap.DoublingPower

/-!
# MassGap.DoublingWilson — the four-dimensional doubling test for Wilson `SU(N)`

`xW N n β v = log ZR (ext n v) N β`, the logarithm of the Wilson partition function on the 4-torus
with sides `2^{v_μ} n` (`RectWilson.ZR`, the tree's convention: ordered plaquette pairs, product Haar).

* `factRep` — in every direction `μ` and at every corner `v`, `ZR` is the trace sequence
  `KernelPower.traceSeq` of the symmetric, continuous, strictly positive transfer kernel
  `RectTransfer.kT` of the transverse slice (`RectTransfer.ZR_eq_traceSeq`), which has a top
  eigenfunction (`KernelEigen.exists_eigen`), so the four trace facts hold
  (`KernelPower.powerFacts`).
* `positive` — `DoublingRecursion.Positive (xW N n β)`: the hypothesis of `DoublingRecursion.rec`
  and `iterate`, now proved for Wilson `SU(N)`, `N ≠ 0`, `β ≥ 0`, `n` even, `n ≥ 2`.
* `wilson_gap` — if `16 log ZR(n⁴) − log ZR((2n)⁴) ≤ 1/7480`, then on every torus of side `2^k n`
  the transfer operator `K` of the gauge-invariant slice (the axis links integrated out) has a unit
  eigenvector `ψ` at `|c| = ‖K‖` and `‖Kⁿ f‖ ≤ ½ ‖K‖ⁿ ‖f‖` for every `f ⊥ ψ`: the second
  transfer eigenvalue is at most `2^{−1/n}` times the first, uniformly in `k`.
-/

namespace MassGap.DoublingWilson

open MeasureTheory Real MassGap MassGap.RectWilson MassGap.RectTransfer MassGap.KernelPower
  MassGap.DoublingRecursion MassGap.SlabKernelOperator

/-- Extents at corner `v`. -/
def ext (n : ℕ) (v : Pt) : Fin 4 → ℕ := fun i => 2 ^ (v i) * n

/-- The corner function. -/
noncomputable def xW (N n : ℕ) (β : ℝ) (v : Pt) : ℝ := Real.log (ZR (ext n v) N β)

theorem E_apply (μ i : Fin 4) : E μ i = if μ = i then 1 else 0 := by
  fin_cases μ <;> fin_cases i <;> rfl

theorem tr_ext_add (n : ℕ) (v : Pt) (μ : Fin 4) :
    tr (ext n (v + E μ)) μ = tr (ext n v) μ := by
  funext j
  simp only [tr, ext, Pi.add_apply, E_apply, if_neg (Ne.symm j.2), add_zero]

theorem ext_add_self (n : ℕ) (v : Pt) (μ : Fin 4) : ext n (v + E μ) μ = 2 * ext n v μ := by
  simp only [ext, Pi.add_apply, E_apply, if_true, pow_add, pow_one]; ring

/-- The trace sequence of the transverse transfer kernel. -/
noncomputable def F (N : ℕ) (β : ℝ) (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (m : ℕ) : ℝ :=
  traceSeq (hS μ T N) (kT μ T N β) m

variable {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)

include hN hβ in
theorem K_pos (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) :
    0 < ‖kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
      (hS μ T N) (hS μ T N)‖ :=
  norm_pos_iff.mpr (kernelCLM_ne_zero _ _ _ _ _ _ _ (kTmin_pos β) (kT_lower hN hβ))

include hN hβ in
/-- The four trace facts for the transverse transfer kernel, at every even `m = 2j ≥ 2`. -/
theorem facts (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (j : ℕ) (hj : 1 ≤ j) :
    ∃ lam s : ℝ, DoublingPower.PowerFacts (F N β μ T) lam s (2 * j) := by
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hS μ T N) (continuous_kT β) zero_le_one (abs_kT_le hN hβ)
      (kT_symm β) (K_pos hN hβ μ T)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_pos hN hβ μ T]
  exact ⟨|c|, _, powerFacts (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
    (kT_symm β) hφm hφb hφ1 heig hc hc0 j hj⟩

variable {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hN hβ hn he in
theorem xW_eq (v : Pt) (μ : Fin 4) :
    xW N n β v = Real.log (F N β μ (tr (ext n v) μ) (ext n v μ)) := by
  obtain ⟨n', rfl⟩ := he
  have hj : 1 ≤ 2 ^ (v μ) * n' := by
    have : 1 ≤ 2 ^ (v μ) := Nat.one_le_two_pow; nlinarith
  unfold xW F
  rw [ZR_eq_traceSeq (μ := μ) hN hβ (2 ^ (v μ) * n') hj (by simp only [ext]; ring)]

include hN hβ hn he in
/-- `ZR` at every corner, in every direction, is realised by the four trace facts. -/
theorem factRep : DoublingPower.FactRep (xW N n β) := by
  intro μ v
  obtain ⟨n', rfl⟩ := he
  set j := 2 ^ (v μ) * n' with hjdef
  have hj : 1 ≤ j := by
    have : 1 ≤ 2 ^ (v μ) := Nat.one_le_two_pow; rw [hjdef]; nlinarith
  have hm : ext (n' + n') v μ = 2 * j := by simp only [ext, hjdef]; ring
  obtain ⟨lam, s, hf⟩ := facts hN hβ μ (tr (ext (n' + n') v) μ) j hj
  refine ⟨F N β μ (tr (ext (n' + n') v) μ), lam, s, 2 * j, hf, ?_, ?_, ?_⟩
  · rw [xW_eq hN hβ hn ⟨n', rfl⟩ v μ, hm]
  · rw [xW_eq hN hβ hn ⟨n', rfl⟩ (v + E μ) μ, tr_ext_add, ext_add_self, hm]
  · rw [xW_eq hN hβ hn ⟨n', rfl⟩ (v + E μ + E μ) μ, tr_ext_add, tr_ext_add, ext_add_self,
      ext_add_self, hm]

include hN hβ hn he in
/-- The doubling hypothesis `Positive`, proved for the Wilson `SU(N)` partition function. -/
theorem positive : Positive (xW N n β) :=
  DoublingPower.positive_of_facts (factRep hN hβ hn he)

theorem corner0 (n : ℕ) : ext n (corner 0) = fun _ => n := by
  funext i; simp [ext, corner]

theorem corner1 (n : ℕ) : ext n (corner 0 + one) = fun _ => 2 * n := by
  funext i
  have : (corner 0 + one) i = 1 := by fin_cases i <;> rfl
  simp [ext, this]

theorem Δ_corner0 (n : ℕ) :
    Δ (xW N n β) (corner 0)
      = 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) := by
  unfold Δ xW; rw [corner0, corner1]

include hN hβ hn he in
/-- **The four-dimensional doubling test for Wilson `SU(N)`.** If one torus of side `n` has
`16 log Z(n⁴) − log Z((2n)⁴) ≤ 1/7480`, then for every `k`, on the torus of side `2^k n`, the
transfer operator `K` in direction `0` (on `L²` of the spatial links of one slice, axis links
integrated out) has a unit eigenvector `ψ` with eigenvalue of modulus `‖K‖`, and every `f ⊥ ψ`
satisfies `‖Kⁿ f‖ ≤ ½ ‖K‖ⁿ ‖f‖`. -/
theorem wilson_gap
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 7480)
    (k : ℕ) :
    ∃ ψ : Lp ℝ 2 (hS 0 (tr (ext n (corner k)) 0) N), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, |c| = ‖kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N)
          (hS 0 (tr (ext n (corner k)) 0) N)‖ ∧
      kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable zero_le_one
          (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N) (hS 0 (tr (ext n (corner k)) 0) N) ψ
        = c • ψ ∧
      ∀ f : Lp ℝ 2 (hS 0 (tr (ext n (corner k)) 0) N), inner ℝ f ψ = 0 →
        ‖((kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N)
          (hS 0 (tr (ext n (corner k)) 0) N)) ^ n) f‖
          ≤ 1 / 2 * ‖kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable
            zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N)
            (hS 0 (tr (ext n (corner k)) 0) N)‖ ^ n * ‖f‖ := by
  set T := tr (ext n (corner k)) 0
  have hx := positive hN hβ hn he
  have hΔ : Δ (xW N n β) (corner 0) ≤ 1 / 7480 := by rw [Δ_corner0]; exact h0
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hS 0 T N) (continuous_kT β) zero_le_one (abs_kT_le hN hβ)
      (kT_symm β) (K_pos hN hβ 0 T)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_pos hN hβ 0 T]
  obtain ⟨n', hn'⟩ := he
  set j := 2 ^ k * n' with hjdef
  have hj : 1 ≤ j := by
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 1 ≤ n' := by omega
    rw [hjdef]; exact Nat.mul_le_mul h1 h2
  have hpf := powerFacts (μ := hS 0 T N) (continuous_kT β).measurable zero_le_one
    (abs_kT_le hN hβ) (kT_symm β) hφm hφb hφ1 heig hc hc0 j hj
  have hm : ext n (corner k) 0 = 2 * j := by simp only [ext, corner, hjdef, hn']; ring
  have h1 : xW N n β (corner k) = Real.log (F N β 0 T (2 * j)) := by
    rw [xW_eq hN hβ hn ⟨n', hn'⟩ (corner k) 0, hm]
  have h2 : xW N n β (corner k + E 0) = Real.log (F N β 0 T (2 * (2 * j))) := by
    rw [xW_eq hN hβ hn ⟨n', hn'⟩ (corner k + E 0) 0, tr_ext_add, ext_add_self, hm]
  have hexc := DoublingPower.excited_le_corner hx hΔ k hpf h1 h2
  have hidx : 2 ^ k * n / 2 = j := by
    rw [hn', hjdef, show 2 ^ k * (n' + n') = 2 * (2 ^ k * n') by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  refine ⟨KernelGap.vac (μ := hS 0 T N) hφm hφb, KernelGap.norm_vac hφm hφb hφ1, c, hc,
    KernelGap.K_vac _ _ _ hφm hφb heig, fun f hf => ?_⟩
  exact KernelGap.gap_of_excited (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
    (kT_symm β) hφm hφb hφ1 heig hc hc0 k n (by omega) ⟨n', hn'⟩ (by rw [hidx]; exact hexc) f hf

#print axioms positive
#print axioms wilson_gap

end MassGap.DoublingWilson
