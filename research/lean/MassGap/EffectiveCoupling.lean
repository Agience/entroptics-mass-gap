import Mathlib
import MassGap.DeltaLengthTower

/-!
# MassGap.EffectiveCoupling — the doubling defect as a coupling: its β-derivative, the rigidity of a
doubling fixed point, and a trapped orbit of the doubling kinematics

Read `g_b(β) = defectW N β (2ᵇ)` as the effective coupling of the blocked theory at side `2ᵇ`. The sharp
seed `g_b ≤ 1/1000` is the basin of the trivial fixed point (`DeltaLengthTower.seedPow_mono`), (B₂) says
`g_b > 1/1000` on every fixed side at arbitrarily large `β`.

* `hasDerivAt_logZR`: `d/dβ log ZR(L) = −⟨S⟩_L`, the mean Wilson action on the torus `L`
  (`meanAction`). The trace-anomaly reading of the free energy, at finite volume.
* `hasDerivAt_defectW`: `d/dβ defectW N β n = ⟨S⟩_{2n} − 16 ⟨S⟩_n`. The β-derivative of the effective
  coupling is the finite-size part of the mean action: the bulk part cancels, as in the defect itself.
* **Rigidity of a doubling fixed point.** `doublingFixed_meanAction`: if the defect at side `n` equals
  the defect at side `2n` on a neighbourhood of `β₀`, then
  `⟨S⟩_{2n} − 16⟨S⟩_n = ⟨S⟩_{4n} − 16⟨S⟩_{2n}` at `β₀`. `meanAction_run`: a scale-free defect on every
  dyadic side from `2^{b₀}` on, near `β₀`, makes `⟨S⟩_{2^{b+1}} − 16 ⟨S⟩_{2^b}` one constant `κ` for every
  `b ≥ b₀`. In per-plaquette terms (`16` plaquettes of side `n` per plaquette of side `2n`) the mean
  action density is `e* + c·16^{−b}`: an exact `L^{−4}` finite-size law, with no running.
* **A trapped orbit of the kinematics.** `trapped_family`: a family of corner functions with every one-
  direction doubling realised by trace facts (`DoublingPower.FactRep`, the only input of the seed climb
  and of `seedPow_mono`), continuous in `β`, seeded at every corner at `β = 0`, and with
  `Δ = 15 log 2` at every corner for `β ≥ 1`. So no consequence of `FactRep`, continuity in `β`, the seed
  at zero coupling and (B₂) together gives the frequent seed. It is the two-level model `1 + r^{vol}`
  with `r` the clamp of `β` to `[0, 1]`; at `r = 1` the two levels are exactly degenerate, the 4D Z₂
  deconfined control's flux degeneracy.

DERIVED (module-wide): `16 = 2⁴` the copies of the side-`n` torus in the side-`2n` torus; `2` the
doubling; `1/1000` the sharp seed; `15 = 16 − 1`; `1` the clamp's upper end, where `r = 1`; `0` the
coupling at which the seed is proved.
-/

noncomputable section

namespace MassGap.EffectiveCoupling

open Real Filter Topology MassGap MassGap.CompactGauge MassGap.DoublingRecursion
  MassGap.DoublingPower MassGap.ZoomSelfScale

variable {N : ℕ}

/-! ## 1. The β-derivative of the effective coupling -/

/-- The mean Wilson action `⟨S⟩` on the rectangular torus `L` at coupling `β`. -/
def meanAction (N : ℕ) (L : Fin 4 → ℕ) (β : ℝ) : ℝ :=
  (RectWilson.sysR L N).expect (probHaar (MassGap.SUN.SU N)) β (RectWilson.sysR L N).action

/-- `d/dβ ZR(L) = −∫ S e^{−βS}`. -/
theorem hasDerivAt_ZR (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) :
    HasDerivAt (fun x => RectWilson.ZR L N x)
      (-((RectWilson.sysR L N).corrNum (probHaar (MassGap.SUN.SU N)) β
        (RectWilson.sysR L N).action)) β := by
  have h := WilsonAnalytic.wilsonSystem_corrNum_hasDerivAt hN (RectWilson.rbd L) β
    (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by norm_num)
  rw [WilsonAnalytic.wilsonSystem_integral_deriv (RectWilson.rbd L) β (fun _ => (1 : ℝ))] at h
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  · simp only [one_mul]
    rfl
  · simp only [RectWilson.ZR, RectWilson.sysR, LatticeGauge.System.corrNum,
      LatticeGauge.System.partition, one_mul]
    rfl

/-- **`d/dβ log ZR(L) = −⟨S⟩_L`.** -/
theorem hasDerivAt_logZR (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) :
    HasDerivAt (fun x => Real.log (RectWilson.ZR L N x)) (-meanAction N L β) β := by
  have h := (hasDerivAt_ZR hN L β).log (DeltaLengthTower.ZR_pos hN L β).ne'
  refine h.congr_deriv ?_
  simp only [meanAction, LatticeGauge.System.expect, neg_div]
  rfl

/-- **The β-derivative of the doubling defect**: `⟨S⟩_{2n} − 16 ⟨S⟩_n`. -/
theorem hasDerivAt_defectW (hN : N ≠ 0) (n : ℕ) (β : ℝ) :
    HasDerivAt (fun x => defectW N x n)
      (meanAction N (fun _ => 2 * n) β - 16 * meanAction N (fun _ => n) β) β := by
  have h1 := hasDerivAt_logZR hN (fun _ => n) β
  have h2 := hasDerivAt_logZR hN (fun _ => 2 * n) β
  have e : (fun x => defectW N x n) = fun x =>
      16 * Real.log (RectWilson.ZR (fun _ => n) N x)
        - Real.log (RectWilson.ZR (fun _ => 2 * n) N x) := by
    funext x; rfl
  rw [e]
  exact ((h1.const_mul 16).sub h2).congr_deriv (by ring)

/-! ## 2. Rigidity of a doubling fixed point -/

/-- **A doubling fixed point near `β₀` fixes the finite-size mean action.** If the defect at side `n`
equals the defect at side `2n` on a neighbourhood of `β₀`, their β-derivatives agree there. -/
theorem doublingFixed_meanAction (hN : N ≠ 0) {n : ℕ} {β₀ : ℝ}
    (h : (fun β => defectW N β n) =ᶠ[𝓝 β₀] fun β => defectW N β (2 * n)) :
    meanAction N (fun _ => 2 * n) β₀ - 16 * meanAction N (fun _ => n) β₀
      = meanAction N (fun _ => 2 * (2 * n)) β₀ - 16 * meanAction N (fun _ => 2 * n) β₀ :=
  (hasDerivAt_defectW hN n β₀).unique ((hasDerivAt_defectW hN (2 * n) β₀).congr_of_eventuallyEq h)

/-- The fixed-point identity at dyadic sides. -/
theorem meanAction_step (hN : N ≠ 0) {b : ℕ} {β₀ : ℝ}
    (h : (fun β => defectW N β (2 ^ b)) =ᶠ[𝓝 β₀] fun β => defectW N β (2 ^ (b + 1))) :
    meanAction N (fun _ => 2 ^ (b + 1)) β₀ - 16 * meanAction N (fun _ => 2 ^ b) β₀
      = meanAction N (fun _ => 2 ^ (b + 2)) β₀ - 16 * meanAction N (fun _ => 2 ^ (b + 1)) β₀ := by
  have e1 : (2 : ℕ) ^ (b + 1) = 2 * 2 ^ b := by ring
  have e2 : (2 : ℕ) ^ (b + 2) = 2 * (2 * 2 ^ b) := by ring
  rw [e1] at h ⊢
  rw [e2]
  exact doublingFixed_meanAction hN h

/-- **A scale-free run of the defect gives one finite-size constant.** If, near `β₀`, the defect at
every dyadic side `2ᵇ`, `b ≥ b₀`, equals the defect at `2ᵇ⁺¹`, then `⟨S⟩_{2^{b+1}} − 16 ⟨S⟩_{2^b}` is the
same number at every `b ≥ b₀`. -/
theorem meanAction_run (hN : N ≠ 0) {b₀ : ℕ} {β₀ : ℝ}
    (h : ∀ b, b₀ ≤ b →
      (fun β => defectW N β (2 ^ b)) =ᶠ[𝓝 β₀] fun β => defectW N β (2 ^ (b + 1))) :
    ∀ j : ℕ, meanAction N (fun _ => 2 ^ (b₀ + j + 1)) β₀ - 16 * meanAction N (fun _ => 2 ^ (b₀ + j)) β₀
      = meanAction N (fun _ => 2 ^ (b₀ + 1)) β₀ - 16 * meanAction N (fun _ => 2 ^ b₀) β₀ := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hs := meanAction_step hN (h (b₀ + j) (by omega))
    have e : b₀ + (j + 1) = b₀ + j + 1 := by omega
    have e' : b₀ + (j + 1) + 1 = b₀ + j + 2 := by omega
    rw [e', e]
    linarith

/-! ## 3. A trapped orbit of the doubling kinematics -/

/-- The two-level corner function: `log (1 + r^{2^{Σ v}})`, the logarithm of a trace with top weight
`1` and one excited level whose relative weight is `r` per unit of the dyadic volume `2^{Σ v}`. -/
def twoLevel (r : ℝ) (v : Pt) : ℝ := Real.log (1 + r ^ (2 ^ (∑ i, v i)))

theorem sum_add_E (v : Pt) (μ : Fin 4) : ∑ i, (v + E μ) i = ∑ i, v i + 1 := by
  rw [show (∑ i, (v + E μ) i) = ∑ i, (v i + E μ i) from rfl, Finset.sum_add_distrib]
  congr 1
  fin_cases μ <;> simp [E, Fin.sum_univ_four]

/-- **The two-level corner function has trace facts in every direction**, at every `r ∈ [0, 1]`. -/
theorem factRep_twoLevel {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : FactRep (twoLevel r) := by
  intro μ v
  refine ⟨fun j => 1 + r ^ (j * 2 ^ (∑ i, v i)), 1, r ^ (2 ^ (∑ i, v i)), 1,
    ⟨one_pos, pow_nonneg h0 _, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp
  · simp only [one_pow, one_mul, mul_one]
    have := pow_le_pow_of_le_one h0 h1
      (show 2 ^ (∑ i, v i) ≤ 2 * 2 ^ (∑ i, v i) by omega)
    linarith
  · have e : r ^ ((2 * 1) * 2 ^ (∑ i, v i)) = (r ^ (2 ^ (∑ i, v i))) ^ 2 := by
      rw [← pow_mul]; congr 1; ring
    simp only [one_pow, one_mul]
    rw [e]
  · have := pow_nonneg h0 ((2 * 1) * 2 ^ (∑ i, v i))
    simp only [one_pow]
    linarith
  · have := pow_nonneg h0 ((2 * (2 * 1)) * 2 ^ (∑ i, v i))
    simp only [one_pow]
    linarith
  · simp [twoLevel]
  · simp only [twoLevel]
    rw [sum_add_E, show 2 ^ (∑ i, v i + 1) = (2 * 1) * 2 ^ (∑ i, v i) by ring]
  · simp only [twoLevel]
    rw [sum_add_E, sum_add_E,
      show 2 ^ (∑ i, v i + 1 + 1) = (2 * (2 * 1)) * 2 ^ (∑ i, v i) by ring]

theorem twoLevel_zero (v : Pt) : twoLevel 0 v = 0 := by
  simp [twoLevel]

theorem twoLevel_one (v : Pt) : twoLevel 1 v = Real.log 2 := by
  simp only [twoLevel, one_pow]
  norm_num

/-- **A trapped orbit.** A family of corner functions with trace facts in every direction at every
coupling, continuous in the coupling, seeded at every corner at `β = 0`, and with the defect
`15 log 2` at every corner for `β ≥ 1`: no seed at any large coupling. -/
theorem trapped_family :
    ∃ X : ℝ → Pt → ℝ, (∀ β, FactRep (X β)) ∧ (∀ v, Continuous fun β => X β v) ∧
      (∀ k, Δ (X 0) (corner k) = 0) ∧
      (∀ β, 1 ≤ β → ∀ k, Δ (X β) (corner k) = 15 * Real.log 2) ∧
      ¬ ∃ᶠ β in atTop, ∃ k, Δ (X β) (corner k) ≤ 1 / 1000 := by
  refine ⟨fun β => twoLevel (max 0 (min β 1)), fun β => ?_, fun v => ?_, fun k => ?_,
    fun β hβ k => ?_, ?_⟩
  · exact factRep_twoLevel (le_max_left _ _) (max_le zero_le_one (min_le_right _ _))
  · refine Continuous.log ?_ fun β => ?_
    · exact continuous_const.add
        ((continuous_const.max (continuous_id.min continuous_const)).pow _)
    · have := pow_nonneg (le_max_left (0 : ℝ) (min β 1)) (2 ^ (∑ i, v i))
      exact (by linarith : (0 : ℝ) < 1 + max 0 (min β 1) ^ (2 ^ (∑ i, v i))).ne'
  · have e : max (0 : ℝ) (min 0 1) = 0 := by norm_num
    simp only [Δ, e, twoLevel_zero]
    ring
  · have e : max (0 : ℝ) (min β 1) = 1 := by
      rw [min_eq_right hβ]; norm_num
    simp only [Δ, e, twoLevel_one]
    ring
  · rw [not_frequently]
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
    rintro ⟨k, hk⟩
    have e : max (0 : ℝ) (min β 1) = 1 := by
      rw [min_eq_right hβ]; norm_num
    have h15 : Δ (fun v => twoLevel (max 0 (min β 1)) v) (corner k) = 15 * Real.log 2 := by
      simp only [Δ, e, twoLevel_one]
      ring
    have hl := Real.log_two_gt_d9
    have hk' : Δ (fun v => twoLevel (max 0 (min β 1)) v) (corner k) ≤ 1 / 1000 := hk
    linarith

end MassGap.EffectiveCoupling

#print axioms MassGap.EffectiveCoupling.hasDerivAt_ZR
#print axioms MassGap.EffectiveCoupling.hasDerivAt_logZR
#print axioms MassGap.EffectiveCoupling.hasDerivAt_defectW
#print axioms MassGap.EffectiveCoupling.doublingFixed_meanAction
#print axioms MassGap.EffectiveCoupling.meanAction_step
#print axioms MassGap.EffectiveCoupling.meanAction_run
#print axioms MassGap.EffectiveCoupling.factRep_twoLevel
#print axioms MassGap.EffectiveCoupling.trapped_family
