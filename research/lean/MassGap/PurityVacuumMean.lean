import Mathlib
import MassGap.PurityHaarProjection
import MassGap.PurityCharacter
import MassGap.GaugeInstances

/-!
# MassGap.PurityVacuumMean — the spatial vacuum mean, Appendix C of the purity paper

Appendix C of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
uses `∫ V_s dU = 0` for `SU(d)` in its defining representation, from the Haar integral of one link
of each plaquette, and `max V_s = b|P_s|`. On one slice `V_s = (b/2)(n − sp)` with
`n = nPl μ T = (c² − c)|TT|` the number of ordered pairs of distinct transverse directions times the
number of sites (`c` transverse directions), so `|P_s| = n/2` (`sp` lists each plaquette in both
orientations, equal by `GaugeGroup.wilsonDensityG_inv`, and equal directions give `0`), and
`V_s = (b/d) Σ_{p ∈ P_s} Re Tr U_p`. `nPl_eq`: `n = 6|TT|`.

* `integral_spTG`: with every transverse period at least `2`, `∫ sp dV = n (1 − q/d)` for every
  `GaugeGroup` (`PurityHaarProjection.integral_wilson_link` on the link `V(ν, y)`).
* `fixedRank_SU`: `q = 0` for `SU(N)`, `N ≥ 2`, in the defining representation (the centre scalar
  `e^{2πi/N} · 1` fixes no nonzero vector).
* `integral_vacuum_SU`, `vacuum_ge_one_SU`: `∫ V_s dV = 0` and `J_s = ∫ e^{−V_s} dV ≥ 1` (Jensen).
* `spTG_one`, `vacuum_le_max`, `vacuum_one`: `V_s ≤ b|P_s|` at `b ≥ 0`, with equality at `V = 1`.

DERIVED (module-wide): `2` the smallest period at which the step `tsh` moves a site, and the
factor `2` of the two orientations in which `sp` lists each plaquette.
-/

namespace MassGap.PurityVacuumMean

open MeasureTheory MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectWilsonG
  MassGap.RectTransferG MassGap.GaugeGroup MassGap.PurityHaarProjection

open scoped Matrix

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-! ## The spatial action of one slice -/

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

variable (μ T) in
/-- `n = (c² − c)|TT|`: ordered pairs of distinct transverse directions, times sites. -/
noncomputable def nPl : ℝ :=
  ((Fintype.card {j : Fin 4 // j ≠ μ} : ℝ) ^ 2 - Fintype.card {j : Fin 4 // j ≠ μ}) *
    Fintype.card (TT μ T)

/-- `n = 6|TT|`: three transverse directions. -/
theorem nPl_eq : nPl μ T = 6 * Fintype.card (TT μ T) := by
  have h : Fintype.card {j : Fin 4 // j ≠ μ} = 3 := by
    fin_cases μ <;> decide
  unfold nPl
  rw [h]
  norm_num

/-- With every transverse period at least `2`, `∫ sp dV = n (1 − q/d)`. -/
theorem integral_spTG (hT : ∀ ν, 2 ≤ T ν) :
    ∫ V, spTG G μ T V ∂(hSG G μ T) = nPl μ T * (1 - (fixedRank G : ℝ) / dim G) := by
  set K : ℝ := 1 - (fixedRank G : ℝ) / dim G
  have hc : ∀ (ν ν' : {j : Fin 4 // j ≠ μ}) (y : TT μ T), Continuous fun V : SpT μ T → G =>
      wilsonDensityG G (V (ν, y) * V (ν', tsh μ T ν y) * (V (ν, tsh μ T ν' y))⁻¹ *
        (V (ν', y))⁻¹) := fun ν ν' y =>
    continuous_wilsonDensityG.comp (((((continuous_apply (ν, y)).mul
      (continuous_apply (ν', tsh μ T ν y))).mul (continuous_apply (ν, tsh μ T ν' y)).inv).mul
      (continuous_apply (ν', y)).inv))
  have hterm : ∀ (ν ν' : {j : Fin 4 // j ≠ μ}) (y : TT μ T), ∫ V,
      wilsonDensityG G (V (ν, y) * V (ν', tsh μ T ν y) * (V (ν, tsh μ T ν' y))⁻¹ *
        (V (ν', y))⁻¹) ∂(hSG G μ T) = K - if ν = ν' then K else 0 := fun ν ν' y => by
    by_cases hne : ν = ν'
    · subst hne
      simp only [mul_inv_cancel_right, mul_inv_cancel, wilsonDensityG_one, integral_zero,
        ↓reduceIte, sub_self]
    · rw [if_neg hne, sub_zero]
      have e : (fun V : SpT μ T → G => wilsonDensityG G (V (ν, y) * V (ν', tsh μ T ν y) *
          (V (ν, tsh μ T ν' y))⁻¹ * (V (ν', y))⁻¹)) = fun V => wilsonDensityG G (V (ν, y) *
          (V (ν', tsh μ T ν y) * ((V (ν, tsh μ T ν' y))⁻¹ * (V (ν', y))⁻¹))) :=
        funext fun V => by simp only [mul_assoc]
      have h1 : ((ν', tsh μ T ν y) : SpT μ T) ≠ (ν, y) := fun h => hne (congrArg Prod.fst h).symm
      have h2 : ((ν, tsh μ T ν' y) : SpT μ T) ≠ (ν, y) := fun h =>
        tsh_ne_self (hT ν') y (congrArg Prod.snd h)
      have h3 : ((ν', y) : SpT μ T) ≠ (ν, y) := fun h => hne (congrArg Prod.fst h).symm
      rw [e]
      exact integral_wilson_link (ν, y)
        ((continuous_apply _).mul ((continuous_apply _).inv.mul (continuous_apply _).inv))
        fun A B h => by rw [h _ h1, h _ h2, h _ h3]
  calc ∫ V, spTG G μ T V ∂(hSG G μ T)
      = ∑ ν, ∑ ν', ∑ _y : TT μ T, (K - if ν = ν' then K else 0) := by
        unfold spTG
        rw [integral_finsetSum _ fun ν _ => integrable_finsetSum _ fun ν' _ =>
          integrable_finsetSum _ fun y _ => integrable_contX (hc ν ν' y)]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [integral_finsetSum _ fun ν' _ =>
          integrable_finsetSum _ fun y _ => integrable_contX (hc ν ν' y)]
        refine Finset.sum_congr rfl fun ν' _ => ?_
        rw [integral_finsetSum _ fun y _ => integrable_contX (hc ν ν' y)]
        exact Finset.sum_congr rfl fun y _ => hterm ν ν' y
    _ = nPl μ T * K := by
        simp only [Finset.sum_sub_distrib, Finset.sum_const, smul_ite, smul_zero,
          Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.card_univ, nsmul_eq_mul, nPl]
        ring

/-! ## `SU(N)` in the defining representation -/

/-- `q = 0` for `SU(N)`, `N ≥ 2`: the centre scalar `e^{2πi/N} · 1` fixes no nonzero vector. -/
theorem fixedRank_SU {N : ℕ} [NeZero N] (hN : 2 ≤ N) : fixedRank (SUN.SU N) = 0 := by
  have hp := Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hω1 : Complex.exp (2 * Real.pi * Complex.I / N) ≠ 1 := hp.ne_one (by omega)
  have hbot : fixedSub (SUN.SU N) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    have h : Matrix.diagonal (fun _ : Fin N => Complex.exp (2 * Real.pi * Complex.I / N)) *ᵥ v =
        v := mem_fixedSub.1 hv (GaugeInstances.centreElt (NeZero.ne N) hp.pow_eq_one)
    funext i
    have hi := congrFun h i
    rw [Matrix.mulVec_diagonal] at hi
    have h0 : (Complex.exp (2 * Real.pi * Complex.I / N) - 1) * v i = 0 := by
      rw [sub_mul, hi, one_mul, sub_self]
    exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hω1)
  unfold fixedRank
  rw [hbot, finrank_bot]

theorem integrable_spTG : Integrable (fun V => spTG G μ T V) (hSG G μ T) :=
  integrable_contX (continuous_spG continuous_id)

/-- `∫ V_s dV = 0` for `SU(N)`, `N ≥ 2`, with `V_s = (b/2)(n − sp)`. -/
theorem integral_vacuum_SU {N : ℕ} [NeZero N] (hN : 2 ≤ N) (hT : ∀ ν, 2 ≤ T ν) (b : ℝ) :
    ∫ V, b / 2 * (nPl μ T - spTG (SUN.SU N) μ T V) ∂(hSG (SUN.SU N) μ T) = 0 := by
  rw [integral_const_mul, integral_sub (integrable_const _) integrable_spTG, integral_spTG hT,
    fixedRank_SU hN]
  simp only [integral_const, probReal_univ, one_smul, Nat.cast_zero, zero_div, sub_zero, mul_one,
    sub_self, mul_zero]

/-- `J_s = ∫ e^{−V_s} dV ≥ 1` for `SU(N)`, `N ≥ 2` (Jensen). -/
theorem vacuum_ge_one_SU {N : ℕ} [NeZero N] (hN : 2 ≤ N) (hT : ∀ ν, 2 ≤ T ν) (b : ℝ) :
    1 ≤ ∫ V, Real.exp (-(b / 2 * (nPl μ T - spTG (SUN.SU N) μ T V))) ∂(hSG (SUN.SU N) μ T) := by
  have hc : Continuous fun V : SpT μ T → SUN.SU N => b / 2 * (nPl μ T - spTG (SUN.SU N) μ T V) :=
    continuous_const.mul (continuous_const.sub (continuous_spG continuous_id))
  exact PurityCharacter.vacuum_ge_one (integrable_contX hc)
    (integrable_contX (Real.continuous_exp.comp hc.neg)) (integral_vacuum_SU hN hT b)

/-- `sp(1) = 0`. -/
theorem spTG_one : spTG G μ T 1 = 0 := by
  simp [spTG, wilsonDensityG_one]

/-- `V_s ≤ b|P_s| = (b/2) n` at `b ≥ 0`. -/
theorem vacuum_le_max {b : ℝ} (hb : 0 ≤ b) (V : SpT μ T → G) :
    b / 2 * (nPl μ T - spTG G μ T V) ≤ b / 2 * nPl μ T :=
  mul_le_mul_of_nonneg_left (sub_le_self _ (spG_nonneg V)) (by positivity)

/-- `V_s(1) = b|P_s|`. -/
theorem vacuum_one (b : ℝ) : b / 2 * (nPl μ T - spTG G μ T 1) = b / 2 * nPl μ T := by
  rw [spTG_one, sub_zero]

end MassGap.PurityVacuumMean

#print axioms MassGap.PurityVacuumMean.nPl_eq
#print axioms MassGap.PurityVacuumMean.integral_spTG
#print axioms MassGap.PurityVacuumMean.fixedRank_SU
#print axioms MassGap.PurityVacuumMean.integrable_spTG
#print axioms MassGap.PurityVacuumMean.integral_vacuum_SU
#print axioms MassGap.PurityVacuumMean.vacuum_ge_one_SU
#print axioms MassGap.PurityVacuumMean.spTG_one
#print axioms MassGap.PurityVacuumMean.vacuum_le_max
#print axioms MassGap.PurityVacuumMean.vacuum_one
