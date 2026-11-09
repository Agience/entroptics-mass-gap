import Mathlib
import MassGap.LocalPotential
import MassGap.PairCorrSharp

/-!
# MassGap.LocalPotentialSharp — the potential box with the pair counted by class

`LocalPotential.potBox_localGapG` bounds every pair's defect linearly from one density check at the
largest coupling `4βb` and tilt `12βb`, and sums the row to `36 · (D₀/τ₀) βb`. Pure Wilson reaches the
capstone floor (`PairCorrSharp`) by counting pairs by class instead: a pair sharing one plaquette
(`n2 = 2`, coupling `2β`, tilt `10β`), two (`n2 = 4`, `4β`, `8β`) or none; row sums
`max(18δ₁, 12δ₁ + 3δ₂)`. This module does the same with the local potential: three density checks
(single, double, and the tilt `12βb` at zero coupling), the defect
`e^{mix} (δ_class + 2(e^{mix} − 1))` (`deltaPotS`), row sums `E · max(18δ₁, 12δ₁ + 3δ₂) + 2E²ν`
(`defectMatrix_potS`) and the local gap (`potBox_localGapS`).

Instance (`potBox_localGap_sharp`): `SU(2)`, `β ≤ 1/20` (`β_std ≤ 1/10`, twice the reach of
`LocalPotential.potBox_localGap_wide`), local norm `≤ 1/16`: local gap `213/1000`.
-/

namespace MassGap.LocalPotentialSharp

open MeasureTheory
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.HeatBath (wt_pos)
open MassGap.PairInterface (realFeature)
open MassGap.PairCount (n2 n2_cases n2_symm)
open MassGap.PairFibreDens (nearTilt)
open MassGap.WeightedHeatBath (FibreHyp)
open MassGap.LocalPotential
open MassGap.ObserverBox (DensCheck densFibreBound_of_check)
open MassGap.AdjacentFibre (fibreHyp_mono)
open MassGap.PairCorrSharp (pairDeltaSharp pairDeltaSharp_row)
open MassGap.WeightedTorus (WBoxLocalGap wBoxLocalGap_of_pairCorr wPairCorrAt_of_fibreHyp)

variable {N : ℕ}

/-- The defect of a pair class: `δ₁` at pair count `2`, `δ₂` at `4`, `0` otherwise.

DERIVED: `2`, `4` are the pair counts of one and two shared plaquettes. -/
def cls (δ₁ δ₂ : ℝ) (n : ℕ) : ℝ := if n = 2 then δ₁ else if n = 4 then δ₂ else 0

/-- **The sharp potential defect**: `e^{mix} (δ_class + 2(e^{mix} − 1))` off the diagonal.

DERIVED: `2` is the additive mixing term; `1` is `e⁰`. -/
noncomputable def deltaPotS {M : ℕ} (δ₁ δ₂ : ℝ) (P : LocalPot N M)
    (l m : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  if l = m then 0 else
    Real.exp (P.mix l m) * (cls δ₁ δ₂ (n2 M l m) + 2 * (Real.exp (P.mix l m) - 1))

/-- **The fibre hypothesis by pair class**, from three density checks: single pairs at `(2βb, 10βb)`,
double at `(4βb, 8βb)`, and the tilt `12βb` at zero coupling (constant `0`).

DERIVED: `2` is the rank; `2`, `10`, `4`, `8`, `12` the coupling and tilt counts of the classes;
`0` the lower end of `β`, `ν`, `δ`. -/
theorem fibreHyp_potS {β βb ν E δ₁ δ₂ D₀ s₁ σ₁ s₂ σ₂ s₀ σ₀ : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ βb)
    (hν0 : 0 ≤ ν) (hE : Real.exp ν ≤ E) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (c1 : DensCheck 4 (1 / 8) 0 s₁ σ₁ (2 * βb) (10 * βb) E δ₁)
    (c2 : DensCheck 4 (1 / 8) 0 s₂ σ₂ (4 * βb) (8 * βb) E δ₂)
    (c0 : DensCheck 4 (1 / 8) 0 s₀ σ₀ (2 * βb) (12 * βb) E D₀)
    {M : ℕ} (hM : 1 ≤ M) (P : LocalPot 2 M) (hν : ∀ l, P.norm l ≤ ν)
    {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m) :
    FibreHyp (wtV (N := 2) β P) l m (deltaPotS δ₁ δ₂ P l m) := by
  have h2 : (2 : ℕ) ≠ 0 := by norm_num
  have hpos : ∀ W, 0 ≤ wtV (N := 2) β P W :=
    fun W => mul_nonneg (wt_pos _ _ _).le (Real.exp_pos _).le
  have hbb : 0 < βb := by have := c1.1; linarith
  have hηl := (P.at_le_norm l).trans (hν l)
  have hηm := (P.at_le_norm m).trans (hν m)
  have hex : 0 ≤ Real.exp (P.mix l m) := (Real.exp_pos _).le
  rcases n2_cases hM hlm with h | h | h
  · -- no shared plaquette: constant zero
    have hτ0 : (0 : ℝ) ≤ β * (n2 M l m : ℝ) := by rw [h]; simp
    have hττ : β * (n2 M l m : ℝ) ≤ 2 * βb := by rw [h]; simp; linarith
    have hB := densFibreBound_of_check h2 MassGap.HaarMomentsSU2.haarConsts_su2 hν0 hE c0 hτ0 hττ
    have H := fibreHyp_localPot h2 hβ0 hM P hlm (c := β * (n2 M l m : ℝ) / (2 * βb) * D₀)
      (by rw [h]; simp) (by rw [h]; push_cast; linarith) hηl hηm hB
    refine fibreHyp_mono hpos H ?_
    unfold deltaPotS cls
    rw [if_neg hlm, h]
    simp
  · -- one shared plaquette
    have hτ0 : (0 : ℝ) ≤ β * (n2 M l m : ℝ) := by rw [h]; push_cast; linarith
    have hττ : β * (n2 M l m : ℝ) ≤ 2 * βb := by rw [h]; push_cast; linarith
    have hB := densFibreBound_of_check h2 MassGap.HaarMomentsSU2.haarConsts_su2 hν0 hE c1 hτ0 hττ
    have hc0 : 0 ≤ β * (n2 M l m : ℝ) / (2 * βb) * δ₁ := by
      rw [h]; push_cast; positivity
    have H := fibreHyp_localPot h2 hβ0 hM P hlm (c := β * (n2 M l m : ℝ) / (2 * βb) * δ₁)
      hc0 (by rw [h]; push_cast; linarith) hηl hηm hB
    refine fibreHyp_mono hpos H ?_
    unfold deltaPotS cls
    rw [if_neg hlm, h, if_pos rfl]
    have hle : β * ((2 : ℕ) : ℝ) / (2 * βb) * δ₁ ≤ δ₁ := by
      have : β * ((2 : ℕ) : ℝ) / (2 * βb) ≤ 1 := by
        rw [div_le_one (by linarith)]; push_cast; linarith
      calc β * ((2 : ℕ) : ℝ) / (2 * βb) * δ₁ ≤ 1 * δ₁ := mul_le_mul_of_nonneg_right this hδ₁
        _ = δ₁ := one_mul _
    exact mul_le_mul_of_nonneg_left (by linarith) hex
  · -- two shared plaquettes
    have hτ0 : (0 : ℝ) ≤ β * (n2 M l m : ℝ) := by rw [h]; push_cast; linarith
    have hττ : β * (n2 M l m : ℝ) ≤ 4 * βb := by rw [h]; push_cast; linarith
    have hB := densFibreBound_of_check h2 MassGap.HaarMomentsSU2.haarConsts_su2 hν0 hE c2 hτ0 hττ
    have hc0 : 0 ≤ β * (n2 M l m : ℝ) / (4 * βb) * δ₂ := by
      rw [h]; push_cast; positivity
    have H := fibreHyp_localPot h2 hβ0 hM P hlm (c := β * (n2 M l m : ℝ) / (4 * βb) * δ₂)
      hc0 (by rw [h]; push_cast; linarith) hηl hηm hB
    refine fibreHyp_mono hpos H ?_
    unfold deltaPotS cls
    rw [if_neg hlm, h, if_neg (by norm_num), if_pos rfl]
    have hle : β * ((4 : ℕ) : ℝ) / (4 * βb) * δ₂ ≤ δ₂ := by
      have : β * ((4 : ℕ) : ℝ) / (4 * βb) ≤ 1 := by
        rw [div_le_one (by linarith)]; push_cast; linarith
      calc β * ((4 : ℕ) : ℝ) / (4 * βb) * δ₂ ≤ 1 * δ₂ := mul_le_mul_of_nonneg_right this hδ₂
        _ = δ₂ := one_mul _
    exact mul_le_mul_of_nonneg_left (by linarith) hex

#print axioms fibreHyp_potS

/-- **The pointwise bound**: `deltaPotS ≤ E · δ_class + 2 E² mix`.

DERIVED: `2` is the additive terms; `1` is `e⁰`; `0` is the sign of the mixed weight. -/
theorem deltaPotS_le {ν E δ₁ δ₂ : ℝ} (hE : Real.exp ν ≤ E) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) {M : ℕ}
    (P : LocalPot N M) (hν : ∀ l, P.norm l ≤ ν) (l m : WilsonHypercubic.Link 4 (M + 1)) :
    deltaPotS δ₁ δ₂ P l m
      ≤ E * (if l = m then 0 else cls δ₁ δ₂ (n2 M l m)) + 2 * E ^ 2 * P.mix l m := by
  have he0 : 0 ≤ P.mix l m := Finset.sum_nonneg fun X _ => P.v_nonneg X
  have hE1 : 1 ≤ E := (Real.one_le_exp (he0.trans ((P.mix_le_at l m).trans
    ((P.at_le_norm l).trans (hν l))))).trans hE
  have hcls : 0 ≤ cls δ₁ δ₂ (n2 M l m) := by unfold cls; split_ifs <;> linarith
  by_cases hlm : l = m
  · unfold deltaPotS
    rw [if_pos hlm, if_pos hlm]
    positivity
  unfold deltaPotS
  rw [if_neg hlm, if_neg hlm]
  set e := P.mix l m with he
  have hle : e ≤ ν := (P.mix_le_at l m).trans ((P.at_le_norm l).trans (hν l))
  have hEe : Real.exp e ≤ E := (Real.exp_le_exp.mpr hle).trans hE
  have hsub : Real.exp e - 1 ≤ e * Real.exp e := by
    have h1 := Real.add_one_le_exp (-e)
    have h2 : Real.exp (-e) * Real.exp e = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos e]
  have hin : cls δ₁ δ₂ (n2 M l m) + 2 * (Real.exp e - 1) ≤ cls δ₁ δ₂ (n2 M l m) + 2 * (e * E) := by
    have : e * Real.exp e ≤ e * E := mul_le_mul_of_nonneg_left hEe he0
    linarith
  have hin0 : 0 ≤ cls δ₁ δ₂ (n2 M l m) + 2 * (e * E) := by
    have : 0 ≤ e * E := mul_nonneg he0 (by linarith)
    linarith
  calc Real.exp e * (cls δ₁ δ₂ (n2 M l m) + 2 * (Real.exp e - 1))
      ≤ Real.exp e * (cls δ₁ δ₂ (n2 M l m) + 2 * (e * E)) :=
        mul_le_mul_of_nonneg_left hin (Real.exp_pos e).le
    _ ≤ E * (cls δ₁ δ₂ (n2 M l m) + 2 * (e * E)) := mul_le_mul_of_nonneg_right hEe hin0
    _ = _ := by ring

#print axioms deltaPotS_le

/-- The class defect off the diagonal is `PairCorrSharp.pairDeltaSharp`.

DERIVED: no numeral. -/
theorem cls_eq_pairDeltaSharp (δ₁ δ₂ : ℝ) (j : ℕ) (l m : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    (if l = m then 0 else cls δ₁ δ₂ (n2 (2 * j + 1) l m)) = pairDeltaSharp δ₁ δ₂ j l m := by
  unfold cls pairDeltaSharp
  rfl

#print axioms cls_eq_pairDeltaSharp

/-- **Row and column sums**: at most `E · max(18δ₁, 12δ₁ + 3δ₂) + 2E²ν ≤ Δ`
(`deltaPotS_le`, `PairCorrSharp.pairDeltaSharp_row`, `LocalPotential.sum_mix_le`).

DERIVED: `18`, `12`, `3` are `pairDeltaSharp_row`'s counts; `2` the additive terms; `0` the lower
end of the entries. -/
theorem defectMatrix_potS {ν E δ₁ δ₂ Δ : ℝ} (hE : Real.exp ν ≤ E) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hΔ : E * max (18 * δ₁) (12 * δ₁ + 3 * δ₂) + 2 * E ^ 2 * ν ≤ Δ) (j : ℕ)
    (P : LocalPot N (2 * j + 1)) (hν : ∀ l, P.norm l ≤ ν) :
    MassGap.BoxGap.DefectMatrix (deltaPotS δ₁ δ₂ P) Δ := by
  have hν0 : 0 ≤ ν := le_trans (Finset.sum_nonneg fun X _ =>
    mul_nonneg (Nat.cast_nonneg _) (P.v_nonneg X)) (hν (Classical.arbitrary _))
  have hE1 : 1 ≤ E := (Real.one_le_exp hν0).trans hE
  have h0 : ∀ l m, 0 ≤ deltaPotS δ₁ δ₂ P l m := fun l m => by
    unfold deltaPotS
    split_ifs
    · exact le_rfl
    · have he : 0 ≤ P.mix l m := Finset.sum_nonneg fun X _ => P.v_nonneg X
      have h1 := Real.one_le_exp he
      have hc : 0 ≤ cls δ₁ δ₂ (n2 (2 * j + 1) l m) := by unfold cls; split_ifs <;> linarith
      positivity
  have hsymm : ∀ l m, deltaPotS δ₁ δ₂ P l m = deltaPotS δ₁ δ₂ P m l := fun l m => by
    unfold deltaPotS
    by_cases h : l = m
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h), n2_symm (2 * j + 1) l m, P.mix_symm l m]
  have hrow : ∀ l, ∑ m, deltaPotS δ₁ δ₂ P l m ≤ Δ := fun l => by
    have hdiag : deltaPotS δ₁ δ₂ P l l = 0 := by unfold deltaPotS; rw [if_pos rfl]
    have hpd : pairDeltaSharp δ₁ δ₂ j l l = 0 := by unfold pairDeltaSharp; rw [if_pos rfl]
    have hcls : ∑ m ∈ Finset.univ.erase l, pairDeltaSharp δ₁ δ₂ j l m
        ≤ max (18 * δ₁) (12 * δ₁ + 3 * δ₂) := by
      have := pairDeltaSharp_row hδ₁ hδ₂ j l
      rwa [← Finset.add_sum_erase _ _ (Finset.mem_univ l), hpd, zero_add] at this
    have hm : ∑ m ∈ Finset.univ.erase l, P.mix l m ≤ ν := (sum_mix_le P l).trans (hν l)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l), hdiag, zero_add]
    calc _ ≤ ∑ m ∈ Finset.univ.erase l,
            (E * pairDeltaSharp δ₁ δ₂ j l m + 2 * E ^ 2 * P.mix l m) :=
          Finset.sum_le_sum fun m _ => by
            have := deltaPotS_le hE hδ₁ hδ₂ P hν l m
            rwa [cls_eq_pairDeltaSharp] at this
      _ = E * ∑ m ∈ Finset.univ.erase l, pairDeltaSharp δ₁ δ₂ j l m
            + 2 * E ^ 2 * ∑ m ∈ Finset.univ.erase l, P.mix l m := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ E * max (18 * δ₁) (12 * δ₁ + 3 * δ₂) + 2 * E ^ 2 * ν := by
          have h1 := mul_le_mul_of_nonneg_left hcls (by linarith : (0 : ℝ) ≤ E)
          have h2 := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 2 * E ^ 2)
          linarith
      _ ≤ Δ := hΔ
  refine ⟨h0, hrow, fun m => ?_⟩
  calc ∑ l, deltaPotS δ₁ δ₂ P l m = ∑ l, deltaPotS δ₁ δ₂ P m l :=
        Finset.sum_congr rfl fun l _ => hsymm l m
    _ ≤ Δ := hrow m

#print axioms defectMatrix_potS

/-- **The sharp box local gap at general constants**: three density checks and
`E · max(18δ₁, 12δ₁ + 3δ₂) + 2E²ν ≤ Δ ≤ 1` give Wilson at `β ≤ βb` times a local potential of local
norm `≤ ν` the local gap `1 − Δ` at every box side and extent.

DERIVED: `1` bounds the entries; the rest as in `fibreHyp_potS`, `defectMatrix_potS`: `4`, `1/8`, `0` the
`SU(2)` Haar constants, `2`, `10`, `4`, `8`, `12` the coupling and tilt counts of the classes, `18`, `12`, `3`
`pairDeltaSharp_row`'s counts. -/
theorem potBox_localGapS {β βb ν E δ₁ δ₂ D₀ s₁ σ₁ s₂ σ₂ s₀ σ₀ Δ : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ βb)
    (hν0 : 0 ≤ ν) (hE : Real.exp ν ≤ E) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (c1 : DensCheck 4 (1 / 8) 0 s₁ σ₁ (2 * βb) (10 * βb) E δ₁)
    (c2 : DensCheck 4 (1 / 8) 0 s₂ σ₂ (4 * βb) (8 * βb) E δ₂)
    (c0 : DensCheck 4 (1 / 8) 0 s₀ σ₀ (2 * βb) (12 * βb) E D₀)
    (hΔ : E * max (18 * δ₁) (12 * δ₁ + 3 * δ₂) + 2 * E ^ 2 * ν ≤ Δ) (hΔ1 : Δ ≤ 1) (F : LocalPotFam 2)
    (hν : ∀ M l, (F.P M).norm l ≤ ν) (n : ℕ) :
    WBoxLocalGap (potWeight β F) n (1 - Δ) :=
  wBoxLocalGap_of_pairCorr (potWeight β F) (Δ := Δ) n (fun j => by
    have hM : 1 ≤ 2 * j + 1 := by omega
    have hD := defectMatrix_potS hE hδ₁ hδ₂ hΔ j (F.P (2 * j + 1)) (hν _)
    refine ⟨deltaPotS δ₁ δ₂ (F.P (2 * j + 1)), hD, fun l m => ?_,
      wPairCorrAt_of_fibreHyp (potWeight β F) j _ hD.1
        (fun l m hlm => fibreHyp_potS hβ0 hβ hν0 hE hδ₁ hδ₂ c1 c2 c0 hM (F.P (2 * j + 1)) (hν _) hlm)⟩
    calc deltaPotS δ₁ δ₂ (F.P (2 * j + 1)) l m ≤ ∑ m', deltaPotS δ₁ δ₂ (F.P (2 * j + 1)) l m' :=
          Finset.single_le_sum (fun m' _ => hD.1 l m') (Finset.mem_univ m)
      _ ≤ Δ := hD.2.1 l
      _ ≤ 1 := hΔ1)

#print axioms potBox_localGapS

/-- The single-pair check at `βb = 1/20`, `E = 16/15`.

DERIVED: `4`, `1/8`, `0` are the `SU(2)` Haar constants; `2`, `10` the single pair's counts; `1/20` the
coupling bound; `16/15 = 1/(1 − 1/16)`. CHOSEN: `1768/10000 ≥ √(1/32)`; `5529/10000 ≥ σ = 0.55281…`;
`331/10000` rounds the computed `0.03299…` up. -/
theorem densCheck_single :
    DensCheck 4 (1 / 8) 0 (1768 / 10000) (5529 / 10000) (2 * (1 / 20)) (10 * (1 / 20)) (16 / 15)
      (331 / 10000) := by
  norm_num [DensCheck, MassGap.PairInterface.dstar, MassGap.PairInterface.dstarNum,
    MassGap.PairInterface.dstarDen, MassGap.PairInterface.dstarE, MassGap.PairInterface.dstarZ,
    MassGap.PairInterface.M2bound, MassGap.PairInterface.mbarBound, MassGap.PairInterface.cR,
    MassGap.PairInterface.cR3]

#print axioms densCheck_single

/-- The double-pair check at `βb = 1/20`, `E = 16/15`.

DERIVED: `4`, `8` the double pair's counts; the rest as in `densCheck_single`. CHOSEN:
`5455/10000 ≥ σ = 0.54544…`; `690/10000` rounds the computed `0.06891…` up; as in `densCheck_single`,
`1/20` the coupling bound, `16/15 = 1/(1 − 1/16)` and `1768/10000 ≥ √(1/32)`. -/
theorem densCheck_double :
    DensCheck 4 (1 / 8) 0 (1768 / 10000) (5455 / 10000) (4 * (1 / 20)) (8 * (1 / 20)) (16 / 15)
      (690 / 10000) := by
  norm_num [DensCheck, MassGap.PairInterface.dstar, MassGap.PairInterface.dstarNum,
    MassGap.PairInterface.dstarDen, MassGap.PairInterface.dstarE, MassGap.PairInterface.dstarZ,
    MassGap.PairInterface.M2bound, MassGap.PairInterface.mbarBound, MassGap.PairInterface.cR,
    MassGap.PairInterface.cR3]

#print axioms densCheck_double

/-- The zero-coupling check at tilt `12 βb`, `E = 16/15` (its constant enters at coupling `0` only).

DERIVED: `2` the coupling slot, `12` the plaquettes per link; the rest as in `densCheck_single`.
CHOSEN: `5622/10000 ≥ σ = 0.56218…`; `343/10000` rounds the computed `0.03427…` up; as in
`densCheck_single`, `1/8` a Haar constant, `1/20` the coupling bound, `16/15 = 1/(1 − 1/16)` and
`1768/10000 ≥ √(1/32)`. -/
theorem densCheck_zero :
    DensCheck 4 (1 / 8) 0 (1768 / 10000) (5622 / 10000) (2 * (1 / 20)) (12 * (1 / 20)) (16 / 15)
      (343 / 10000) := by
  norm_num [DensCheck, MassGap.PairInterface.dstar, MassGap.PairInterface.dstarNum,
    MassGap.PairInterface.dstarDen, MassGap.PairInterface.dstarE, MassGap.PairInterface.dstarZ,
    MassGap.PairInterface.M2bound, MassGap.PairInterface.mbarBound, MassGap.PairInterface.cR,
    MassGap.PairInterface.cR3]

#print axioms densCheck_zero

/-- **The sharp potential box**: `SU(2)`, `β ≤ 1/20` (`β_std ≤ 1/10`) and a gauge-invariant local
potential of local norm `≤ 1/16` have local gap `213/1000` at every box side and extent.

DERIVED: `213/1000 = 1 − 787/1000`; `787/1000` bounds `(16/15) · (12 · 0.0331 + 3 · 0.069)
+ 2 (16/15)² / 16 = 0.78670…`; `16/15 = 1/(1 − 1/16)`; `1/20` the coupling bound of `densCheck_single`. -/
theorem potBox_localGap_sharp {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 20) (F : LocalPotFam 2)
    (hν : ∀ M l, (F.P M).norm l ≤ 1 / 16) (n : ℕ) :
    WBoxLocalGap (potWeight β F) n (213 / 1000) := by
  have hE : Real.exp (1 / 16) ≤ 16 / 15 := by
    have := MassGap.ObserverBox.exp_le_inv_one_sub (x := 1 / 16) (q := 1 / 16) (by norm_num) le_rfl
      (by norm_num)
    linarith [show (1 : ℝ) / (1 - 1 / 16) = 16 / 15 by norm_num]
  have hmax : max (18 * (331 / 10000 : ℝ)) (12 * (331 / 10000) + 3 * (690 / 10000))
      = 12 * (331 / 10000) + 3 * (690 / 10000) := max_eq_right (by norm_num)
  have h := potBox_localGapS hβ0 hβ (by norm_num) hE (by norm_num) (by norm_num) densCheck_single
    densCheck_double densCheck_zero (Δ := 787 / 1000) (by rw [hmax]; norm_num) (by norm_num) F hν n
  have e : (1 : ℝ) - 787 / 1000 = 213 / 1000 := by norm_num
  rw [e] at h
  exact h

#print axioms potBox_localGap_sharp

end MassGap.LocalPotentialSharp
