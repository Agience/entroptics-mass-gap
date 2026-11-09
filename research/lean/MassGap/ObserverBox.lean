import Mathlib
import MassGap.AdjacentFibre
import MassGap.WeightedTorus

noncomputable section

/-!
# MassGap.ObserverBox — the box local gap of Wilson plus an adjacent-plaquette coupling

The observer's coarse theory at its resolution is measured to be Wilson at a small effective
coupling with a small adjacent-plaquette coupling `λ` (CLAY-HANDOVER §5a). This file assembles the
box local gap of that family: the weight `wtAdj (bdT M) β λ` is a `WeightedTorus.TorusWeight`
(`adjWeight`), and its fibre hypotheses (`AdjacentFibre.torus_fibreHyp_adj_dens`) form a defect
matrix whose row sums the counts of `AdjacentFibre` bound.
-/

namespace MassGap.ObserverBox

open MeasureTheory
open MassGap.SUN (SU)
open MassGap.HeatBath (bdT wt wt_pos continuous_wt)
open MassGap.WeightedHeatBath (wtAdj adjAct adjSet dens continuous_dens)
open MassGap.WeightedTorus (TorusWeight)

variable {N : ℕ}

/-- The adjacent-pair action is continuous.

DERIVED: no numeral. -/
theorem continuous_adjAct (M : ℕ) :
    Continuous (adjAct (N := N) (bdT M)) := by
  unfold adjAct
  exact continuous_finset_sum _ fun pq _ => (continuous_dens _ pq.1).mul (continuous_dens _ pq.2)

#print axioms continuous_adjAct

/-- The adjacent-pair action is gauge invariant (`LocalGauge.wilsonDensity_gaugeTransform`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem adjAct_gauge (M : ℕ) (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    adjAct (bdT M) (LocalGauge.gaugeTransform g W) = adjAct (bdT M) W := by
  unfold adjAct dens
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [LocalGauge.wilsonDensity_gaugeTransform g W pq.1, LocalGauge.wilsonDensity_gaugeTransform g W pq.2]

#print axioms adjAct_gauge

/-- **Wilson plus an adjacent-plaquette coupling as a torus weight.**

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def adjWeight (β lam : ℝ) : TorusWeight N where
  Φ M := wtAdj (bdT M) β lam
  pos M W := mul_pos (wt_pos _ _ _) (Real.exp_pos _)
  cont M := (continuous_wt _ _).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_adjAct M)))
  gauge M g W := by
    show wt (bdT M) β (LocalGauge.gaugeTransform g W)
        * Real.exp (-lam * adjAct (bdT M) (LocalGauge.gaugeTransform g W))
      = wt (bdT M) β W * Real.exp (-lam * adjAct (bdT M) W)
    rw [adjAct_gauge, show wt (bdT M) β (LocalGauge.gaugeTransform g W) = wt (bdT M) β W from
      LocalGauge.boltz_gauge_invariant_local g β W]

/-! ## One density check gives a linear fibre bound below it -/

open MassGap.CompactGauge (probHaar)
open MassGap.PairInterface (dstar dstarNum dstarDen dstarE dstarZ cR cR3 FE realFeature
  continuous_realFeature norm_realFeature HaarConsts M2bound mbarBound)
open MassGap.PairFibreDens (Dens nearTilt DensFibreBound DensBounds densFibreBound_of_densBounds
  densBounds_mono densFibreBound_mono densBounds_nearTilt)
open MassGap.TiltedHaar (cR_nonneg cR3_nonneg exp_sub_one_sub_le tiltBounds_of_haarConsts)

/-- The pair partition bound decreases in the coupling.

DERIVED: `0` is the lower end of `τ`; `2` is the square. -/
theorem dstarZ_anti {τ τ₀ mb : ℝ} (hτ : 0 ≤ τ) (h : τ ≤ τ₀) : dstarZ τ₀ mb ≤ dstarZ τ mb := by
  unfold dstarZ
  nlinarith [sq_nonneg mb]

#print axioms dstarZ_anti

/-- The pair denominator decreases in the coupling (with `c₂ = cR τ`).

DERIVED: `0` is the lower end of `τ`, `M₂`, `σ`, `mb`; `2` is the square and the halving. -/
theorem dstarDen_anti {τ τ₀ M₂ σ mb : ℝ} (hτ : 0 ≤ τ) (hττ : τ ≤ τ₀) (hM : 0 ≤ M₂) (hσ : 0 ≤ σ)
    (hmb : 0 ≤ mb) (hZ : 0 < dstarZ τ₀ mb) :
    dstarDen τ₀ M₂ σ mb (cR τ₀) ≤ dstarDen τ M₂ σ mb (cR τ) := by
  have hτ₀ : 0 ≤ τ₀ := hτ.trans hττ
  have hc : cR τ ≤ cR τ₀ := by unfold cR; gcongr
  have hZτ := dstarZ_anti (mb := mb) hτ hττ
  have hZτ0 : 0 < dstarZ τ mb := lt_of_lt_of_le hZ hZτ
  have he : ∀ t, dstarE t M₂ σ mb (cR t) = t * (σ * mb + cR t * t * M₂ / 2) := fun t => by
    unfold dstarE
    ring
  have he0 : ∀ t, 0 ≤ t → 0 ≤ σ * mb + cR t * t * M₂ / 2 := fun t ht => by
    have := cR_nonneg ht
    positivity
  have hcm : cR τ * τ * M₂ ≤ cR τ₀ * τ₀ * M₂ :=
    mul_le_mul_of_nonneg_right (mul_le_mul hc hττ hτ (cR_nonneg hτ₀)) hM
  have hemono : σ * mb + cR τ * τ * M₂ / 2 ≤ σ * mb + cR τ₀ * τ₀ * M₂ / 2 := by linarith
  unfold dstarDen
  rw [he τ, he τ₀]
  have h1 : (τ * (σ * mb + cR τ * τ * M₂ / 2)) ^ 2 ≤ (τ₀ * (σ * mb + cR τ₀ * τ₀ * M₂ / 2)) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hτ (he0 τ hτ)) (mul_le_mul hττ hemono (he0 τ hτ) hτ₀) 2
  have h2 : (τ * (σ * mb + cR τ * τ * M₂ / 2)) ^ 2 / dstarZ τ mb
      ≤ (τ₀ * (σ * mb + cR τ₀ * τ₀ * M₂ / 2)) ^ 2 / dstarZ τ₀ mb :=
    calc _ ≤ (τ₀ * (σ * mb + cR τ₀ * τ₀ * M₂ / 2)) ^ 2 / dstarZ τ mb :=
          div_le_div_of_nonneg_right h1 hZτ0.le
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) hZ hZτ
  have h3 : τ * mb ≤ τ₀ * mb := mul_le_mul_of_nonneg_right hττ hmb
  linarith

#print axioms dstarDen_anti

/-- **The numeric density check** at the coupling `τ₀`, tilt `κ`, density ratio bound `E ≥ e^η`
and Haar constants `D, q4, t3`: side conditions and `dstar ≤ D₀` with the moment constants
`E² M2bound`, `E (mbarBound + E − 1)` of `PairFibreDens.densBounds_nearTilt`.

DERIVED: `0` is the lower end; `3` is the range of `TiltedHaar`'s `exp` bounds; `1` is `e⁰`; `2` is
the square. -/
def DensCheck (D q4 t3 s σ τ₀ κ E D₀ : ℝ) : Prop :=
  0 < τ₀ ∧ τ₀ ≤ 3 ∧ 0 ≤ κ ∧ κ ≤ 3 ∧ 0 ≤ s ∧ 0 ≤ σ ∧ q4 / D ≤ s ^ 2 ∧ 1 ≤ E ∧
    E ^ 2 * M2bound D q4 t3 κ ≤ σ ^ 2 ∧
    0 < dstarZ τ₀ (E * (mbarBound D q4 t3 s κ + E - 1)) ∧
    0 < dstarDen τ₀ (E ^ 2 * M2bound D q4 t3 κ) σ (E * (mbarBound D q4 t3 s κ + E - 1)) (cR τ₀) ∧
    dstar τ₀ (E ^ 2 * M2bound D q4 t3 κ) σ (E * (mbarBound D q4 t3 s κ + E - 1)) (cR τ₀) ≤ D₀

/-- **A density check gives the linear fibre bound below `τ₀`**: for `0 ≤ τ ≤ τ₀`, the density
fibre bound at constant `(τ/τ₀) D₀` on the densities within `e^{±η}` of a tilt of norm `κ`
(`TiltedHaar.tiltBounds_of_haarConsts`, `PairFibreDens.densBounds_nearTilt`,
`PairFibreDens.densFibreBound_of_densBounds`, `AdjacentFibre.dstar_le_linear`).

DERIVED: `0` is the lower end and the excluded rank; `1` is the feature norm bound; `2` is the
square; `3` is the range of the `exp` bounds. -/
theorem densFibreBound_of_check (hN : N ≠ 0) (H : HaarConsts (probHaar (SU N)) (realFeature N))
    {s σ τ₀ κ E D₀ η : ℝ} (hη : 0 ≤ η) (hE : Real.exp η ≤ E)
    (hc : DensCheck H.D H.q4 H.t3 s σ τ₀ κ E D₀) {τ : ℝ} (hτ : 0 ≤ τ) (hττ : τ ≤ τ₀) :
    DensFibreBound (probHaar (SU N)) (realFeature N) (τ / τ₀ * D₀) τ
      (nearTilt (realFeature N) κ η) := by
  obtain ⟨hτ₀, hτ₃, hκ0, hκ3, hs0, hσ0, hs, hE1, hM2, hZ, hden, hD⟩ := hc
  have hX := continuous_realFeature N
  have hX1 : ∀ g : SU N, ‖realFeature N g‖ ≤ 1 := fun g => (norm_realFeature hN g).le
  have hTB := tiltBounds_of_haarConsts H hX hX1 hκ0 hκ3 hs0 hs
  have hM0 : 0 ≤ M2bound H.D H.q4 H.t3 κ := by
    unfold M2bound
    exact add_nonneg (add_nonneg (div_nonneg zero_le_one H.D_pos.le) (mul_nonneg H.t3_nonneg hκ0))
      (mul_nonneg (mul_nonneg (cR_nonneg hκ0) H.q4_nonneg) (sq_nonneg κ))
  have hmb0 : 0 ≤ mbarBound H.D H.q4 H.t3 s κ := by
    unfold mbarBound
    exact add_nonneg (add_nonneg (div_nonneg hκ0 H.D_pos.le)
        (div_nonneg (mul_nonneg H.t3_nonneg (sq_nonneg κ)) zero_le_two))
      (mul_nonneg (mul_nonneg (cR3_nonneg hκ0) (sq_nonneg κ)) hs0)
  have he1 : 1 ≤ Real.exp η := Real.one_le_exp hη
  have hDB := densBounds_nearTilt (P := probHaar (SU N)) hX hX1 hη hM0 hmb0 hTB
  have hDB' : DensBounds (probHaar (SU N)) (realFeature N) (nearTilt (realFeature N) κ η)
      (E ^ 2 * M2bound H.D H.q4 H.t3 κ) (E * (mbarBound H.D H.q4 H.t3 s κ + E - 1)) := by
    refine densBounds_mono hDB ?_ ?_
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos η).le hE 2) hM0
    · exact mul_le_mul hE (by linarith) (by linarith) (by linarith)
  have hMp : 0 ≤ E ^ 2 * M2bound H.D H.q4 H.t3 κ := by positivity
  have hmp : 0 ≤ E * (mbarBound H.D H.q4 H.t3 s κ + E - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hF := densFibreBound_of_densBounds (P := probHaar (SU N)) hX hX1 hτ hMp hmp (cR_nonneg hτ)
    hDB' (fun u hu => exp_sub_one_sub_le hu (hττ.trans hτ₃)) hσ0 hM2
    (lt_of_lt_of_le hZ (dstarZ_anti hτ hττ)) (lt_of_lt_of_le hden
      (dstarDen_anti hτ hττ hMp hσ0 hmp hZ))
  refine densFibreBound_mono hF ?_
  calc _ ≤ τ / τ₀ * dstar τ₀ (E ^ 2 * M2bound H.D H.q4 H.t3 κ) σ
          (E * (mbarBound H.D H.q4 H.t3 s κ + E - 1)) (cR τ₀) :=
        MassGap.AdjacentFibre.dstar_le_linear hτ hττ hτ₀ hMp hσ0 hmp hZ hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hD (div_nonneg hτ hτ₀.le)

#print axioms densFibreBound_of_check

/-- **The observer box's density check**, `SU(2)`: at `τ₀ = 361/1250`, `κ = 219/1250`,
`E = 1250/1241`, `dstar ≤ 109/1250`.

DERIVED: `4`, `1/8`, `0` are `HaarMomentsSU2.haarConsts_su2`'s `D`, `q4`, `t3`;
`361/1250 = 4/200 + (192 · 4 + 2 · 2304)/20000` is the largest pair coupling on the box
(`n2 ≤ 4`, `sum_cross_le`); `219/1250 = 12 (1/200 + 192/20000)`; `1250/1241 = 1/(1 − 9/1250)` bounds
`e^{144/20000}`. CHOSEN: `1768/10000 ≥ √(1/32)`; `5057/10000 ≥ √M₂ = √0.255704…`; `109/1250 = 0.0872`
rounds the computed `0.0871101…` up. -/
theorem densCheck_obs :
    DensCheck 4 (1 / 8) 0 (1768 / 10000) (5057 / 10000) (361 / 1250) (219 / 1250) (1250 / 1241)
      (109 / 1250) := by
  norm_num [DensCheck, dstar, dstarNum, dstarDen, dstarE, dstarZ, M2bound, mbarBound, cR, cR3]

#print axioms densCheck_obs

/-! ## The defect matrix of the observer box and its row sums -/

open MassGap.PairCount (n2 n2_symm n2_cases sum_n2_le)
open MassGap.AdjacentFibre (crossSet sum_cross_le sum_cross_le' torus_fibreHyp_adj_dens)
open MassGap.WeightedHeatBath (FibreHyp)
open MassGap.WeightedTorus (WBoxLocalGap wBoxLocalGap_of_pairCorr wPairCorrAt_of_fibreHyp)
open MassGap.BoxGap (DefectMatrix)

/-- The coupling bound of the pair `(l, m)`: `β n2 + |λ| (192 n2 + #cross(l, m) + #cross(m, l))`.

DERIVED: Inherited: `192 = 2 · 2 · 48` from `AdjacentFibre.wtAdj_dens_eq` (the density bound `2`, the two
orders of a pair, `card_partners_le`'s `48`); `4` the dimension; `1` the successor writing the extent. -/
def tauP (β lam : ℝ) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  β * (n2 M l m : ℝ) + |lam| * (192 * (n2 M l m : ℝ)
    + (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ)))

/-- The mixed-part bound of the pair `(l, m)`: `48 n2 |λ|`.

DERIVED: Inherited: `48 = 2 · 24` from `AdjacentFibre.card_mix_le` via `wtAdj_dens_eq` (the two orders,
`24 = 12 + 12` plaquettes through `l` or `m`); `4` the dimension; `1` the successor writing the extent. -/
def epsP (lam : ℝ) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  48 * (n2 M l m : ℝ) * |lam|

/-- **The observer box's defect matrix**: `0` on the diagonal, and
`e^ε ((τ/τ₀) D₀ + 2 (e^ε − 1))` at a pair, with `τ₀ = 361/1250`, `D₀ = 109/1250` (`densCheck_obs`).

DERIVED: `361/1250`, `109/1250` are `densCheck_obs`'s; `2` is the perturbation lemma's two additive
terms; `1` is `e⁰`; `0` is the diagonal. -/
def deltaObs (β lam : ℝ) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  if l = m then 0 else
    Real.exp (epsP lam M l m) * (tauP β lam M l m / (361 / 1250) * (109 / 1250)
      + 2 * (Real.exp (epsP lam M l m) - 1))

/-- `e^x ≤ 1/(1 − q)` for `0 ≤ x ≤ q < 1` (`Real.exp_bound_div_one_sub_of_interval`).

DERIVED: `0`, `1` are the interval's ends. -/
theorem exp_le_inv_one_sub {x q : ℝ} (hx : 0 ≤ x) (hxq : x ≤ q) (hq : q < 1) :
    Real.exp x ≤ 1 / (1 - q) :=
  (Real.exp_bound_div_one_sub_of_interval hx (by linarith)).trans
    (one_div_le_one_div_of_le (by linarith) (by linarith))

#print axioms exp_le_inv_one_sub

/-- The pair counts on the box: `n2 ≤ 4`, each cross count at most `2304`.

DERIVED: `4` is `n2_cases`'s largest value; `2304` is `sum_cross_le`'s bound; `1` is the least `M`. -/
theorem pair_counts_le {M : ℕ} (hM : 1 ≤ M) {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m) :
    (n2 M l m : ℝ) ≤ 4 ∧ ((crossSet M l m).card : ℝ) ≤ 2304 ∧ ((crossSet M m l).card : ℝ) ≤ 2304 := by
  refine ⟨?_, ?_, ?_⟩
  · rcases n2_cases hM hlm with h | h | h <;> rw [h] <;> norm_num
  · have h := (Finset.single_le_sum (f := fun m => (crossSet M l m).card)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)).trans (sum_cross_le M l)
    exact_mod_cast h
  · have h := (Finset.single_le_sum (f := fun m => (crossSet M m l).card)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)).trans (sum_cross_le' M l)
    exact_mod_cast h

#print axioms pair_counts_le

/-- **Every pair of the observer box has its fibre hypothesis at `deltaObs`**
(`AdjacentFibre.torus_fibreHyp_adj_dens`, `densFibreBound_of_check`, `densCheck_obs`).

DERIVED: `2` is the rank; `1` is the least `M`; `0` is the lower end of `β`; `1/200`, `1/20000` are the
box; `144/20000 ≤ 9/1250` is the density spread; the rest as in `densCheck_obs`. -/
theorem fibreHyp_obs {β lam : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) (hl : |lam| ≤ 1 / 20000) {M : ℕ}
    (hM : 1 ≤ M) {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m) :
    FibreHyp (wtAdj (N := 2) (bdT M) β lam) l m (deltaObs β lam M l m) := by
  have h2 : (2 : ℕ) ≠ 0 := by norm_num
  obtain ⟨hn, hc1, hc2⟩ := pair_counts_le hM hlm
  have hn0 : (0 : ℝ) ≤ n2 M l m := Nat.cast_nonneg _
  have hc10 : (0 : ℝ) ≤ (crossSet M l m).card := Nat.cast_nonneg _
  have hc20 : (0 : ℝ) ≤ (crossSet M m l).card := Nat.cast_nonneg _
  have hla := abs_nonneg lam
  have hτ0 : 0 ≤ tauP β lam M l m := by unfold tauP; positivity
  have hττ : tauP β lam M l m ≤ 361 / 1250 := by
    unfold tauP
    nlinarith [mul_le_mul hβ hn hn0 (by norm_num : (0 : ℝ) ≤ 1 / 200)]
  have hη : Real.exp (144 * |lam|) ≤ 1250 / 1241 := by
    have := exp_le_inv_one_sub (x := 144 * |lam|) (q := 9 / 1250) (by positivity) (by linarith)
      (by norm_num)
    linarith [show (1 : ℝ) / (1 - 9 / 1250) = 1250 / 1241 by norm_num]
  have hB := densFibreBound_of_check h2 MassGap.HaarMomentsSU2.haarConsts_su2 (by positivity) hη
    densCheck_obs hτ0 hττ
  have hκ : (β + 192 * |lam|) * (12 - (n2 M l m : ℝ)) ≤ 219 / 1250 := by
    have h1 : 12 - (n2 M l m : ℝ) ≤ 12 := by linarith
    have h2' : 0 ≤ β + 192 * |lam| := by positivity
    nlinarith
  have H := torus_fibreHyp_adj_dens h2 hβ0 lam hM hlm (c := tauP β lam M l m / (361 / 1250) * (109 / 1250))
    (τ := tauP β lam M l m) (κ := 219 / 1250) (by positivity) le_rfl hκ hB
  unfold deltaObs epsP
  rw [if_neg hlm]
  exact H

#print axioms fibreHyp_obs

/-- **The pointwise bound of a defect entry**: `deltaObs ≤ a n2 + b (#cross(l, m) + #cross(m, l))`
with `a = E₂ (D₀/τ₀)(β + 192|λ|) + 96 E₂² |λ|`, `b = E₂ (D₀/τ₀)|λ|`, `E₂ = 625/619 ≥ e^{192|λ|}`
(`e^x − 1 ≤ x e^x`).

DERIVED: `625/619 = 1/(1 − 192/20000)`; `96 = 2 · 48`; `192 = 48 · 4`; the rest as in `deltaObs`:
`361/1250` (`τ₀`), `109/1250` (`D₀`) are `densCheck_obs`'s; `1/20000` the `λ` side of the box of
`fibreHyp_obs`. -/
theorem deltaObs_le {β lam : ℝ} (hβ0 : 0 ≤ β) (hl : |lam| ≤ 1 / 20000) {M : ℕ} (hM : 1 ≤ M)
    (l m : WilsonHypercubic.Link 4 (M + 1)) :
    deltaObs β lam M l m
      ≤ ((625 / 619) * ((109 / 1250) / (361 / 1250)) * (β + 192 * |lam|)
          + 96 * (625 / 619) ^ 2 * |lam|) * (n2 M l m : ℝ)
        + (625 / 619) * ((109 / 1250) / (361 / 1250)) * |lam|
          * (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ)) := by
  have hla := abs_nonneg lam
  have hn0 : (0 : ℝ) ≤ n2 M l m := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ ((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ) := by positivity
  by_cases hlm : l = m
  · unfold deltaObs
    rw [if_pos hlm]
    positivity
  obtain ⟨hn, -, -⟩ := pair_counts_le hM hlm
  unfold deltaObs
  rw [if_neg hlm]
  set e := epsP lam M l m with he
  have he0 : 0 ≤ e := by rw [he]; unfold epsP; positivity
  have heq : e ≤ 192 / 20000 := by
    rw [he]; unfold epsP
    nlinarith [mul_le_mul hn hl hla (by norm_num : (0 : ℝ) ≤ 4)]
  have hE : Real.exp e ≤ 625 / 619 := by
    have := exp_le_inv_one_sub he0 heq (by norm_num)
    linarith [show (1 : ℝ) / (1 - 192 / 20000) = 625 / 619 by norm_num]
  have hsub : Real.exp e - 1 ≤ e * Real.exp e := by
    have h1 := Real.add_one_le_exp (-e)
    have h2 : Real.exp (-e) * Real.exp e = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos e]
  have hE0 : 1 ≤ Real.exp e := Real.one_le_exp he0
  have hτ : tauP β lam M l m / (361 / 1250) * (109 / 1250)
      = ((109 / 1250) / (361 / 1250)) * (β * (n2 M l m : ℝ) + |lam| * (192 * (n2 M l m : ℝ)
        + (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ)))) := by
    unfold tauP; ring
  rw [hτ]
  have hτ0 : 0 ≤ β * (n2 M l m : ℝ) + |lam| * (192 * (n2 M l m : ℝ)
        + (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ))) := by positivity
  have hinner : ((109 / 1250) / (361 / 1250)) * (β * (n2 M l m : ℝ) + |lam| * (192 * (n2 M l m : ℝ)
        + (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ))))
        + 2 * (Real.exp e - 1)
      ≤ ((109 / 1250) / (361 / 1250)) * (β * (n2 M l m : ℝ) + |lam| * (192 * (n2 M l m : ℝ)
        + (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ))))
        + 2 * (e * (625 / 619)) := by
    have : e * Real.exp e ≤ e * (625 / 619) := mul_le_mul_of_nonneg_left hE he0
    linarith
  have hin0 : 0 ≤ ((109 / 1250) / (361 / 1250)) * (β * (n2 M l m : ℝ) + |lam| * (192 * (n2 M l m : ℝ)
        + (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ))))
        + 2 * (e * (625 / 619)) := by positivity
  calc _ ≤ Real.exp e * (((109 / 1250) / (361 / 1250)) * (β * (n2 M l m : ℝ)
          + |lam| * (192 * (n2 M l m : ℝ)
          + (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ)))) + 2 * (e * (625 / 619))) :=
        mul_le_mul_of_nonneg_left hinner (Real.exp_pos e).le
    _ ≤ (625 / 619) * (((109 / 1250) / (361 / 1250)) * (β * (n2 M l m : ℝ)
          + |lam| * (192 * (n2 M l m : ℝ)
          + (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ)))) + 2 * (e * (625 / 619))) :=
        mul_le_mul_of_nonneg_right hE hin0
    _ = _ := by rw [he]; unfold epsP; ring

#print axioms deltaObs_le

/-- The defect matrix is symmetric (`PairCount.n2_symm`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem deltaObs_symm (β lam : ℝ) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1)) :
    deltaObs β lam M l m = deltaObs β lam M m l := by
  unfold deltaObs tauP epsP
  by_cases h : l = m
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), n2_symm M l m, add_comm ((crossSet M l m).card : ℝ)]

#print axioms deltaObs_symm

/-- **The row sums of the observer box's defect matrix are at most `407/1000`** (`deltaObs_le`,
`PairCount.sum_n2_le`, `sum_cross_le`, `sum_cross_le'`).

DERIVED: `36` is `sum_n2_le`'s bound; `2304` is `sum_cross_le`'s; `407/1000` rounds the computed
`0.4066…` up; `1` is the least `M`; the rest as in `deltaObs_le`; `1/200`, `1/20000` the coupling box of
`fibreHyp_obs`. -/
theorem row_deltaObs_le {β lam : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) (hl : |lam| ≤ 1 / 20000)
    {M : ℕ} (hM : 1 ≤ M) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ∑ m, deltaObs β lam M l m ≤ 407 / 1000 := by
  have hla := abs_nonneg lam
  set a := (625 / 619) * ((109 / 1250) / (361 / 1250)) * (β + 192 * |lam|)
    + 96 * (625 / 619) ^ 2 * |lam| with ha
  set b := (625 / 619) * ((109 / 1250) / (361 / 1250)) * |lam| with hb
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hdiag : deltaObs β lam M l l = 0 := by unfold deltaObs; rw [if_pos rfl]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l), hdiag, zero_add]
  have hpt : ∀ m ∈ Finset.univ.erase l, deltaObs β lam M l m
      ≤ a * (n2 M l m : ℝ) + b * (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ)) :=
    fun m _ => by rw [ha, hb]; exact deltaObs_le hβ0 hl hM l m
  have hn : (∑ m ∈ Finset.univ.erase l, (n2 M l m : ℝ)) ≤ 36 := by exact_mod_cast sum_n2_le hM l
  have hc1 : (∑ m ∈ Finset.univ.erase l, ((crossSet M l m).card : ℝ)) ≤ 2304 := by
    have h := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset l Finset.univ)
      (fun _ _ _ => Nat.zero_le _) : ∑ m ∈ Finset.univ.erase l, (crossSet M l m).card
        ≤ ∑ m, (crossSet M l m).card).trans (sum_cross_le M l)
    exact_mod_cast h
  have hc2 : (∑ m ∈ Finset.univ.erase l, ((crossSet M m l).card : ℝ)) ≤ 2304 := by
    have h := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset l Finset.univ)
      (fun _ _ _ => Nat.zero_le _) : ∑ m ∈ Finset.univ.erase l, (crossSet M m l).card
        ≤ ∑ m, (crossSet M m l).card).trans (sum_cross_le' M l)
    exact_mod_cast h
  calc _ ≤ ∑ m ∈ Finset.univ.erase l, (a * (n2 M l m : ℝ)
          + b * (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ))) :=
        Finset.sum_le_sum hpt
    _ = a * ∑ m ∈ Finset.univ.erase l, (n2 M l m : ℝ)
          + b * (∑ m ∈ Finset.univ.erase l, ((crossSet M l m).card : ℝ)
            + ∑ m ∈ Finset.univ.erase l, ((crossSet M m l).card : ℝ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ a * 36 + b * (2304 + 2304) := by
        gcongr
    _ ≤ 407 / 1000 := by
        rw [ha, hb]
        nlinarith

#print axioms row_deltaObs_le

/-- **The observer box is a defect matrix with row and column sums at most `407/1000`.**

DERIVED: as `row_deltaObs_le`; `0` is the lower end of the entries; `407/1000` the row bound of
`row_deltaObs_le`; `1/200`, `1/20000` the coupling box of `fibreHyp_obs`. -/
theorem defectMatrix_obs {β lam : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) (hl : |lam| ≤ 1 / 20000)
    {M : ℕ} (hM : 1 ≤ M) : DefectMatrix (deltaObs β lam M) (407 / 1000) := by
  have h0 : ∀ l m, 0 ≤ deltaObs β lam M l m := fun l m => by
    unfold deltaObs
    split_ifs with h
    · exact le_rfl
    · have he : 0 ≤ epsP lam M l m := by unfold epsP; positivity
      have ht : 0 ≤ tauP β lam M l m := by unfold tauP; positivity
      have := Real.one_le_exp he
      positivity
  refine ⟨h0, fun l => row_deltaObs_le hβ0 hβ hl hM l, fun m => ?_⟩
  calc ∑ l, deltaObs β lam M l m = ∑ l, deltaObs β lam M m l :=
        Finset.sum_congr rfl fun l _ => deltaObs_symm β lam M l m
    _ ≤ 407 / 1000 := row_deltaObs_le hβ0 hβ hl hM m

#print axioms defectMatrix_obs

/-- **The box local gap of the observer theory**: Wilson at `β ≤ 1/200` plus an adjacent-plaquette
coupling `|λ| ≤ 1/20000` (Lean normalisation; `β_std ≤ 1/100`, `|λ_std| ≤ 1/2500`) has the local gap
`593/1000` at every box side and every extent (`WeightedTorus.wBoxLocalGap_of_pairCorr`,
`wPairCorrAt_of_fibreHyp`, `fibreHyp_obs`, `defectMatrix_obs`).

DERIVED: `593/1000 = 1 − 407/1000`; `2` is the rank; `1` bounds the entries (`407/1000 ≤ 1`); `1/200`,
`1/20000` the coupling box of `fibreHyp_obs`. -/
theorem obsBox_localGap {β lam : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) (hl : |lam| ≤ 1 / 20000)
    (n : ℕ) : WBoxLocalGap (adjWeight (N := 2) β lam) n (593 / 1000) := by
  have h := wBoxLocalGap_of_pairCorr (adjWeight (N := 2) β lam) (Δ := 407 / 1000) n (fun j => by
    have hM : 1 ≤ 2 * j + 1 := by omega
    have hD := defectMatrix_obs hβ0 hβ hl hM
    refine ⟨deltaObs β lam (2 * j + 1), hD, fun l m => ?_,
      wPairCorrAt_of_fibreHyp (adjWeight β lam) j _ hD.1
        (fun l m hlm => fibreHyp_obs hβ0 hβ hl hM hlm)⟩
    calc deltaObs β lam (2 * j + 1) l m ≤ ∑ m', deltaObs β lam (2 * j + 1) l m' :=
          Finset.single_le_sum (fun m' _ => hD.1 l m') (Finset.mem_univ m)
      _ ≤ 407 / 1000 := hD.2.1 l
      _ ≤ 1 := by norm_num)
  have e : (1 : ℝ) - 407 / 1000 = 593 / 1000 := by norm_num
  rw [e] at h
  exact h

#print axioms obsBox_localGap

end MassGap.ObserverBox
