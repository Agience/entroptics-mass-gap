import Mathlib
import MassGap.BoxDobrushin
import MassGap.LocalPotential
import MassGap.WeightedHeatBath
import MassGap.WeightedTorus

noncomputable section

/-!
# MassGap.BoxDobrushinCoupling — the single-link kernel of the box and Dobrushin's comparison

`BoxDobrushin` proves the propagation, the tilt bound and the numbers of a Dobrushin influence
estimate. This module supplies the pieces it takes as inputs, for the box weight
`LocalPotential.wtV β P` (Wilson times `e^{potential}`) and its heat baths
`WeightedHeatBath.wAvg`.

1. **The pointwise lemma** (`wtV_update_ratio`). Changing the link `k` multiplies the weight seen
   by the link `l` by `K · exp(h_W + h_V)`, with `K > 0` not depending on the value at `l`,
   `|h_W| ≤ 2β · n2(l, k)` (four times `β` per unoriented plaquette through both links) and
   `|h_V| ≤ 2 · mix(l, k)`, uniformly in the rest of the configuration.
2. **The influence matrix of the box** (`tilt_weighted`, `wAvg_link_infl`, `infl_wtV`,
   `rowSum_box`). The heat bath at `l` moves the mean of every continuous `[0, 1]`-valued function
   of the link variable by at most `C(l, k) = q(e^{2β n2(l,k)}) + q(e^{2 mix(l,k)})` when the link `k`
   changes; at Lean `β ≤ 1/40` and local norm `≤ 1/16` the row sums of `C` are `≤ 39/40`.
3. **Dobrushin's comparison in oscillation form** (`osc_step`). For any positive continuous
   weight with influence matrix `C`, a bound `v` on the single-link oscillations of a continuous `f`
   gives for the heat bath at `l` the bound `v_k + C(l, k) v_l` at `k ≠ l` and `0` at `l`.
4. **Sweeps** (`osc_sweep`, `osc_sweep_full`, `osc_iter`, `abs_sub_le_sum_osc`). A sweep through every
   link contracts the total oscillation by the row-sum bound `α`; `n` sweeps leave a function within
   `αⁿ Σ v` of a constant. With `DLRLimit.dlr_eq_at_of_kernel_near_const` this gives uniqueness of the
   heat-bath-invariant state (`state_unique_of_infl`, `state_unique_wtV`).

## Scope

The comparison is in Föllmer's oscillation form, which needs no coupling. It acts on the finite
periodic box, where the sweep contracts the oscillation in every link at once. The spatial form
(influence of a far boundary on a local observable, the `hrec` / `hread` inputs of
`BoxDobrushin.dlr_eq_of_influence` for a box inside a larger lattice) and the covariance bound that
`ObserverEnergyGap.LatClusterRateOn` asks for are not derived here.
-/

namespace MassGap.BoxDobrushinCoupling

open MeasureTheory
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.HeatBath (bdT wt wt_pos continuous_wt exists_abs_le integrable_of_abs_le
  wilsonHol_update_of_not_mem)
open MassGap.WilsonLattice (wilsonHol)
open MassGap.WilsonAction (wilsonDensity wilsonDensity_nonneg wilsonDensity_le_two)
open MassGap.PairCount (n2 wilsonHol_diag n2_cases sum_n2_le)
open MassGap.LocalPotential (LocalPot wtV sum_mix_le)
open MassGap.BoxDobrushin (qfun qfun_mul_le tilt_core wilsonPair_le potPair_le)
open MassGap.WeightedHeatBath (wNum wPart wAvg wPart_pos wAvg_update continuous_wAvg)

variable {N : ℕ}

/-! ## 1. The pointwise lemma -/

section Pointwise

variable {M : ℕ}

/-- The Wilson weight is `exp(−β Σ_p φ(U_p))` over the oriented plaquettes.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem wt_eq (β : ℝ) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    wt (bdT M) β W = Real.exp (-β * ∑ p, wilsonDensity (wilsonHol (bdT M) p W)) := rfl

#print axioms wt_eq

/-- The oriented non-diagonal plaquettes whose boundary visits both `l` and `k`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `1`, `2` in
`p.1.1`, `p.1.2` are projections. -/
def pairPlaq (M : ℕ) (l k : WilsonHypercubic.Link 4 (M + 1)) :
    Finset (WilsonHypercubic.Plaq 4 (M + 1)) :=
  Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
    p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ k ∈ (bdT M p).map Prod.fst)

/-- There are `n2 M l k` of them, by definition.

DERIVED: `4`, `1` as in `pairPlaq`. -/
theorem card_pairPlaq (l k : WilsonHypercubic.Link 4 (M + 1)) :
    (pairPlaq M l k).card = n2 M l k := rfl

#print axioms card_pairPlaq

/-- **Off the pair locus, the change of a plaquette density under `k ↦ x` does not read the
variable at `l`**: a diagonal plaquette has holonomy `1`; a plaquette missing `l` does not read it;
a plaquette missing `k` does not change.

DERIVED: `4`, `1` as in `pairPlaq`. -/
theorem wilson_diff_const {l k : WilsonHypercubic.Link 4 (M + 1)} (hlk : l ≠ k)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) (x : SU N) {p : WilsonHypercubic.Plaq 4 (M + 1)}
    (hp : p ∉ pairPlaq M l k) (g g' : SU N) :
    wilsonDensity (wilsonHol (bdT M) p (Function.update (Function.update W k x) l g))
        - wilsonDensity (wilsonHol (bdT M) p (Function.update W l g))
      = wilsonDensity (wilsonHol (bdT M) p (Function.update (Function.update W k x) l g'))
        - wilsonDensity (wilsonHol (bdT M) p (Function.update W l g')) := by
  by_cases hd : p.1.1 = p.1.2
  · simp only [wilsonHol_diag M p hd, sub_self]
  by_cases hl : l ∈ (bdT M p).map Prod.fst
  · have hk : k ∉ (bdT M p).map Prod.fst := fun hk =>
      hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, hl, hk⟩)
    rw [Function.update_comm (Ne.symm hlk) x g W, Function.update_comm (Ne.symm hlk) x g' W]
    have hr := fun (V : WilsonHypercubic.Link 4 (M + 1) → SU N) (y : SU N) =>
      wilsonHol_update_of_not_mem (bdT M) p hk V y
    simp only [hr, sub_self]
  · have hr := fun (V : WilsonHypercubic.Link 4 (M + 1) → SU N) (y : SU N) =>
      wilsonHol_update_of_not_mem (bdT M) p hl V y
    simp only [hr]

#print axioms wilson_diff_const

/-- **Off the mixed terms, the change of a potential term under `k ↦ x` does not read `l`.**

DERIVED: `4`, `1` as in `pairPlaq`. -/
theorem pot_diff_const (P : LocalPot N M) {l k : WilsonHypercubic.Link 4 (M + 1)} (hlk : l ≠ k)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) (x : SU N) {X : P.ι}
    (hX : ¬ (l ∈ P.supp X ∧ k ∈ P.supp X)) (g g' : SU N) :
    P.V X (Function.update (Function.update W k x) l g) - P.V X (Function.update W l g)
      = P.V X (Function.update (Function.update W k x) l g') - P.V X (Function.update W l g') := by
  by_cases hl : l ∈ P.supp X
  · have hk : k ∉ P.supp X := fun hk => hX ⟨hl, hk⟩
    rw [Function.update_comm (Ne.symm hlk) x g W, Function.update_comm (Ne.symm hlk) x g' W]
    have hr := fun (V : WilsonHypercubic.Link 4 (M + 1) → SU N) (y : SU N) => P.reads X V k y hk
    simp only [hr, sub_self]
  · have hr := fun (V : WilsonHypercubic.Link 4 (M + 1) → SU N) (y : SU N) => P.reads X V l y hl
    simp only [hr]

#print axioms pot_diff_const

/-- **The pointwise lemma.** For `l ≠ k`, changing the link `k` to `x` multiplies the weight seen by
the link `l` by `K · exp(h_W(g) + h_V(g))`: `K > 0` does not read `g`,
`|h_W| ≤ 2β n2(l, k)` (each of the `n2` oriented plaquettes through both links has density in
`[0, 2]`) and `|h_V| ≤ 2 mix(l, k)` (each mixed term is bounded by `v X`), uniformly in `W`.

DERIVED: `0` is the excluded colour count and the sign of `β`, `K`; `2` is the length of the density
range `[0, 2]` and the two values a mixed term is compared at; `4`, `1` as in `pairPlaq`. -/
theorem wtV_update_ratio (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (P : LocalPot N M)
    {l k : WilsonHypercubic.Link 4 (M + 1)} (hlk : l ≠ k)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) (x : SU N) :
    ∃ (K : ℝ) (hW hV : SU N → ℝ), 0 < K ∧ (∀ g, |hW g| ≤ 2 * β * n2 M l k) ∧
      (∀ g, |hV g| ≤ 2 * P.mix l k) ∧
      ∀ g, wtV β P (Function.update (Function.update W k x) l g)
        = K * Real.exp (hW g + hV g) * wtV β P (Function.update W l g) := by
  obtain ⟨dW, hdW⟩ : ∃ dW : WilsonHypercubic.Plaq 4 (M + 1) → SU N → ℝ, ∀ p g, dW p g =
      wilsonDensity (wilsonHol (bdT M) p (Function.update (Function.update W k x) l g))
        - wilsonDensity (wilsonHol (bdT M) p (Function.update W l g)) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨dV, hdV⟩ : ∃ dV : P.ι → SU N → ℝ, ∀ X g, dV X g =
      P.V X (Function.update (Function.update W k x) l g) - P.V X (Function.update W l g) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨QX, hQX⟩ : ∃ QX : Finset P.ι,
      QX = Finset.univ.filter (fun X => l ∈ P.supp X ∧ k ∈ P.supp X) := ⟨_, rfl⟩
  refine ⟨Real.exp (-β * ∑ p ∈ (pairPlaq M l k)ᶜ, dW p 1
      + ∑ X ∈ Finset.univ.filter (fun X => ¬ (l ∈ P.supp X ∧ k ∈ P.supp X)), dV X 1),
    fun g => -β * ∑ p ∈ pairPlaq M l k, dW p g, fun g => ∑ X ∈ QX, dV X g,
    Real.exp_pos _, ?_, ?_, ?_⟩
  · intro g
    have h1 : ∀ p, |dW p g| ≤ 2 := fun p => by
      have a1 := wilsonDensity_nonneg hN
        (wilsonHol (bdT M) p (Function.update (Function.update W k x) l g))
      have a2 := wilsonDensity_le_two hN
        (wilsonHol (bdT M) p (Function.update (Function.update W k x) l g))
      have a3 := wilsonDensity_nonneg hN (wilsonHol (bdT M) p (Function.update W l g))
      have a4 := wilsonDensity_le_two hN (wilsonHol (bdT M) p (Function.update W l g))
      rw [hdW, abs_le]
      constructor <;> linarith
    have hs : |∑ p ∈ pairPlaq M l k, dW p g| ≤ 2 * (n2 M l k : ℝ) := by
      calc |∑ p ∈ pairPlaq M l k, dW p g| ≤ ∑ p ∈ pairPlaq M l k, |dW p g| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _p ∈ pairPlaq M l k, (2 : ℝ) := Finset.sum_le_sum fun p _ => h1 p
        _ = 2 * (n2 M l k : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, card_pairPlaq]; ring
    show |-β * ∑ p ∈ pairPlaq M l k, dW p g| ≤ 2 * β * n2 M l k
    rw [abs_mul, abs_neg, abs_of_nonneg hβ]
    calc β * |∑ p ∈ pairPlaq M l k, dW p g| ≤ β * (2 * (n2 M l k : ℝ)) :=
          mul_le_mul_of_nonneg_left hs hβ
      _ = 2 * β * n2 M l k := by ring
  · intro g
    show |∑ X ∈ QX, dV X g| ≤ 2 * P.mix l k
    calc |∑ X ∈ QX, dV X g| ≤ ∑ X ∈ QX, |dV X g| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ X ∈ QX, 2 * P.v X := Finset.sum_le_sum fun X _ => by
          have b1 := abs_le.mp (P.bound X (Function.update (Function.update W k x) l g))
          have b2 := abs_le.mp (P.bound X (Function.update W l g))
          rw [hdV, abs_le]
          constructor <;> linarith
      _ = 2 * P.mix l k := by rw [← Finset.mul_sum, hQX]; rfl
  · intro g
    have hWs : ∑ p, wilsonDensity (wilsonHol (bdT M) p (Function.update (Function.update W k x) l g))
        = ∑ p, wilsonDensity (wilsonHol (bdT M) p (Function.update W l g))
          + (∑ p ∈ pairPlaq M l k, dW p g + ∑ p ∈ (pairPlaq M l k)ᶜ, dW p 1) := by
      have e1 : ∀ p, wilsonDensity (wilsonHol (bdT M) p (Function.update (Function.update W k x) l g))
          = wilsonDensity (wilsonHol (bdT M) p (Function.update W l g)) + dW p g := fun p => by
        rw [hdW]; ring
      have e2 : ∑ p ∈ (pairPlaq M l k)ᶜ, dW p g = ∑ p ∈ (pairPlaq M l k)ᶜ, dW p 1 :=
        Finset.sum_congr rfl fun p hp => by
          rw [hdW, hdW]
          exact wilson_diff_const hlk W x (Finset.mem_compl.mp hp) g 1
      rw [Finset.sum_congr rfl (fun p _ => e1 p), Finset.sum_add_distrib, ← e2,
        Finset.sum_add_sum_compl]
    have hVs : P.tot (Function.update (Function.update W k x) l g)
        = P.tot (Function.update W l g) + (∑ X ∈ QX, dV X g
          + ∑ X ∈ Finset.univ.filter (fun X => ¬ (l ∈ P.supp X ∧ k ∈ P.supp X)), dV X 1) := by
      have e1 : ∀ X, P.V X (Function.update (Function.update W k x) l g)
          = P.V X (Function.update W l g) + dV X g := fun X => by
        rw [hdV]; ring
      have e2 : ∑ X ∈ Finset.univ.filter (fun X => ¬ (l ∈ P.supp X ∧ k ∈ P.supp X)), dV X g
          = ∑ X ∈ Finset.univ.filter (fun X => ¬ (l ∈ P.supp X ∧ k ∈ P.supp X)), dV X 1 :=
        Finset.sum_congr rfl fun X hX => by
          rw [hdV, hdV]
          exact pot_diff_const P hlk W x (Finset.mem_filter.mp hX).2 g 1
      unfold LocalPot.tot
      rw [Finset.sum_congr rfl (fun X _ => e1 X), Finset.sum_add_distrib, ← e2, hQX,
        Finset.sum_filter_add_sum_filter_not]
    unfold wtV
    rw [wt_eq, wt_eq, hWs, hVs]
    simp only [← Real.exp_add]
    congr 1
    ring

#print axioms wtV_update_ratio

end Pointwise

/-! ## 2. The influence matrix of the box -/

section Influence

/-- Continuous functions on `SU(N)` are Haar integrable.

DERIVED: no numeral. -/
theorem integrable_cont {F : SU N → ℝ} (hF : Continuous F) : Integrable F (probHaar (SU N)) := by
  obtain ⟨C, hC⟩ := exists_abs_le hF
  exact integrable_of_abs_le _ hF.measurable hC

#print axioms integrable_cont

/-- **A bounded tilt of a weighted Haar average**: for `ρ > 0`, `A ≤ w ≤ A s²` and `0 ≤ φ ≤ 1`, all
continuous, `|∫φwρ/∫wρ − ∫φρ/∫ρ| ≤ (s − 1)/(s + 1)` (`BoxDobrushin.tilt_core` at `A ∫ρ`).

DERIVED: `0` is the sign; `1` is the unit of `s` and of `φ`; `2` is the square of `s`. -/
theorem tilt_weighted {ρ w φ : SU N → ℝ} (hρ : Continuous ρ) (hw : Continuous w)
    (hφ : Continuous φ) (hρ0 : ∀ g, 0 < ρ g) {A s : ℝ} (hA : 0 < A) (hs : 1 ≤ s)
    (hlo : ∀ g, A ≤ w g) (hhi : ∀ g, w g ≤ A * s ^ 2) (hφ0 : ∀ g, 0 ≤ φ g) (hφ1 : ∀ g, φ g ≤ 1) :
    |(∫ g, φ g * (w g * ρ g) ∂(probHaar (SU N))) / (∫ g, w g * ρ g ∂(probHaar (SU N)))
      - (∫ g, φ g * ρ g ∂(probHaar (SU N))) / (∫ g, ρ g ∂(probHaar (SU N)))|
      ≤ (s - 1) / (s + 1) := by
  have iρ := integrable_cont hρ
  have iφρ := integrable_cont (hφ.mul hρ)
  have iwρ := integrable_cont (hw.mul hρ)
  have iφwρ := integrable_cont (hφ.mul (hw.mul hρ))
  set R := ∫ g, ρ g ∂(probHaar (SU N)) with hR
  set P := ∫ g, φ g * ρ g ∂(probHaar (SU N)) with hP
  set Z := ∫ g, w g * ρ g ∂(probHaar (SU N)) with hZ
  set X := ∫ g, φ g * (w g * ρ g) ∂(probHaar (SU N)) with hX
  obtain ⟨g0, -, hg0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hρ.continuousOn
  have hRpos : 0 < R := by
    have h := integral_mono (integrable_const (ρ g0)) iρ (fun g => hg0 (Set.mem_univ g))
    have hu1 : (probHaar (SU N)).real Set.univ = 1 := by simp [Measure.real, measure_univ]
    simp only [integral_const, smul_eq_mul, hu1, one_mul] at h
    exact lt_of_lt_of_le (hρ0 g0) h
  have hP0 : 0 ≤ P := integral_nonneg fun g => mul_nonneg (hφ0 g) (hρ0 g).le
  have hPR : P ≤ R := integral_mono iφρ iρ fun g => by
    have := mul_le_mul_of_nonneg_right (hφ1 g) (hρ0 g).le
    simpa using this
  have hXhi : X ≤ A * s ^ 2 * P := by
    have h := integral_mono iφwρ (iφρ.const_mul (A * s ^ 2)) fun g => by
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hhi g) (hρ0 g).le) (hφ0 g)
      show φ g * (w g * ρ g) ≤ A * s ^ 2 * (φ g * ρ g)
      nlinarith
    rwa [integral_const_mul] at h
  have hXlo : A * P ≤ X := by
    have h := integral_mono (iφρ.const_mul A) iφwρ fun g => by
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hlo g) (hρ0 g).le) (hφ0 g)
      show A * (φ g * ρ g) ≤ φ g * (w g * ρ g)
      nlinarith
    rwa [integral_const_mul] at h
  have hZX : Z - X = ∫ g, (w g * ρ g - φ g * (w g * ρ g)) ∂(probHaar (SU N)) :=
    (integral_sub iwρ iφwρ).symm
  have hRP : R - P = ∫ g, (ρ g - φ g * ρ g) ∂(probHaar (SU N)) := (integral_sub iρ iφρ).symm
  have hZXlo : A * (R - P) ≤ Z - X := by
    rw [hZX, hRP, ← integral_const_mul]
    refine integral_mono ((iρ.sub iφρ).const_mul A) (iwρ.sub iφwρ) fun g => ?_
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hlo g) (hρ0 g).le)
      (show 0 ≤ 1 - φ g by linarith [hφ1 g])
    show A * (ρ g - φ g * ρ g) ≤ w g * ρ g - φ g * (w g * ρ g)
    nlinarith
  have hZXhi : Z - X ≤ A * s ^ 2 * (R - P) := by
    rw [hZX, hRP, ← integral_const_mul]
    refine integral_mono (iwρ.sub iφwρ) ((iρ.sub iφρ).const_mul (A * s ^ 2)) fun g => ?_
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hhi g) (hρ0 g).le)
      (show 0 ≤ 1 - φ g by linarith [hφ1 g])
    show w g * ρ g - φ g * (w g * ρ g) ≤ A * s ^ 2 * (ρ g - φ g * ρ g)
    nlinarith
  have hX0 : 0 ≤ X := le_trans (mul_nonneg hA.le hP0) hXlo
  have hZX0 : 0 ≤ Z - X := le_trans (mul_nonneg hA.le (by linarith)) hZXlo
  have hZpos : 0 < Z := by
    have : 0 < A * R := mul_pos hA hRpos
    nlinarith
  have hq0 : 0 ≤ P / R := div_nonneg hP0 hRpos.le
  have hq1 : P / R ≤ 1 := (div_le_one hRpos).mpr hPR
  have hAR : 0 < A * R := mul_pos hA hRpos
  have hR0 : R ≠ 0 := hRpos.ne'
  have eP : A * R * s ^ 2 * (P / R) = A * s ^ 2 * P := by first | (field_simp; ring) | field_simp
  have eQ : A * R * (1 - P / R) = A * (R - P) := by first | (field_simp; ring) | field_simp
  have eP' : A * R * s ^ 2 * (1 - P / R) = A * s ^ 2 * (R - P) := by first | (field_simp; ring) | field_simp
  have eQ' : A * R * (1 - (1 - P / R)) = A * P := by first | (field_simp; ring) | field_simp
  have hup : X / (X + (Z - X)) - P / R ≤ (s - 1) / (s + 1) :=
    tilt_core hAR hs hq0 hq1 hX0 (by rw [eP]; exact hXhi) (by rw [eQ]; exact hZXlo)
      (by linarith)
  have hdn : (Z - X) / ((Z - X) + X) - (1 - P / R) ≤ (s - 1) / (s + 1) :=
    tilt_core hAR hs (by linarith) (by linarith) hZX0 (by rw [eP']; exact hZXhi)
      (by rw [eQ']; exact hXlo) (by linarith)
  have e1 : X + (Z - X) = Z := by ring
  have e2 : (Z - X) / ((Z - X) + X) = 1 - X / Z := by
    rw [show (Z - X) + X = Z by ring]
    field_simp
  rw [e1] at hup
  rw [e2] at hdn
  rw [abs_le]
  constructor <;> linarith

#print axioms tilt_weighted

variable {M : ℕ}

/-- `wtV` is positive.

DERIVED: `0` is the sign asserted. -/
theorem wtV_pos (β : ℝ) (P : LocalPot N M) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    0 < wtV β P W := mul_pos (wt_pos _ _ _) (Real.exp_pos _)

#print axioms wtV_pos

/-- `wtV` is continuous.

DERIVED: no numeral. -/
theorem continuous_wtV (β : ℝ) (P : LocalPot N M) : Continuous (wtV (N := N) β P) :=
  (continuous_wt _ _).mul (Real.continuous_exp.comp P.continuous_tot)

#print axioms continuous_wtV

/-- **The influence of the link `k` on the heat bath of the box at `l`**: for every continuous
`0 ≤ φ ≤ 1` of the link variable, changing `k` moves its heat-bath mean at `l` by at most
`q(e^{2β n2(l,k)}) + q(e^{2 mix(l,k)})` (`wtV_update_ratio`, `tilt_weighted`, `qfun_mul_le`).

DERIVED: `0` is the excluded colour count and the sign of `β`; `2` as in `wtV_update_ratio` and the
square in `A s²`; `1` the bounds on `φ`; `4`, `1` as in `pairPlaq`. -/
theorem wAvg_link_infl (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (P : LocalPot N M)
    {l k : WilsonHypercubic.Link 4 (M + 1)} (hlk : l ≠ k)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) (x : SU N) {φ : SU N → ℝ} (hφ : Continuous φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ1 : ∀ g, φ g ≤ 1) :
    |wAvg (wtV β P) l (fun V => φ (V l)) (Function.update W k x)
        - wAvg (wtV β P) l (fun V => φ (V l)) W|
      ≤ qfun (Real.exp (2 * β * n2 M l k)) + qfun (Real.exp (2 * P.mix l k)) := by
  obtain ⟨K, hW, hV, hK, hWb, hVb, hrat⟩ := wtV_update_ratio hN hβ P hlk W x
  set a : ℝ := 2 * β * n2 M l k with ha
  set b : ℝ := 2 * P.mix l k with hb
  have ha0 : 0 ≤ a := le_trans (abs_nonneg _) (hWb 1)
  have hb0 : 0 ≤ b := le_trans (abs_nonneg _) (hVb 1)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : SU N → ℝ, ∀ g, ρ g = wtV β P (Function.update W l g) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : SU N → ℝ, ∀ g, w g = Real.exp (hW g + hV g) := ⟨_, fun _ => rfl⟩
  have hρ0 : ∀ g, 0 < ρ g := fun g => by rw [hρ]; exact wtV_pos β P _
  have hρc : Continuous ρ := by
    have : ρ = fun g => wtV β P (Function.update W l g) := funext hρ
    rw [this]
    exact (continuous_wtV β P).comp (continuous_const.update l continuous_id)
  have hw' : ∀ g, w g = wtV β P (Function.update (Function.update W k x) l g) / (K * ρ g) :=
    fun g => by
      rw [hrat g, hw, hρ]
      field_simp [(wtV_pos β P (Function.update W l g)).ne']
  have hwc : Continuous w := by
    have : w = fun g => wtV β P (Function.update (Function.update W k x) l g) / (K * ρ g) :=
      funext hw'
    rw [this]
    exact ((continuous_wtV β P).comp (continuous_const.update l continuous_id)).div
      (continuous_const.mul hρc) (fun g => (mul_pos hK (hρ0 g)).ne')
  have hlo : ∀ g, Real.exp (-(a + b)) ≤ w g := fun g => by
    rw [hw]
    apply Real.exp_le_exp.2
    have h1 := (abs_le.1 (hWb g)).1
    have h2 := (abs_le.1 (hVb g)).1
    linarith
  have hhi : ∀ g, w g ≤ Real.exp (-(a + b)) * Real.exp (a + b) ^ 2 := fun g => by
    rw [hw, sq, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 := (abs_le.1 (hWb g)).2
    have h2 := (abs_le.1 (hVb g)).2
    linarith
  have e0 : wAvg (wtV β P) l (fun V => φ (V l)) W
      = (∫ g, φ g * ρ g ∂(probHaar (SU N))) / (∫ g, ρ g ∂(probHaar (SU N))) := by
    unfold wAvg wNum wPart
    simp only [Function.update_self, ← hρ]
  have e1 : wAvg (wtV β P) l (fun V => φ (V l)) (Function.update W k x)
      = (∫ g, φ g * (w g * ρ g) ∂(probHaar (SU N))) / (∫ g, w g * ρ g ∂(probHaar (SU N))) := by
    unfold wAvg wNum wPart
    have r2 : ∀ g, wtV β P (Function.update (Function.update W k x) l g) = K * (w g * ρ g) :=
      fun g => by rw [hrat g, hw, hρ]; ring
    have r1' : ∀ g, φ g * (K * (w g * ρ g)) = K * (φ g * (w g * ρ g)) := fun g => by ring
    simp only [Function.update_self, r2]
    simp only [r1', integral_const_mul]
    exact mul_div_mul_left _ _ hK.ne'
  rw [e0, e1]
  refine (tilt_weighted hρc hwc hφ hρ0 (Real.exp_pos _) (Real.one_le_exp (by linarith)) hlo hhi
    hφ0 hφ1).trans ?_
  have := qfun_mul_le (Real.one_le_exp ha0) (Real.one_le_exp hb0)
  rw [← Real.exp_add] at this
  exact this

#print axioms wAvg_link_infl

/-- **The influence matrix of the box**: `C(l, k) = q(e^{2β n2(l,k)}) + q(e^{2 mix(l,k)})` off the
diagonal, `0` on it.

DERIVED: `0` is the diagonal entry; `2` as in `wAvg_link_infl`; `4`, `1` as in `pairPlaq`. -/
def boxInfl (β : ℝ) (P : LocalPot N M) (l k : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  if l = k then 0 else qfun (Real.exp (2 * β * n2 M l k)) + qfun (Real.exp (2 * P.mix l k))

/-- `q` is non-negative at `s ≥ 1`.

DERIVED: `0` the sign; `1` the unit. -/
theorem qfun_nonneg {s : ℝ} (hs : 1 ≤ s) : 0 ≤ qfun s := by
  unfold qfun
  exact div_nonneg (by linarith) (by linarith)

#print axioms qfun_nonneg

/-- The mixed weight is non-negative.

DERIVED: `0` the sign. -/
theorem mix_nonneg (P : LocalPot N M) (l k : WilsonHypercubic.Link 4 (M + 1)) : 0 ≤ P.mix l k :=
  Finset.sum_nonneg fun X _ => P.v_nonneg X

#print axioms mix_nonneg

/-- The box influence matrix is non-negative.

DERIVED: `0` the sign; `2`, `4`, `1` as in `boxInfl`. -/
theorem boxInfl_nonneg {β : ℝ} (hβ : 0 ≤ β) (P : LocalPot N M)
    (l k : WilsonHypercubic.Link 4 (M + 1)) : 0 ≤ boxInfl β P l k := by
  unfold boxInfl
  split_ifs
  · exact le_rfl
  · exact add_nonneg (qfun_nonneg (Real.one_le_exp (by positivity)))
      (qfun_nonneg (Real.one_le_exp (by linarith [mix_nonneg P l k])))

#print axioms boxInfl_nonneg

/-- **One Wilson pair at multiplicity `n2`**: `q(e^{2β n2}) ≤ (n2/2) q(e^{4β})` for
`n2 ∈ {0, 2, 4}` (`PairCount.n2_cases`; `q(e^{8β}) ≤ 2 q(e^{4β})` by `qfun_mul_le`).

DERIVED: `1` the least `M`; `2`, `4` the multiplicities and `4 = 2 · 2`; `8 = 2 · 4`. -/
theorem wilsonPair_mult {β : ℝ} (hβ : 0 ≤ β) (hM : 1 ≤ M) {l k : WilsonHypercubic.Link 4 (M + 1)}
    (hlk : l ≠ k) :
    qfun (Real.exp (2 * β * n2 M l k)) ≤ (n2 M l k : ℝ) / 2 * qfun (Real.exp (4 * β)) := by
  rcases n2_cases hM hlk with h | h | h <;> rw [h]
  · simp [qfun]
  · norm_num
    ring_nf
    exact le_rfl
  · have h4 : Real.exp (2 * β * ((4 : ℕ) : ℝ)) = Real.exp (4 * β) * Real.exp (4 * β) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [h4]
    have := qfun_mul_le (Real.one_le_exp (show 0 ≤ 4 * β by linarith))
      (Real.one_le_exp (show 0 ≤ 4 * β by linarith))
    push_cast
    linarith

#print axioms wilsonPair_mult

/-- **The row sum of the box influence matrix is at most `39/40`** at Lean `β ≤ 1/40` and local
norm `≤ 1/16`: the Wilson part is `≤ (Σ n2 / 2) q(e^{4β}) ≤ 18 · 53/1053` (`PairCount.sum_n2_le`,
`BoxDobrushin.wilsonPair_le`), the potential part `≤ (35/32) Σ mix ≤ (35/32)/16`
(`LocalPotential.sum_mix_le`, `BoxDobrushin.potPair_le`).

DERIVED: `1` the least `M`; `1/40`, `1/16` the coupling and norm bounds; `36` the pair count of
`sum_n2_le`, `18 = 36/2`; `53/1053`, `35/32` from `wilsonPair_le`, `potPair_le`;
`39/40 ≥ 18 · 53/1053 + 35/512 = 0.97434…`. -/
theorem rowSum_box {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 40) (hM : 1 ≤ M) (P : LocalPot N M)
    (l : WilsonHypercubic.Link 4 (M + 1)) (hnorm : P.norm l ≤ 1 / 16) :
    ∑ k, boxInfl β P l k ≤ 39 / 40 := by
  have hsplit : ∑ k, boxInfl β P l k = ∑ k ∈ Finset.univ.erase l,
      (qfun (Real.exp (2 * β * n2 M l k)) + qfun (Real.exp (2 * P.mix l k))) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
    simp only [boxInfl, ↓reduceIte, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hk))]
  rw [hsplit, Finset.sum_add_distrib]
  have hq4 := wilsonPair_le hβ0 hβ
  have hq40 : 0 ≤ qfun (Real.exp (4 * β)) := qfun_nonneg (Real.one_le_exp (by linarith))
  have hWs : ∑ k ∈ Finset.univ.erase l, qfun (Real.exp (2 * β * n2 M l k))
      ≤ 18 * (53 / 1053) := by
    calc ∑ k ∈ Finset.univ.erase l, qfun (Real.exp (2 * β * n2 M l k))
        ≤ ∑ k ∈ Finset.univ.erase l, (n2 M l k : ℝ) / 2 * qfun (Real.exp (4 * β)) :=
          Finset.sum_le_sum fun k hk =>
            wilsonPair_mult hβ0 hM (Ne.symm (Finset.ne_of_mem_erase hk))
      _ = (∑ k ∈ Finset.univ.erase l, (n2 M l k : ℝ)) / 2 * qfun (Real.exp (4 * β)) := by
          rw [Finset.sum_div, Finset.sum_mul]
      _ ≤ 36 / 2 * (53 / 1053) := by
          have h36 : (∑ k ∈ Finset.univ.erase l, (n2 M l k : ℝ)) ≤ 36 := by
            exact_mod_cast sum_n2_le hM l
          have hn0 : 0 ≤ (∑ k ∈ Finset.univ.erase l, (n2 M l k : ℝ)) :=
            Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
          have := mul_le_mul (div_le_div_of_nonneg_right h36 (by norm_num : (0 : ℝ) ≤ 2)) hq4 hq40
            (by norm_num)
          linarith
      _ = 18 * (53 / 1053) := by norm_num
  have hmix : ∑ k ∈ Finset.univ.erase l, P.mix l k ≤ 1 / 16 := (sum_mix_le P l).trans hnorm
  have hVs : ∑ k ∈ Finset.univ.erase l, qfun (Real.exp (2 * P.mix l k)) ≤ 35 / 32 * (1 / 16) := by
    have hle : ∀ k ∈ Finset.univ.erase l, P.mix l k ≤ 1 / 16 := fun k hk =>
      le_trans (Finset.single_le_sum (fun j _ => mix_nonneg P l j) hk) hmix
    calc ∑ k ∈ Finset.univ.erase l, qfun (Real.exp (2 * P.mix l k))
        ≤ ∑ k ∈ Finset.univ.erase l, 35 / 32 * P.mix l k :=
          Finset.sum_le_sum fun k hk => potPair_le (mix_nonneg P l k) (hle k hk)
      _ = 35 / 32 * ∑ k ∈ Finset.univ.erase l, P.mix l k := by rw [Finset.mul_sum]
      _ ≤ 35 / 32 * (1 / 16) := by linarith
  linarith

#print axioms rowSum_box

end Influence

/-! ## 3. Dobrushin's comparison in oscillation form -/

section Oscillation

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **`v` bounds the single-link oscillations of `f`**: changing the link `k` moves `f` by at most
`v k`. -/
def OscLe (f : (Lk → SU N) → ℝ) (v : Lk → ℝ) : Prop :=
  ∀ W k g, |f (Function.update W k g) - f W| ≤ v k

/-- **`C` is an influence matrix of the heat baths of `Φ`**: changing the link `k ≠ l` moves the
heat-bath mean at `l` of every continuous `[0, 1]`-valued function of the variable at `l` by at most
`C l k`.

DERIVED: `0`, `1` are the range of the test functions. -/
def Infl (Φ : (Lk → SU N) → ℝ) (C : Lk → Lk → ℝ) : Prop :=
  ∀ l k, l ≠ k → ∀ (W : Lk → SU N) (x : SU N) (φ : SU N → ℝ), Continuous φ → (∀ e, 0 ≤ φ e) →
    (∀ e, φ e ≤ 1) →
    |wAvg Φ l (fun V => φ (V l)) (Function.update W k x) - wAvg Φ l (fun V => φ (V l)) W| ≤ C l k

/-- The oscillation vector after the heat bath at `l`: `0` at `l`, `v k + C l k · v l` elsewhere.

DERIVED: `0` is the oscillation at the averaged link. -/
def oscStep (C : Lk → Lk → ℝ) (l : Lk) (v : Lk → ℝ) : Lk → ℝ :=
  fun k => if k = l then 0 else v k + C l k * v l

/-- **The box weight has the influence matrix `boxInfl`** (`wAvg_link_infl`).

DERIVED: `0` the excluded colour count and the sign of `β`; `4`, `1` as in `pairPlaq`. -/
theorem infl_wtV (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {M : ℕ} (P : LocalPot N M) :
    Infl (wtV β P) (boxInfl β P) := by
  intro l k hlk W x φ hφ hφ0 hφ1
  have h := wAvg_link_infl hN hβ P hlk W x hφ hφ0 hφ1
  unfold boxInfl
  rwa [if_neg hlk]

#print axioms infl_wtV

omit [Fintype Lk] in
/-- An oscillation bound is non-negative.

DERIVED: `0` the sign; `1` the group identity used as a configuration. -/
theorem OscLe.nonneg {f : (Lk → SU N) → ℝ} {v : Lk → ℝ} (hv : OscLe f v) (k : Lk) : 0 ≤ v k := by
  have h := hv (fun _ => 1) k 1
  have e : Function.update (fun _ : Lk => (1 : SU N)) k 1 = fun _ => 1 := by
    funext j; by_cases hj : j = k <;> simp [Function.update, hj]
  rw [e, sub_self, abs_zero] at h
  exact h

#print axioms OscLe.nonneg

omit [Fintype Lk] in
/-- **The heat bath is a normalised average**: two continuous functions within `c` of each other on
the fibre of `l` at `W` have heat-bath means within `c`.

DERIVED: no numeral. -/
theorem wAvg_sub_le {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) (l : Lk)
    {f h : (Lk → SU N) → ℝ} (hf : Continuous f) (hh : Continuous h) (W : Lk → SU N) {c : ℝ}
    (hc : ∀ g, |f (Function.update W l g) - h (Function.update W l g)| ≤ c) :
    |wAvg Φ l f W - wAvg Φ l h W| ≤ c := by
  have hu : Continuous (fun g : SU N => Function.update W l g) := continuous_const.update l continuous_id
  have iρ : Integrable (fun g => Φ (Function.update W l g)) (probHaar (SU N)) :=
    integrable_cont (hcont.comp hu)
  have ifρ : Integrable (fun g => f (Function.update W l g) * Φ (Function.update W l g))
      (probHaar (SU N)) := integrable_cont ((hf.comp hu).mul (hcont.comp hu))
  have ihρ : Integrable (fun g => h (Function.update W l g) * Φ (Function.update W l g))
      (probHaar (SU N)) := integrable_cont ((hh.comp hu).mul (hcont.comp hu))
  have hR := wPart_pos hpos hcont l W
  unfold wAvg
  rw [div_sub_div_same, abs_div, abs_of_pos hR, div_le_iff₀ hR]
  unfold wNum wPart
  rw [← integral_sub ifρ ihρ, ← integral_const_mul, abs_le]
  constructor
  · rw [← integral_neg]
    refine integral_mono (iρ.const_mul c).neg (ifρ.sub ihρ) fun g => ?_
    have h1 := (abs_le.mp (hc g)).1
    have h2 := hpos (Function.update W l g)
    show -(c * Φ (Function.update W l g)) ≤ f (Function.update W l g) * Φ (Function.update W l g)
      - h (Function.update W l g) * Φ (Function.update W l g)
    nlinarith
  · refine integral_mono (ifρ.sub ihρ) (iρ.const_mul c) fun g => ?_
    have h1 := (abs_le.mp (hc g)).2
    have h2 := hpos (Function.update W l g)
    show f (Function.update W l g) * Φ (Function.update W l g)
      - h (Function.update W l g) * Φ (Function.update W l g) ≤ c * Φ (Function.update W l g)
    nlinarith

#print axioms wAvg_sub_le

omit [Fintype Lk] in
/-- **The heat bath is affine**: `wAvg (a + b h) = a + b wAvg h` for continuous `h`.

DERIVED: no numeral. -/
theorem wAvg_affine {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) (l : Lk)
    {h : (Lk → SU N) → ℝ} (hh : Continuous h) (a b : ℝ) (W : Lk → SU N) :
    wAvg Φ l (fun V => a + b * h V) W = a + b * wAvg Φ l h W := by
  have hu : Continuous (fun g : SU N => Function.update W l g) := continuous_const.update l continuous_id
  have iρ : Integrable (fun g => Φ (Function.update W l g)) (probHaar (SU N)) :=
    integrable_cont (hcont.comp hu)
  have ihρ : Integrable (fun g => h (Function.update W l g) * Φ (Function.update W l g))
      (probHaar (SU N)) := integrable_cont ((hh.comp hu).mul (hcont.comp hu))
  have hR := (wPart_pos hpos hcont l W).ne'
  unfold wAvg wNum
  have e : ∀ g, (a + b * h (Function.update W l g)) * Φ (Function.update W l g)
      = a * Φ (Function.update W l g) + b * (h (Function.update W l g) * Φ (Function.update W l g)) :=
    fun g => by ring
  simp only [e]
  rw [integral_add (iρ.const_mul a) (ihρ.const_mul b), integral_const_mul, integral_const_mul]
  unfold wPart
  unfold wPart at hR
  field_simp

#print axioms wAvg_affine

/-- **Dobrushin's comparison, one heat bath (Föllmer's step).** If `v` bounds the single-link
oscillations of a continuous `f` and `C ≥ 0` is an influence matrix of the positive continuous weight
`Φ`, then `oscStep C l v` bounds those of the heat bath of `f` at `l`.

DERIVED: `0` the sign of `C` and the oscillation at `l`; `1` the range of the rescaled fibre
function. -/
theorem osc_step {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    {C : Lk → Lk → ℝ} (hC : Infl Φ C) {f : (Lk → SU N) → ℝ} (hf : Continuous f)
    {v : Lk → ℝ} (hv : OscLe f v) (l : Lk) : OscLe (wAvg Φ l f) (oscStep C l v) := by
  intro W k x
  unfold oscStep
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, wAvg_update, sub_self, abs_zero]
  rw [if_neg hkl]
  have hlk : l ≠ k := Ne.symm hkl
  -- the fibre function of `f` at `W`
  obtain ⟨ψ, hψ⟩ : ∃ ψ : SU N → ℝ, ∀ g, ψ g = f (Function.update W l g) := ⟨_, fun _ => rfl⟩
  have hu : Continuous (fun g : SU N => Function.update W l g) := continuous_const.update l continuous_id
  have hψc : Continuous ψ := by
    have : ψ = fun g => f (Function.update W l g) := funext hψ
    rw [this]; exact hf.comp hu
  have hF : Continuous (fun V : Lk → SU N => ψ (V l)) := hψc.comp (continuous_apply l)
  -- step 1: replace `f` by its fibre function at `W`, at cost `v k`
  have s1 : |wAvg Φ l f (Function.update W k x) - wAvg Φ l (fun V => ψ (V l)) (Function.update W k x)|
      ≤ v k := by
    refine wAvg_sub_le hpos hcont l hf hF _ fun g => ?_
    rw [Function.update_self, hψ, Function.update_comm hkl x g W]
    exact hv _ k x
  have s0 : wAvg Φ l (fun V => ψ (V l)) W = wAvg Φ l f W := by
    unfold wAvg wNum
    simp only [Function.update_self, hψ]
  -- step 2: the fibre function has range in `[m, m + v l]`
  obtain ⟨g0, -, hg0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hψc.continuousOn
  have hmin : ∀ g, ψ g0 ≤ ψ g := fun g => hg0 (Set.mem_univ g)
  have hrng : ∀ g, ψ g - ψ g0 ≤ v l := fun g => by
    have h := hv (Function.update W l g0) l g
    rw [Function.update_idem, ← hψ, ← hψ] at h
    exact (le_abs_self _).trans h
  have hvl : 0 ≤ v l := hv.nonneg l
  have hC0 : 0 ≤ C l k := by
    have h := hC l k hlk W x (fun _ => 0) continuous_const (fun _ => le_rfl) (fun _ => zero_le_one)
    exact (abs_nonneg _).trans h
  have s2 : |wAvg Φ l (fun V => ψ (V l)) (Function.update W k x) - wAvg Φ l (fun V => ψ (V l)) W|
      ≤ C l k * v l := by
    rcases hvl.eq_or_lt with h0 | hpos'
    · have hconst : ∀ g, ψ g = ψ g0 := fun g => le_antisymm (by linarith [hrng g]) (hmin g)
      have e : (fun V : Lk → SU N => ψ (V l)) = fun V => ψ g0 + 0 * ψ (V l) := by
        funext V; rw [hconst]; ring
      rw [e, wAvg_affine hpos hcont l hF, wAvg_affine hpos hcont l hF]
      simp only [zero_mul, add_zero, sub_self, abs_zero]
      exact mul_nonneg hC0 hvl
    · obtain ⟨φ, hφ⟩ : ∃ φ : SU N → ℝ, ∀ g, φ g = (ψ g - ψ g0) / v l := ⟨_, fun _ => rfl⟩
      have hφc : Continuous φ := by
        have : φ = fun g => (ψ g - ψ g0) / v l := funext hφ
        rw [this]; exact (hψc.sub continuous_const).div_const _
      have hφ0 : ∀ g, 0 ≤ φ g := fun g => by
        rw [hφ]; exact div_nonneg (by linarith [hmin g]) hvl
      have hφ1 : ∀ g, φ g ≤ 1 := fun g => by
        rw [hφ, div_le_one hpos']; exact hrng g
      have e : (fun V : Lk → SU N => ψ (V l)) = fun V => ψ g0 + v l * φ (V l) := by
        funext V; rw [hφ]; field_simp; ring
      have hφF : Continuous (fun V : Lk → SU N => φ (V l)) := hφc.comp (continuous_apply l)
      rw [e, wAvg_affine hpos hcont l hφF, wAvg_affine hpos hcont l hφF]
      have h := hC l k hlk W x φ hφc hφ0 hφ1
      rw [show ψ g0 + v l * wAvg Φ l (fun V => φ (V l)) (Function.update W k x)
          - (ψ g0 + v l * wAvg Φ l (fun V => φ (V l)) W)
          = v l * (wAvg Φ l (fun V => φ (V l)) (Function.update W k x)
            - wAvg Φ l (fun V => φ (V l)) W) by ring, abs_mul, abs_of_nonneg hvl]
      nlinarith
  rw [← s0]
  calc |wAvg Φ l f (Function.update W k x) - wAvg Φ l (fun V => ψ (V l)) W|
      ≤ |wAvg Φ l f (Function.update W k x) - wAvg Φ l (fun V => ψ (V l)) (Function.update W k x)|
        + |wAvg Φ l (fun V => ψ (V l)) (Function.update W k x) - wAvg Φ l (fun V => ψ (V l)) W| :=
        abs_sub_le _ _ _
    _ ≤ v k + C l k * v l := by linarith

#print axioms osc_step

end Oscillation

/-! ## 4. Sweeps and the uniqueness of the heat-bath-invariant state -/

section Sweep

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **The sweep along a list of links**: the heat baths at the links of `L`, in order. -/
def sweep (Φ : (Lk → SU N) → ℝ) : List Lk → ((Lk → SU N) → ℝ) → ((Lk → SU N) → ℝ)
  | [], f => f
  | l :: L, f => sweep Φ L (wAvg Φ l f)

/-- A sweep keeps continuity (`WeightedHeatBath.continuous_wAvg`).

DERIVED: no numeral. -/
theorem continuous_sweep {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) :
    ∀ (L : List Lk) {f : (Lk → SU N) → ℝ}, Continuous f → Continuous (sweep Φ L f)
  | [], _, hf => hf
  | l :: L, _, hf => continuous_sweep hpos hcont L (continuous_wAvg hpos hcont l hf)

#print axioms continuous_sweep

/-- **The oscillation budget along a sweep.** Let `C ≥ 0` be an influence matrix with row sums
`≤ α ≤ 1`. If `u` bounds the oscillations of `f`, `u ≥ v` off a set `S` of links already swept and
`Σ u ≤ α Σ_S v + Σ_{Sᶜ} v`, then after the sweep along `L` there is a bound `u'` with the same three
properties for `S ∪ L`.

DERIVED: `0` the sign; `1` the bound on `α`. -/
theorem osc_sweep {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    {C : Lk → Lk → ℝ} (hC : Infl Φ C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα1 : α ≤ 1) (v : Lk → ℝ) :
    ∀ (L : List Lk) (S : Finset Lk) (f : (Lk → SU N) → ℝ) (u : Lk → ℝ), Continuous f →
      OscLe f u → (∀ k ∉ S, v k ≤ u k) → ∑ k, u k ≤ α * ∑ k ∈ S, v k + ∑ k ∈ Sᶜ, v k →
      ∃ u' : Lk → ℝ, OscLe (sweep Φ L f) u' ∧ (∀ k ∉ S ∪ L.toFinset, v k ≤ u' k) ∧
        ∑ k, u' k ≤ α * ∑ k ∈ S ∪ L.toFinset, v k + ∑ k ∈ (S ∪ L.toFinset)ᶜ, v k
  | [], S, f, u, _, hu, hS, hsum => ⟨u, hu, by simpa using hS, by simpa using hsum⟩
  | l :: L, S, f, u, hf, hu, hS, hsum => by
    have hu0 : ∀ k, 0 ≤ u k := hu.nonneg
    set u1 := oscStep C l u with hu1
    have hosc : OscLe (wAvg Φ l f) u1 := osc_step hpos hcont hC hf hu l
    have hS1 : ∀ k ∉ insert l S, v k ≤ u1 k := fun k hk => by
      have hkl : k ≠ l := fun h => hk (h ▸ Finset.mem_insert_self l S)
      have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
      simp only [hu1, oscStep, if_neg hkl]
      have := mul_nonneg (hC0 l k) (hu0 l)
      linarith [hS k hkS]
    -- the total after one heat bath
    have htot : ∑ k, u1 k ≤ ∑ k, u k - (1 - α) * u l := by
      have e : ∑ k, u1 k = ∑ k ∈ Finset.univ.erase l, (u k + C l k * u l) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
        simp only [hu1, oscStep, ↓reduceIte, zero_add]
        exact Finset.sum_congr rfl fun k hk => by rw [if_neg (Finset.ne_of_mem_erase hk)]
      have e2 : ∑ k ∈ Finset.univ.erase l, (u k + C l k * u l)
          = (∑ k, u k - u l) + (∑ k ∈ Finset.univ.erase l, C l k) * u l := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.add_sum_erase _ u (Finset.mem_univ l)]
        ring
      have hCe : ∑ k ∈ Finset.univ.erase l, C l k ≤ α := by
        refine le_trans ?_ (hrow l)
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
        linarith [hC0 l l]
      rw [e, e2]
      nlinarith [hu0 l]
    have hsum1 : ∑ k, u1 k ≤ α * ∑ k ∈ insert l S, v k + ∑ k ∈ (insert l S)ᶜ, v k := by
      by_cases hlS : l ∈ S
      · rw [Finset.insert_eq_of_mem hlS]
        nlinarith [hu0 l]
      · rw [Finset.sum_insert hlS, Finset.compl_insert]
        have hc : ∑ k ∈ Sᶜ, v k = v l + ∑ k ∈ Sᶜ.erase l, v k :=
          (Finset.add_sum_erase _ _ (Finset.mem_compl.mpr hlS)).symm
        rw [hc] at hsum
        have := hS l hlS
        nlinarith
    obtain ⟨u', h1, h2, h3⟩ := osc_sweep hpos hcont hC hC0 hrow hα1 v L (insert l S) (wAvg Φ l f) u1
      (continuous_wAvg hpos hcont l hf) hosc hS1 hsum1
    have eS : insert l S ∪ L.toFinset = S ∪ (l :: L).toFinset := by
      rw [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
    rw [eS] at h2 h3
    exact ⟨u', h1, h2, h3⟩

#print axioms osc_sweep

/-- **A full sweep contracts the total oscillation by `α`**: if `L` visits every link and `v` bounds
the oscillations of a continuous `f`, the sweep has a bound `u'` with `Σ u' ≤ α Σ v`.

DERIVED: `1` the bound on `α`. -/
theorem osc_sweep_full {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    {C : Lk → Lk → ℝ} (hC : Infl Φ C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα1 : α ≤ 1) {L : List Lk} (hL : ∀ l, l ∈ L)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) {v : Lk → ℝ} (hv : OscLe f v) :
    ∃ u' : Lk → ℝ, OscLe (sweep Φ L f) u' ∧ ∑ k, u' k ≤ α * ∑ k, v k := by
  obtain ⟨u', h1, -, h3⟩ := osc_sweep hpos hcont hC hC0 hrow hα1 v L ∅ f v hf hv
    (fun _ _ => le_rfl) (by simp)
  have hU : (∅ : Finset Lk) ∪ L.toFinset = Finset.univ := by
    ext l; simp [hL l]
  rw [hU, Finset.compl_univ, Finset.sum_empty, add_zero] at h3
  exact ⟨u', h1, h3⟩

#print axioms osc_sweep_full

/-- **`n` full sweeps leave total oscillation `≤ αⁿ Σ v`.**

DERIVED: `0` the sign of `α`; `1` the bound on `α`. -/
theorem osc_iter {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    {C : Lk → Lk → ℝ} (hC : Infl Φ C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {L : List Lk} (hL : ∀ l, l ∈ L) :
    ∀ (n : ℕ) {f : (Lk → SU N) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, OscLe f v →
      ∃ u : Lk → ℝ, OscLe ((sweep Φ L)^[n] f) u ∧ ∑ k, u k ≤ α ^ n * ∑ k, v k
  | 0, _, _, v, hv => ⟨v, hv, by simp⟩
  | n + 1, f, hf, v, hv => by
    obtain ⟨u1, h1, h1s⟩ := osc_sweep_full hpos hcont hC hC0 hrow hα1 hL hf hv
    obtain ⟨u, hu, hus⟩ := osc_iter hpos hcont hC hC0 hrow hα0 hα1 hL n
      (continuous_sweep hpos hcont L hf) h1
    refine ⟨u, by rwa [Function.iterate_succ_apply], hus.trans ?_⟩
    rw [pow_succ]
    have := mul_le_mul_of_nonneg_left h1s (pow_nonneg hα0 n)
    linarith

#print axioms osc_iter

omit [Fintype Lk] in
/-- **Oscillations add up**: changing the links of a finite set `s` one at a time moves `F` by at
most `Σ_{k ∈ s} u k`.

DERIVED: no numeral. -/
theorem abs_sub_le_osc_finset {F : (Lk → SU N) → ℝ} {u : Lk → ℝ} (hu : OscLe F u)
    (W W' : Lk → SU N) (s : Finset Lk) :
    |F W - F (fun k => if k ∈ s then W' k else W k)| ≤ ∑ k ∈ s, u k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have e : (fun k => if k ∈ insert a s then W' k else W k)
        = Function.update (fun k => if k ∈ s then W' k else W k) a (W' a) := by
      funext k
      by_cases hk : k = a
      · subst hk; simp
      · simp [Function.update, hk]
    rw [e, Finset.sum_insert ha]
    have h2 := hu (fun k => if k ∈ s then W' k else W k) a (W' a)
    calc |F W - F (Function.update (fun k => if k ∈ s then W' k else W k) a (W' a))|
        ≤ |F W - F (fun k => if k ∈ s then W' k else W k)|
          + |F (fun k => if k ∈ s then W' k else W k)
            - F (Function.update (fun k => if k ∈ s then W' k else W k) a (W' a))| :=
          abs_sub_le _ _ _
      _ ≤ ∑ k ∈ s, u k + u a := by rw [abs_sub_comm] at h2; linarith
      _ = u a + ∑ k ∈ s, u k := by ring

#print axioms abs_sub_le_osc_finset

/-- **Total oscillation bounds the range**: `|F W − F W'| ≤ Σ u`.

DERIVED: no numeral. -/
theorem abs_sub_le_sum_osc {F : (Lk → SU N) → ℝ} {u : Lk → ℝ} (hu : OscLe F u)
    (W W' : Lk → SU N) : |F W - F W'| ≤ ∑ k, u k := by
  have h := abs_sub_le_osc_finset hu W W' Finset.univ
  simpa using h

#print axioms abs_sub_le_sum_osc

/-- **Mixing of the heat-bath sweep**: under the influence hypotheses, after `n` full sweeps a
continuous `f` with oscillation bound `v` varies by at most `αⁿ Σ v` over all configurations.

DERIVED: `0`, `1` as in `osc_iter`. -/
theorem sweep_mixing {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    {C : Lk → Lk → ℝ} (hC : Infl Φ C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {L : List Lk} (hL : ∀ l, l ∈ L)
    (n : ℕ) {f : (Lk → SU N) → ℝ} (hf : Continuous f) {v : Lk → ℝ} (hv : OscLe f v)
    (W W' : Lk → SU N) :
    |(sweep Φ L)^[n] f W - (sweep Φ L)^[n] f W'| ≤ α ^ n * ∑ k, v k := by
  obtain ⟨u, hu, hus⟩ := osc_iter hpos hcont hC hC0 hrow hα0 hα1 hL n hf hv
  exact (abs_sub_le_sum_osc hu W W').trans hus

#print axioms sweep_mixing

/-- A continuous function on the compact configuration space has a finite oscillation bound.

DERIVED: `2` the two values compared. -/
theorem oscLe_of_continuous {f : (Lk → SU N) → ℝ} (hf : Continuous f) :
    ∃ v : Lk → ℝ, OscLe f v := by
  obtain ⟨B, hB⟩ := exists_abs_le hf
  refine ⟨fun _ => 2 * B, fun W k g => ?_⟩
  have h1 := abs_le.mp (hB (Function.update W k g))
  have h2 := abs_le.mp (hB W)
  rw [abs_le]
  constructor <;> linarith

#print axioms oscLe_of_continuous

/-- The `n`-fold full sweep as a map of continuous observables.

DERIVED: no numeral. -/
def sweepC {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) (L : List Lk)
    (n : ℕ) (f : C(Lk → SU N, ℝ)) : C(Lk → SU N, ℝ) :=
  ⟨(sweep Φ L)^[n] f, by
    induction n with
    | zero => exact f.continuous
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact continuous_sweep hpos hcont L ih⟩

/-- A state invariant under every single heat bath is invariant under every sweep.

DERIVED: no numeral. -/
theorem state_sweep {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    (ν : DLRLimit.State (Lk → SU N))
    (hν : ∀ l (f : C(Lk → SU N, ℝ)),
      ν ⟨wAvg Φ l f, continuous_wAvg hpos hcont l f.continuous⟩ = ν f) :
    ∀ (L : List Lk) (f : C(Lk → SU N, ℝ)),
      ν ⟨sweep Φ L f, continuous_sweep hpos hcont L f.continuous⟩ = ν f
  | [], f => rfl
  | l :: L, f => by
    have h := state_sweep hpos hcont ν hν L ⟨wAvg Φ l f, continuous_wAvg hpos hcont l f.continuous⟩
    exact h.trans (hν l f)

#print axioms state_sweep

/-- **Uniqueness of the heat-bath-invariant state under Dobrushin's condition**: for a positive
continuous weight with a non-negative influence matrix of row sums `≤ α < 1`, two states on the
continuous observables of the box invariant under every single heat bath agree
(`sweep_mixing`, `DLRLimit.dlr_eq_at_of_kernel_near_const`).

DERIVED: `0` the sign of `α`, `ε`; `1` the strict bound on `α`. -/
theorem state_unique_of_infl {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W)
    (hcont : Continuous Φ) {C : Lk → Lk → ℝ} (hC : Infl Φ C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {ν ν' : DLRLimit.State (Lk → SU N)}
    (hν : ∀ l (f : C(Lk → SU N, ℝ)),
      ν ⟨wAvg Φ l f, continuous_wAvg hpos hcont l f.continuous⟩ = ν f)
    (hν' : ∀ l (f : C(Lk → SU N, ℝ)),
      ν' ⟨wAvg Φ l f, continuous_wAvg hpos hcont l f.continuous⟩ = ν' f)
    (f : C(Lk → SU N, ℝ)) : ν f = ν' f := by
  obtain ⟨L, hL⟩ : ∃ L : List Lk, ∀ l, l ∈ L := ⟨Finset.univ.toList, fun l => by simp⟩
  have hdlr : ∀ σ : DLRLimit.State (Lk → SU N), (∀ l (f : C(Lk → SU N, ℝ)),
      σ ⟨wAvg Φ l f, continuous_wAvg hpos hcont l f.continuous⟩ = σ f) →
      DLRLimit.IsDLR (sweepC hpos hcont L) σ := by
    intro σ hσ n g
    induction n generalizing g with
    | zero => rfl
    | succ n ih =>
      have e : sweepC hpos hcont L (n + 1) g
          = sweepC hpos hcont L n ⟨sweep Φ L g, continuous_sweep hpos hcont L g.continuous⟩ := by
        ext W
        show (sweep Φ L)^[n + 1] g W = (sweep Φ L)^[n] (sweep Φ L g) W
        rw [Function.iterate_succ_apply]
      rw [e, ih]
      exact state_sweep hpos hcont σ hσ L g
  obtain ⟨v, hv⟩ := oscLe_of_continuous f.continuous
  refine DLRLimit.dlr_eq_at_of_kernel_near_const (fun ε hε => ?_) (hdlr ν hν) (hdlr ν' hν')
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (|∑ k, v k| + 1) by positivity) hα1
  obtain ⟨W0⟩ : Nonempty (Lk → SU N) := ⟨fun _ => 1⟩
  refine ⟨n, sweepC hpos hcont L n f W0, fun W => ?_⟩
  have h := sweep_mixing hpos hcont hC hC0 hrow hα0 hα1.le hL n f.continuous hv W W0
  have hαn : 0 ≤ α ^ n := pow_nonneg hα0 n
  have h2 : α ^ n * (|∑ k, v k| + 1) < ε := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < |∑ k, v k| + 1)).1 hn
    linarith
  have h3 : α ^ n * ∑ k, v k ≤ α ^ n * (|∑ k, v k| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self (∑ k, v k)]) hαn
  show |(sweep Φ L)^[n] f W - (sweep Φ L)^[n] f W0| ≤ ε
  linarith

#print axioms state_unique_of_infl

/-- **Dobrushin uniqueness for the box weight** at Lean `β ≤ 1/40` and local norm `≤ 1/16` at every
link: two states on the continuous observables of the periodic box of extent `M + 1 ≥ 2` invariant
under every single-link heat bath of `wtV β P` agree (`infl_wtV`, `rowSum_box`,
`state_unique_of_infl` at `α = 39/40`).

DERIVED: `0` the excluded colour count and the sign of `β`; `1` the least `M`; `1/40`, `1/16`,
`39/40` as in `rowSum_box`; `4`, `1` as in `pairPlaq`. -/
theorem state_unique_wtV (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 40) {M : ℕ}
    (hM : 1 ≤ M) (P : LocalPot N M) (hnorm : ∀ l, P.norm l ≤ 1 / 16)
    {ν ν' : DLRLimit.State (WilsonHypercubic.Link 4 (M + 1) → SU N)}
    (hν : ∀ l (f : C(WilsonHypercubic.Link 4 (M + 1) → SU N, ℝ)),
      ν ⟨wAvg (wtV β P) l f,
        continuous_wAvg (wtV_pos β P) (continuous_wtV β P) l f.continuous⟩ = ν f)
    (hν' : ∀ l (f : C(WilsonHypercubic.Link 4 (M + 1) → SU N, ℝ)),
      ν' ⟨wAvg (wtV β P) l f,
        continuous_wAvg (wtV_pos β P) (continuous_wtV β P) l f.continuous⟩ = ν' f)
    (f : C(WilsonHypercubic.Link 4 (M + 1) → SU N, ℝ)) : ν f = ν' f :=
  state_unique_of_infl (wtV_pos β P) (continuous_wtV β P) (infl_wtV hN hβ0 P)
    (boxInfl_nonneg hβ0 P) (fun l => rowSum_box hβ0 hβ hM P l (hnorm l)) (by norm_num)
    (by norm_num) hν hν' f

#print axioms state_unique_wtV

/-- **The Gibbs state of a positive continuous weight**: `f ↦ ∫ f Φ / ∫ Φ` against the product Haar
measure (`WeightedTorus.wExpect`), as a state on the continuous observables.

DERIVED: `0` the sign; `1` the constant observable and its value. -/
def gibbsState {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) :
    DLRLimit.State (Lk → SU N) where
  toFun f := MassGap.WeightedTorus.wExpect Φ f
  map_add' f g := by
    unfold MassGap.WeightedTorus.wExpect
    obtain ⟨Cf, hCf⟩ := exists_abs_le (f.continuous.mul hcont)
    obtain ⟨Cg, hCg⟩ := exists_abs_le (g.continuous.mul hcont)
    have i1 : Integrable (fun W => f W * Φ W) (Measure.pi fun _ : Lk => probHaar (SU N)) :=
      integrable_of_abs_le _ (f.continuous.mul hcont).measurable hCf
    have i2 : Integrable (fun W => g W * Φ W) (Measure.pi fun _ : Lk => probHaar (SU N)) :=
      integrable_of_abs_le _ (g.continuous.mul hcont).measurable hCg
    rw [← add_div, ← integral_add i1 i2]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    simp only [ContinuousMap.add_apply]
    ring
  map_smul' c f := by
    unfold MassGap.WeightedTorus.wExpect
    have e : ∀ W, (c • f) W * Φ W = c * (f W * Φ W) := fun W => by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]; ring
    simp only [e, integral_const_mul]
    ring
  nonneg' f hf := div_nonneg (integral_nonneg fun W => mul_nonneg (hf W) (hpos W).le)
    (integral_nonneg fun W => (hpos W).le)
  one' := by
    unfold MassGap.WeightedTorus.wExpect
    obtain ⟨C, hC⟩ := exists_abs_le hcont
    have hint : Integrable Φ (Measure.pi fun _ : Lk => probHaar (SU N)) :=
      integrable_of_abs_le _ hcont.measurable hC
    have hZ : 0 < ∫ W, Φ W ∂(Measure.pi fun _ : Lk => probHaar (SU N)) := by
      rw [integral_pos_iff_support_of_nonneg (fun W => (hpos W).le) hint]
      have hsupp : Function.support Φ = Set.univ :=
        Set.eq_univ_of_forall fun W => Function.mem_support.mpr (hpos W).ne'
      rw [hsupp, measure_univ]
      exact one_pos
    simp only [ContinuousMap.one_apply, one_mul]
    exact div_self hZ.ne'

/-- **The Gibbs state is invariant under every single heat bath** (`WeightedTorus.expect_wAvg`).

DERIVED: no numeral. -/
theorem gibbsState_invariant {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    (l : Lk) (f : C(Lk → SU N, ℝ)) :
    gibbsState hpos hcont ⟨wAvg Φ l f, continuous_wAvg hpos hcont l f.continuous⟩
      = gibbsState hpos hcont f :=
  MassGap.WeightedTorus.expect_wAvg hpos hcont l f.continuous

#print axioms gibbsState_invariant

/-- **Every heat-bath-invariant state of the box is its Gibbs state** at Lean `β ≤ 1/40` and local
norm `≤ 1/16` (`state_unique_wtV` against `gibbsState`, which satisfies the hypothesis, so the
statement is not vacuous).

DERIVED: as in `state_unique_wtV`; Inherited: `1/40`, `1/16` the coupling and norm bounds of
`rowSum_box`. -/
theorem state_eq_gibbs_wtV (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 40) {M : ℕ}
    (hM : 1 ≤ M) (P : LocalPot N M) (hnorm : ∀ l, P.norm l ≤ 1 / 16)
    {ν : DLRLimit.State (WilsonHypercubic.Link 4 (M + 1) → SU N)}
    (hν : ∀ l (f : C(WilsonHypercubic.Link 4 (M + 1) → SU N, ℝ)),
      ν ⟨wAvg (wtV β P) l f,
        continuous_wAvg (wtV_pos β P) (continuous_wtV β P) l f.continuous⟩ = ν f)
    (f : C(WilsonHypercubic.Link 4 (M + 1) → SU N, ℝ)) :
    ν f = MassGap.WeightedTorus.wExpect (wtV β P) f :=
  state_unique_wtV hN hβ0 hβ hM P hnorm hν
    (gibbsState_invariant (wtV_pos β P) (continuous_wtV β P)) f

#print axioms state_eq_gibbs_wtV

/-- **The heat-bath sweep converges to the Gibbs expectation geometrically**: for every
configuration `W`, `|Tⁿ f (W) − ⟨f⟩| ≤ αⁿ Σ v` (`sweep_mixing`; the Gibbs state is invariant under
the sweep, `state_sweep`).

DERIVED: `0`, `1` as in `osc_iter`. -/
theorem sweep_to_gibbs {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    {C : Lk → Lk → ℝ} (hC : Infl Φ C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {L : List Lk} (hL : ∀ l, l ∈ L)
    (n : ℕ) (f : C(Lk → SU N, ℝ)) {v : Lk → ℝ} (hv : OscLe f v) (W : Lk → SU N) :
    |(sweep Φ L)^[n] f W - gibbsState hpos hcont f| ≤ α ^ n * ∑ k, v k := by
  set σ := gibbsState hpos hcont
  set B := α ^ n * ∑ k, v k
  have hinv' : ∀ (m : ℕ) (g : C(Lk → SU N, ℝ)), σ (sweepC hpos hcont L m g) = σ g := by
    intro m
    induction m with
    | zero => intro g; rfl
    | succ m ih =>
      intro g
      have e : sweepC hpos hcont L (m + 1) g
          = sweepC hpos hcont L m ⟨sweep Φ L g, continuous_sweep hpos hcont L g.continuous⟩ := by
        ext V
        show (sweep Φ L)^[m + 1] g V = (sweep Φ L)^[m] (sweep Φ L g) V
        rw [Function.iterate_succ_apply]
      rw [e, ih]
      exact state_sweep hpos hcont σ (gibbsState_invariant hpos hcont) L g
  have hinv := hinv' n f
  have hmix := fun V => sweep_mixing hpos hcont hC hC0 hrow hα0 hα1 hL n f.continuous hv V W
  have hlo : ∀ V, (((sweep Φ L)^[n] f W - B) • (1 : C(Lk → SU N, ℝ))) V
      ≤ sweepC hpos hcont L n f V := fun V => by
    have := (abs_le.mp (hmix V)).1
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    show _ ≤ (sweep Φ L)^[n] f V
    linarith
  have hhi : ∀ V, sweepC hpos hcont L n f V
      ≤ (((sweep Φ L)^[n] f W + B) • (1 : C(Lk → SU N, ℝ))) V := fun V => by
    have := (abs_le.mp (hmix V)).2
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    show (sweep Φ L)^[n] f V ≤ _
    linarith
  have h1 := σ.mono hlo
  have h2 := σ.mono hhi
  rw [σ.map_smul, σ.map_one, mul_one, hinv] at h1 h2
  rw [abs_le]
  constructor <;> linarith

#print axioms sweep_to_gibbs

end Sweep

end MassGap.BoxDobrushinCoupling
