import Mathlib
import MassGap.PairCorr
import MassGap.ClayRoutes
import MassGap.PairInterface
import MassGap.HaarMomentsSU2
import MassGap.HaarMomentsSU3
import MassGap.TiltedHaar
import MassGap.PairFibreAbstract
import MassGap.PairCount
import MassGap.PairWeight

noncomputable section

/-!
# MassGap.PairCorrSharp — the box check at the capstone floor for `SU(2)` and `SU(3)`

## What it gives

1. `gibbs_corr_le_of_fibre`: `PairCorr.gibbs_corr_le` with its weight-range hypothesis replaced by a
   fibre covariance hypothesis (the proof is `gibbs_corr_le`'s, with `fibre_corr_config`'s appeal to
   `fibre_corr_le` replaced by the hypothesis).
2. `pairCorr_twoCond_sharp`: the two-link correlation at constant `c` from
   `FibreBound (probHaar (SU N)) (realFeature N) c (β n2) (β(12 − n2))` (`PairWeight.wt_fibre_eq`,
   `hfib_of_fibreBound`). No smallness of `β` is assumed.
3. `pairDeltaSharp δ₁ δ₂ j`: `δ₁` at pair count `2`, `δ₂` at `4`, `0` otherwise; a `DefectMatrix`
   with sums at most `max(18δ₁, 12δ₁ + 3δ₂)` (`PairCount.sum_n2_le`, `PairCount.card_n2_four_le`).
4. `pairCorrAt_sharp`, `boxPairCorr_sharp`: the pair count is `0`, `2` or `4`
   (`PairCount.n2_cases`); count `0` has a product fibre law (`PairFibreAbstract.fibreBound_zero`).
5. The floor `floorBeta N = 17N²/(88π²)`, the numeric checks (`PairCheck`, `norm_num` on rationals),
   `boxPatchGap_floor_su2 : BoxPatchGap (floorBeta 2) 2606 (307/10000)` and
   `boxPatchGap_floor_su3 : BoxPatchGap (floorBeta 3) 545 (367/2500)`.
6. `clay_continuum_floor_su2`, `clay_continuum_floor_su3`: `ClayRoutes.clay_continuum_of_boxPatchGap`
   at `β₀ = βUV = floorBeta N`, where `_hpeak` holds by `le_rfl`. The open inputs E, N, Y and the UV
   step below the box's rate are hypotheses.
-/

namespace MassGap.PairCorrSharp

open MeasureTheory
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.HeatBath MassGap.HeatBathErgodic MassGap.KnabeCriterion MassGap.BoxGap
open MassGap.PeriodicState (torusObs)
open MassGap.PairCorr (heatNum2 twoCondExp)
open MassGap.PairInterface MassGap.PairCount MassGap.PairWeight MassGap.PairFibreAbstract
open MassGap.TiltedHaar

/-! ## 1. The Gibbs correlation bound from a fibre bound -/

section Gibbs

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq] [DecidableEq Lk]

/-- **THE GIBBS CORRELATION BOUND FROM A FIBRE BOUND.** As `PairCorr.gibbs_corr_le`, with the
hypothesis "the fibre weight lies in `[m₀, κ m₀]`" replaced by the fibre covariance bound at every
frozen `W`.

DERIVED: `0` is the sign of `c` and the vanishing numerator and mean; `2` is the square and the
halving. -/
theorem gibbs_corr_le_of_fibre (bd : Pq → List (Lk × Bool)) (β : ℝ) {l m : Lk} (hlm : l ≠ m)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) (hzero : ∀ W, heatNum2 bd β l m f W = 0)
    {c : ℝ} (hc : 0 ≤ c)
    (hfib : ∀ (W : Lk → SU N) (a b : SU N → ℝ), Continuous a → Continuous b →
      ∫ h, a h * havg l (wt (N := N) bd β) (Function.update W m h) ∂(probHaar (SU N)) = 0 →
      ∫ h, ∫ g, a h * b g * wt bd β (Function.update (Function.update W m h) l g)
          ∂(probHaar (SU N)) ∂(probHaar (SU N))
        ≤ c / 2 * (∫ h, a h ^ 2 * havg l (wt (N := N) bd β) (Function.update W m h)
              ∂(probHaar (SU N))
            + ∫ g, b g ^ 2 * havg m (wt (N := N) bd β) (Function.update W l g) ∂(probHaar (SU N)))) :
    ∫ W, heatAvg bd β l f W * heatAvg bd β m f W * wt bd β W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      ≤ c / 2 * (∫ W, heatAvg bd β l f W * heatAvg bd β l f W * wt bd β W
            ∂(Measure.pi fun _ : Lk => probHaar (SU N))
          + ∫ W, heatAvg bd β m f W * heatAvg bd β m f W * wt bd β W
            ∂(Measure.pi fun _ : Lk => probHaar (SU N))) := by
  have hml : m ≠ l := Ne.symm hlm
  have cA := continuous_heatAvg bd β l hf
  have cB := continuous_heatAvg bd β m hf
  have cw := continuous_wt (N := N) bd β
  have cAB : Continuous (fun V => heatAvg bd β l f V * heatAvg bd β m f V * wt bd β V) :=
    (cA.mul cB).mul cw
  have cAA : Continuous (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V) :=
    (cA.mul cA).mul cw
  have cBB : Continuous (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V) :=
    (cB.mul cB).mul cw
  have e1 : ∫ W, heatAvg bd β l f W * heatAvg bd β m f W * wt bd β W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      = ∫ W, havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β m f V * wt bd β V)) W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N)) :=
    ((integral_havg m (continuous_havg l cAB)).trans (integral_havg l cAB)).symm
  have e2 : ∫ W, heatAvg bd β l f W * heatAvg bd β l f W * wt bd β W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      = ∫ W, havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N)) :=
    ((integral_havg m (continuous_havg l cAA)).trans (integral_havg l cAA)).symm
  have e3 : ∫ W, heatAvg bd β m f W * heatAvg bd β m f W * wt bd β W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      = ∫ W, havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N)) :=
    ((integral_havg l (continuous_havg m cBB)).trans (integral_havg m cBB)).symm
  -- the fibre bound at every frozen configuration (`PairCorr.fibre_corr_config` with `hfib`)
  have hpt : ∀ W, havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β m f V * wt bd β V)) W
      ≤ c / 2 * (havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
        + havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W) := by
    intro W
    have ha : Continuous (fun h => heatAvg bd β l f (Function.update W m h)) :=
      (continuous_heatAvg bd β l hf).comp (continuous_const.update m continuous_id)
    have hb : Continuous (fun g => heatAvg bd β m f (Function.update W l g)) :=
      (continuous_heatAvg bd β m hf).comp (continuous_const.update l continuous_id)
    have hz : ∫ h, heatAvg bd β l f (Function.update W m h)
        * havg l (wt (N := N) bd β) (Function.update W m h) ∂(probHaar (SU N)) = 0 := by
      have e : ∀ h, heatAvg bd β l f (Function.update W m h)
          * havg l (wt (N := N) bd β) (Function.update W m h)
          = heatNum bd β l f (Function.update W m h) := fun h =>
        div_mul_cancel₀ _ (heatPart_pos bd β l _).ne'
      calc ∫ h, heatAvg bd β l f (Function.update W m h)
            * havg l (wt (N := N) bd β) (Function.update W m h) ∂(probHaar (SU N))
          = ∫ h, heatNum bd β l f (Function.update W m h) ∂(probHaar (SU N)) :=
            integral_congr_ae (Filter.Eventually.of_forall e)
        _ = 0 := hzero W
    have key := hfib W (fun h => heatAvg bd β l f (Function.update W m h))
      (fun g => heatAvg bd β m f (Function.update W l g)) ha hb hz
    have E1 : havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β m f V * wt bd β V)) W
        = ∫ h, ∫ g, heatAvg bd β l f (Function.update W m h)
            * heatAvg bd β m f (Function.update W l g)
            * wt bd β (Function.update (Function.update W m h) l g)
            ∂(probHaar (SU N)) ∂(probHaar (SU N)) := by
      unfold havg
      refine integral_congr_ae (Filter.Eventually.of_forall (fun h => ?_))
      refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
      show heatAvg bd β l f (Function.update (Function.update W m h) l g)
          * heatAvg bd β m f (Function.update (Function.update W m h) l g)
          * wt bd β (Function.update (Function.update W m h) l g)
        = heatAvg bd β l f (Function.update W m h) * heatAvg bd β m f (Function.update W l g)
          * wt bd β (Function.update (Function.update W m h) l g)
      rw [heatAvg_update bd β l f (Function.update W m h) g, Function.update_comm hml h g W,
        heatAvg_update bd β m f (Function.update W l g) h]
    have E2 : havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
        = ∫ h, heatAvg bd β l f (Function.update W m h) ^ 2
            * havg l (wt (N := N) bd β) (Function.update W m h) ∂(probHaar (SU N)) := by
      unfold havg
      refine integral_congr_ae (Filter.Eventually.of_forall (fun h => ?_))
      show ∫ g, heatAvg bd β l f (Function.update (Function.update W m h) l g)
            * heatAvg bd β l f (Function.update (Function.update W m h) l g)
            * wt bd β (Function.update (Function.update W m h) l g) ∂(probHaar (SU N))
        = heatAvg bd β l f (Function.update W m h) ^ 2
          * ∫ g, wt bd β (Function.update (Function.update W m h) l g) ∂(probHaar (SU N))
      simp only [heatAvg_update, integral_const_mul, sq]
    have E3 : havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W
        = ∫ g, heatAvg bd β m f (Function.update W l g) ^ 2
            * havg m (wt (N := N) bd β) (Function.update W l g) ∂(probHaar (SU N)) := by
      unfold havg
      refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
      show ∫ h, heatAvg bd β m f (Function.update (Function.update W l g) m h)
            * heatAvg bd β m f (Function.update (Function.update W l g) m h)
            * wt bd β (Function.update (Function.update W l g) m h) ∂(probHaar (SU N))
        = heatAvg bd β m f (Function.update W l g) ^ 2
          * ∫ h, wt bd β (Function.update (Function.update W l g) m h) ∂(probHaar (SU N))
      simp only [heatAvg_update, integral_const_mul, sq]
    rw [E1, E2, E3]
    exact key
  have i1 : Integrable
      (fun W => havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β m f V * wt bd β V)) W)
      (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    haar_integrable (continuous_havg m (continuous_havg l cAB))
  have i2 : Integrable
      (fun W => havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W)
      (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    haar_integrable (continuous_havg m (continuous_havg l cAA))
  have i3 : Integrable
      (fun W => havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W)
      (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    haar_integrable (continuous_havg l (continuous_havg m cBB))
  have i23 : Integrable
      (fun W => c / 2
        * (havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
          + havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W))
      (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    haar_integrable (continuous_const.mul ((continuous_havg m (continuous_havg l cAA)).add
      (continuous_havg l (continuous_havg m cBB))))
  rw [e1, e2, e3]
  calc ∫ W, havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β m f V * wt bd β V)) W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      ≤ ∫ W, c / 2
          * (havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
            + havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W)
          ∂(Measure.pi fun _ : Lk => probHaar (SU N)) :=
        integral_mono i1 i23 hpt
    _ = c / 2
          * (∫ W, havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
              ∂(Measure.pi fun _ : Lk => probHaar (SU N))
            + ∫ W, havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W
              ∂(Measure.pi fun _ : Lk => probHaar (SU N))) := by
        rw [integral_const_mul, integral_add i2 i3]

#print axioms gibbs_corr_le_of_fibre

end Gibbs

/-! ## 2. The torus pair from the fibre bound -/

section Torus

variable {N : ℕ}

/-- **The fibre hypothesis of `gibbs_corr_le_of_fibre` from a `FibreBound`** (`PairWeight.wt_fibre_eq`
rewrites the weight; `havg l wt (W[m ↦ h]) = ∫ g, fibreWeight h g`; `Function.update_comm` for the
`m`-marginal).

DERIVED: `4` is the spacetime dimension; `1` is the least `M` and the successor writing the extent;
`0` is the excluded rank, the lower end of `β` and the vanishing mean; `12` is the non-diagonal
plaquette count per link; `2` is the square and the halving. -/
theorem hfib_of_fibreBound (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {M : ℕ} (hM : 1 ≤ M)
    {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m) {c : ℝ}
    (hB : FibreBound (probHaar (SU N)) (realFeature N) c (β * (n2 M l m : ℝ))
      (β * (12 - (n2 M l m : ℝ))))
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) (a b : SU N → ℝ) (ha : Continuous a)
    (hb : Continuous b)
    (hz : ∫ h, a h * havg l (wt (N := N) (bdT M) β) (Function.update W m h) ∂(probHaar (SU N)) = 0) :
    ∫ h, ∫ g, a h * b g * wt (bdT M) β (Function.update (Function.update W m h) l g)
        ∂(probHaar (SU N)) ∂(probHaar (SU N))
      ≤ c / 2 * (∫ h, a h ^ 2 * havg l (wt (N := N) (bdT M) β) (Function.update W m h)
            ∂(probHaar (SU N))
          + ∫ g, b g ^ 2 * havg m (wt (N := N) (bdT M) β) (Function.update W l g)
            ∂(probHaar (SU N))) := by
  obtain ⟨K, T, α, γ, hK, hT, hα, hγ, hw⟩ := wt_fibre_eq hN hβ hM hlm W
  have hq : ∀ h, havg l (wt (N := N) (bdT M) β) (Function.update W m h)
      = ∫ g, fibreWeight (realFeature N) K T α γ h g ∂(probHaar (SU N)) := by
    intro h
    show ∫ g, wt (bdT M) β (Function.update (Function.update W m h) l g) ∂(probHaar (SU N)) = _
    exact integral_congr_ae (Filter.Eventually.of_forall (fun g => hw h g))
  have hp : ∀ g, havg m (wt (N := N) (bdT M) β) (Function.update W l g)
      = ∫ h, fibreWeight (realFeature N) K T α γ h g ∂(probHaar (SU N)) := by
    intro g
    show ∫ h, wt (bdT M) β (Function.update (Function.update W l g) m h) ∂(probHaar (SU N)) = _
    have e : ∀ h, wt (bdT M) β (Function.update (Function.update W l g) m h)
        = fibreWeight (realFeature N) K T α γ h g := fun h => by
      rw [Function.update_comm hlm g h W]
      exact hw h g
    exact integral_congr_ae (Filter.Eventually.of_forall e)
  have ez : ∀ h, a h * havg l (wt (N := N) (bdT M) β) (Function.update W m h)
      = a h * ∫ g, fibreWeight (realFeature N) K T α γ h g ∂(probHaar (SU N)) :=
    fun h => by rw [hq h]
  have hz' : ∫ h, a h * ∫ g, fibreWeight (realFeature N) K T α γ h g ∂(probHaar (SU N))
      ∂(probHaar (SU N)) = 0 :=
    (integral_congr_ae (μ := probHaar (SU N)) (Filter.Eventually.of_forall ez)).symm.trans hz
  have key := hB K T α γ hK hT hα hγ a b ha hb hz'
  have e1i : ∀ h, ∫ g, a h * b g * wt (bdT M) β (Function.update (Function.update W m h) l g)
        ∂(probHaar (SU N))
      = ∫ g, a h * b g * fibreWeight (realFeature N) K T α γ h g ∂(probHaar (SU N)) := by
    intro h
    have e : ∀ g, a h * b g * wt (bdT M) β (Function.update (Function.update W m h) l g)
        = a h * b g * fibreWeight (realFeature N) K T α γ h g := fun g => by rw [hw h g]
    exact integral_congr_ae (Filter.Eventually.of_forall e)
  have e1 := integral_congr_ae (μ := probHaar (SU N)) (Filter.Eventually.of_forall e1i)
  have e2i : ∀ h, a h ^ 2 * havg l (wt (N := N) (bdT M) β) (Function.update W m h)
      = a h ^ 2 * ∫ g, fibreWeight (realFeature N) K T α γ h g ∂(probHaar (SU N)) :=
    fun h => by rw [hq h]
  have e2 := integral_congr_ae (μ := probHaar (SU N)) (Filter.Eventually.of_forall e2i)
  have e3i : ∀ g, b g ^ 2 * havg m (wt (N := N) (bdT M) β) (Function.update W l g)
      = b g ^ 2 * ∫ h, fibreWeight (realFeature N) K T α γ h g ∂(probHaar (SU N)) :=
    fun g => by rw [hp g]
  have e3 := integral_congr_ae (μ := probHaar (SU N)) (Filter.Eventually.of_forall e3i)
  rw [e1, e2, e3]
  exact key

#print axioms hfib_of_fibreBound

/-- **THE TWO-LINK CORRELATION AT CONSTANT `c`**, the proof of `PairCorr.pairCorr_twoCond` with
`gibbs_corr_le_of_fibre` and `hfib_of_fibreBound` in place of `gibbs_corr_le` and its weight range.
No smallness of `β` is assumed.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the lower end of `β` and `c` and the excluded rank;
`12` is the non-diagonal plaquette count per link; `2` is the halving. -/
theorem pairCorr_twoCond_sharp (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (j : ℕ)
    {l m : WilsonHypercubic.Link 4 (2 * j + 1 + 1)} (hlm : l ≠ m) {c : ℝ} (hc : 0 ≤ c)
    (hB : FibreBound (probHaar (SU N)) (realFeature N) c (β * (n2 (2 * j + 1) l m : ℝ))
      (β * (12 - (n2 (2 * j + 1) l m : ℝ))))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    torusForm hN β j (torusCondExp β (2 * j + 1) l (x - twoCondExp β (2 * j + 1) l m x))
        (torusCondExp β (2 * j + 1) m (x - twoCondExp β (2 * j + 1) l m x))
      ≤ c * (torusForm hN β j (torusCondExp β (2 * j + 1) l (x - twoCondExp β (2 * j + 1) l m x))
            (torusCondExp β (2 * j + 1) l (x - twoCondExp β (2 * j + 1) l m x))
          + torusForm hN β j (torusCondExp β (2 * j + 1) m (x - twoCondExp β (2 * j + 1) l m x))
            (torusCondExp β (2 * j + 1) m (x - twoCondExp β (2 * j + 1) l m x))) / 2 := by
  obtain ⟨F, hFdef⟩ : ∃ F : (WilsonHypercubic.Link 4 (2 * j + 1 + 1) → SU N) → ℝ,
      F = fun V => torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) V
        - PairCorr.heatAvg2 (bdT (2 * j + 1)) β l m
            (torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ))) V := ⟨_, rfl⟩
  have hFc : Continuous F := by
    rw [hFdef]
    exact (continuous_torusObs _ _).sub
      (PairCorr.continuous_heatAvg2 (bdT (2 * j + 1)) β l m (continuous_torusObs _ _))
  have hzero : ∀ W, heatNum2 (bdT (2 * j + 1)) β l m F W = 0 := fun W => by
    rw [hFdef]
    exact PairCorr.heatNum2_sub_self (bdT (2 * j + 1)) β hlm (continuous_torusObs _ _) W
  have hF : torusObs (2 * j + 1) ((x - twoCondExp β (2 * j + 1) l m x
      : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) : C(GibbsSpec.IConf (SU N), ℝ))
      = F := by
    rw [hFdef]
    funext V
    show torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) V
        - torusObs (2 * j + 1)
            (PairCorr.heatLift2 β (2 * j + 1) l m (x : C(GibbsSpec.IConf (SU N), ℝ))) V
      = torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) V
        - PairCorr.heatAvg2 (bdT (2 * j + 1)) β l m
            (torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ))) V
    rw [PairCorr.torusObs_heatLift2]
  have hM : 1 ≤ 2 * j + 1 := by omega
  have hg := gibbs_corr_le_of_fibre (bdT (2 * j + 1)) β hlm hFc hzero hc
    (fun W a b ha hb hz => hfib_of_fibreBound hN hβ0 hM hlm hB W a b ha hb hz)
  have hZ := MassGap.WilsonReal.wilsonSystem_partition_pos hN (bdT (2 * j + 1)) β
  rw [torusForm_eq_integral, torusForm_eq_integral, torusForm_eq_integral,
    PairCorr.torusObs_condExp β (2 * j + 1) l, PairCorr.torusObs_condExp β (2 * j + 1) m, hF]
  refine le_trans (div_le_div_of_nonneg_right hg hZ.le) (le_of_eq ?_)
  ring

#print axioms pairCorr_twoCond_sharp

end Torus

/-! ## 3. The sharp defect matrix -/

section Defect

/-- **The sharp pair defect**: `δ₁` at pair count `2`, `δ₂` at pair count `4`, `0` on the diagonal
and at pair count `0` (collinear pairs and pairs sharing no plaquette: the fibre law is a product).

DERIVED: `4` is the spacetime dimension and the double pair count; `2 * j + 1` is the index of the
even-extent family and the `+ 1` its successor writing the extent; `2` is the single pair count;
`0` is the defect of a product law. -/
def pairDeltaSharp (δ₁ δ₂ : ℝ) (j : ℕ) (l m : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) : ℝ :=
  if l = m then 0
  else if n2 (2 * j + 1) l m = 2 then δ₁
  else if n2 (2 * j + 1) l m = 4 then δ₂
  else 0

/-- **Row sums**: `Σₘ pairDeltaSharp ≤ max(18δ₁, 12δ₁ + 3δ₂)`. With `a` partners at count `2` and
`b` at count `4`: `2a + 4b ≤ 36` (`PairCount.sum_n2_le`), `b ≤ 3` (`PairCount.card_n2_four_le`), so
`aδ₁ + bδ₂ ≤ 18δ₁ + b(δ₂ − 2δ₁) ≤ max(18δ₁, 12δ₁ + 3δ₂)`.

DERIVED: `18 = 36/2`, the generic count of single partners; `12 = 18 − 2 · 3` and `3` the side-2
counts; `0` is the sign of `δ₁`, `δ₂`; `4`, `2 * j + 1`, `+ 1` as in `pairDeltaSharp`. -/
theorem pairDeltaSharp_row {δ₁ δ₂ : ℝ} (h1 : 0 ≤ δ₁) (h2 : 0 ≤ δ₂) (j : ℕ)
    (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    ∑ m, pairDeltaSharp δ₁ δ₂ j l m ≤ max (18 * δ₁) (12 * δ₁ + 3 * δ₂) := by
  have hM : 1 ≤ 2 * j + 1 := by omega
  obtain ⟨A, hA⟩ : ∃ A : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)),
      A = (Finset.univ.erase l).filter (fun m => n2 (2 * j + 1) l m = 2) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)),
      B = (Finset.univ.erase l).filter (fun m => n2 (2 * j + 1) l m = 4) := ⟨_, rfl⟩
  -- the sum is `|A| δ₁ + |B| δ₂`
  have hsplit : ∑ m, pairDeltaSharp δ₁ δ₂ j l m
      = ∑ m ∈ Finset.univ.erase l, ((if n2 (2 * j + 1) l m = 2 then δ₁ else 0)
          + (if n2 (2 * j + 1) l m = 4 then δ₂ else 0)) := by
    rw [← Finset.sum_erase Finset.univ
      (show pairDeltaSharp δ₁ δ₂ j l l = 0 by simp [pairDeltaSharp])]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hml : l ≠ m := fun h => (Finset.mem_erase.mp hm).1 h.symm
    unfold pairDeltaSharp
    rw [if_neg hml]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have hval : ∑ m, pairDeltaSharp δ₁ δ₂ j l m = (A.card : ℝ) * δ₁ + (B.card : ℝ) * δ₂ := by
    rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, ← hA, ← hB]
  -- the counts
  have hcount : 2 * A.card + 4 * B.card ≤ 36 := by
    have hle : ∑ m ∈ Finset.univ.erase l, ((if n2 (2 * j + 1) l m = 2 then 2 else 0)
        + (if n2 (2 * j + 1) l m = 4 then 4 else 0))
        ≤ ∑ m ∈ Finset.univ.erase l, n2 (2 * j + 1) l m :=
      Finset.sum_le_sum (fun m _ => by split_ifs <;> omega)
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
      Finset.sum_const, smul_eq_mul, smul_eq_mul, ← hA, ← hB] at hle
    have := sum_n2_le hM l
    omega
  have hB3 : B.card ≤ 3 := by
    have hBeq : B = Finset.univ.filter
        (fun m : WilsonHypercubic.Link 4 (2 * j + 1 + 1) => m ≠ l ∧ n2 (2 * j + 1) l m = 4) := by
      rw [hB]
      ext m
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and,
        iff_self]
    rw [hBeq]
    exact card_n2_four_le hM l
  have hc1 : (A.card : ℝ) * 2 + (B.card : ℝ) * 4 ≤ 36 := by
    have : ((2 * A.card + 4 * B.card : ℕ) : ℝ) ≤ 36 := by exact_mod_cast hcount
    push_cast at this
    linarith
  have hc2 : (B.card : ℝ) ≤ 3 := by exact_mod_cast hB3
  have hb0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have ha : (A.card : ℝ) ≤ 18 - 2 * B.card := by linarith
  have key1 : (A.card : ℝ) * δ₁ ≤ (18 - 2 * B.card) * δ₁ := mul_le_mul_of_nonneg_right ha h1
  rw [hval]
  rcases le_total (2 * δ₁) δ₂ with hd | hd
  · have key2 : (B.card : ℝ) * (δ₂ - 2 * δ₁) ≤ 3 * (δ₂ - 2 * δ₁) :=
      mul_le_mul_of_nonneg_right hc2 (by linarith)
    have hfin : (A.card : ℝ) * δ₁ + (B.card : ℝ) * δ₂ ≤ 12 * δ₁ + 3 * δ₂ := by linarith
    exact le_trans hfin (le_max_right _ _)
  · have key2 : 0 ≤ (B.card : ℝ) * (2 * δ₁ - δ₂) := mul_nonneg hb0 (by linarith)
    have hfin : (A.card : ℝ) * δ₁ + (B.card : ℝ) * δ₂ ≤ 18 * δ₁ := by linarith
    exact le_trans hfin (le_max_left _ _)

#print axioms pairDeltaSharp_row

/-- **Column sums** (`PairCount.n2_symm`, `pairDeltaSharp_row`).

DERIVED: the bound of `pairDeltaSharp_row`, by symmetry of the pair count: `18 = 36/2`, the generic
count of single partners (`2a + 4b ≤ 36`); `3` bounds the partners at pair count `4`
(`PairCount.card_n2_four_le`) and `12 = 18 − 2 · 3`; `0` is the sign of `δ₁`, `δ₂`; `4` is the
spacetime dimension; `2 * j + 1` is the index of the even-extent family and the `+ 1` its successor
writing the extent. -/
theorem pairDeltaSharp_col {δ₁ δ₂ : ℝ} (h1 : 0 ≤ δ₁) (h2 : 0 ≤ δ₂) (j : ℕ)
    (m : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    ∑ l, pairDeltaSharp δ₁ δ₂ j l m ≤ max (18 * δ₁) (12 * δ₁ + 3 * δ₂) := by
  have hsym : ∀ l, pairDeltaSharp δ₁ δ₂ j l m = pairDeltaSharp δ₁ δ₂ j m l := by
    intro l
    unfold pairDeltaSharp
    rw [n2_symm (2 * j + 1) l m]
    by_cases h : l = m
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [Finset.sum_congr rfl (fun l _ => hsym l)]
  exact pairDeltaSharp_row h1 h2 j m

#print axioms pairDeltaSharp_col

/-- **The sharp defect matrix.**

DERIVED: the row and column bound of `pairDeltaSharp_row` and `pairDeltaSharp_col`: `18 = 36/2`, the
generic count of single partners; `3` bounds the partners at pair count `4` and
`12 = 18 − 2 · 3`; `0` is the sign of `δ₁`, `δ₂`. -/
theorem pairDeltaSharp_defect {δ₁ δ₂ : ℝ} (h1 : 0 ≤ δ₁) (h2 : 0 ≤ δ₂) (j : ℕ) :
    DefectMatrix (pairDeltaSharp δ₁ δ₂ j) (max (18 * δ₁) (12 * δ₁ + 3 * δ₂)) := by
  refine ⟨fun l m => ?_, fun l => pairDeltaSharp_row h1 h2 j l,
    fun m => pairDeltaSharp_col h1 h2 j m⟩
  unfold pairDeltaSharp
  split_ifs
  · exact le_refl 0
  · exact h1
  · exact h2
  · exact le_refl 0

#print axioms pairDeltaSharp_defect

end Defect

/-! ## 4. The two-link correlation at every extent -/

section Sharp

variable {N : ℕ}

/-- **The two-link correlation bound at every extent from two fibre bounds**: `y = twoCondExp x` for
every pair; `n2 ∈ {0, 2, 4}` (`PairCount.n2_cases`); count `2` uses `h1` at `(2β, 10β)`, count `4`
uses `h2` at `(4β, 8β)`, count `0` uses `PairFibreAbstract.fibreBound_zero`.

DERIVED: `2`, `10 = 12 − 2` and `4`, `8 = 12 − 4` are the coupling and tilt counts of the single and
double pairs; `0` is the lower end of `β`, `δ₁`, `δ₂` and the excluded rank. -/
theorem pairCorrAt_sharp (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (j : ℕ) {δ₁ δ₂ : ℝ}
    (h1 : FibreBound (probHaar (SU N)) (realFeature N) δ₁ (2 * β) (10 * β))
    (h2 : FibreBound (probHaar (SU N)) (realFeature N) δ₂ (4 * β) (8 * β))
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) :
    PairCorrAt hN β j (pairDeltaSharp δ₁ δ₂ j) := by
  intro l m hlm x
  refine ⟨twoCondExp β (2 * j + 1) l m x, PairCorr.torusCondExp_twoCondExp_l β (2 * j + 1) hlm x,
    PairCorr.torusCondExp_twoCondExp_m β (2 * j + 1) l m x, ?_⟩
  have hM : 1 ≤ 2 * j + 1 := by omega
  rcases n2_cases hM hlm with h0 | h2' | h4
  · have hδ : pairDeltaSharp δ₁ δ₂ j l m = 0 := by
      unfold pairDeltaSharp
      rw [if_neg hlm, h0, if_neg (show ¬ (0 : ℕ) = 2 by norm_num),
        if_neg (show ¬ (0 : ℕ) = 4 by norm_num)]
    have hB : FibreBound (probHaar (SU N)) (realFeature N) 0 (β * (n2 (2 * j + 1) l m : ℝ))
        (β * (12 - (n2 (2 * j + 1) l m : ℝ))) := by
      rw [h0, Nat.cast_zero, mul_zero]
      exact fibreBound_zero (continuous_realFeature N) _
    rw [hδ]
    exact pairCorr_twoCond_sharp hN hβ0 j hlm le_rfl hB x
  · have hδ : pairDeltaSharp δ₁ δ₂ j l m = δ₁ := by
      unfold pairDeltaSharp
      rw [if_neg hlm, if_pos h2']
    have hB : FibreBound (probHaar (SU N)) (realFeature N) δ₁ (β * (n2 (2 * j + 1) l m : ℝ))
        (β * (12 - (n2 (2 * j + 1) l m : ℝ))) := by
      have e1 : β * (n2 (2 * j + 1) l m : ℝ) = 2 * β := by
        rw [h2']
        push_cast
        ring
      have e2 : β * (12 - (n2 (2 * j + 1) l m : ℝ)) = 10 * β := by
        rw [h2']
        push_cast
        ring
      rw [e1, e2]
      exact h1
    rw [hδ]
    exact pairCorr_twoCond_sharp hN hβ0 j hlm hδ₁ hB x
  · have hδ : pairDeltaSharp δ₁ δ₂ j l m = δ₂ := by
      unfold pairDeltaSharp
      rw [if_neg hlm, if_neg (show ¬ n2 (2 * j + 1) l m = 2 by omega), if_pos h4]
    have hB : FibreBound (probHaar (SU N)) (realFeature N) δ₂ (β * (n2 (2 * j + 1) l m : ℝ))
        (β * (12 - (n2 (2 * j + 1) l m : ℝ))) := by
      have e1 : β * (n2 (2 * j + 1) l m : ℝ) = 4 * β := by
        rw [h4]
        push_cast
        ring
      have e2 : β * (12 - (n2 (2 * j + 1) l m : ℝ)) = 8 * β := by
        rw [h4]
        push_cast
        ring
      rw [e1, e2]
      exact h2
    rw [hδ]
    exact pairCorr_twoCond_sharp hN hβ0 j hlm hδ₂ hB x

#print axioms pairCorrAt_sharp

/-- **`BoxPairCorr` from two fibre bounds** (`pairDeltaSharp_defect`, `pairCorrAt_sharp`).

DERIVED: `18`, `12`, `3` as in `pairDeltaSharp_row`; `2`, `10`, `4`, `8` as in `pairCorrAt_sharp`;
`1` is `BoxPairCorr`'s entry bound; `0` is the lower end of `β`, `δ₁`, `δ₂` and the excluded rank. -/
theorem boxPairCorr_sharp (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) {δ₁ δ₂ : ℝ}
    (h1 : FibreBound (probHaar (SU N)) (realFeature N) δ₁ (2 * β) (10 * β))
    (h2 : FibreBound (probHaar (SU N)) (realFeature N) δ₂ (4 * β) (8 * β))
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ₁1 : δ₁ ≤ 1) (hδ₂1 : δ₂ ≤ 1) :
    BoxPairCorr hN β (max (18 * δ₁) (12 * δ₁ + 3 * δ₂)) := by
  intro j
  refine ⟨pairDeltaSharp δ₁ δ₂ j, pairDeltaSharp_defect hδ₁ hδ₂ j, fun l m => ?_,
    pairCorrAt_sharp hN hβ0 j h1 h2 hδ₁ hδ₂⟩
  unfold pairDeltaSharp
  split_ifs
  · exact zero_le_one
  · exact hδ₁1
  · exact hδ₂1
  · exact zero_le_one

#print axioms boxPairCorr_sharp

end Sharp

/-! ## 5. The floor -/

section Floor

/-- **The capstone floor** `17N²/(88π²)`, the peak of `AsymptoticScaling.aRun N` and the least
`βUV` that `ClayRoutes.clay_continuum_of_boxPatchGap` admits (`_hpeak`).

DERIVED: `17`, `88`, `2` are the peak's constants as `ClayRoutes.clay_continuum_of_boxPatchGap`
states them (`17N²/(44π²)` of `aRunStd` at `β_std = 2β`). -/
def floorBeta (N : ℕ) : ℝ := 17 * (N : ℝ) ^ 2 / (88 * Real.pi ^ 2)

/-- The floor is positive.

DERIVED: `0` is the sign and the excluded rank. -/
theorem floorBeta_pos {N : ℕ} (hN : N ≠ 0) : 0 < floorBeta N := by
  unfold floorBeta
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  exact div_pos (mul_pos (by norm_num) (pow_pos hN' 2))
    (mul_pos (by norm_num) (pow_pos Real.pi_pos 2))

#print axioms floorBeta_pos

/-- **`floorBeta 2 ≤ 783/10000`** (`Real.pi_gt_d4`: `π² > 3.1415² > 680000/68904`).

DERIVED: `2` is the rank. CHOSEN: `783/10000` rounds `68/(88π²) = 0.0782936…` up at the fourth
decimal. -/
theorem floorBeta_two_le : floorBeta 2 ≤ 783 / 10000 := by
  unfold floorBeta
  have hπ : (3.1415 : ℝ) * 3.1415 < Real.pi * Real.pi :=
    mul_self_lt_mul_self (by norm_num) Real.pi_gt_d4
  have hpos : (0 : ℝ) < 88 * Real.pi ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  push_cast
  nlinarith [hπ]

#print axioms floorBeta_two_le

/-- **`floorBeta 3 ≤ 881/5000`** (`Real.pi_gt_d4`).

DERIVED: `3` is the rank. CHOSEN: `881/5000 = 0.1762` rounds `153/(88π²) = 0.1761608…` up at the
fourth decimal. -/
theorem floorBeta_three_le : floorBeta 3 ≤ 881 / 5000 := by
  unfold floorBeta
  have hπ : (3.1415 : ℝ) * 3.1415 < Real.pi * Real.pi :=
    mul_self_lt_mul_self (by norm_num) Real.pi_gt_d4
  have hpos : (0 : ℝ) < 88 * Real.pi ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  push_cast
  nlinarith [hπ]

#print axioms floorBeta_three_le

/-- **The numeric check of one pair type**: the rational side conditions and `dstar ≤ δ` at the
rational coupling `τ`, tilt `κ`, Haar constants `D, q4, t3` and square-root bounds `s ≥ √(q4/D)`,
`σ ≥ √M₂`. Every conjunct is decided by `norm_num` after unfolding `PairCheck`, `dstar`, `dstarNum`,
`dstarDen`, `dstarE`, `dstarZ`, `M2bound`, `mbarBound`, `cR`, `cR3`.

DERIVED: `0` is the lower end; `3` is the range of `TiltedHaar`'s `exp` bounds; `2` is the square. -/
def PairCheck (D q4 t3 s σ τ κ δ : ℝ) : Prop :=
  0 ≤ τ ∧ τ ≤ 3 ∧ 0 ≤ κ ∧ κ ≤ 3 ∧ 0 ≤ s ∧ 0 ≤ σ ∧ q4 / D ≤ s ^ 2 ∧
    M2bound D q4 t3 κ ≤ σ ^ 2 ∧ 0 < dstarZ τ (mbarBound D q4 t3 s κ) ∧
    0 < dstarDen τ (M2bound D q4 t3 κ) σ (mbarBound D q4 t3 s κ) (cR τ) ∧
    dstar τ (M2bound D q4 t3 κ) σ (mbarBound D q4 t3 s κ) (cR τ) ≤ δ

/-- **A numeric check gives a fibre bound** (`TiltedHaar.tiltBounds_of_haarConsts`,
`TiltedHaar.exp_sub_one_sub_le` at `r = τ`, `PairFibreAbstract.fibreBound_of_tiltBounds`,
`PairInterface.norm_realFeature`, `PairInterface.continuous_realFeature`).

DERIVED: `0` is the excluded rank. -/
theorem fibreBound_of_pairCheck {N : ℕ} (hN : N ≠ 0)
    (H : HaarConsts (probHaar (SU N)) (realFeature N)) {s σ τ κ δ : ℝ}
    (hc : PairCheck H.D H.q4 H.t3 s σ τ κ δ) :
    FibreBound (probHaar (SU N)) (realFeature N) δ τ κ := by
  obtain ⟨hτ0, hτ3, hκ0, hκ3, hs0, hσ0, hs, hM2, hZ, hden, hδ⟩ := hc
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
  have hc₂ : ∀ u : ℝ, |u| ≤ τ → Real.exp u - 1 - u ≤ cR τ * u ^ 2 :=
    fun u hu => exp_sub_one_sub_le hu hτ3
  have hF := fibreBound_of_tiltBounds hX hX1 hτ0 hM0 hmb0 (cR_nonneg hτ0) hTB hc₂ hσ0 hM2 hZ hden
  exact hF.mono hδ le_rfl le_rfl

#print axioms fibreBound_of_pairCheck

/-- **`SU(2)`, single pair** (`n2 = 2`): `dstar ≤ 133/2500` at `τ = 2 · 783/10000`,
`κ = 10 · 783/10000`.

DERIVED: `4`, `1/8`, `0` are `HaarMomentsSU2.haarConsts_su2`'s `D`, `q4`, `t3`; `2`, `10` are the
single pair's counts; `783/10000` is `floorBeta_two_le`'s bound. CHOSEN: `1768/10000 ≥ √(1/32)`,
`5484/10000 ≥ √M₂ = √0.300663…`; `133/2500 = 0.0532` rounds the computed `0.0531815…` up. -/
theorem pairCheck_su2_single :
    PairCheck 4 (1 / 8) 0 (1768 / 10000) (5484 / 10000) (2 * (783 / 10000)) (10 * (783 / 10000))
      (133 / 2500) := by
  norm_num [PairCheck, dstar, dstarNum, dstarDen, dstarE, dstarZ, M2bound, mbarBound, cR, cR3]

#print axioms pairCheck_su2_single

/-- **`SU(2)`, double pair** (`n2 = 4`, extent `2`).

DERIVED: `4`, `1/8`, `0` as in `pairCheck_su2_single`; `4`, `8` are the double pair's counts;
`783/10000` is `floorBeta_two_le`'s bound. CHOSEN: `1768/10000 ≥ √(1/32)`, `5297/10000 ≥ √M₂ =
√0.280567…`; `1103/10000` rounds the computed `0.1102716…` up. -/
theorem pairCheck_su2_double :
    PairCheck 4 (1 / 8) 0 (1768 / 10000) (5297 / 10000) (4 * (783 / 10000)) (8 * (783 / 10000))
      (1103 / 10000) := by
  norm_num [PairCheck, dstar, dstarNum, dstarDen, dstarE, dstarZ, M2bound, mbarBound, cR, cR3]

#print axioms pairCheck_su2_double

/-- **`SU(3)`, single pair.**

DERIVED: `18`, `1/96`, `1/108` are `HaarMomentsSU3.haarConsts_su3`'s `D`, `q4`, `t3`; `2`, `10` are
the single pair's counts; `881/5000` is `floorBeta_three_le`'s bound. CHOSEN: `2406/100000 ≥ √(1/1728)`,
`3226/10000 ≥ √M₂ = √0.104061…`; `469/10000` rounds the computed `0.0468780…` up. -/
theorem pairCheck_su3_single :
    PairCheck 18 (1 / 96) (1 / 108) (2406 / 100000) (3226 / 10000) (2 * (881 / 5000))
      (10 * (881 / 5000)) (469 / 10000) := by
  norm_num [PairCheck, dstar, dstarNum, dstarDen, dstarE, dstarZ, M2bound, mbarBound, cR, cR3]

#print axioms pairCheck_su3_single

/-- **`SU(3)`, double pair.**

DERIVED: `18`, `1/96`, `1/108` as in `pairCheck_su3_single`; `4`, `8` are the double pair's counts;
`881/5000` is `floorBeta_three_le`'s bound. CHOSEN: `2406/100000 ≥ √(1/1728)`,
`2937/10000 ≥ √M₂ = √0.086242…`; `121/1250 = 0.0968` rounds the computed `0.0967742…` up. -/
theorem pairCheck_su3_double :
    PairCheck 18 (1 / 96) (1 / 108) (2406 / 100000) (2937 / 10000) (4 * (881 / 5000))
      (8 * (881 / 5000)) (121 / 1250) := by
  norm_num [PairCheck, dstar, dstarNum, dstarDen, dstarE, dstarZ, M2bound, mbarBound, cR, cR3]

#print axioms pairCheck_su3_double

/-- **The `SU(2)` box pair correlation at the floor**: `Δ = max(18 · 133/2500, 12 · 133/2500 +
3 · 1103/10000) = 9693/10000` (`fibreBound_of_pairCheck`, `FibreBound.mono` with `floorBeta_two_le`,
`boxPairCorr_sharp`).

DERIVED: `2` is the rank; `9693/10000 = 12 · 0.0532 + 3 · 0.1103`, the larger branch. -/
theorem boxPairCorr_floor_su2 (h2 : (2 : ℕ) ≠ 0) :
    BoxPairCorr h2 (floorBeta 2) (9693 / 10000) := by
  have hb := floorBeta_two_le
  have hb0 := (floorBeta_pos h2).le
  have hF1 : FibreBound (probHaar (SU 2)) (realFeature 2) (133 / 2500) (2 * floorBeta 2)
      (10 * floorBeta 2) :=
    (fibreBound_of_pairCheck h2 HaarMomentsSU2.haarConsts_su2 pairCheck_su2_single).mono le_rfl
      (by linarith) (by linarith)
  have hF2 : FibreBound (probHaar (SU 2)) (realFeature 2) (1103 / 10000) (4 * floorBeta 2)
      (8 * floorBeta 2) :=
    (fibreBound_of_pairCheck h2 HaarMomentsSU2.haarConsts_su2 pairCheck_su2_double).mono le_rfl
      (by linarith) (by linarith)
  have h := boxPairCorr_sharp h2 hb0 hF1 hF2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hmax : max (18 * (133 / 2500 : ℝ)) (12 * (133 / 2500) + 3 * (1103 / 10000))
      = 9693 / 10000 := by
    rw [max_eq_right (show (18 * (133 / 2500 : ℝ)) ≤ 12 * (133 / 2500) + 3 * (1103 / 10000) by
      norm_num)]
    norm_num
  rw [hmax] at h
  exact h

#print axioms boxPairCorr_floor_su2

/-- **The `SU(3)` box pair correlation at the floor**: `Δ = 12 · 0.0469 + 3 · 0.0968 = 2133/2500`.

DERIVED: `3` is the rank; `2133/2500 = 0.8532`, the larger branch of `max(18δ₁, 12δ₁ + 3δ₂)`. -/
theorem boxPairCorr_floor_su3 (h3 : (3 : ℕ) ≠ 0) :
    BoxPairCorr h3 (floorBeta 3) (2133 / 2500) := by
  have hb := floorBeta_three_le
  have hb0 := (floorBeta_pos h3).le
  have hF1 : FibreBound (probHaar (SU 3)) (realFeature 3) (469 / 10000) (2 * floorBeta 3)
      (10 * floorBeta 3) :=
    (fibreBound_of_pairCheck h3 HaarMomentsSU3.haarConsts_su3 pairCheck_su3_single).mono le_rfl
      (by linarith) (by linarith)
  have hF2 : FibreBound (probHaar (SU 3)) (realFeature 3) (121 / 1250) (4 * floorBeta 3)
      (8 * floorBeta 3) :=
    (fibreBound_of_pairCheck h3 HaarMomentsSU3.haarConsts_su3 pairCheck_su3_double).mono le_rfl
      (by linarith) (by linarith)
  have h := boxPairCorr_sharp h3 hb0 hF1 hF2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hmax : max (18 * (469 / 10000 : ℝ)) (12 * (469 / 10000) + 3 * (121 / 1250))
      = 2133 / 2500 := by
    rw [max_eq_right (show (18 * (469 / 10000 : ℝ)) ≤ 12 * (469 / 10000) + 3 * (121 / 1250) by
      norm_num)]
    norm_num
  rw [hmax] at h
  exact h

#print axioms boxPairCorr_floor_su3

/-- **THE `SU(2)` BOX CHECK AT THE FLOOR**: side `2606`, gap `307/10000`
(`BoxGap.boxPairDefect_of_pairCorr`, `BoxGap.boxLocalGap_of_pairDefect`, which holds at every side).
At this side the threshold `(40n − 36)/n² ≈ 0.01534` is about half the gap, so the box's Knabe constant,
and with it the IR rate `HeatBathLocal.boxRate` the UV step must beat, is about half the gap.

DERIVED: `2` is the rank and `0` in `2 ≠ 0` its non-vanishing; `307/10000 = 1 − 9693/10000`;
`40`, `36` are the threshold's. CHOSEN:
`2606 = ⌈80/(307/10000)⌉₊`, the side at which the threshold is about half the gap. -/
theorem boxPatchGap_floor_su2 (h2 : (2 : ℕ) ≠ 0) :
    BoxPatch.BoxPatchGap h2 (floorBeta 2) 2606 (307 / 10000) := by
  have h := boxLocalGap_of_pairDefect h2 2606
    (boxPairDefect_of_pairCorr h2 (boxPairCorr_floor_su2 h2))
  have hg : (1 : ℝ) - 9693 / 10000 = 307 / 10000 := by norm_num
  rw [hg] at h
  exact ⟨by norm_num, by norm_num, h⟩

#print axioms boxPatchGap_floor_su2

/-- **THE `SU(3)` BOX CHECK AT THE FLOOR**: side `545`, gap `367/2500`
(`BoxGap.boxLocalGap_of_pairDefect`); the threshold `(40n − 36)/n² ≈ 0.07327` is about half the gap.

DERIVED: `3` is the rank and `0` in `3 ≠ 0` its non-vanishing; `367/2500 = 1 − 2133/2500`;
`40`, `36` are the threshold's. CHOSEN:
`545 = ⌈80/(367/2500)⌉₊`, the side at which the threshold is about half the gap. -/
theorem boxPatchGap_floor_su3 (h3 : (3 : ℕ) ≠ 0) :
    BoxPatch.BoxPatchGap h3 (floorBeta 3) 545 (367 / 2500) := by
  have h := boxLocalGap_of_pairDefect h3 545
    (boxPairDefect_of_pairCorr h3 (boxPairCorr_floor_su3 h3))
  have hg : (1 : ℝ) - 2133 / 2500 = 367 / 2500 := by norm_num
  rw [hg] at h
  exact ⟨by norm_num, by norm_num, h⟩

#print axioms boxPatchGap_floor_su3

end Floor

/-! ## 6. The continuum statement at the floor -/

section Capstone

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger

/-- **THE CONTINUUM CLAY STATEMENT AT THE FLOOR, `SU(2)`.** `ClayRoutes.clay_continuum_of_boxPatchGap`
at `β₀ = βUV = floorBeta 2` (`_hpeak` by `le_rfl`, `floorBeta_pos`), `boxPatchGap_floor_su2`; the open
inputs E (`hB`), N (`hconv`), Y (`hY`) and the UV step below the box's rate (`huv`) are carried.

DERIVED: `2` is the rank; `0` is the reflection plane and the lower end of `L`; `4` in `Fin 4` is
the spacetime dimension; `2606`, `307/10000` are `boxPatchGap_floor_su2`'s side and gap. -/
theorem clay_continuum_floor_su2 (h2 : (2 : ℕ) ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU 2) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep h2 (Renorm.connected h2 Z)) {L : ℝ} (hL : 0 < L)
    (huv : ClayRoutes.UVBelowIR τ 0 h2 (floorBeta 2) (floorBeta 2)
      (HeatBathLocal.boxRate 2 (floorBeta 2) 2606 (307 / 10000)))
    (O : LField (MassGap.SUN.SU 2)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep h2 (Renorm.connected h2 Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum h2 Z τ hZ hB L :=
  ClayRoutes.clay_continuum_of_boxPatchGap (by norm_num) h2 Z τ hZ hB hL
    (β₀ := floorBeta 2) (βUV := floorBeta 2) (floorBeta_pos h2) le_rfl le_rfl
    (boxPatchGap_floor_su2 h2) huv O G hconv hY

#print axioms clay_continuum_floor_su2

/-- **THE CONTINUUM CLAY STATEMENT AT THE FLOOR, `SU(3)`.**

DERIVED: `3` is the rank; `0` is the reflection plane and the lower end of `L`; `4` in `Fin 4` is
the spacetime dimension; `545`, `367/2500` are `boxPatchGap_floor_su3`'s side and gap. -/
theorem clay_continuum_floor_su3 (h3 : (3 : ℕ) ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU 3) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep h3 (Renorm.connected h3 Z)) {L : ℝ} (hL : 0 < L)
    (huv : ClayRoutes.UVBelowIR τ 0 h3 (floorBeta 3) (floorBeta 3)
      (HeatBathLocal.boxRate 3 (floorBeta 3) 545 (367 / 2500)))
    (O : LField (MassGap.SUN.SU 3)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep h3 (Renorm.connected h3 Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum h3 Z τ hZ hB L :=
  ClayRoutes.clay_continuum_of_boxPatchGap (by norm_num) h3 Z τ hZ hB hL
    (β₀ := floorBeta 3) (βUV := floorBeta 3) (floorBeta_pos h3) le_rfl le_rfl
    (boxPatchGap_floor_su3 h3) huv O G hconv hY

#print axioms clay_continuum_floor_su3

end Capstone

end MassGap.PairCorrSharp
