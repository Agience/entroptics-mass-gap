import Mathlib
import MassGap.HeatBath
import MassGap.PairCorr
import MassGap.FibrePerturb
import MassGap.PairCorrSharp

/-!
# MassGap.WeightedHeatBath — the heat bath of an arbitrary positive continuous weight

The box-gap chain builds its conditional expectations from the heat bath of the Wilson weight
`HeatBath.wt bd β` (`HeatBath.heatAvg`). An observer's coarse theory is Wilson times further local
factors (adjacent-plaquette products), so the chain is restated over an abstract weight `Φ`. This
module is that restatement's first layer: the heat bath of any positive continuous weight on the
link variables, the facts about it that never read the weight's form, and the identification of the
Wilson heat bath as its instance at `Φ = wt bd β`, by definition.

## What it gives

* `wNum`, `wPart`, `wAvg`: numerator, normalisation and heat bath of `Φ` at a link.
* `wPart_pos`, `wAvg_update`, `wAvg_of_readsNot`, `wAvg_mul_left`: positivity of the normalisation,
  the heat bath not reading its own link, fixing what does not read it, and pulling out a factor that
  does not read it. None of these uses more of `Φ` than positivity and continuity.
* `heatAvg_eq_wAvg`: `HeatBath.heatAvg bd β = wAvg (wt bd β)`, so every statement here specialises to
  the Wilson chain with no second definition of its heat bath.
-/

namespace MassGap.WeightedHeatBath

open MeasureTheory
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.HeatBathErgodic (havg continuous_havg havg_update havg_update_other havg_sub
  integral_havg haar_integrable)
open MassGap.PairCorr (heatAvg2 heatNum2 integral_pos_of_pos pairLocSum pairRestSum wt_split_pair)
open MassGap.WilsonLattice (wilsonHol)
open MassGap.WilsonAction (wilsonDensity continuous_wilsonDensity wilsonDensity_nonneg wilsonDensity_le_two)
open MassGap.PlaqVariance (continuous_wilsonHol)
open MassGap.FibrePerturb (CovBoundOn pW covBoundOn_perturb_cont covBoundOn_const_mul)
open MassGap.HeatBath (bdT wilsonHol_update_of_not_mem wt_pos continuous_wt heatAvg wt exists_abs_le integrable_of_abs_le locW restSum wt_split
  restSum_update continuous_locW SharePlaq not_sharePlaq_symm locW_update_other)

variable {N : ℕ} {Lk : Type} [DecidableEq Lk]

/-- The heat-bath numerator of the weight `Φ` at the link `l`: `∫ g, f(W[l ↦ g]) Φ(W[l ↦ g]) dg`. -/
noncomputable def wNum (Φ : (Lk → SU N) → ℝ) (l : Lk) (f : (Lk → SU N) → ℝ) (W : Lk → SU N) : ℝ :=
  ∫ g, f (Function.update W l g) * Φ (Function.update W l g) ∂(probHaar (SU N))

/-- The heat-bath normalisation of the weight `Φ` at the link `l`: `∫ g, Φ(W[l ↦ g]) dg`. -/
noncomputable def wPart (Φ : (Lk → SU N) → ℝ) (l : Lk) (W : Lk → SU N) : ℝ :=
  ∫ g, Φ (Function.update W l g) ∂(probHaar (SU N))

/-- **The heat bath of the weight `Φ` at the link `l`**: `wNum / wPart`. -/
noncomputable def wAvg (Φ : (Lk → SU N) → ℝ) (l : Lk) (f : (Lk → SU N) → ℝ) (W : Lk → SU N) : ℝ :=
  wNum Φ l f W / wPart Φ l W

/-- The normalisation is positive for a positive continuous weight on the compact group.

DERIVED: `0` is the sign asserted; `1` is the Haar mass of the group. -/
theorem wPart_pos {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) (l : Lk)
    (W : Lk → SU N) : 0 < wPart Φ l W := by
  have hc : Continuous (fun g : SU N => Φ (Function.update W l g)) :=
    hcont.comp (continuous_const.update l continuous_id)
  obtain ⟨C, hC⟩ := exists_abs_le hc
  have hint : Integrable (fun g : SU N => Φ (Function.update W l g)) (probHaar (SU N)) :=
    integrable_of_abs_le _ hc.measurable hC
  unfold wPart
  rw [integral_pos_iff_support_of_nonneg (fun g => (hpos _).le) hint]
  have hsupp : Function.support (fun g : SU N => Φ (Function.update W l g)) = Set.univ :=
    Set.eq_univ_of_forall (fun g => Function.mem_support.mpr (hpos _).ne')
  rw [hsupp, measure_univ]
  exact one_pos

#print axioms wPart_pos

/-- The heat bath does not read the variable at `l` (`Function.update_idem`).

DERIVED: no numeral. -/
theorem wAvg_update (Φ : (Lk → SU N) → ℝ) (l : Lk) (f : (Lk → SU N) → ℝ) (W : Lk → SU N)
    (h : SU N) : wAvg Φ l f (Function.update W l h) = wAvg Φ l f W := by
  simp only [wAvg, wNum, wPart, Function.update_idem]

#print axioms wAvg_update

/-- **The heat bath fixes every function not reading `l`.**

DERIVED: no numeral. -/
theorem wAvg_of_readsNot {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    (l : Lk) {f : (Lk → SU N) → ℝ} (hf : ∀ W g, f (Function.update W l g) = f W) (W : Lk → SU N) :
    wAvg Φ l f W = f W := by
  unfold wAvg wNum
  simp only [hf, integral_const_mul]
  exact mul_div_cancel_right₀ _ (wPart_pos hpos hcont l W).ne'

#print axioms wAvg_of_readsNot

/-- **A factor not reading `l` comes out on the left.**

DERIVED: no numeral. -/
theorem wAvg_mul_left (Φ : (Lk → SU N) → ℝ) (l : Lk) {a f : (Lk → SU N) → ℝ}
    (ha : ∀ W g, a (Function.update W l g) = a W) (W : Lk → SU N) :
    wAvg Φ l (fun V => a V * f V) W = a W * wAvg Φ l f W := by
  unfold wAvg wNum
  simp only [ha, mul_assoc, integral_const_mul]
  exact mul_div_assoc _ _ _

#print axioms wAvg_mul_left

/-- **The Wilson heat bath is the instance at `Φ = wt bd β`**, by definition: every statement about
`wAvg` specialises to `HeatBath.heatAvg` with no second definition of its heat bath.

DERIVED: no numeral. -/
theorem heatAvg_eq_wAvg {Pq : Type} [Fintype Lk] [Fintype Pq] (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (l : Lk) (f : (Lk → SU N) → ℝ) (W : Lk → SU N) :
    heatAvg bd β l f W = wAvg (wt bd β) l f W := rfl

#print axioms heatAvg_eq_wAvg

/-! ## Local weights: the factorisation the commutation of heat baths needs -/

/-- **A local weight**: at every link `l` the weight factors as `Φ = loc l · rest l`, with `rest l`
nowhere zero and not reading `l`, `loc l` continuous, and an interaction relation `R` such that
`loc l` does not read `l'` unless `R l l'`. The Wilson weight is one (`wilsonLocal`, with `R` sharing a
plaquette); Wilson times adjacent-plaquette products is another, with a wider `R`. -/
structure LocalWeight (N : ℕ) (Lk : Type) [DecidableEq Lk] where
  Φ : (Lk → SU N) → ℝ
  loc : Lk → (Lk → SU N) → ℝ
  rest : Lk → (Lk → SU N) → ℝ
  R : Lk → Lk → Prop
  split : ∀ l W, Φ W = loc l W * rest l W
  rest_update : ∀ l W g, rest l (Function.update W l g) = rest l W
  rest_ne : ∀ l W, rest l W ≠ 0
  loc_cont : ∀ l, Continuous (loc l)
  R_symm : ∀ l l', ¬ R l l' → ¬ R l' l
  loc_update_other : ∀ l l', ¬ R l l' → ∀ W h, loc l (Function.update W l' h) = loc l W

/-- **The heat bath reads only the local factor**: `rest l` does not read `l` and cancels between
numerator and normalisation.

DERIVED: no numeral. -/
theorem wAvg_eq_loc (L : LocalWeight N Lk) (l : Lk) (f : (Lk → SU N) → ℝ) (W : Lk → SU N) :
    wAvg L.Φ l f W
      = (∫ g, f (Function.update W l g) * L.loc l (Function.update W l g) ∂(probHaar (SU N)))
        / ∫ g, L.loc l (Function.update W l g) ∂(probHaar (SU N)) := by
  have hw : ∀ g, L.Φ (Function.update W l g) = L.loc l (Function.update W l g) * L.rest l W := by
    intro g
    rw [L.split l, L.rest_update]
  unfold wAvg wNum wPart
  simp only [hw, ← mul_assoc, integral_mul_const]
  exact mul_div_mul_right _ _ (L.rest_ne l W)

#print axioms wAvg_eq_loc

/-- **Two heat baths as one double integral**, at links `l ≠ l'` that do not interact.

DERIVED: no numeral. -/
theorem wAvg_wAvg_eq (L : LocalWeight N Lk) {l l' : Lk} (hll : l ≠ l') (hs : ¬ L.R l l')
    (f : (Lk → SU N) → ℝ) (W : Lk → SU N) :
    wAvg L.Φ l (wAvg L.Φ l' f) W
      = (∫ g, ∫ h, f (Function.update (Function.update W l g) l' h)
            * (L.loc l' (Function.update W l' h) * L.loc l (Function.update W l g))
            ∂(probHaar (SU N)) ∂(probHaar (SU N)))
        / ((∫ h, L.loc l' (Function.update W l' h) ∂(probHaar (SU N)))
            * ∫ g, L.loc l (Function.update W l g) ∂(probHaar (SU N))) := by
  have hE' : ∀ (V : Lk → SU N) (g : SU N), L.loc l' (Function.update V l g) = L.loc l' V :=
    fun V g => L.loc_update_other l' l (L.R_symm l l' hs) V g
  have hinner : ∀ g, wAvg L.Φ l' f (Function.update W l g)
      = (∫ h, f (Function.update (Function.update W l g) l' h)
            * L.loc l' (Function.update W l' h) ∂(probHaar (SU N)))
        / ∫ h, L.loc l' (Function.update W l' h) ∂(probHaar (SU N)) := by
    intro g
    rw [wAvg_eq_loc L l' f (Function.update W l g)]
    have hc : ∀ h, L.loc l' (Function.update (Function.update W l g) l' h)
        = L.loc l' (Function.update W l' h) := by
      intro h
      rw [Function.update_comm hll g h W, hE']
    simp only [hc]
  have hnum : ∀ g, wAvg L.Φ l' f (Function.update W l g) * L.loc l (Function.update W l g)
      = (∫ h, f (Function.update (Function.update W l g) l' h)
            * (L.loc l' (Function.update W l' h) * L.loc l (Function.update W l g))
            ∂(probHaar (SU N)))
        / ∫ h, L.loc l' (Function.update W l' h) ∂(probHaar (SU N)) := by
    intro g
    rw [hinner g, div_mul_eq_mul_div, ← integral_mul_const]
    simp only [mul_assoc]
  rw [wAvg_eq_loc L l (wAvg L.Φ l' f) W]
  simp only [hnum]
  rw [integral_div, div_div]

#print axioms wAvg_wAvg_eq

/-- **Heat baths at non-interacting links commute** on continuous functions: the double integral of
`wAvg_wAvg_eq` is symmetric by `Function.update_comm` and `integral_integral_swap`.

DERIVED: no numeral. -/
theorem wAvg_comm (L : LocalWeight N Lk) {l l' : Lk} (hll : l ≠ l') (hs : ¬ L.R l l')
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) (W : Lk → SU N) :
    wAvg L.Φ l (wAvg L.Φ l' f) W = wAvg L.Φ l' (wAvg L.Φ l f) W := by
  rw [wAvg_wAvg_eq L hll hs f W, wAvg_wAvg_eq L (Ne.symm hll) (L.R_symm l l' hs) f W,
    mul_comm (∫ h, L.loc l (Function.update W l h) ∂(probHaar (SU N)))]
  congr 1
  have hu2 : Continuous (fun p : SU N × SU N =>
      Function.update (Function.update W l p.1) l' p.2) :=
    ((continuous_const : Continuous fun _ : SU N × SU N => W).update l continuous_fst).update l'
      continuous_snd
  have hu1 : Continuous (fun p : SU N × SU N => Function.update W l p.1) :=
    continuous_const.update l continuous_fst
  have hu1' : Continuous (fun p : SU N × SU N => Function.update W l' p.2) :=
    continuous_const.update l' continuous_snd
  have hcont : Continuous (fun p : SU N × SU N =>
      f (Function.update (Function.update W l p.1) l' p.2)
        * (L.loc l' (Function.update W l' p.2) * L.loc l (Function.update W l p.1))) :=
    (hf.comp hu2).mul (((L.loc_cont l').comp hu1').mul ((L.loc_cont l).comp hu1))
  obtain ⟨C, hC⟩ := exists_abs_le hcont
  have hint : Integrable (Function.uncurry fun g h =>
      f (Function.update (Function.update W l g) l' h)
        * (L.loc l' (Function.update W l' h) * L.loc l (Function.update W l g)))
      ((probHaar (SU N)).prod (probHaar (SU N))) :=
    integrable_of_abs_le _ hcont.measurable hC
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun h => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
  show f (Function.update (Function.update W l g) l' h)
      * (L.loc l' (Function.update W l' h) * L.loc l (Function.update W l g))
    = f (Function.update (Function.update W l' h) l g)
      * (L.loc l (Function.update W l g) * L.loc l' (Function.update W l' h))
  rw [Function.update_comm hll g h W, mul_comm (L.loc l' (Function.update W l' h))]

#print axioms wAvg_comm

/-- **The Wilson weight is a local weight**: `wt = locW · e^{−β restSum}` (`HeatBath.wt_split`), the rest
not reading `l` (`HeatBath.restSum_update`), `locW` continuous and not reading links outside the
plaquettes through `l` (`HeatBath.locW_update_other`), the relation sharing a plaquette.

DERIVED: no numeral. -/
noncomputable def wilsonLocal {Pq : Type} [Fintype Lk] [Fintype Pq] (bd : Pq → List (Lk × Bool))
    (β : ℝ) : LocalWeight N Lk where
  Φ := wt bd β
  loc := locW bd β
  rest := fun l W => Real.exp (-β * restSum bd l W)
  R := SharePlaq bd
  split := fun l W => wt_split bd β l W
  rest_update := fun l W g => by simp only [restSum_update]
  rest_ne := fun _ _ => (Real.exp_pos _).ne'
  loc_cont := fun l => continuous_locW bd β l
  R_symm := fun _ _ h => not_sharePlaq_symm h
  loc_update_other := fun _ _ h W g => locW_update_other bd β h W g

/-- **The Wilson local weight's `Φ` is the Wilson weight**, by definition, so `wAvg_comm` at
`wilsonLocal` is the commutation of the Wilson heat baths at links sharing no plaquette.

DERIVED: no numeral. -/
theorem wilsonLocal_Φ {Pq : Type} [Fintype Lk] [Fintype Pq] (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    (wilsonLocal (N := N) bd β).Φ = wt bd β := rfl

#print axioms wilsonLocal_Φ


/-! ## The two-link heat bath of a weight -/

section TwoLink

variable [Fintype Lk]

/-- The two-link numerator of the weight `Φ`: the Haar average at `m` of the Haar average at `l` of
`f Φ`. -/
noncomputable def w2Num (Φ : (Lk → SU N) → ℝ) (l m : Lk) (f : (Lk → SU N) → ℝ) (W : Lk → SU N) : ℝ :=
  havg m (havg l (fun V => f V * Φ V)) W

/-- The two-link normalisation of the weight `Φ`. -/
noncomputable def w2Part (Φ : (Lk → SU N) → ℝ) (l m : Lk) (W : Lk → SU N) : ℝ :=
  havg m (havg l Φ) W

/-- **The two-link heat bath of the weight `Φ`**: `w2Num / w2Part`. -/
noncomputable def w2Avg (Φ : (Lk → SU N) → ℝ) (l m : Lk) (f : (Lk → SU N) → ℝ) (W : Lk → SU N) : ℝ :=
  w2Num Φ l m f W / w2Part Φ l m W

/-- **The Wilson two-link heat bath is the instance at `Φ = wt bd β`**, by definition.

DERIVED: no numeral. -/
theorem heatAvg2_eq_w2Avg {Pq : Type} [Fintype Pq] (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (l m : Lk) (f : (Lk → SU N) → ℝ) (W : Lk → SU N) :
    heatAvg2 bd β l m f W = w2Avg (wt bd β) l m f W := rfl

#print axioms heatAvg2_eq_w2Avg

/-- The two-link normalisation is positive.

DERIVED: `0` is the sign asserted. -/
theorem w2Part_pos {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) (l m : Lk)
    (W : Lk → SU N) : 0 < w2Part Φ l m W := by
  show 0 < ∫ h, havg l Φ (Function.update W m h) ∂(probHaar (SU N))
  exact integral_pos_of_pos ((continuous_havg l hcont).comp (continuous_const.update m continuous_id))
    (fun h => wPart_pos hpos hcont l (Function.update W m h))

#print axioms w2Part_pos

/-- The two-link heat bath of a continuous function is continuous.

DERIVED: no numeral. -/
theorem continuous_w2Avg {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    (l m : Lk) {f : (Lk → SU N) → ℝ} (hf : Continuous f) : Continuous (w2Avg Φ l m f) :=
  (continuous_havg m (continuous_havg l (hf.mul hcont))).div
    (continuous_havg m (continuous_havg l hcont)) (fun W => (w2Part_pos hpos hcont l m W).ne')

#print axioms continuous_w2Avg

/-- The two-link heat bath does not read `m`.

DERIVED: no numeral. -/
theorem w2Avg_update_m (Φ : (Lk → SU N) → ℝ) (l m : Lk) (f : (Lk → SU N) → ℝ) (W : Lk → SU N)
    (h : SU N) : w2Avg Φ l m f (Function.update W m h) = w2Avg Φ l m f W := by
  simp only [w2Avg, w2Num, w2Part, havg_update]

#print axioms w2Avg_update_m

/-- The two-link heat bath does not read `l`, for `l ≠ m`.

DERIVED: no numeral. -/
theorem w2Avg_update_l (Φ : (Lk → SU N) → ℝ) {l m : Lk} (hlm : l ≠ m) (f : (Lk → SU N) → ℝ)
    (W : Lk → SU N) (g : SU N) : w2Avg Φ l m f (Function.update W l g) = w2Avg Φ l m f W := by
  unfold w2Avg w2Num w2Part
  rw [havg_update_other (φ := havg l (fun V => f V * Φ V)) (Ne.symm hlm)
      (fun V g' => havg_update l _ V g') W g,
    havg_update_other (φ := havg l Φ) (Ne.symm hlm) (fun V g' => havg_update l _ V g') W g]

#print axioms w2Avg_update_l

/-- **The two-link heat bath fixes every function reading neither `l` nor `m`.**

DERIVED: no numeral. -/
theorem w2Avg_of_readsNot {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    (l m : Lk) {f : (Lk → SU N) → ℝ} (hl : ∀ W g, f (Function.update W l g) = f W)
    (hm : ∀ W h, f (Function.update W m h) = f W) (W : Lk → SU N) : w2Avg Φ l m f W = f W := by
  have hnum : w2Num Φ l m f W = f W * w2Part Φ l m W := by
    unfold w2Num w2Part havg
    simp only [hl, hm, integral_const_mul]
  unfold w2Avg
  rw [hnum]
  exact mul_div_cancel_right₀ _ (w2Part_pos hpos hcont l m W).ne'

#print axioms w2Avg_of_readsNot

/-- The heat bath of a continuous function is continuous.

DERIVED: no numeral. -/
theorem continuous_wAvg {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) (l : Lk)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) : Continuous (wAvg Φ l f) :=
  (continuous_havg l (hf.mul hcont)).div (continuous_havg l hcont)
    (fun W => (wPart_pos hpos hcont l W).ne')

#print axioms continuous_wAvg

/-- **The Gibbs correlation bound from a fibre bound, for any positive continuous weight**
(`PairCorrSharp.gibbs_corr_le_of_fibre` with the Wilson weight replaced by `Φ`; its proof uses only
positivity and continuity of the weight).

DERIVED: `0` is the sign of `c` and the vanishing numerator and mean; `2` is the square and the
halving. -/
theorem w_gibbs_corr_le_of_fibre {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    {l m : Lk} (hlm : l ≠ m)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) (hzero : ∀ W, w2Num Φ l m f W = 0)
    {c : ℝ} (hc : 0 ≤ c)
    (hfib : ∀ (W : Lk → SU N) (a b : SU N → ℝ), Continuous a → Continuous b →
      ∫ h, a h * havg l (Φ) (Function.update W m h) ∂(probHaar (SU N)) = 0 →
      ∫ h, ∫ g, a h * b g * Φ (Function.update (Function.update W m h) l g)
          ∂(probHaar (SU N)) ∂(probHaar (SU N))
        ≤ c / 2 * (∫ h, a h ^ 2 * havg l (Φ) (Function.update W m h)
              ∂(probHaar (SU N))
            + ∫ g, b g ^ 2 * havg m (Φ) (Function.update W l g) ∂(probHaar (SU N)))) :
    ∫ W, wAvg Φ l f W * wAvg Φ m f W * Φ W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      ≤ c / 2 * (∫ W, wAvg Φ l f W * wAvg Φ l f W * Φ W
            ∂(Measure.pi fun _ : Lk => probHaar (SU N))
          + ∫ W, wAvg Φ m f W * wAvg Φ m f W * Φ W
            ∂(Measure.pi fun _ : Lk => probHaar (SU N))) := by
  have hml : m ≠ l := Ne.symm hlm
  have cA := continuous_wAvg hpos hcont l hf
  have cB := continuous_wAvg hpos hcont m hf
  have cw := hcont
  have cAB : Continuous (fun V => wAvg Φ l f V * wAvg Φ m f V * Φ V) :=
    (cA.mul cB).mul cw
  have cAA : Continuous (fun V => wAvg Φ l f V * wAvg Φ l f V * Φ V) :=
    (cA.mul cA).mul cw
  have cBB : Continuous (fun V => wAvg Φ m f V * wAvg Φ m f V * Φ V) :=
    (cB.mul cB).mul cw
  have e1 : ∫ W, wAvg Φ l f W * wAvg Φ m f W * Φ W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      = ∫ W, havg m (havg l (fun V => wAvg Φ l f V * wAvg Φ m f V * Φ V)) W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N)) :=
    ((integral_havg m (continuous_havg l cAB)).trans (integral_havg l cAB)).symm
  have e2 : ∫ W, wAvg Φ l f W * wAvg Φ l f W * Φ W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      = ∫ W, havg m (havg l (fun V => wAvg Φ l f V * wAvg Φ l f V * Φ V)) W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N)) :=
    ((integral_havg m (continuous_havg l cAA)).trans (integral_havg l cAA)).symm
  have e3 : ∫ W, wAvg Φ m f W * wAvg Φ m f W * Φ W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      = ∫ W, havg l (havg m (fun V => wAvg Φ m f V * wAvg Φ m f V * Φ V)) W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N)) :=
    ((integral_havg l (continuous_havg m cBB)).trans (integral_havg m cBB)).symm
  -- the fibre bound at every frozen configuration (`PairCorr.fibre_corr_config` with `hfib`)
  have hpt : ∀ W, havg m (havg l (fun V => wAvg Φ l f V * wAvg Φ m f V * Φ V)) W
      ≤ c / 2 * (havg m (havg l (fun V => wAvg Φ l f V * wAvg Φ l f V * Φ V)) W
        + havg l (havg m (fun V => wAvg Φ m f V * wAvg Φ m f V * Φ V)) W) := by
    intro W
    have ha : Continuous (fun h => wAvg Φ l f (Function.update W m h)) :=
      (continuous_wAvg hpos hcont l hf).comp (continuous_const.update m continuous_id)
    have hb : Continuous (fun g => wAvg Φ m f (Function.update W l g)) :=
      (continuous_wAvg hpos hcont m hf).comp (continuous_const.update l continuous_id)
    have hz : ∫ h, wAvg Φ l f (Function.update W m h)
        * havg l (Φ) (Function.update W m h) ∂(probHaar (SU N)) = 0 := by
      have e : ∀ h, wAvg Φ l f (Function.update W m h)
          * havg l (Φ) (Function.update W m h)
          = wNum Φ l f (Function.update W m h) := fun h =>
        div_mul_cancel₀ _ (wPart_pos hpos hcont l _).ne'
      calc ∫ h, wAvg Φ l f (Function.update W m h)
            * havg l (Φ) (Function.update W m h) ∂(probHaar (SU N))
          = ∫ h, wNum Φ l f (Function.update W m h) ∂(probHaar (SU N)) :=
            integral_congr_ae (Filter.Eventually.of_forall e)
        _ = 0 := hzero W
    have key := hfib W (fun h => wAvg Φ l f (Function.update W m h))
      (fun g => wAvg Φ m f (Function.update W l g)) ha hb hz
    have E1 : havg m (havg l (fun V => wAvg Φ l f V * wAvg Φ m f V * Φ V)) W
        = ∫ h, ∫ g, wAvg Φ l f (Function.update W m h)
            * wAvg Φ m f (Function.update W l g)
            * Φ (Function.update (Function.update W m h) l g)
            ∂(probHaar (SU N)) ∂(probHaar (SU N)) := by
      unfold havg
      refine integral_congr_ae (Filter.Eventually.of_forall (fun h => ?_))
      refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
      show wAvg Φ l f (Function.update (Function.update W m h) l g)
          * wAvg Φ m f (Function.update (Function.update W m h) l g)
          * Φ (Function.update (Function.update W m h) l g)
        = wAvg Φ l f (Function.update W m h) * wAvg Φ m f (Function.update W l g)
          * Φ (Function.update (Function.update W m h) l g)
      rw [wAvg_update Φ l f (Function.update W m h) g, Function.update_comm hml h g W,
        wAvg_update Φ m f (Function.update W l g) h]
    have E2 : havg m (havg l (fun V => wAvg Φ l f V * wAvg Φ l f V * Φ V)) W
        = ∫ h, wAvg Φ l f (Function.update W m h) ^ 2
            * havg l (Φ) (Function.update W m h) ∂(probHaar (SU N)) := by
      unfold havg
      refine integral_congr_ae (Filter.Eventually.of_forall (fun h => ?_))
      show ∫ g, wAvg Φ l f (Function.update (Function.update W m h) l g)
            * wAvg Φ l f (Function.update (Function.update W m h) l g)
            * Φ (Function.update (Function.update W m h) l g) ∂(probHaar (SU N))
        = wAvg Φ l f (Function.update W m h) ^ 2
          * ∫ g, Φ (Function.update (Function.update W m h) l g) ∂(probHaar (SU N))
      simp only [wAvg_update, integral_const_mul, sq]
    have E3 : havg l (havg m (fun V => wAvg Φ m f V * wAvg Φ m f V * Φ V)) W
        = ∫ g, wAvg Φ m f (Function.update W l g) ^ 2
            * havg m (Φ) (Function.update W l g) ∂(probHaar (SU N)) := by
      unfold havg
      refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
      show ∫ h, wAvg Φ m f (Function.update (Function.update W l g) m h)
            * wAvg Φ m f (Function.update (Function.update W l g) m h)
            * Φ (Function.update (Function.update W l g) m h) ∂(probHaar (SU N))
        = wAvg Φ m f (Function.update W l g) ^ 2
          * ∫ h, Φ (Function.update (Function.update W l g) m h) ∂(probHaar (SU N))
      simp only [wAvg_update, integral_const_mul, sq]
    rw [E1, E2, E3]
    exact key
  have i1 : Integrable
      (fun W => havg m (havg l (fun V => wAvg Φ l f V * wAvg Φ m f V * Φ V)) W)
      (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    haar_integrable (continuous_havg m (continuous_havg l cAB))
  have i2 : Integrable
      (fun W => havg m (havg l (fun V => wAvg Φ l f V * wAvg Φ l f V * Φ V)) W)
      (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    haar_integrable (continuous_havg m (continuous_havg l cAA))
  have i3 : Integrable
      (fun W => havg l (havg m (fun V => wAvg Φ m f V * wAvg Φ m f V * Φ V)) W)
      (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    haar_integrable (continuous_havg l (continuous_havg m cBB))
  have i23 : Integrable
      (fun W => c / 2
        * (havg m (havg l (fun V => wAvg Φ l f V * wAvg Φ l f V * Φ V)) W
          + havg l (havg m (fun V => wAvg Φ m f V * wAvg Φ m f V * Φ V)) W))
      (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    haar_integrable (continuous_const.mul ((continuous_havg m (continuous_havg l cAA)).add
      (continuous_havg l (continuous_havg m cBB))))
  rw [e1, e2, e3]
  calc ∫ W, havg m (havg l (fun V => wAvg Φ l f V * wAvg Φ m f V * Φ V)) W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      ≤ ∫ W, c / 2
          * (havg m (havg l (fun V => wAvg Φ l f V * wAvg Φ l f V * Φ V)) W
            + havg l (havg m (fun V => wAvg Φ m f V * wAvg Φ m f V * Φ V)) W)
          ∂(Measure.pi fun _ : Lk => probHaar (SU N)) :=
        integral_mono i1 i23 hpt
    _ = c / 2
          * (∫ W, havg m (havg l (fun V => wAvg Φ l f V * wAvg Φ l f V * Φ V)) W
              ∂(Measure.pi fun _ : Lk => probHaar (SU N))
            + ∫ W, havg l (havg m (fun V => wAvg Φ m f V * wAvg Φ m f V * Φ V)) W
              ∂(Measure.pi fun _ : Lk => probHaar (SU N))) := by
        rw [integral_const_mul, integral_add i2 i3]


#print axioms w_gibbs_corr_le_of_fibre

end TwoLink

/-! ## The Wilson weight with an adjacent-plaquette coupling

The observer's coarse theory carries, besides the single-plaquette Wilson action, a coupling between
plaquettes that share a link (measured on the stored and GPU ensembles; CLAY-HANDOVER §5a). This
section writes that weight, `wt · e^{−λ Σ_{adjacent p ≠ q} d(p) d(q)}` with `d` the Wilson plaquette
density, and shows it is a local weight whose interaction relation is: two links meet in a plaquette,
or both touch one adjacent pair. -/

section Adjacent

variable [Fintype Lk] {Pq : Type} [Fintype Pq] [DecidableEq Pq]

/-- The plaquette density `d(p) = wilsonDensity (holonomy of p)`. -/
noncomputable def dens (bd : Pq → List (Lk × Bool)) (p : Pq) (W : Lk → SU N) : ℝ :=
  wilsonDensity (wilsonHol bd p W)

/-- The ordered pairs of distinct plaquettes that share a link. -/
def adjSet (bd : Pq → List (Lk × Bool)) : Finset (Pq × Pq) :=
  Finset.univ.filter fun pq => pq.1 ≠ pq.2 ∧ ∃ x ∈ (bd pq.1).map Prod.fst, x ∈ (bd pq.2).map Prod.fst

/-- A plaquette pair touches the link `l` when either plaquette's boundary visits `l`. -/
def Touches (bd : Pq → List (Lk × Bool)) (l : Lk) (pq : Pq × Pq) : Prop :=
  l ∈ (bd pq.1).map Prod.fst ∨ l ∈ (bd pq.2).map Prod.fst

instance (bd : Pq → List (Lk × Bool)) (l : Lk) : DecidablePred (Touches bd l) :=
  fun _ => instDecidableOr

/-- The adjacent-pair action of the pairs touching `l`. -/
noncomputable def adjLoc (bd : Pq → List (Lk × Bool)) (l : Lk) (W : Lk → SU N) : ℝ :=
  ∑ pq ∈ (adjSet bd).filter (Touches bd l), dens bd pq.1 W * dens bd pq.2 W

/-- The adjacent-pair action of the pairs not touching `l`. -/
noncomputable def adjRest (bd : Pq → List (Lk × Bool)) (l : Lk) (W : Lk → SU N) : ℝ :=
  ∑ pq ∈ (adjSet bd).filter (fun pq => ¬ Touches bd l pq), dens bd pq.1 W * dens bd pq.2 W

/-- The adjacent-pair action. -/
noncomputable def adjAct (bd : Pq → List (Lk × Bool)) (W : Lk → SU N) : ℝ :=
  ∑ pq ∈ adjSet bd, dens bd pq.1 W * dens bd pq.2 W

/-- The adjacent-pair action splits at `l` (`Finset.sum_filter_add_sum_filter_not`).

DERIVED: no numeral. -/
theorem adjAct_split (bd : Pq → List (Lk × Bool)) (l : Lk) (W : Lk → SU N) :
    adjAct bd W = adjLoc bd l W + adjRest bd l W :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

#print axioms adjAct_split

/-- A plaquette density does not read a link its boundary does not visit.

DERIVED: no numeral. -/
theorem dens_update_of_not_mem (bd : Pq → List (Lk × Bool)) (p : Pq) {l : Lk}
    (hl : l ∉ (bd p).map Prod.fst) (W : Lk → SU N) (g : SU N) :
    dens bd p (Function.update W l g) = dens bd p W := by
  unfold dens
  rw [wilsonHol_update_of_not_mem bd p hl W g]

#print axioms dens_update_of_not_mem

/-- A plaquette density is continuous.

DERIVED: no numeral. -/
theorem continuous_dens (bd : Pq → List (Lk × Bool)) (p : Pq) : Continuous (dens (N := N) bd p) :=
  continuous_wilsonDensity.comp (continuous_wilsonHol bd p)

/-- The pairs not touching `l` do not read `l`.

DERIVED: no numeral. -/
theorem adjRest_update (bd : Pq → List (Lk × Bool)) (l : Lk) (W : Lk → SU N) (g : SU N) :
    adjRest bd l (Function.update W l g) = adjRest bd l W := by
  unfold adjRest
  refine Finset.sum_congr rfl fun pq hpq => ?_
  have hn : ¬ Touches bd l pq := (Finset.mem_filter.mp hpq).2
  unfold Touches at hn
  push_neg at hn
  rw [dens_update_of_not_mem bd pq.1 hn.1, dens_update_of_not_mem bd pq.2 hn.2]

#print axioms adjRest_update

/-- **The interaction relation of the adjacent-coupled weight**: `l` and `l'` share a plaquette, or
both touch one adjacent pair. -/
def RAdj (bd : Pq → List (Lk × Bool)) (l l' : Lk) : Prop :=
  SharePlaq bd l l' ∨ ∃ pq ∈ adjSet bd, Touches bd l pq ∧ Touches bd l' pq

/-- The pairs touching `l` do not read a link `l'` outside the interaction relation.

DERIVED: no numeral. -/
theorem adjLoc_update_other (bd : Pq → List (Lk × Bool)) {l l' : Lk} (hR : ¬ RAdj bd l l')
    (W : Lk → SU N) (g : SU N) :
    adjLoc bd l (Function.update W l' g) = adjLoc bd l W := by
  unfold adjLoc
  refine Finset.sum_congr rfl fun pq hpq => ?_
  obtain ⟨hpqA, hl⟩ := Finset.mem_filter.mp hpq
  have hn : ¬ Touches bd l' pq := fun h => hR (Or.inr ⟨pq, hpqA, hl, h⟩)
  unfold Touches at hn
  push_neg at hn
  rw [dens_update_of_not_mem bd pq.1 hn.1, dens_update_of_not_mem bd pq.2 hn.2]

#print axioms adjLoc_update_other

/-- The local adjacent-pair action is continuous.

DERIVED: no numeral. -/
theorem continuous_adjLoc (bd : Pq → List (Lk × Bool)) (l : Lk) :
    Continuous (adjLoc (N := N) bd l) :=
  continuous_finsetSum _ fun pq _ => (continuous_dens bd pq.1).mul (continuous_dens bd pq.2)

/-- **The Wilson weight with an adjacent-plaquette coupling `λ`**: `wt · e^{−λ adjAct}`. -/
noncomputable def wtAdj (bd : Pq → List (Lk × Bool)) (β lam : ℝ) (W : Lk → SU N) : ℝ :=
  wt bd β W * Real.exp (-lam * adjAct bd W)

/-- **The adjacent-coupled weight is a local weight**, with
`loc l = locW l · e^{−λ adjLoc l}`, `rest l = e^{−β restSum l} · e^{−λ adjRest l}` and relation `RAdj`.

DERIVED: no numeral. -/
noncomputable def wilsonAdjLocal (bd : Pq → List (Lk × Bool)) (β lam : ℝ) : LocalWeight N Lk where
  Φ := wtAdj bd β lam
  loc := fun l W => locW bd β l W * Real.exp (-lam * adjLoc bd l W)
  rest := fun l W => Real.exp (-β * restSum bd l W) * Real.exp (-lam * adjRest bd l W)
  R := RAdj bd
  split := fun l W => by
    unfold wtAdj
    rw [wt_split bd β l W, adjAct_split bd l W, mul_add, Real.exp_add]
    ring
  rest_update := fun l W g => by simp only [restSum_update, adjRest_update]
  rest_ne := fun _ _ => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
  loc_cont := fun l => (continuous_locW bd β l).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_adjLoc bd l)))
  R_symm := fun l l' h hr => h (by
    rcases hr with hs | ⟨pq, hpq, h1, h2⟩
    · exact Or.inl (by
        by_contra hn
        exact not_sharePlaq_symm hn hs)
    · exact Or.inr ⟨pq, hpq, h2, h1⟩)
  loc_update_other := fun l l' h W g => by
    have hs : ¬ SharePlaq bd l l' := fun hs => h (Or.inl hs)
    simp only [locW_update_other bd β hs W g, adjLoc_update_other bd h W g]

/-- At `λ = 0` the adjacent-coupled weight is the Wilson weight.

DERIVED: `0` is the coupling; `1` is `e^0`. -/
theorem wtAdj_zero (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Lk → SU N) :
    wtAdj bd β 0 W = wt bd β W := by
  simp [wtAdj]

#print axioms wtAdj_zero

end Adjacent

/-! ## The pair split of the adjacent-coupled weight

The box gap's pair step reads the conditional law of two links `l, m`. For the adjacent-coupled
weight that law is the Wilson pair weight times `e^{−λ adjLoc₂}`, where `adjLoc₂` collects the
adjacent pairs touching `l` or `m`; everything else factors out. Each density lies in `[0, 2]`, so the
extra exponent is bounded by `4 |λ|` times the number of those pairs: the `ε` of
`FibrePerturb.covBound_perturb`. -/

section AdjacentPair

variable [Fintype Lk] {Pq : Type} [Fintype Pq] [DecidableEq Pq]

/-- A plaquette pair touches `l` or `m`. -/
def Touches2 (bd : Pq → List (Lk × Bool)) (l m : Lk) (pq : Pq × Pq) : Prop :=
  Touches bd l pq ∨ Touches bd m pq

instance (bd : Pq → List (Lk × Bool)) (l m : Lk) : DecidablePred (Touches2 bd l m) :=
  fun _ => instDecidableOr

/-- The adjacent-pair action of the pairs touching `l` or `m`. -/
noncomputable def adjLoc2 (bd : Pq → List (Lk × Bool)) (l m : Lk) (W : Lk → SU N) : ℝ :=
  ∑ pq ∈ (adjSet bd).filter (Touches2 bd l m), dens bd pq.1 W * dens bd pq.2 W

/-- The adjacent-pair action of the pairs touching neither `l` nor `m`. -/
noncomputable def adjRest2 (bd : Pq → List (Lk × Bool)) (l m : Lk) (W : Lk → SU N) : ℝ :=
  ∑ pq ∈ (adjSet bd).filter (fun pq => ¬ Touches2 bd l m pq), dens bd pq.1 W * dens bd pq.2 W

/-- The adjacent-pair action splits at the pair.

DERIVED: no numeral. -/
theorem adjAct_split2 (bd : Pq → List (Lk × Bool)) (l m : Lk) (W : Lk → SU N) :
    adjAct bd W = adjLoc2 bd l m W + adjRest2 bd l m W :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

#print axioms adjAct_split2

/-- The pairs touching neither link do not read `l`.

DERIVED: no numeral. -/
theorem adjRest2_update_l (bd : Pq → List (Lk × Bool)) (l m : Lk) (W : Lk → SU N) (g : SU N) :
    adjRest2 bd l m (Function.update W l g) = adjRest2 bd l m W := by
  unfold adjRest2
  refine Finset.sum_congr rfl fun pq hpq => ?_
  have hn : ¬ Touches2 bd l m pq := (Finset.mem_filter.mp hpq).2
  unfold Touches2 Touches at hn
  push_neg at hn
  rw [dens_update_of_not_mem bd pq.1 hn.1.1, dens_update_of_not_mem bd pq.2 hn.1.2]

#print axioms adjRest2_update_l

/-- The pairs touching neither link do not read `m`.

DERIVED: no numeral. -/
theorem adjRest2_update_m (bd : Pq → List (Lk × Bool)) (l m : Lk) (W : Lk → SU N) (g : SU N) :
    adjRest2 bd l m (Function.update W m g) = adjRest2 bd l m W := by
  unfold adjRest2
  refine Finset.sum_congr rfl fun pq hpq => ?_
  have hn : ¬ Touches2 bd l m pq := (Finset.mem_filter.mp hpq).2
  unfold Touches2 Touches at hn
  push_neg at hn
  rw [dens_update_of_not_mem bd pq.1 hn.2.1, dens_update_of_not_mem bd pq.2 hn.2.2]

#print axioms adjRest2_update_m

/-- **The adjacent-coupled weight factors at the pair**: the Wilson pair factor times `e^{−λ adjLoc₂}`,
times a remainder reading neither link (`PairCorr.wt_split_pair`, `adjAct_split2`).

DERIVED: no numeral. -/
theorem wtAdj_split_pair (bd : Pq → List (Lk × Bool)) (β lam : ℝ) (l m : Lk) (W : Lk → SU N) :
    wtAdj bd β lam W
      = (Real.exp (-β * pairLocSum bd l m W) * Real.exp (-lam * adjLoc2 bd l m W))
        * (Real.exp (-β * pairRestSum bd l m W) * Real.exp (-lam * adjRest2 bd l m W)) := by
  unfold wtAdj
  rw [wt_split_pair bd β l m W, adjAct_split2 bd l m W, mul_add, Real.exp_add]
  ring

#print axioms wtAdj_split_pair

/-- **The pair perturbation is bounded**: `|λ adjLoc₂| ≤ 4 |λ| · #{adjacent pairs touching l or m}`, each
density lying in `[0, 2]` (`WilsonAction.wilsonDensity_nonneg`, `wilsonDensity_le_two`).

DERIVED: `4 = 2 · 2` is the largest product of two densities; `0` is the excluded rank in `hN`. -/
theorem abs_adjLoc2_le (hN : N ≠ 0) (bd : Pq → List (Lk × Bool)) (lam : ℝ) (l m : Lk)
    (W : Lk → SU N) :
    |lam * adjLoc2 bd l m W| ≤ 4 * |lam| * ((adjSet bd).filter (Touches2 bd l m)).card := by
  rw [abs_mul, mul_comm (4 : ℝ), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg lam)
  unfold adjLoc2
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_comm, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun pq _ => ?_
  have h1 := wilsonDensity_nonneg hN (wilsonHol bd pq.1 W)
  have h2 := wilsonDensity_le_two hN (wilsonHol bd pq.1 W)
  have h3 := wilsonDensity_nonneg hN (wilsonHol bd pq.2 W)
  have h4 := wilsonDensity_le_two hN (wilsonHol bd pq.2 W)
  unfold dens
  rw [abs_of_nonneg (mul_nonneg h1 h3)]
  nlinarith

#print axioms abs_adjLoc2_le

end AdjacentPair

/-! ## The fibre hypothesis for the adjacent-coupled weight -/

section AdjacentFibre

variable [Fintype Lk] {Pq : Type} [Fintype Pq] [DecidableEq Pq]

/-- The local adjacent-pair action at a pair is continuous.

DERIVED: no numeral. -/
theorem continuous_adjLoc2 (bd : Pq → List (Lk × Bool)) (l m : Lk) :
    Continuous (adjLoc2 (N := N) bd l m) :=
  continuous_finsetSum _ fun pq _ => (continuous_dens bd pq.1).mul (continuous_dens bd pq.2)

/-- The fibre hypothesis of `w_gibbs_corr_le_of_fibre` for a weight `Φ` at the pair `l, m` and constant
`c`: at every frozen `W`, for continuous `a, b` with `a` centred, the pair covariance bound.

DERIVED: `0` is the vanishing mean; `2` is the square and the halving. -/
def FibreHyp (Φ : (Lk → SU N) → ℝ) (l m : Lk) (c : ℝ) : Prop :=
  ∀ (W : Lk → SU N) (a b : SU N → ℝ), Continuous a → Continuous b →
    ∫ h, a h * havg l Φ (Function.update W m h) ∂(probHaar (SU N)) = 0 →
    ∫ h, ∫ g, a h * b g * Φ (Function.update (Function.update W m h) l g)
        ∂(probHaar (SU N)) ∂(probHaar (SU N))
      ≤ c / 2 * (∫ h, a h ^ 2 * havg l Φ (Function.update W m h) ∂(probHaar (SU N))
          + ∫ g, b g ^ 2 * havg m Φ (Function.update W l g) ∂(probHaar (SU N)))

/-- At a frozen `W`, the fibre hypothesis is `CovBoundOn` the continuous bounded functions for the pair
weight `w(h, g) = Φ(W[m ↦ h][l ↦ g])` (the second marginal by `Function.update_comm`).

DERIVED: no numeral. -/
theorem fibreHyp_iff (Φ : (Lk → SU N) → ℝ) {l m : Lk} (hlm : l ≠ m) (c : ℝ) :
    FibreHyp Φ l m c ↔ ∀ W : Lk → SU N,
      CovBoundOn (fun a : SU N → ℝ => Continuous a ∧ ∃ C, ∀ x, |a x| ≤ C) (probHaar (SU N))
        (fun h g => Φ (Function.update (Function.update W m h) l g)) c := by
  have hp : ∀ (W : Lk → SU N) (g : SU N),
      pW (probHaar (SU N)) (fun h g => Φ (Function.update (Function.update W m h) l g)) g
        = havg m Φ (Function.update W l g) := fun W g => by
    unfold pW havg
    exact integral_congr_ae (Filter.Eventually.of_forall fun h => by
      show Φ (Function.update (Function.update W m h) l g)
        = Φ (Function.update (Function.update W l g) m h)
      rw [Function.update_comm (Ne.symm hlm) h g W])
  have e : ∀ (W : Lk → SU N) (b : SU N → ℝ),
      ∫ g, b g ^ 2 * pW (probHaar (SU N))
          (fun h g => Φ (Function.update (Function.update W m h) l g)) g ∂(probHaar (SU N))
        = ∫ g, b g ^ 2 * havg m Φ (Function.update W l g) ∂(probHaar (SU N)) := fun W b =>
    integral_congr_ae (Filter.Eventually.of_forall fun g => by dsimp only; rw [hp W g])
  constructor
  · intro H W a b ha hb hcent
    have key := H W a b ha.1 hb.1 hcent
    show _ ≤ _
    rw [e W b]
    exact key
  · intro H W a b ha hb hcent
    obtain ⟨Ca, hCa⟩ := exists_abs_le ha
    obtain ⟨Cb, hCb⟩ := exists_abs_le hb
    have key := H W a b ⟨ha, Ca, hCa⟩ ⟨hb, Cb, hCb⟩ hcent
    rw [e W b] at key
    exact key

#print axioms fibreHyp_iff

/-- **The fibre hypothesis passes from the Wilson weight to the adjacent-coupled weight**: with
`ε = 4 |λ| · #{adjacent pairs touching l or m}`, a Wilson fibre bound at `c` gives the adjacent-coupled
one at `e^ε (c + 2 (e^ε − 1))` (`FibrePerturb.covBoundOn_perturb_cont`, the remainder `e^{−λ adjRest₂}`
reading neither link and leaving by `FibrePerturb.covBoundOn_const_mul`).

DERIVED: `4` is the largest product of two densities; `2` is the two additive terms; `1` is `e^0`;
`0` is the sign of `c` and the excluded rank in `hN`. -/
theorem fibreHyp_adj (hN : N ≠ 0) (bd : Pq → List (Lk × Bool)) (β lam : ℝ) {l m : Lk} (hlm : l ≠ m)
    {c : ℝ} (hc : 0 ≤ c) (H : FibreHyp (wt (N := N) bd β) l m c) :
    FibreHyp (wtAdj (N := N) bd β lam) l m
      (Real.exp (4 * |lam| * ((adjSet bd).filter (Touches2 bd l m)).card)
        * (c + 2 * (Real.exp (4 * |lam| * ((adjSet bd).filter (Touches2 bd l m)).card) - 1))) := by
  set ε := 4 * |lam| * (((adjSet bd).filter (Touches2 bd l m)).card : ℝ) with hεdef
  have hε : 0 ≤ ε := by positivity
  rw [fibreHyp_iff _ hlm] at H ⊢
  intro W
  set w : SU N → SU N → ℝ := fun h g => wt bd β (Function.update (Function.update W m h) l g)
    with hwdef
  set V : SU N → SU N → ℝ := fun h g => -lam * adjLoc2 bd l m (Function.update (Function.update W m h) l g)
    with hVdef
  have hu : Continuous (fun p : SU N × SU N => Function.update (Function.update W m p.1) l p.2) :=
    ((continuous_const : Continuous fun _ : SU N × SU N => W).update m continuous_fst).update l
      continuous_snd
  have hwc : Continuous (Function.uncurry w) := (continuous_wt bd β).comp hu
  have hVc : Continuous (Function.uncurry V) :=
    continuous_const.mul ((continuous_adjLoc2 bd l m).comp hu)
  have hwG : FibrePerturb.Good w := by
    obtain ⟨C, hC⟩ := exists_abs_le hwc
    exact ⟨hwc.measurable, C, fun h g => hC (h, g)⟩
  have hw0 : ∀ h g, 0 ≤ w h g := fun h g => (wt_pos bd β _).le
  have hVb : ∀ h g, |V h g| ≤ ε := fun h g => by
    show |-lam * adjLoc2 bd l m _| ≤ _
    rw [neg_mul, abs_neg]
    exact abs_adjLoc2_le hN bd lam l m _
  have hpert := covBoundOn_perturb_cont (probHaar (SU N)) hc hε hwG hw0 hVc.measurable hVb (H W)
  have hC : 0 < Real.exp (-lam * adjRest2 bd l m W) := Real.exp_pos _
  have hscaled := covBoundOn_const_mul _ (probHaar (SU N)) hC hpert
  have heq : (fun h g => Real.exp (-lam * adjRest2 bd l m W) * (w h g * Real.exp (V h g)))
      = fun h g => wtAdj bd β lam (Function.update (Function.update W m h) l g) := by
    funext h g
    have hr : adjRest2 bd l m (Function.update (Function.update W m h) l g) = adjRest2 bd l m W := by
      rw [adjRest2_update_l, adjRest2_update_m]
    unfold wtAdj
    rw [adjAct_split2 bd l m, hr]
    simp only [hwdef, hVdef]
    rw [mul_add, Real.exp_add]
    ring
  rw [heq] at hscaled
  exact hscaled

#print axioms fibreHyp_adj

end AdjacentFibre

/-! ## The torus pairs -/

section TorusAdjacent

open MassGap.PairInterface (FibreBound realFeature)
open MassGap.PairCount (n2)

/-- **The adjacent-coupled fibre hypothesis at a torus pair, from the Wilson fibre bound**: the
`FibreBound` that `PairCorrSharp.hfib_of_fibreBound` turns into the Wilson fibre hypothesis at the
pair, carried through `fibreHyp_adj`.

DERIVED: `12` is the non-diagonal plaquette count per link (the tilt's complement); `4` is the
spacetime dimension and the largest product of two densities; `2` is the two additive terms; `1` is
`e^0` and the least torus side minus one; `0` is the sign of `β`, `c` and the excluded rank. -/
theorem torus_fibreHyp_adj (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (lam : ℝ) {M : ℕ} (hM : 1 ≤ M)
    {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m) {c : ℝ} (hc : 0 ≤ c)
    (hB : FibreBound (probHaar (SU N)) (realFeature N) c (β * (n2 M l m : ℝ))
      (β * (12 - (n2 M l m : ℝ)))) :
    FibreHyp (wtAdj (N := N) (bdT M) β lam) l m
      (Real.exp (4 * |lam| * (((adjSet (bdT M)).filter (Touches2 (bdT M) l m)).card : ℝ))
        * (c + 2 * (Real.exp (4 * |lam|
            * (((adjSet (bdT M)).filter (Touches2 (bdT M) l m)).card : ℝ)) - 1))) :=
  fibreHyp_adj hN (bdT M) β lam hlm hc
    (fun W a b ha hb hz => MassGap.PairCorrSharp.hfib_of_fibreBound hN hβ hM hlm hB W a b ha hb hz)

#print axioms torus_fibreHyp_adj

end TorusAdjacent

end MassGap.WeightedHeatBath
