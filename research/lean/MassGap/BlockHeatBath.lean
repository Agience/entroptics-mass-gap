import Mathlib
import MassGap.BlockGapDef

noncomputable section

/-!
# MassGap.BlockHeatBath — the block conditional expectations of the periodic Wilson measures

`BlockGapDef.blockGap` is a supremum over families of `BlockGapDef.WilsonBlockBath`; without an instance
the set is empty and the gap is `0` by definition. This module constructs the instance: the conditional
expectation of the periodic Wilson measure given every link outside a finite set `S` of torus links, built as
`HeatBath.heatAvg` is built for one link, with `BoxGap.glue` in place of `Function.update`.

## What it gives

1. **The block average of a finite Wilson system.** `blkAvg bd β S f W`: the average of `f` over the links of
   `S` with the Wilson weight, the rest held at `W`:
   `(∫ V, f (glue S W V) wt (glue S W V) dV) / ∫ V, wt (glue S W V) dV` against the product Haar measure. It
   does not read `S` (`blkAvg_glue`, `blkAvg_update_mem`), fixes functions not reading `S`
   (`blkAvg_of_readsNot`), pulls out factors not reading `S`, is linear and continuous on continuous
   functions, and satisfies the DLR identity and detailed balance (`expect_blkAvg`, `expect_blkAvg_mul`).
2. **Gauge invariance.** `glue_gauge`: `glue S (g·W) V = g·(glue S W (g⁻¹·V))`, and the product Haar measure
   is invariant under `g⁻¹·` (`LocalGauge.gaugeEquiv_measurePreserving`): `blkAvg_gauge`.
3. **The torus conditional expectation.** `blkLift`, `torusBlkCondExp β M S` on the periodic gauge-invariant
   observables: `torusForm`-self-adjoint (`torusBlkCondExp_selfAdj`), idempotent, its values read no link
   of `S`, and it keeps every observable reading none of them (`readsNot_glue`: an observable unchanged by
   each single-link update in `S` is unchanged by the whole glue).
4. **The instance.** `wilsonBlockBath hN β n j`: `BlockGapDef.WilsonBlockBath` with the boxes
   `BoxGap.boxLinks n k`. `blockGapSet_nonempty`: `0` is attained, so `blockGap` is the supremum of a
   non-empty set of gaps of an actual dynamics.

DERIVED (module-wide): `4` the spacetime dimension; `2 * j + 1` the index of the even-extent family and
`+ 1` its successor; `0` the signs and the excluded rank; `1` the constant function.
-/

namespace MassGap.BlockHeatBath

open MeasureTheory
open MassGap.LatticeGauge
open MassGap.WilsonLattice (wilsonSystem wilsonHol)
open MassGap.WilsonAction (wilsonDensity)
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)
open MassGap.KnabeCriterion
open MassGap.HeatBath
open MassGap.BoxGap (glue glue_of_mem glue_of_not_mem)
open MassGap.PeriodicState (torusObs torusState)
open MassGap.InfiniteLattice (siteMod linkMod pullback finMod)

/-! ## 1. Gluing -/

section Glue

variable {ι Ω : Type} [DecidableEq ι]

/-- Re-gluing over the same set forgets the inner fibre.

DERIVED: no numeral. -/
theorem glue_glue_left (S : Finset ι) (W V V' : ι → Ω) : glue S (glue S W V') V = glue S W V := by
  funext i
  by_cases hi : i ∈ S
  · rw [glue_of_mem hi, glue_of_mem hi]
  · rw [glue_of_not_mem hi, glue_of_not_mem hi, glue_of_not_mem hi]

#print axioms glue_glue_left

/-- Updating a link of `S` outside the fibre changes nothing.

DERIVED: no numeral. -/
theorem glue_update_out (S : Finset ι) (W V : ι → Ω) {l : ι} (hl : l ∈ S) (g : Ω) :
    glue S (Function.update W l g) V = glue S W V := by
  funext i
  by_cases hi : i ∈ S
  · rw [glue_of_mem hi, glue_of_mem hi]
  · have hne : i ≠ l := fun h => hi (h ▸ hl)
    rw [glue_of_not_mem hi, glue_of_not_mem hi, Function.update_of_ne hne]

#print axioms glue_update_out

/-- Gluing one more link is one update.

DERIVED: no numeral. -/
theorem glue_insert (S : Finset ι) (W V : ι → Ω) {l : ι} (hl : l ∉ S) :
    glue (insert l S) W V = Function.update (glue S W V) l (V l) := by
  funext i
  by_cases hi : i = l
  · subst hi
    rw [glue_of_mem (Finset.mem_insert_self i S), Function.update_self]
  · rw [Function.update_of_ne hi]
    by_cases hS : i ∈ S
    · rw [glue_of_mem (Finset.mem_insert_of_mem hS), glue_of_mem hS]
    · have hS' : i ∉ insert l S := by
        rw [Finset.mem_insert]; exact fun h => h.elim hi hS
      rw [glue_of_not_mem hS', glue_of_not_mem hS]

#print axioms glue_insert

/-- **A function unchanged by each single-link update in `S` is unchanged by the glue.**

DERIVED: no numeral. -/
theorem readsNot_glue {β : Type*} (S : Finset ι) {f : (ι → Ω) → β}
    (hf : ∀ l ∈ S, ∀ W g, f (Function.update W l g) = f W) (W V : ι → Ω) :
    f (glue S W V) = f W := by
  induction S using Finset.induction_on generalizing W with
  | empty =>
    congr 1
  | insert l S hl ih =>
    rw [glue_insert S W V hl, hf l (Finset.mem_insert_self l S)]
    exact ih (fun l' hl' W' g => hf l' (Finset.mem_insert_of_mem hl') W' g) W

#print axioms readsNot_glue

variable [TopologicalSpace Ω]

/-- Gluing is continuous in the outer configuration.

DERIVED: no numeral. -/
theorem continuous_glue_left (S : Finset ι) (V : ι → Ω) :
    Continuous (fun W : ι → Ω => glue S W V) := by
  refine continuous_pi (fun i => ?_)
  by_cases hi : i ∈ S
  · simp only [glue_of_mem hi]; exact continuous_const
  · simp only [glue_of_not_mem hi]; exact continuous_apply i

#print axioms continuous_glue_left

/-- Gluing is continuous in the fibre.

DERIVED: no numeral. -/
theorem continuous_glue_right (S : Finset ι) (W : ι → Ω) :
    Continuous (fun V : ι → Ω => glue S W V) := by
  refine continuous_pi (fun i => ?_)
  by_cases hi : i ∈ S
  · simp only [glue_of_mem hi]; exact continuous_apply i
  · simp only [glue_of_not_mem hi]; exact continuous_const

#print axioms continuous_glue_right

end Glue

/-! ## 2. The block average of a finite Wilson system -/

section BlockAvg

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq] [DecidableEq Lk]

/-- The Wilson system's link type is `Lk`; its decidable equality is `Lk`'s. -/
local instance decEqSystemLinkB (bd : Pq → List (Lk × Bool)) :
    DecidableEq (wilsonSystem bd (wilsonDensity (N := N))).Link :=
  inferInstanceAs (DecidableEq Lk)

/-- The block numerator `∫ V, f (glue S W V) wt (glue S W V) dV`.

DERIVED: no numeral. -/
def blkNum (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) (f : (Lk → SU N) → ℝ)
    (W : Lk → SU N) : ℝ :=
  ∫ V, f (glue S W V) * wt bd β (glue S W V) ∂(Measure.pi fun _ : Lk => probHaar (SU N))

/-- The block normalisation `∫ V, wt (glue S W V) dV`.

DERIVED: no numeral. -/
def blkPart (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) (W : Lk → SU N) : ℝ :=
  ∫ V, wt bd β (glue S W V) ∂(Measure.pi fun _ : Lk => probHaar (SU N))

/-- **The block average**: `blkNum / blkPart`.

DERIVED: no numeral. -/
def blkAvg (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) (f : (Lk → SU N) → ℝ)
    (W : Lk → SU N) : ℝ :=
  blkNum bd β S f W / blkPart bd β S W

/-- The normalisation is positive.

DERIVED: `0` the sign; `1` the total mass. -/
theorem blkPart_pos (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) (W : Lk → SU N) :
    0 < blkPart bd β S W := by
  have hc : Continuous (fun V : Lk → SU N => wt bd β (glue S W V)) :=
    (continuous_wt bd β).comp (continuous_glue_right S W)
  obtain ⟨C, hC⟩ := exists_abs_le hc
  have hint : Integrable (fun V : Lk → SU N => wt bd β (glue S W V))
      (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    integrable_of_abs_le _ hc.measurable hC
  unfold blkPart
  rw [integral_pos_iff_support_of_nonneg (fun V => (wt_pos bd β _).le) hint]
  have hsupp : Function.support (fun V : Lk → SU N => wt bd β (glue S W V)) = Set.univ :=
    Set.eq_univ_of_forall (fun V => Function.mem_support.mpr (wt_pos bd β _).ne')
  rw [hsupp, measure_univ]
  exact one_pos

#print axioms blkPart_pos

/-- The numerator's integrand is integrable for continuous `f`.

DERIVED: no numeral. -/
theorem integrable_glue (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) (W : Lk → SU N) :
    Integrable (fun V => f (glue S W V) * wt bd β (glue S W V))
      (Measure.pi fun _ : Lk => probHaar (SU N)) := by
  have hF : Continuous (fun V => f V * wt bd β V) := hf.mul (continuous_wt bd β)
  obtain ⟨C, hC⟩ := exists_abs_le hF
  exact integrable_of_abs_le _ (hF.comp (continuous_glue_right S W)).measurable (fun V => hC _)

#print axioms integrable_glue

/-- **The block average does not read the block**: it depends on `W` only off `S`.

DERIVED: no numeral. -/
theorem blkAvg_glue (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) (f : (Lk → SU N) → ℝ)
    (W V' : Lk → SU N) : blkAvg bd β S f (glue S W V') = blkAvg bd β S f W := by
  simp only [blkAvg, blkNum, blkPart, glue_glue_left]

#print axioms blkAvg_glue

/-- Updating a link of the block changes nothing.

DERIVED: no numeral. -/
theorem blkAvg_update_mem (bd : Pq → List (Lk × Bool)) (β : ℝ) {S : Finset Lk} {l : Lk}
    (hl : l ∈ S) (f : (Lk → SU N) → ℝ) (W : Lk → SU N) (g : SU N) :
    blkAvg bd β S f (Function.update W l g) = blkAvg bd β S f W := by
  simp only [blkAvg, blkNum, blkPart, glue_update_out S W _ hl g]

#print axioms blkAvg_update_mem

/-- **The block average fixes every function not reading the block.**

DERIVED: no numeral. -/
theorem blkAvg_of_readsNot (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk)
    {f : (Lk → SU N) → ℝ} (hf : ∀ W V, f (glue S W V) = f W) (W : Lk → SU N) :
    blkAvg bd β S f W = f W := by
  unfold blkAvg blkNum
  simp only [hf, integral_const_mul]
  exact mul_div_cancel_right₀ _ (blkPart_pos bd β S W).ne'

#print axioms blkAvg_of_readsNot

/-- **A factor not reading the block comes out on the left.**

DERIVED: no numeral. -/
theorem blkAvg_mul_left (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk)
    {a f : (Lk → SU N) → ℝ} (ha : ∀ W V, a (glue S W V) = a W) (W : Lk → SU N) :
    blkAvg bd β S (fun U => a U * f U) W = a W * blkAvg bd β S f W := by
  unfold blkAvg blkNum
  simp only [ha, mul_assoc, integral_const_mul]
  exact mul_div_assoc _ _ _

#print axioms blkAvg_mul_left

/-- **A factor not reading the block comes out on the right.**

DERIVED: no numeral. -/
theorem blkAvg_mul_right (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk)
    {a f : (Lk → SU N) → ℝ} (ha : ∀ W V, a (glue S W V) = a W) (W : Lk → SU N) :
    blkAvg bd β S (fun U => f U * a U) W = blkAvg bd β S f W * a W := by
  have hfun : (fun U => f U * a U) = (fun U => a U * f U) := funext fun U => mul_comm _ _
  rw [hfun, blkAvg_mul_left bd β S ha W, mul_comm]

#print axioms blkAvg_mul_right

/-- Homogeneity.

DERIVED: no numeral. -/
theorem blkAvg_const_mul (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) (c : ℝ)
    (f : (Lk → SU N) → ℝ) (W : Lk → SU N) :
    blkAvg bd β S (fun U => c * f U) W = c * blkAvg bd β S f W :=
  blkAvg_mul_left bd β S (a := fun _ => c) (fun _ _ => rfl) W

#print axioms blkAvg_const_mul

/-- Additivity on continuous functions.

DERIVED: no numeral. -/
theorem blkAvg_add (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) {f g : (Lk → SU N) → ℝ}
    (hf : Continuous f) (hg : Continuous g) (W : Lk → SU N) :
    blkAvg bd β S (fun U => f U + g U) W = blkAvg bd β S f W + blkAvg bd β S g W := by
  unfold blkAvg blkNum
  rw [← add_div]
  congr 1
  simp only [add_mul]
  exact integral_add (integrable_glue bd β S hf W) (integrable_glue bd β S hg W)

#print axioms blkAvg_add

/-- The numerator is continuous in the outer configuration.

DERIVED: no numeral. -/
theorem continuous_blkNum (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) : Continuous (blkNum bd β S f) := by
  have hF : Continuous (fun V => f V * wt bd β V) := hf.mul (continuous_wt bd β)
  obtain ⟨C, hC⟩ := exists_abs_le hF
  show Continuous (fun W => ∫ V, f (glue S W V) * wt bd β (glue S W V)
    ∂(Measure.pi fun _ : Lk => probHaar (SU N)))
  refine continuous_of_dominated (bound := fun _ => C) (fun W => ?_) (fun W => ?_)
    (integrable_const C) ?_
  · exact (hF.comp (continuous_glue_right S W)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun V => by rw [Real.norm_eq_abs]; exact hC _)
  · exact Filter.Eventually.of_forall (fun V => hF.comp (continuous_glue_left S V))

#print axioms continuous_blkNum

/-- The normalisation is the numerator of the constant `1`.

DERIVED: `1` the constant function. -/
theorem blkPart_eq (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) :
    blkPart (N := N) bd β S = blkNum bd β S (fun _ => 1) := by
  funext W
  unfold blkPart blkNum
  simp only [one_mul]

#print axioms blkPart_eq

/-- The block average of a continuous function is continuous.

DERIVED: no numeral. -/
theorem continuous_blkAvg (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) : Continuous (blkAvg bd β S f) := by
  have hP : Continuous (blkPart (N := N) bd β S) := by
    rw [blkPart_eq]
    exact continuous_blkNum bd β S continuous_const
  exact (continuous_blkNum bd β S hf).div hP (fun W => (blkPart_pos bd β S W).ne')

#print axioms continuous_blkAvg

/-- **The DLR identity for the block, integrated.**

DERIVED: no numeral. -/
theorem integral_blkAvg_mul_wt (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) :
    ∫ W, blkAvg bd β S f W * wt bd β W ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      = ∫ W, f W * wt bd β W ∂(Measure.pi fun _ : Lk => probHaar (SU N)) := by
  have hc1 : Continuous (fun W => blkAvg bd β S f W * wt bd β W) :=
    (continuous_blkAvg bd β S hf).mul (continuous_wt bd β)
  have hc2 : Continuous (fun W => f W * wt bd β W) := hf.mul (continuous_wt bd β)
  obtain ⟨C1, hC1⟩ := exists_abs_le hc1
  obtain ⟨C2, hC2⟩ := exists_abs_le hc2
  rw [BoxGap.integral_eq_integral_glue (probHaar (SU N)) S _ hc1.measurable hC1,
    BoxGap.integral_eq_integral_glue (probHaar (SU N)) S _ hc2.measurable hC2]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun W => ?_))
  show ∫ V, blkAvg bd β S f (glue S W V) * wt bd β (glue S W V)
      ∂(Measure.pi fun _ : Lk => probHaar (SU N))
    = ∫ V, f (glue S W V) * wt bd β (glue S W V) ∂(Measure.pi fun _ : Lk => probHaar (SU N))
  simp only [blkAvg_glue, integral_const_mul]
  show blkAvg bd β S f W * blkPart bd β S W = blkNum bd β S f W
  unfold blkAvg
  exact div_mul_cancel₀ _ (blkPart_pos bd β S W).ne'

#print axioms integral_blkAvg_mul_wt

/-- **The DLR identity for the block.**

DERIVED: no numeral. -/
theorem expect_blkAvg (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) {f : (Lk → SU N) → ℝ}
    (hf : Continuous f) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β (blkAvg bd β S f)
      = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β f := by
  unfold System.expect System.corrNum
  exact congrArg
    (fun t => t / (wilsonSystem bd (wilsonDensity (N := N))).partition (probHaar (SU N)) β)
    (integral_blkAvg_mul_wt bd β S hf)

#print axioms expect_blkAvg

/-- **Detailed balance for the block.**

DERIVED: no numeral. -/
theorem expect_blkAvg_mul (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk)
    {f g : (Lk → SU N) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
        (fun W => blkAvg bd β S f W * g W)
      = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
        (fun W => f W * blkAvg bd β S g W) :=
  calc (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
        (fun W => blkAvg bd β S f W * g W)
      = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
          (blkAvg bd β S (fun W => blkAvg bd β S f W * g W)) :=
        (expect_blkAvg bd β S ((continuous_blkAvg bd β S hf).mul hg)).symm
    _ = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
          (fun W => blkAvg bd β S f W * blkAvg bd β S g W) := by
        congr 1
        funext W
        exact blkAvg_mul_left bd β S (fun V V' => blkAvg_glue bd β S f V V') W
    _ = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
          (blkAvg bd β S (fun W => f W * blkAvg bd β S g W)) := by
        congr 1
        funext W
        exact (blkAvg_mul_right bd β S (fun V V' => blkAvg_glue bd β S g V V') W).symm
    _ = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
          (fun W => f W * blkAvg bd β S g W) :=
        expect_blkAvg bd β S (hf.mul (continuous_blkAvg bd β S hg))

#print axioms expect_blkAvg_mul

end BlockAvg

/-! ## 3. The periodic lattice -/

section Torus

variable {N : ℕ}

/-- **Gluing intertwines the gauge action**: `glue S (g·W) V = g·(glue S W (g⁻¹·V))`.

DERIVED: `4` the spacetime dimension; `1` the successor writing the extent. -/
theorem glue_gauge {M : ℕ} (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (W V : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    glue S (LocalGauge.gaugeTransform g W) V
      = LocalGauge.gaugeTransform g (glue S W (LocalGauge.gaugeTransform (fun x => (g x)⁻¹) V)) := by
  funext l
  by_cases hl : l ∈ S
  · rw [glue_of_mem hl]
    show V l = g l.2 * glue S W (LocalGauge.gaugeTransform (fun x => (g x)⁻¹) V) l
      * (g (WilsonHypercubic.shift l.1 l.2))⁻¹
    rw [glue_of_mem hl]
    show V l = g l.2 * ((g l.2)⁻¹ * V l * ((g (WilsonHypercubic.shift l.1 l.2))⁻¹)⁻¹)
      * (g (WilsonHypercubic.shift l.1 l.2))⁻¹
    group
  · rw [glue_of_not_mem hl]
    show g l.2 * W l * (g (WilsonHypercubic.shift l.1 l.2))⁻¹
      = g l.2 * glue S W (LocalGauge.gaugeTransform (fun x => (g x)⁻¹) V) l
        * (g (WilsonHypercubic.shift l.1 l.2))⁻¹
    rw [glue_of_not_mem hl]

#print axioms glue_gauge

/-- **The block average keeps torus gauge invariance.**

DERIVED: `4` the spacetime dimension; `1` the successor writing the extent. -/
theorem blkAvg_gauge (β : ℝ) {M : ℕ} (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    {φ : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ}
    (hφ : ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
      (W : WilsonHypercubic.Link 4 (M + 1) → SU N), φ (LocalGauge.gaugeTransform g W) = φ W)
    (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    blkAvg (bdT M) β S φ (LocalGauge.gaugeTransform g W) = blkAvg (bdT M) β S φ W := by
  have hwt : ∀ U : WilsonHypercubic.Link 4 (M + 1) → SU N,
      wt (bdT M) β (LocalGauge.gaugeTransform g U) = wt (bdT M) β U :=
    fun U => LocalGauge.boltz_gauge_invariant_local g β U
  have hmp := LocalGauge.gaugeEquiv_measurePreserving (d := 4) (n := M + 1) (SU N)
    (fun x => (g x)⁻¹)
  have hnum : blkNum (bdT M) β S φ (LocalGauge.gaugeTransform g W) = blkNum (bdT M) β S φ W := by
    unfold blkNum
    simp only [glue_gauge S g W, hφ, hwt]
    exact hmp.integral_comp' (fun V => φ (glue S W V) * wt (bdT M) β (glue S W V))
  have hpart : blkPart (bdT M) β S (LocalGauge.gaugeTransform g W) = blkPart (bdT M) β S W := by
    unfold blkPart
    simp only [glue_gauge S g W, hwt]
    exact hmp.integral_comp' (fun V => wt (bdT M) β (glue S W V))
  unfold blkAvg
  rw [hnum, hpart]

#print axioms blkAvg_gauge

/-- **The block average lifted to `ℤ⁴` observables.**

DERIVED: `4` the spacetime dimension; `1` the successor writing the extent. -/
def blkLift (β : ℝ) (M : ℕ) (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    (F : C(GibbsSpec.IConf (SU N), ℝ)) : C(GibbsSpec.IConf (SU N), ℝ) :=
  ⟨fun U => blkAvg (bdT M) β S (torusObs M F) (restrictConf M U),
    (continuous_blkAvg (bdT M) β S (continuous_torusObs M F)).comp (continuous_restrictConf M)⟩

/-- The torus reading of the lifted block average is the block average of the torus reading.

DERIVED: `4` the spacetime dimension; `1` the successor writing the extent. -/
theorem torusObs_blkLift (β : ℝ) (M : ℕ) (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    (F : C(GibbsSpec.IConf (SU N), ℝ)) :
    torusObs M (blkLift β M S F) = blkAvg (bdT M) β S (torusObs M F) := by
  funext W
  show blkAvg (bdT M) β S (torusObs M F) (restrictConf M (pullback M W))
    = blkAvg (bdT M) β S (torusObs M F) W
  rw [restrictConf_pullback]

#print axioms torusObs_blkLift

/-- **The lifted block average keeps periodic gauge invariance.**

DERIVED: `4` the spacetime dimension; `1` the successor writing the extent. -/
theorem blkLift_mem (β : ℝ) (M : ℕ) (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    {F : C(GibbsSpec.IConf (SU N), ℝ)} (hF : F ∈ periodicGaugeInvSubmodule (N := N) M) :
    blkLift β M S F ∈ periodicGaugeInvSubmodule (N := N) M := by
  show ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (U : GibbsSpec.IConf (SU N)),
    blkLift β M S F (GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) U)
      = blkLift β M S F U
  intro g U
  show blkAvg (bdT M) β S (torusObs M F)
      (restrictConf M (GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) U))
    = blkAvg (bdT M) β S (torusObs M F) (restrictConf M U)
  rw [restrictConf_igauge]
  exact blkAvg_gauge β S (fun g' W => torusObs_gauge hF g' W) g (restrictConf M U)

#print axioms blkLift_mem

/-- **The block conditional expectation** as a linear map of the periodic gauge-invariant observables.

DERIVED: `4` the spacetime dimension; `1` the successor writing the extent. -/
def torusBlkCondExp (β : ℝ) (M : ℕ) (S : Finset (WilsonHypercubic.Link 4 (M + 1))) :
    ↥(periodicGaugeInvSubmodule (N := N) M) →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) M) where
  toFun x := ⟨blkLift β M S (x : C(GibbsSpec.IConf (SU N), ℝ)), blkLift_mem β M S x.2⟩
  map_add' x y := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro U
    show blkAvg (bdT M) β S
        (torusObs M ((x : C(GibbsSpec.IConf (SU N), ℝ)) + (y : C(GibbsSpec.IConf (SU N), ℝ))))
        (restrictConf M U)
      = blkAvg (bdT M) β S (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
        + blkAvg (bdT M) β S (torusObs M (y : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
    exact blkAvg_add (bdT M) β S (continuous_torusObs M _) (continuous_torusObs M _)
      (restrictConf M U)
  map_smul' c x := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro U
    show blkAvg (bdT M) β S (torusObs M (c • (x : C(GibbsSpec.IConf (SU N), ℝ))))
        (restrictConf M U)
      = c * blkAvg (bdT M) β S (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
    exact blkAvg_const_mul (bdT M) β S c _ (restrictConf M U)

/-- **Self-adjointness for `torusForm`** (detailed balance for the block).

DERIVED: `4` the spacetime dimension; `2 * j + 1` the index and `+ 1` its successor; `0` the
excluded rank. -/
theorem torusBlkCondExp_selfAdj (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (S : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)))
    (x y : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    torusForm hN β j (torusBlkCondExp β (2 * j + 1) S x) y
      = torusForm hN β j x (torusBlkCondExp β (2 * j + 1) S y) := by
  rw [torusForm_apply, torusForm_apply]
  show ReflectPositive.EW (d := 4) (n := 2 * j + 1 + 1) N β
      (fun W => torusObs (2 * j + 1) (blkLift β (2 * j + 1) S (x : C(GibbsSpec.IConf (SU N), ℝ))) W
        * torusObs (2 * j + 1) (y : C(GibbsSpec.IConf (SU N), ℝ)) W)
    = ReflectPositive.EW (d := 4) (n := 2 * j + 1 + 1) N β
      (fun W => torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) W
        * torusObs (2 * j + 1) (blkLift β (2 * j + 1) S (y : C(GibbsSpec.IConf (SU N), ℝ))) W)
  rw [torusObs_blkLift, torusObs_blkLift]
  exact expect_blkAvg_mul (bdT (2 * j + 1)) β S (continuous_torusObs _ _)
    (continuous_torusObs _ _)

#print axioms torusBlkCondExp_selfAdj

/-- **Idempotence.**

DERIVED: `4` the spacetime dimension; `1` the successor writing the extent. -/
theorem torusBlkCondExp_idem (β : ℝ) (M : ℕ) (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    torusBlkCondExp β M S (torusBlkCondExp β M S x) = torusBlkCondExp β M S x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show blkAvg (bdT M) β S (torusObs M (blkLift β M S (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = blkAvg (bdT M) β S (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
  rw [torusObs_blkLift]
  exact blkAvg_of_readsNot (bdT M) β S (fun W V => blkAvg_glue (bdT M) β S _ W V) _

#print axioms torusBlkCondExp_idem

/-- **The values read no link of the block.**

DERIVED: `4` the spacetime dimension; `2 * j + 1` the index and `+ 1` its successor. -/
theorem torusBlkCondExp_readsNot (β : ℝ) (j : ℕ)
    (S : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    ∀ l ∈ S, ReadsNot j l ((torusBlkCondExp β (2 * j + 1) S x
      : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) : C(GibbsSpec.IConf (SU N), ℝ)) := by
  intro l hl
  unfold ReadsNot
  intro W g
  show torusObs (2 * j + 1) (blkLift β (2 * j + 1) S (x : C(GibbsSpec.IConf (SU N), ℝ)))
      (Function.update W l g)
    = torusObs (2 * j + 1) (blkLift β (2 * j + 1) S (x : C(GibbsSpec.IConf (SU N), ℝ))) W
  rw [torusObs_blkLift]
  exact blkAvg_update_mem (bdT (2 * j + 1)) β hl _ W g

#print axioms torusBlkCondExp_readsNot

/-- **Observables reading no link of the block are kept.**

DERIVED: `4` the spacetime dimension; `2 * j + 1` the index and `+ 1` its successor. -/
theorem torusBlkCondExp_keeps (β : ℝ) (j : ℕ)
    (S : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
    (hx : ∀ l ∈ S, ReadsNot j l (x : C(GibbsSpec.IConf (SU N), ℝ))) :
    torusObs (2 * j + 1)
        ((torusBlkCondExp β (2 * j + 1) S x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
          : C(GibbsSpec.IConf (SU N), ℝ))
      = torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) := by
  show torusObs (2 * j + 1) (blkLift β (2 * j + 1) S (x : C(GibbsSpec.IConf (SU N), ℝ)))
    = torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ))
  rw [torusObs_blkLift]
  funext W
  exact blkAvg_of_readsNot (bdT (2 * j + 1)) β S (readsNot_glue S (fun l hl W g => hx l hl W g)) W

#print axioms torusBlkCondExp_keeps

/-- **The block heat-bath system of the Wilson measure**, with the boxes `BoxGap.boxLinks n k`.

DERIVED: `0` the excluded rank. -/
def wilsonBlockBath (hN : N ≠ 0) (β : ℝ) (n j : ℕ) : BlockGapDef.WilsonBlockBath hN β n j where
  condExp k := torusBlkCondExp β (2 * j + 1) (BoxGap.boxLinks n k)
  selfAdj k := torusBlkCondExp_selfAdj hN β j (BoxGap.boxLinks n k)
  idem k := torusBlkCondExp_idem β (2 * j + 1) (BoxGap.boxLinks n k)
  reads_not k x := torusBlkCondExp_readsNot β j (BoxGap.boxLinks n k) x
  keeps k x hx := torusBlkCondExp_keeps β j (BoxGap.boxLinks n k) x hx

/-- **The gap set is non-empty**: the instance attains `0`.

DERIVED: `0` the attained gap and the excluded rank. -/
theorem blockGapSet_nonempty (hN : N ≠ 0) (β : ℝ) (n : ℕ) :
    (BlockGapDef.blockGapSet hN β n).Nonempty := by
  refine ⟨0, le_rfl, fun j => wilsonBlockBath hN β n j, Filter.Eventually.of_forall (fun j x => ?_)⟩
  rw [zero_mul]
  exact torusForm_nonneg hN β j _

#print axioms blockGapSet_nonempty

end Torus

end MassGap.BlockHeatBath
