import Mathlib
import MassGap.BlockHeatBath

noncomputable section

/-!
# MassGap.BlockCommute — block conditional expectations: locality and commutation off shared plaquettes

`BlockHeatBath.blkAvg` is the conditional expectation of a finite Wilson system given every link outside a
finite set `S`. This module proves the two properties a sweep of such expectations needs, as
`HeatBath.heatAvg_eq_loc` and `HeatBath.heatAvg_comm` prove them for one link.

## What it gives

1. **The block's own weight.** `blkLocW bd β S`: the Boltzmann factor of the plaquettes whose boundary word
   visits a link of `S`. `wt_split_blk`: `wt = blkLocW · e^{−β · rest}`, the rest not reading `S`
   (`blkRestSum_glue`), so `blkAvg_eq_loc`: the block average uses `blkLocW` alone.
2. **Locality.** `blkAvg_update_far`: if `f` does not read a link `l` outside `S` that lies on no plaquette
   through `S`, neither does `blkAvg S f`.
3. **Commutation.** `blkAvg_comm`: for disjoint `S`, `T` such that no plaquette visits a link of both,
   `blkAvg S (blkAvg T f) = blkAvg T (blkAvg S f)` on continuous `f`: both are one double integral
   (`blkAvg_blkAvg_eq`), symmetric by `glue_comm` and Fubini (`integral_integral_swap`).
4. **On the torus.** `torusBlkCondExp_comm` (exact equality of linear maps), and
   `torusBlkCondExp_readsNot_far`: the torus conditional expectation of a box keeps `ReadsNot` at every
   link outside the box sharing no plaquette with it.

DERIVED (module-wide): `4` the spacetime dimension; `2 * j + 1` the index of the even-extent family and
`+ 1` its successor; `1` the successor writing the extent.
-/

namespace MassGap.BlockCommute

open MeasureTheory
open MassGap.LatticeGauge
open MassGap.WilsonLattice (wilsonSystem wilsonHol)
open MassGap.WilsonAction (wilsonDensity)
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)
open MassGap.KnabeCriterion
open MassGap.HeatBath
open MassGap.BlockHeatBath
open MassGap.BoxGap (glue glue_of_mem glue_of_not_mem)
open MassGap.PeriodicState (torusObs)

/-! ## 1. Gluing over two disjoint sets -/

section Glue

variable {ι Ω : Type} [DecidableEq ι]

/-- **Gluing over disjoint sets commutes.**

DERIVED: no numeral. -/
theorem glue_comm {S T : Finset ι} (hST : Disjoint S T) (W V V' : ι → Ω) :
    glue T (glue S W V) V' = glue S (glue T W V') V := by
  funext i
  by_cases hT : i ∈ T
  · have hS : i ∉ S := Finset.disjoint_right.mp hST hT
    rw [glue_of_mem hT, glue_of_not_mem hS, glue_of_mem hT]
  · rw [glue_of_not_mem hT]
    by_cases hS : i ∈ S
    · rw [glue_of_mem hS, glue_of_mem hS]
    · rw [glue_of_not_mem hS, glue_of_not_mem hS, glue_of_not_mem hT]

#print axioms glue_comm

/-- Updating a link outside `S` commutes with gluing over `S`.

DERIVED: no numeral. -/
theorem glue_update_not_mem {S : Finset ι} {l : ι} (hl : l ∉ S) (W V : ι → Ω) (g : Ω) :
    glue S (Function.update W l g) V = Function.update (glue S W V) l g := by
  funext i
  by_cases hi : i = l
  · subst hi
    rw [glue_of_not_mem hl, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hi]
    by_cases hS : i ∈ S
    · rw [glue_of_mem hS, glue_of_mem hS]
    · rw [glue_of_not_mem hS, glue_of_not_mem hS, Function.update_of_ne hi]

#print axioms glue_update_not_mem

variable [TopologicalSpace Ω]

/-- The double glue is jointly continuous in the two fibres.

DERIVED: no numeral. -/
theorem continuous_glue_glue (S T : Finset ι) (W : ι → Ω) :
    Continuous (fun p : (ι → Ω) × (ι → Ω) => glue T (glue S W p.1) p.2) := by
  refine continuous_pi (fun i => ?_)
  by_cases hT : i ∈ T
  · simp only [glue_of_mem hT]
    exact (continuous_apply i).comp continuous_snd
  · simp only [glue_of_not_mem hT]
    by_cases hS : i ∈ S
    · simp only [glue_of_mem hS]
      exact (continuous_apply i).comp continuous_fst
    · simp only [glue_of_not_mem hS]
      exact continuous_const

#print axioms continuous_glue_glue

end Glue

/-! ## 2. The block's own weight -/

section LocalWeight

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq] [DecidableEq Lk]

/-- The Wilson system's link type is `Lk`; its decidable equality is `Lk`'s. -/
local instance decEqSystemLinkC (bd : Pq → List (Lk × Bool)) :
    DecidableEq (wilsonSystem bd (wilsonDensity (N := N))).Link :=
  inferInstanceAs (DecidableEq Lk)

/-- **A plaquette visits `S`**: its boundary word contains a link of `S`.

DERIVED: no numeral. -/
def Visits (bd : Pq → List (Lk × Bool)) (S : Finset Lk) (p : Pq) : Prop :=
  ∃ l ∈ S, l ∈ (bd p).map Prod.fst

instance (bd : Pq → List (Lk × Bool)) (S : Finset Lk) : DecidablePred (Visits bd S) :=
  fun p => inferInstanceAs (Decidable (∃ l ∈ S, l ∈ (bd p).map Prod.fst))

/-- The action of the plaquettes visiting `S`.

DERIVED: no numeral. -/
def blkLocSum (bd : Pq → List (Lk × Bool)) (S : Finset Lk) (W : Lk → SU N) : ℝ :=
  ∑ p ∈ Finset.univ.filter (Visits bd S), wilsonDensity (wilsonHol bd p W)

/-- The action of the plaquettes not visiting `S`.

DERIVED: no numeral. -/
def blkRestSum (bd : Pq → List (Lk × Bool)) (S : Finset Lk) (W : Lk → SU N) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => ¬ Visits bd S p), wilsonDensity (wilsonHol bd p W)

/-- **The block's own weight** `e^{−β · blkLocSum}`.

DERIVED: no numeral. -/
def blkLocW (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) (W : Lk → SU N) : ℝ :=
  Real.exp (-β * blkLocSum bd S W)

/-- The weight factors at the block: `wt = blkLocW · e^{−β · blkRestSum}`.

DERIVED: no numeral. -/
theorem wt_split_blk (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) (W : Lk → SU N) :
    wt bd β W = blkLocW bd β S W * Real.exp (-β * blkRestSum bd S W) := by
  unfold wt blkLocW
  show Real.exp (-β * (wilsonSystem bd (wilsonDensity (N := N))).action W) = _
  have hsplit : (wilsonSystem bd (wilsonDensity (N := N))).action W
      = blkLocSum bd S W + blkRestSum bd S W := by
    show ∑ p, wilsonDensity (wilsonHol bd p W) = _
    unfold blkLocSum blkRestSum
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
  rw [hsplit, mul_add, Real.exp_add]

#print axioms wt_split_blk

/-- The rest of the action does not read `S`.

DERIVED: no numeral. -/
theorem blkRestSum_glue (bd : Pq → List (Lk × Bool)) (S : Finset Lk) (W V : Lk → SU N) :
    blkRestSum bd S (glue S W V) = blkRestSum bd S W := by
  refine readsNot_glue S (f := blkRestSum bd S) (fun l hl W' g => ?_) W V
  unfold blkRestSum
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hnv : ¬ Visits bd S p := (Finset.mem_filter.mp hp).2
  have hlp : l ∉ (bd p).map Prod.fst := fun h => hnv ⟨l, hl, h⟩
  rw [wilsonHol_update_of_not_mem bd p hlp]

#print axioms blkRestSum_glue

/-- The block's weight does not read a link on no plaquette visiting `S`.

DERIVED: no numeral. -/
theorem blkLocW_update_far (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) {l : Lk}
    (hl : ∀ p, Visits bd S p → l ∉ (bd p).map Prod.fst) (W : Lk → SU N) (g : SU N) :
    blkLocW bd β S (Function.update W l g) = blkLocW bd β S W := by
  unfold blkLocW blkLocSum
  congr 2
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [wilsonHol_update_of_not_mem bd p (hl p (Finset.mem_filter.mp hp).2)]

#print axioms blkLocW_update_far

/-- The block's weight does not read the links of a set `T` that no plaquette visiting `S` contains.

DERIVED: no numeral. -/
theorem blkLocW_glue_other (bd : Pq → List (Lk × Bool)) (β : ℝ) {S T : Finset Lk}
    (h : ∀ p, Visits bd S p → ∀ l ∈ T, l ∉ (bd p).map Prod.fst) (U V : Lk → SU N) :
    blkLocW bd β S (glue T U V) = blkLocW bd β S U :=
  readsNot_glue T (f := blkLocW bd β S)
    (fun l hl W g => blkLocW_update_far bd β S (fun p hp => h p hp l hl) W g) U V

#print axioms blkLocW_glue_other

omit [Fintype Lk] in
/-- The block's weight is continuous.

DERIVED: no numeral. -/
theorem continuous_blkLocW (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) :
    Continuous (blkLocW (N := N) bd β S) := by
  have hS : Continuous (fun W : Lk → SU N =>
      ∑ p ∈ Finset.univ.filter (Visits bd S), wilsonDensity (wilsonHol bd p W)) :=
    continuous_finsetSum _ (fun p _ => MassGap.WilsonAction.continuous_wilsonDensity.comp
      (MassGap.PlaqVariance.continuous_wilsonHol bd p))
  exact Real.continuous_exp.comp (continuous_const.mul hS)

#print axioms continuous_blkLocW

/-- **The block average uses the block's own weight**: the rest of the weight does not read `S` and
cancels.

DERIVED: no numeral. -/
theorem blkAvg_eq_loc (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) (f : (Lk → SU N) → ℝ)
    (W : Lk → SU N) :
    blkAvg bd β S f W
      = (∫ V, f (glue S W V) * blkLocW bd β S (glue S W V)
          ∂(Measure.pi fun _ : Lk => probHaar (SU N)))
        / ∫ V, blkLocW bd β S (glue S W V) ∂(Measure.pi fun _ : Lk => probHaar (SU N)) := by
  have hw : ∀ V, wt bd β (glue S W V)
      = blkLocW bd β S (glue S W V) * Real.exp (-β * blkRestSum bd S W) := by
    intro V
    rw [wt_split_blk bd β S, blkRestSum_glue]
  unfold blkAvg blkNum blkPart
  simp only [hw, ← mul_assoc, integral_mul_const]
  exact mul_div_mul_right _ _ (Real.exp_pos _).ne'

#print axioms blkAvg_eq_loc

/-- **Locality of the block average.** If `f` does not read a link `l ∉ S` lying on no plaquette that
visits `S`, neither does `blkAvg S f`.

DERIVED: no numeral. -/
theorem blkAvg_update_far (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) {l : Lk}
    (hlS : l ∉ S) (hl : ∀ p, Visits bd S p → l ∉ (bd p).map Prod.fst) {f : (Lk → SU N) → ℝ}
    (hf : ∀ W g, f (Function.update W l g) = f W) (W : Lk → SU N) (g : SU N) :
    blkAvg bd β S f (Function.update W l g) = blkAvg bd β S f W := by
  rw [blkAvg_eq_loc, blkAvg_eq_loc]
  simp only [glue_update_not_mem hlS, hf, blkLocW_update_far bd β S hl]

#print axioms blkAvg_update_far

/-- **Two block averages as one double integral.** For disjoint `S`, `T` such that no plaquette visiting
`S` contains a link of `T`, nor conversely.

DERIVED: no numeral. -/
theorem blkAvg_blkAvg_eq (bd : Pq → List (Lk × Bool)) (β : ℝ) {S T : Finset Lk}
    (hST : Disjoint S T) (hTS : ∀ p, Visits bd T p → ∀ l ∈ S, l ∉ (bd p).map Prod.fst)
    (f : (Lk → SU N) → ℝ) (W : Lk → SU N) :
    blkAvg bd β S (blkAvg bd β T f) W
      = (∫ V, ∫ V', f (glue T (glue S W V) V')
            * (blkLocW bd β T (glue T W V') * blkLocW bd β S (glue S W V))
            ∂(Measure.pi fun _ : Lk => probHaar (SU N)) ∂(Measure.pi fun _ : Lk => probHaar (SU N)))
        / ((∫ V', blkLocW bd β T (glue T W V') ∂(Measure.pi fun _ : Lk => probHaar (SU N)))
            * ∫ V, blkLocW bd β S (glue S W V) ∂(Measure.pi fun _ : Lk => probHaar (SU N))) := by
  have hc : ∀ V V', blkLocW bd β T (glue T (glue S W V) V') = blkLocW bd β T (glue T W V') := by
    intro V V'
    rw [glue_comm hST, blkLocW_glue_other bd β hTS]
  have hinner : ∀ V, blkAvg bd β T f (glue S W V)
      = (∫ V', f (glue T (glue S W V) V') * blkLocW bd β T (glue T W V')
            ∂(Measure.pi fun _ : Lk => probHaar (SU N)))
        / ∫ V', blkLocW bd β T (glue T W V') ∂(Measure.pi fun _ : Lk => probHaar (SU N)) := by
    intro V
    rw [blkAvg_eq_loc bd β T f (glue S W V)]
    simp only [hc V]
  have hnum : ∀ V, blkAvg bd β T f (glue S W V) * blkLocW bd β S (glue S W V)
      = (∫ V', f (glue T (glue S W V) V')
            * (blkLocW bd β T (glue T W V') * blkLocW bd β S (glue S W V))
            ∂(Measure.pi fun _ : Lk => probHaar (SU N)))
        / ∫ V', blkLocW bd β T (glue T W V') ∂(Measure.pi fun _ : Lk => probHaar (SU N)) := by
    intro V
    rw [hinner V, div_mul_eq_mul_div, ← integral_mul_const]
    simp only [mul_assoc]
  rw [blkAvg_eq_loc bd β S (blkAvg bd β T f) W]
  simp only [hnum]
  rw [integral_div, div_div]

#print axioms blkAvg_blkAvg_eq

/-- **Block averages over sets sharing no plaquette commute** on continuous functions.

DERIVED: no numeral. -/
theorem blkAvg_comm (bd : Pq → List (Lk × Bool)) (β : ℝ) {S T : Finset Lk} (hST : Disjoint S T)
    (hsep : ∀ p, Visits bd S p → ∀ l ∈ T, l ∉ (bd p).map Prod.fst)
    (hsep' : ∀ p, Visits bd T p → ∀ l ∈ S, l ∉ (bd p).map Prod.fst)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) (W : Lk → SU N) :
    blkAvg bd β S (blkAvg bd β T f) W = blkAvg bd β T (blkAvg bd β S f) W := by
  rw [blkAvg_blkAvg_eq bd β hST hsep' f W, blkAvg_blkAvg_eq bd β hST.symm hsep f W,
    mul_comm (∫ V', blkLocW bd β S (glue S W V') ∂(Measure.pi fun _ : Lk => probHaar (SU N)))]
  congr 1
  have hcont : Continuous (fun p : (Lk → SU N) × (Lk → SU N) =>
      f (glue T (glue S W p.1) p.2)
        * (blkLocW bd β T (glue T W p.2) * blkLocW bd β S (glue S W p.1))) :=
    (hf.comp (continuous_glue_glue S T W)).mul
      (((continuous_blkLocW bd β T).comp ((continuous_glue_right T W).comp continuous_snd)).mul
        ((continuous_blkLocW bd β S).comp ((continuous_glue_right S W).comp continuous_fst)))
  obtain ⟨C, hC⟩ := exists_abs_le hcont
  have hint : Integrable (Function.uncurry fun V V' =>
      f (glue T (glue S W V) V')
        * (blkLocW bd β T (glue T W V') * blkLocW bd β S (glue S W V)))
      ((Measure.pi fun _ : Lk => probHaar (SU N)).prod (Measure.pi fun _ : Lk => probHaar (SU N))) :=
    integrable_of_abs_le _ hcont.measurable hC
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun V' => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun V => ?_))
  show f (glue T (glue S W V) V')
      * (blkLocW bd β T (glue T W V') * blkLocW bd β S (glue S W V))
    = f (glue S (glue T W V') V)
      * (blkLocW bd β S (glue S W V) * blkLocW bd β T (glue T W V'))
  rw [glue_comm hST, mul_comm (blkLocW bd β T (glue T W V'))]

#print axioms blkAvg_comm

end LocalWeight

/-! ## 3. On the torus -/

section Torus

variable {N : ℕ}

/-- **Torus block expectations over sets sharing no plaquette commute** (exactly).

DERIVED: `4` the spacetime dimension; `1` the successor writing the extent. -/
theorem torusBlkCondExp_comm (β : ℝ) (M : ℕ) {S T : Finset (WilsonHypercubic.Link 4 (M + 1))}
    (hST : Disjoint S T)
    (hsep : ∀ p, Visits (bdT M) S p → ∀ l ∈ T, l ∉ (bdT M p).map Prod.fst)
    (hsep' : ∀ p, Visits (bdT M) T p → ∀ l ∈ S, l ∉ (bdT M p).map Prod.fst)
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    torusBlkCondExp β M S (torusBlkCondExp β M T x) = torusBlkCondExp β M T (torusBlkCondExp β M S x) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show blkAvg (bdT M) β S (torusObs M (blkLift β M T (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = blkAvg (bdT M) β T (torusObs M (blkLift β M S (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
  rw [torusObs_blkLift, torusObs_blkLift]
  exact blkAvg_comm (bdT M) β hST hsep hsep' (continuous_torusObs M _) _

#print axioms torusBlkCondExp_comm

/-- **Locality on the torus.** The block expectation keeps `ReadsNot` at a link outside the block lying on
no plaquette that visits it.

DERIVED: `4` the spacetime dimension; `2 * j + 1` the index and `+ 1` its successor. -/
theorem torusBlkCondExp_readsNot_far (β : ℝ) (j : ℕ)
    (S : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1))) {l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)}
    (hlS : l ∉ S) (hl : ∀ p, Visits (bdT (2 * j + 1)) S p → l ∉ (bdT (2 * j + 1) p).map Prod.fst)
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
    (hx : ReadsNot j l (x : C(GibbsSpec.IConf (SU N), ℝ))) :
    ReadsNot j l ((torusBlkCondExp β (2 * j + 1) S x
      : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) : C(GibbsSpec.IConf (SU N), ℝ)) := by
  unfold ReadsNot
  intro W g
  show torusObs (2 * j + 1) (blkLift β (2 * j + 1) S (x : C(GibbsSpec.IConf (SU N), ℝ)))
      (Function.update W l g)
    = torusObs (2 * j + 1) (blkLift β (2 * j + 1) S (x : C(GibbsSpec.IConf (SU N), ℝ))) W
  rw [torusObs_blkLift]
  exact blkAvg_update_far (bdT (2 * j + 1)) β S hlS hl (fun W' g' => hx W' g') W g

#print axioms torusBlkCondExp_readsNot_far

end Torus

end MassGap.BlockCommute
